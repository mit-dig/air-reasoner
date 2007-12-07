"""Amord.py

an attempt at an amord implementation built on cwm

"""

import weakref
#WVD = weakref.WeakValueDictionary
WVD = dict
from collections import deque

import llyn
from formula import Formula, StoredStatement
from term import List, Env

import diag
progress = diag.progress

import tms
import rete

GOAL = 1

debugLevel = 0


class FormulaTMS(object):
    def __init__(self, workingContext):
        self.tms = tms.TMS('FormulaTMS', self.event)
        self.nodes = WVD()
        self.workingContext = workingContext
        workingContext.tms = self
        self.premises = set()
        self.falseAssumptions = set()
        self.contexts = {}
        

    def getAuxTriple(self, auxid, subject, predicate, object, variables):
        if (auxid, subject, predicate, object, variables) not in self.nodes:
            a = tms.Node(self.tms, (auxid, subject, predicate, object, variables))
            self.nodes[(auxid, subject, predicate, object, variables)] = a
        return self.nodes[(auxid, subject, predicate, object, variables)]

    def justifyAuxTriple(self, auxid, subject, predicate, object, variables, rule, antecedents):
        auxnode = self.getAuxTriple(auxid, subject, predicate, object, variables)
        node = self.getTriple(subject, predicate, object)
        a = tms.AndExpression(list(antecedents))
        n = tms.NotExpression(node)
        auxnode.justify(rule, [a,n])


    def getContext(self, id):
        if id not in self.contexts:
            self.contexts[id] = self.workingContext.newFormula()
        return self.contexts[id]

    def getTriple(self, subject, predicate, object, variables=None):
        if (subject, predicate, object, variables) not in self.nodes:
            a = tms.Node(self.tms, (subject, predicate, object, variables))
            self.nodes[(subject, predicate, object, variables)] = a
        return self.nodes[(subject, predicate, object, variables)]

    def getThing(self, thing):
        if thing not in self.nodes:
            a = tms.Node(self.tms, thing)
            self.nodes[thing] = a
        return self.nodes[thing]

    def getStatement(self, (subject, predicate, object, variables)):
        return self.workingContext.statementsMatching(subj=subject, pred=predicate, obj=object)[0]

    def getAuxStatement(self, (auxid, subject, predicate, object, variables)):
        return self.getContext(auxid).statementsMatching(subj=subject, pred=predicate, obj=object)[0]

    def event(self, node, justification):
        if isinstance(justification, tms.Premise):
            self.premises.add(justification)
        if justification is False:
            if isinstance(node.datum, Rule):
                pass # not worth the work
            if isinstance(node.datum, tuple):
                if len(node.datum) == 4:
                    self.workingContext.removeStatement(self.getStatement(node.datum))
                    self.getContext(GOAL).removeStatement(self.getStatement(node.datum))
                else:
                    self.getContext(GOAL).removeStatement(self.getAuxStatement(node.datum))
        if isinstance(node.datum, Rule):
            if debugLevel >= 2:
                if node.datum.goal:
                    progress('\tNow supporting goal rule %s because of %s' % (node.datum, justification))
                else:
                    progress('\tNow supporting rule %s because of %s' % (node.datum, justification))
            node.datum.compileToRete()
            if debugLevel >= 3:
                progress('\t\t ... built rule')
        if isinstance(node.datum, Formula):
            if debugLevel >= 10:
                progress('Now supporting %s because of %s' % (node.datum, justification))
            self.workingContext.loadFormulaWithSubstitution(node.datum)
        if isinstance(node.datum, tuple):
#            print '\t ... now supporting %s because of %s' % (node, justification)
            if len(node.datum) == 4:
                triple = node.datum[:3]
                variables = node.datum[3]
                if variables is None:
                    self.workingContext.add(*triple)                
                    self.getContext(GOAL).add(*triple)
                else:  # slow path --- do we need it?
                    s, p, o = triple
                    s1 = self.workingContext._buildStoredStatement(subj=s,
                                                                 pred=p,
                                                                 obj=o,
                                                                why=None)
                    if isinstance(s1, int):
                        raise TypeError(node)
                    s1.variables = v
                    result = self.workingContext. _addStatement(s1)
                    
                    s2 = getContext(GOAL)._buildStoredStatement(subj=s,
                                                                 pred=p,
                                                                 obj=o,
                                                                why=None)
                    if isinstance(s2, int):
                        raise TypeError(node)
                    s2.variables = v
                    result = self.getContext(GOAL). _addStatement(s1)
            else:
                if debugLevel > 7:
                    progress('\t ... now supporting goal %s because of %s' % (node, justification))
                c, s, p, o, v = node.datum
                statement = self.getContext(c)._buildStoredStatement(subj=s,
                                                                 pred=p,
                                                                 obj=o,
                                                                why=None)
                if isinstance(statement, int):
                    raise TypeError(node)
                statement.variables = v
                result = self.getContext(c). _addStatement(statement)
#                print 'added %s, a total of %s statements' % (statement, result)
                
        

def canonicalizeVariables(statement, variables):
    subj, pred, obj = statement.spo()
    store = statement.context().store
    varMapping = {}
    count = [0]
    def newVariable():
        count[0] += 1
        return store.newSymbol('http://example.com/vars/#variable%s' % count[0])
    def canNode(node):
        if node in varMapping:
            return varMapping[node]
        if node in variables:
            varMapping[node] = newVariable()
            return varMapping[node]
        if isinstance(node, List):
            return node.store.newList([canNode(x) for x in node])
        if isinstance(node, Formula):
            if node.occurringIn(variables):
                raise ValueError(node)
            return node
        return node
    return (canNode(subj), canNode(pred), canNode(obj)), frozenset(varMapping.values())

class Assertion(object):
    def __init__(self, pattern, support=None, rule=None):
        self.pattern = pattern
        self.support = support
        self.rule = rule

    def substitution(self, bindings):
        if self.support is None:
            support = None
        else:
            supportList = []
            for x in self.support:
                if isinstance(x, frozenset):
                    supportList.append(x)
                else:
                    supportList.append(x.substitution(bindings))
            support = frozenset(supportList)

        return Assertion(self.pattern.substitution(bindings), support, self.rule)

    def __repr__(self):
        return 'Assertion(%s,%s,%s)' % (self.pattern, self.support, self.rule)

    def __eq__(self, other):
        return isinstance(other, Assertion) and self.pattern == other.pattern

    def __hash__(self):
        return hash((self.pattern, self.__class__)) 

    
        

class AuxTripleJustifier(object):
    def __init__(self, tms, *args):
        self.tms = tms
        self.args = args

    def __call__(self):
        self.tms.justifyAuxTriple(*self.args)


class Rule(object):
    def __init__(self, eventLoop, tms, vars, label, pattern, result, goal=False, matchName=None, sourceNode=None):
        self.generatedLabel = False
        if label is None or label=='None':
            self.generatedLabel = True
            if not goal:
                label = '[pattern=%s]' % pattern
            else:
                label= '[goal=%s]' % pattern
        self.label = label
        self.eventLoop = eventLoop
        self.success = False
        self.tms = tms
        self.vars = vars | pattern.existentials()
        self.pattern = pattern
        self.patternToCompare = frozenset([x.spo() for x in pattern])
        self.result = result
        self.goal = goal
        self.matchName = matchName
        self.sourceNode = sourceNode
        if debugLevel > 15:        
            print '''just made a rule, with
        tms=%s,
        vars=%s
        label=%s
        pattern=%s
        result=%s
        matchName=%s''' % (tms, self.vars, label, pattern, result, matchName)


    def __eq__(self, other):
        return isinstance(other, Rule) and \
               self.eventLoop is other.eventLoop and \
               self.tms is other.tms and \
               self.goal == other.goal and \
               self.vars == other.vars and \
               self.patternToCompare == other.patternToCompare and \
               self.result == other.result and \
               self.matchName == other.matchName

    def __hash__(self):
        return hash((Rule, self.eventLoop, self.tms, self.vars, self.pattern, frozenset(self.result), self.goal, self.matchName))

    def __repr__(self):
        return '%s with vars %s' % (self.label.encode('utf_8'), self.vars)

    def compileToRete(self):
        patterns = self.pattern.statements
        if self.goal:
            workingContext = self.tms.getContext(GOAL)
        else:
            workingContext = self.tms.workingContext
            for triple in patterns:
                    (s, p, o), newVars = canonicalizeVariables(triple, self.vars)
                    self.eventLoop.add(AuxTripleJustifier(self.tms, GOAL, s, p, o, newVars, self.label, [self.tms.getThing(self)]))
        index = workingContext._index
        bottomBeta = rete.compilePattern(index, patterns, self.vars, buildGoals=False, goalPatterns=self.goal)
        trueBottom =  rete.ProductionNode(bottomBeta, self.onSuccess, self.onFailure)
        return trueBottom

    def addTriple(self, triple):
        self.tms.getTriple(*triple.spo()).assume()
    def retractTriple(self, triple):
        self.tms.getTriple(*triple.spo()).retract()

    def onSuccess(self, (triples, environment, penalty)):
        self.success = True
        def internal():
            if debugLevel > 12:
                progress('%s succeeded, with triples %s and env %s' % (self.label, triples, env))
            env = environment
            triplesTMS = []
            goals = []
            unSupported = []
            for triple in triples:
                t = self.tms.getTriple(*triple.spo())
                if t.supported:
                    triplesTMS.append(t)
                else:
                    t2 = self.tms.getAuxTriple(GOAL, triple.subject(), triple.predicate(), triple.object(), triple.variables)
                    if t2.supported:
                        goals.append((triple, t2))
                    else:
                        unSupported.append(triple)

            if self.matchName:
                if self.matchName in env:
                    return
                env = env.bind(self.matchName, (frozenset(triplesTMS + [x[1] for x in goals]), Env()))
            if goals and unSupported:
                raise RuntimeError(goals, unSupported) #This will never do!
            elif goals:
                if not self.goal:
                    raise RuntimeError('how did I get here?\nI matched %s, which are goals, but I don\'t want goals' % goals)
#                print 'we goal succeeded! %s, %s' % (triples, self.result)
                envDict = env.asDict()
                for triple, _ in goals:
                    assert not triple.variables.intersection(env.keys())
                    newVars = triple.variables.intersection(envDict.values())
                    if newVars:
                        raise NotImplementedError("I don't know how to add variables")
                
                for r in self.result:
                    r12 = r.substitution(env.asDict())
                    r2 = r12.pattern
                    support = r12.support
                    ruleId = r12.rule
                    assert isinstance(r2, Rule) or not r2.occurringIn(self.vars), (r2, env, penalty, self.label)
    #            print '   ...... so about to assert %s' % r2
                    r2TMS = self.tms.getThing(r2)
                    if support is None:
                        r2TMS.justify(self.label, triplesTMS + [self.tms.getThing(self)])
                    else:
                        supportTMS = reduce(frozenset.union, support, frozenset())
                        r2TMS.justify(ruleId, supportTMS)
                    assert self.tms.getThing(self).supported
                    assert r2TMS.supported                
#                raise NotImplementedError(goals) #todo: handle goals
            elif unSupported:
                raise RuntimeError(triple, self)
                for triple in unSupported:
                    assert isinstance(triple, rete.BogusTriple), triple
                    boundTriple = triple.substitution(env.asDict())
                    (s, p, o), newVars = canonicalizeVariables(boundTriple, self.vars)
                    self.tms.justifyAuxTriple(GOAL, s, p, o, newVars, self.label, [self.tms.getThing(self)])
            else:
                if self.goal:
                    return
#                print 'we succeeded! %s, %s' % (triples, self.result)
                for r in self.result:
                    r12 = r.substitution(env.asDict())
                    r2 = r12.pattern
                    support = r12.support
                    ruleId = r12.rule
                    assert isinstance(r2, Rule) or not r2.occurringIn(self.vars), (r2, env, penalty, self.label)
    #            print '   ...... so about to assert %s' % r2
                    r2TMS = self.tms.getThing(r2)
                    if support is None:
                        r2TMS.justify(self.label, triplesTMS + [self.tms.getThing(self)])
                    else:
                        supportTMS = reduce(frozenset.union, support, frozenset())
                        r2TMS.justify(ruleId, supportTMS)
                    assert self.tms.getThing(self).supported
                    assert r2TMS.supported
        self.eventLoop.add(internal)
    def onFailure(self):
        self.success = False
        def internal():
            if self.success:
                return
#        print '%s failed, so about to do %s' % (self.label, self.alternate)
##            for r in self.alternate:
##                r2 = r
###            print '   ...... so about to assert %s' % r2
##                r2TMS = self.tms.getThing(r2)
##                r2TMS.justify(self.label, [self.tms.getThing(self)])
##                assert self.tms.getThing(self).supported
##                assert r2TMS.supported
##        if self.alternate:
##            self.eventLoop.addAlternate(internal)

    def substitution(self, env):
        pattern = self.pattern.substitution(env)
        result = [x.substitution(env) for x in self.result]
        if self.generatedLabel:
            label = None
        else:
            label = self.label
        return self.__class__(self.eventLoop, self.tms, self.vars, label, pattern, result, self.goal, self.matchName)

    @classmethod
    def compileFromTriples(cls, eventLoop, tms, F, node, goal=False, vars=frozenset()):
        assert tms is not None
        rdfs = F.newSymbol('http://www.w3.org/2000/01/rdf-schema')
        rdf = F.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
        p = F.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/air')

        vars = vars.union(F.each(subj=node, pred=p['variable']))
        
        label = F.the(subj=node, pred=p['label'])
        pattern = F.the(subj=node, pred=p['pattern'])
        subrules = [Assertion(cls.compileFromTriples(eventLoop, tms, F, x, vars=vars))
                    for x in F.each(subj=node, pred=p['rule'])]
        goal_subrules = [Assertion(cls.compileFromTriples(eventLoop, tms, F, x, goal=True, vars=vars))
                         for x in F.each(subj=node, pred=p['goal-rule'])]
        simple_assertions = F.each(subj=node, pred=p['assert'])
        complex_assertions = F.each(subj=node, pred=p['assertion'])
        assertions = []
        for assertion in simple_assertions:
            assertions.append(Assertion(assertion))
        for assertion in complex_assertions:
            statement = F.the(subj=assertion, pred=p['statement'])
            justNode = F.the(subj=assertion, pred=p['justification'])
            antecedents = frozenset(F.each(subj=justNode, pred=p['antecedent']))
            rule_id = F.the(subj=justNode, pred=p['rule-id'])
            assertions.append(Assertion(statement, antecedents, rule_id))
        matchedGraph = F.the(subj=node, pred=p['matched-graph'])
        
        self = cls(eventLoop, tms,
                   vars, unicode(label),
                   pattern,
                   subrules + assertions + goal_subrules,
                   goal=goal, matchName=matchedGraph, sourceNode=node)
        return self

    @classmethod
    def compileCwmRule(cls, eventLoop, tms, F, triple):
        assert tms is not None
        label = "Rule from cwm with pattern %s" % triple.subject()
        pattern = triple.subject()
        assertions = [triple.object()]
        vars = frozenset(F.universals())
        self = cls(eventLoop, tms, vars, unicode(label), pattern, assertions, [])
        return self


    @classmethod
    def compileFormula(cls, eventLoop, formulaTMS, pf):
        rdf = pf.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
        p = pf.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/air')
        policies = pf.each(pred=rdf['type'], obj=p['Policy'])
        globalVars = frozenset(pf.each(pred=rdf['type'], obj=p['Variable']))
        cwm_rules = [cls.compileCwmRule(eventLoop,
                                        formulaTMS,
                                        pf,
                                        x)
                     for x in pf.each(pred=pf.store.implies)]
        rules = [cls.compileFromTriples(eventLoop,
                                                             formulaTMS,
                                                             pf,
                                                             x,
                                                             vars=globalVars.union(pf.each(subj=y, pred=p['variable'])))
                          for x in reduce(list.__add__, [pf.each(subj=y, pred=p['rule']) for y in policies], [])]
        goal_rules = [cls.compileFromTriples(eventLoop,
                                                             formulaTMS,
                                                             pf,
                                                             x,
                                                             vars=globalVars.union(pf.each(subj=y, pred=p['variable'])))
                          for x in reduce(list.__add__, [pf.each(subj=y, pred=p['goal-rule']) for y in policies], [])]
        return rules, goal_rules, cwm_rules               


class EventLoop(object):
    def __init__(self):
        self.events = deque()
        self.alternateEvents = deque()

    def add(self, event):
        self.events.appendleft(event)

    def addAlternate(self, event):
        self.alternateEvents.appendleft(event)

    def next(self):
        if self.events:
            return self.events.pop()()
        return self.alternateEvents.pop()()

    def __len__(self):
        return len(self.events) + len(self.alternateEvents)


def supportTrace(tmsNodes):
    pending = set()
    reasons = {}
    premises = set()
    def nf(self):
#            print 'running nf(%s), %s, %s' % (self, self.__class__, self.justifications)
        if self in reasons:
            return True
        if self in pending:
            return False
        if self.assumed():
            premises.add(self)
            reasons[self] = '[premise]'
        pending.add(self)
        for just in self.justifications:
            if just.evaluate(nf):
                reasons[self] = just
                return True
        return False
    for tmsNode in tmsNodes:
        a = nf(tmsNode)
    return reasons, premises

def removeFormulae(reasons, premises):
    newReasons = {}
    for node, reason in reasons.items():
        if node in premises:
            newReasons[node] = reason
        else:
            nodes = reasons[node].expression.nodes()
            if len(nodes) == 1:
                parent = list(nodes)[0]
                if isinstance(parent.datum, Formula):
                    newReasons[node] = reasons[parent]
                else:
                    newReasons[node] = reason
            else:
                newReasons[node] = reason
    return newReasons

def removeBaseRules(baseRule, reasons, premises):
    newReasons = {}
    for node, reason in reasons.items():
        if isinstance(node.datum, Rule):
            if node.datum.sourceNode is not None and baseRule(node.datum.sourceNode):
                pass # What goes here?
        else:
            newReasons[node] = reason

def simpleTraceOutput(tmsNodes, reasons, premises):
    done = set()
    strings = []
    def nf2(self):
        if self in done:
            return True
        done.add(self)
        if self in premises:
            retVal = True
            strings.append('%s [premise]' % self)
        else:
            retVal = reasons[self].evaluate(nf2)
            strings.append('%s <= (%s)' % (self, ', '.join([str(x) for x in reasons[self].expression.nodes()])))
        return retVal
    for tmsNode in tmsNodes:
        nf2(tmsNode)
    return strings


def setupTMS(store):
    workingContext = store.newFormula()
    workingContext.keepOpen = True
    formulaTMS = FormulaTMS(workingContext)
    return formulaTMS
    

def loadFactFormula(formulaTMS, uri, closureMode=""):
    store = formulaTMS.workingContext.store
    f = store.newFormula()
    f.setClosureMode(closureMode)
    f = store.load(uri, openFormula=f)
    formulaTMS.getThing(f).assume()
    return f

    

baseFactsURI = 'http://dig.csail.mit.edu/TAMI/2007/amord/base-assumptions.ttl'
baseRulesURI = 'http://dig.csail.mit.edu/TAMI/2007/amord/base-rules.ttl'

def testPolicy(logURIs, policyURIs):
    import time
    store = llyn.RDFStore()
    formulaTMS = setupTMS(store)
    workingContext = formulaTMS.workingContext

## We are done with cwm setup
    startTime = time.time()

    logFormulae = []
    for logURI in logURIs:
        logFormulae.append(loadFactFormula(formulaTMS, logURI, "")) # should it be "p"?
    baseFactsFormula = loadFactFormula(formulaTMS, baseFactsURI)

    eventLoop = EventLoop()

    policyFormulae = []
    for policyURI in policyURIs:
        policyFormulae.append(store.load(policyURI))
    baseRulesFormula = store.load(baseRulesURI)

#    rdfsRulesFormula = store.load('http://python-dlp.googlecode.com/files/pD-rules.n3')
    
    rdf = workingContext.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
    owl = workingContext.newSymbol('http://www.w3.org/2002/07/owl')
    p = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/air')
    u = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/s0/university')
    s9 = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-policy')
    s9Log = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-log')


#    AIRFormula = store.load(p.uriref() + '.ttl')
#    formulaTMS.getThing(AIRFormula).assume()
        
#    formulaTMS.getTriple(p['data'], rdf['type'], owl['TransitiveProperty']).assume()

    compileStartTime = time.time()

    rdfsRules = [] #[Rule.compileCwmRule(eventLoop, formulaTMS, rdfsRulesFormula, x) for x in rdfsRulesFormula.statementsMatching(pred=store.implies)]



    allRules = []
    allGoalRules = []
    for pf in policyFormulae + [baseRulesFormula]:    
        rules, goal_rules, cwm_rules = Rule.compileFormula(eventLoop, formulaTMS, pf)
        allRules += rules
        allGoalRules += goal_rules
    print 'rules = ', allRules
    print 'goal rules = ', goal_rules
    ruleAssumptions = []
    for rule in rdfsRules + allRules + allGoalRules:
        a  = formulaTMS.getThing(rule)
        ruleAssumptions.append(a)
        a.assume()

    eventStartTime = time.time()
    Formula._isReasoning = True
    while eventLoop:
        eventLoop.next()
    Formula._isReasoning = False        

# See how long it took (minus output)
    now = time.time()
    totalTime = now - startTime
    print 'time reasoning took=', totalTime
    print '  of which %s was after loading, and %s was actual reasoning' % (now-compileStartTime, now-eventStartTime)

#    rete.printRete()
    triples = list(workingContext.statementsMatching(pred=p['compliant-with']) +
                   workingContext.statementsMatching(pred=p['non-compliant-with']))
    if triples:
        print 'I can prove the following compliance statements:'
    else:
        print 'There is nothing to prove'
        
    tmsNodes = [formulaTMS.getTriple(triple.subject(), triple.predicate(), triple.object(), None) for triple in triples]
    reasons, premises = supportTrace(tmsNodes)
    strings = simpleTraceOutput(tmsNodes, reasons, premises)
    print '\n'.join(strings)
            
    return workingContext.n3String()


knownScenarios = {
    's0' : ( ['http://dig.csail.mit.edu/TAMI/2007/s0/log.n3'],
             ['http://dig.csail.mit.edu/TAMI/2007/s0/mit-policy.n3'] ),
    's0Local' : ( ['../../s0/log.n3'],
                  [  '../../s0/mit-policy.n3'] )

}

def runScenario(s):
    if s not in knownScenarios:
        raise ValueError("I don't know about scenario %s" % s)
    facts, rules = knownScenarios[s]
    return testPolicy(facts, rules)

def main():
    from optparse import OptionParser
    usage = "usage: %prog [options] scenarioName"
    parser = OptionParser(usage)
    parser.add_option('--profile', dest="profile", action="store_true", default=False,
                      help="""Instead of displaying output, display profile information.
                      This requires the hotshot module, and is a bit slow
                      """)

    (options, args) = parser.parse_args()
    if not args:
        args = ['s0']
    call = lambda : runScenario(args[0])
    if options.profile:
        stdout = sys.stdout
        import hotshot, hotshot.stats
        import tempfile
        fname = tempfile.mkstemp()[1]
        print fname
        sys.stdout = null = file('/dev/null', 'w')
        profiler = hotshot.Profile(fname)
        profiler.runcall(call)
        profiler.close()
        sys.stdout = stdout
        null.close()
        print 'done running. Ready to do stats'
        stats = hotshot.stats.load(fname)
        stats.strip_dirs()
        stats.sort_stats('cumulative', 'time', 'calls')
        stats.print_stats(60)
        stats.sort_stats('time', 'cumulative', 'calls')
        stats.print_stats(60)
    else:
        print call()

        


if __name__ == '__main__':
    main()

