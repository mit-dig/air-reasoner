"""Amord.py

an attempt at an amord implementation built on cwm

"""

import weakref
#WVD = weakref.WeakValueDictionary
WVD = dict
from collections import deque

import llyn
from formula import Formula, StoredStatement
from term import List

import tms
import rete

GOAL = 1


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
        if variables.intersection([subject, predicate, object]):
            auxnode.justify(rule, list(antecedents))
        else:
            node = self.getTriple(subject, predicate, object)
            a = tms.AndExpression(list(antecedents))
            n = tms.NotExpression(node)
            auxnode.justify(rule, [a,n])


    def getContext(self, id):
        if id not in self.contexts:
            self.contexts[id] = self.workingContext.newFormula()
        return self.contexts[id]

    def getTriple(self, subject, predicate, object):
        if (subject, predicate, object) not in self.nodes:
            a = tms.Node(self.tms, (subject, predicate, object))
            self.nodes[(subject, predicate, object)] = a
        return self.nodes[(subject, predicate, object)]

    def getThing(self, thing):
        if thing not in self.nodes:
            a = tms.Node(self.tms, thing)
            self.nodes[thing] = a
        return self.nodes[thing]

    def getStatement(self, (subject, predicate, object)):
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
                if len(node.datum) == 3:
                    self.workingContext.removeStatement(self.getStatement(node.datum))
                    self.getContext(GOAL).removeStatement(self.getStatement(node.datum))
                else:
                    self.getContext(GOAL).removeStatement(self.getAuxStatement(node.datum))
        if isinstance(node.datum, Rule):
            if node.datum.goal:
                print 'Now supporting GOAL rule %s because of %s' % (node.datum, justification)
            else:
                print 'Now supporting rule %s because of %s' % (node.datum, justification)
            node.datum.compileToRete()
        if isinstance(node.datum, Formula):
#            print 'Now supporting %s because of %s' % (node.datum, justification)
            self.workingContext.loadFormulaWithSubstitution(node.datum)
        if isinstance(node.datum, tuple):
#            print '\t ... now supporting %s because of %s' % (node, justification)
            if len(node.datum) == 3:
                self.workingContext.add(*node.datum)
                self.getContext(GOAL).add(*node.datum)
            else:
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


class Rule(object):
    def __init__(self, eventLoop, tms, vars, label, pattern, result, goal=False):
        self.generatedLabel = False
        if label is None or label=='None':
            self.generatedLabel = True
            label = '[pattern=%s]' % pattern.statements
        self.label = label
        self.eventLoop = eventLoop
        self.success = False
        self.tms = tms
        self.vars = vars | pattern.existentials()
        self.pattern = pattern
        self.result = result
        self.goal = goal
##        print '''just made a rule, with
##    tms=%s,
##    vars=%s
##    label=%s
##    pattern=%s
##    result=%s ''' % (tms, self.vars, label, pattern, result)

    def __eq__(self, other):
        return isinstance(other, Rule) and \
               self.eventLoop is other.eventLoop and \
               self.tms is other.tms and \
               self.vars == other.vars and \
               self.pattern == other.pattern and \
               self.result == other.result and \
               self.goal == other.goal

    def __hash__(self):
        return hash((self.eventLoop, self.tms, self.vars, self.pattern, frozenset(self.result), self.goal))

    def __repr__(self):
        return '%s with vars %s' % (self.label.encode('utf_8'), self.vars)

    def compileToRete(self):
        patterns = self.pattern.statements
        if self.goal:
            workingContext = self.tms.getContext(GOAL)
        else:
            workingContext = self.tms.workingContext
            # We are on! make goals!
            for statement in patterns:
                (s, p, o), newVars = canonicalizeVariables(statement, self.vars)
                self.tms.justifyAuxTriple(GOAL, s, p, o, newVars, self.label, [self.tms.getThing(self)])
            
        index = workingContext._index
        bottomBeta = rete.compilePattern(index, patterns, self.vars, buildGoals=False, goalPatterns=self.goal)
        trueBottom =  rete.ProductionNode(bottomBeta, self.onSuccess, self.onFailure)
        return trueBottom

    def addTriple(self, triple):
        self.tms.getTriple(*triple.spo()).assume()
    def retractTriple(self, triple):
        self.tms.getTriple(*triple.spo()).retract()

    def onSuccess(self, (triples, env, penalty)):
        self.success = True
        def internal():
#            print '%s succeeded, with triples %s and env %s' % (self.label, triples, env)
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
            if goals and unSupported:
                raise RuntimeError(goals, unSupported) #This will never do!
            elif goals:
                if not self.goal:
                    raise RuntimeError('how did I get here?')
#                print 'we goal succeeded! %s, %s' % (triples, self.result)
                envDict = env.asDict()
                for triple, _ in goals:
                    assert not triple.variables.intersection(env.keys())
                    newVars = triple.variables.intersection(envDict.values())
                    if newVars:
                        raise NotImplementedError("I don't know how to add variables")
                
                for r in self.result:
                    r2 = r.substitution(env.asDict())
                    assert isinstance(r2, Rule) or not r2.occurringIn(self.vars), (r2, env, penalty, self.label)
    #            print '   ...... so about to assert %s' % r2
                    r2TMS = self.tms.getThing(r2)
                    r2TMS.justify(self.label, triplesTMS + [self.tms.getThing(self)])
                    assert self.tms.getThing(self).supported
                    assert r2TMS.supported                
#                raise NotImplementedError(goals) #todo: handle goals
            elif unSupported:
                raise RuntimeError("I should no longer be able to get here")
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
                    r2 = r.substitution(env.asDict())
                    assert isinstance(r2, Rule) or not r2.occurringIn(self.vars), (r2, env, penalty, self.label)
    #            print '   ...... so about to assert %s' % r2
                    r2TMS = self.tms.getThing(r2)
                    r2TMS.justify(self.label, triplesTMS + [self.tms.getThing(self)])
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
        return self.__class__(self.eventLoop, self.tms, self.vars, label, pattern, result, self.goal)

    @classmethod
    def compileFromTriples(cls, eventLoop, tms, F, node, goal=False, vars=frozenset()):
        assert tms is not None
        rdfs = F.newSymbol('http://www.w3.org/2000/01/rdf-schema')
        rdf = F.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
        p = F.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/air')

        vars = vars.union(F.each(subj=node, pred=p['variable']))
        
        label = F.the(subj=node, pred=p['label'])
        pattern = F.the(subj=node, pred=p['pattern'])
        subrules = [cls.compileFromTriples(eventLoop, tms, F, x, vars=vars) for x in F.each(subj=node, pred=p['rule'])]
        goal_subrules = [cls.compileFromTriples(eventLoop, tms, F, x, goal=True, vars=vars) for x in F.each(subj=node, pred=p['goal-rule'])]
        assertions = F.each(subj=node, pred=p['assert'])
        
        self = cls(eventLoop, tms, vars, unicode(label), pattern, subrules + assertions + goal_subrules, goal=goal)
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

def testPolicy(logURI, policyURI):
    import time
    store = llyn.RDFStore()
    workingContext = store.newFormula()
    workingContext.keepOpen = True
    formulaTMS = FormulaTMS(workingContext)

## We are done with cwm setup
    startTime = time.time()

    logFormula = store.newFormula()
    logFormula.setClosureMode("") # should it be "p"?
    logFormula = store.load(logURI, openFormula=logFormula)
    formulaTMS.getThing(logFormula).assume()


    eventLoop = EventLoop()

    policyFormula = store.load(policyURI)
    baseRulesFormula = store.load('http://dig.csail.mit.edu/TAMI/2007/amord/base-rules.ttl')

#    rdfsRulesFormula = store.load('http://python-dlp.googlecode.com/files/pD-rules.n3')
    
    rdf = policyFormula.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
    owl = policyFormula.newSymbol('http://www.w3.org/2002/07/owl')
    p = policyFormula.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/air')
    u = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/s0/university')
    s9 = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-policy')
    s9Log = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-log')


#    AIRFormula = store.load(p.uriref() + '.ttl')
#    formulaTMS.getThing(AIRFormula).assume()
        
    formulaTMS.getTriple(p['data'], rdf['type'], owl['TransitiveProperty']).assume()
    

    compileStartTime = time.time()

    rdfsRules = [] #[Rule.compileCwmRule(eventLoop, formulaTMS, rdfsRulesFormula, x) for x in rdfsRulesFormula.statementsMatching(pred=store.implies)]
    totalRules = []
    for rf in (policyFormula, baseRulesFormula):
        globalVars = frozenset(rf.each(pred=rdf['type'], obj=p['Variable']))
        policies = rf.each(pred=rdf['type'], obj=p['Policy'])
    
        rules = [Rule.compileFromTriples(eventLoop,
                  formulaTMS,
                  rf,
                  x,
                  goal=False,
                  vars=globalVars.union(rf.each(subj=y, pred=p['variable'])))
                  for x in reduce(list.__add__,
                                  [rf.each(subj=y,
                                           pred=p['rule'])
                                   for y in policies],
                                [])]
        goal_rules = [Rule.compileFromTriples(eventLoop,
                  formulaTMS,
                  rf,
                  x,
                  goal=True,
                  vars=globalVars.union(rf.each(subj=y, pred=p['variable'])))
                for x in reduce(list.__add__,
                                [rf.each(subj=y,
                                         pred=p['goal-rule'])
                                 for y in policies],
                             [])]
        totalRules += rules
        totalRules += goal_rules
    print 'rules = ', totalRules
    ruleAssumptions = []
    for rule in rdfsRules + totalRules:
        a  = formulaTMS.getThing(rule)
        ruleAssumptions.append(a)
        a.assume()

    eventStartTime = time.time()

    while eventLoop:
        eventLoop.next()

# See how long it took (minus output)
    now = time.time()
    totalTime = now - startTime
    print 'time reasoning took=', totalTime
    print '  of which %s was after loading, and %s was actual reasoning' % (now-compileStartTime, now-eventStartTime)

#    rete.printRete()
    triples = list(workingContext.statementsMatching(pred=p['compliant-with']))
    supportDict = {}
    if triples:
        print 'I can prove the following compliance statements:'
    else:
        print 'There is nothing to prove'
    for triple in triples:
        print '\n\nready to prove %s\n' % (triple.spo(),)
        tmsNode = formulaTMS.getTriple(*triple.spo())
        def f(consequent, just, antecedents, support):
                if consequent is tmsNode:
                    supportDict[tmsNode] = formulaTMS.falseAssumptions & support
        tmsNode.walkSupport(f)
        if supportDict[tmsNode]:
            tmsNode.why()
        else:
            print "\nI'll print the proof once we give up on false hypotheses"
        
    for falsehood in formulaTMS.falseAssumptions:
        falsehood.retract()

    for triple in triples:
        tmsNode = formulaTMS.getTriple(*triple.spo())
        if not tmsNode.supported:
            print '\n\nHowever, we made false assumptions to get %s' % (triple.spo(),)
            print '\t', supportDict[tmsNode]
            print 'if those were true, we would have gotten what we wanted'
        else:
            print '\n\nThe real proof of %s is as follows' % (triple.spo(),)
            tmsNode.why()
    
            
    return workingContext.n3String()


if __name__ == '__main__':
#    print testPolicy('http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-log.n3',
#                     'http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-policy.n3')
    print testPolicy('http://dig.csail.mit.edu/TAMI/2007/s0/log.n3',
                     'http://dig.csail.mit.edu/TAMI/2007/s0/mit-policy.n3')
##    print testPolicy('../../s0/log.n3',
##                     '../../amord/base-rules.ttl')
