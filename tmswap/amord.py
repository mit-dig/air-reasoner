"""Amord.py

an attempt at an amord implementation built on cwm

"""

import weakref
WVD = weakref.WeakValueDictionary
#WVD = dict
from collections import deque

import llyn
from formula import Formula, StoredStatement

import tms
import rete


class FormulaTMS(object):
    def __init__(self, workingContext):
        self.tms = tms.TMS('FormulaTMS', self.event)
        self.nodes = WVD()
        self.workingContext = workingContext
        workingContext.tms = self
        self.premises = set()
        self.falseAssumptions = set()
        

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

    def event(self, node, justification):
        if isinstance(justification, tms.Premise):
            self.premises.add(justification)
        if justification is False:
            if isinstance(node.datum, Rule):
                pass # not worth the work
            if isinstance(node.datum, tuple):
                self.workingContext.removeStatement(self.getStatement(node.datum))
        if isinstance(node.datum, Rule):
#            print 'Now supporting rule %s because of %s' % (node.datum.label, justification)
            node.datum.compileToRete()
        if isinstance(node.datum, Formula):
#            print 'Now supporting %s because of %s' % (node.datum, justification)
            self.workingContext.loadFormulaWithSubstitution(node.datum)
        if isinstance(node.datum, tuple):
#            print '\t ... now supporting %s because of %s' % (node, justification)
            self.workingContext.add(*node.datum)
        


class Rule(object):
    def __init__(self, eventLoop, tms, vars, label, pattern, result, alternate):
        self.label = label
        self.eventLoop = eventLoop
        self.success = False
        self.tms = tms
        self.vars = vars | pattern.existentials()
        self.pattern = pattern
        self.result = result
        self.alternate = alternate
##        print '''just made a rule, with
##    tms=%s,
##    vars=%s
##    label=%s
##    pattern=%s
##    result=%s
##    alternate=%s''' % (tms, self.vars, label, pattern, result, alternate)

    def compileToRete(self):
        workingContext = self.tms.workingContext
        index = workingContext._index
        patterns = self.pattern.statements
        bottomBeta = rete.compilePattern(index, patterns, self.vars)
        trueBottom =  rete.ProductionNode(bottomBeta, self.onSuccess, self.onFailure)
        return trueBottom

    def onSuccess(self, (triples, env)):
        self.success = True
        def internal():
#        print '%s succeeded, with triples %s and env %s' % (self.label, triples, env)
            for r in self.result:
                r2 = r.substitution(env.asDict())
#            print '   ...... so about to assert %s' % r2
                r2TMS = self.tms.getThing(r2)
                triplesTMS = [self.tms.getTriple(*x.spo()) for x in triples]
                r2TMS.justify(self.label, triplesTMS + [self.tms.getThing(self)])
                assert self.tms.getThing(self).supported
                for x in triplesTMS:
                    if not x.supported:
                        x.assume()
                        self.tms.falseAssumptions.add(x)
                assert r2TMS.supported
        self.eventLoop.add(internal)
    def onFailure(self):
        self.success = False
        def internal():
            if self.success:
                return
#        print '%s failed, so about to do %s' % (self.label, self.alternate)
            for r in self.alternate:
                r2 = r
#            print '   ...... so about to assert %s' % r2
                r2TMS = self.tms.getThing(r2)
                r2TMS.justify(self.label, [self.tms.getThing(self)])
                assert self.tms.getThing(self).supported
                assert r2TMS.supported
        if self.alternate:
            self.eventLoop.addAlternate(internal)

    def substitution(self, env):
        pattern = self.pattern.substitution(env)
        result = [x.substitution(env) for x in self.result]
        alternate = [x.substitution(env) for x in self.alternate]
        return self.__class__(self.eventLoop, self.tms, self.vars, self.label, pattern, result, alternate)

    @classmethod
    def compileFromTriples(cls, eventLoop, tms, F, node):
        assert tms is not None
        rdfs = F.newSymbol('http://www.w3.org/2000/01/rdf-schema')
        rdf = F.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
        p = F.newSymbol('http://dig.csail.mit.edu/TAMI/2007/rei+/policy')
        
        label = F.the(subj=node, pred=rdfs['label'])
        pattern = F.the(subj=node, pred=p['pattern'])
        subrules = [cls.compileFromTriples(eventLoop, tms, F, x) for x in F.each(subj=node, pred=p['subrule'])]
        assertions = F.each(subj=node, pred=p['assert'])
        alternate = F.each(subj=node, pred=p['alt'])
        alternateAssertions = []
        for x in alternate:
            alternateAssertions.extend(F.each(subj=x, pred=p['assert']))
        

        alternateSubruleNodes = []
        for x in [F.each(subj=y, pred=p['subrule']) for y in alternate]:
            alternateSubruleNodes.extend(x)
        alternateSubrules = [cls.compileFromTriples(eventLoop, tms, F, x) for x in alternateSubruleNodes]

        vars = frozenset(F.each(pred=rdf['type'], obj=p['Variable']))
        self = cls(eventLoop, tms, vars, unicode(label), pattern, subrules + assertions, alternateSubrules + alternateAssertions)
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
    
    logFormula = store.load(logURI)
    formulaTMS.getThing(logFormula).assume()

    eventLoop = EventLoop()

    policyFormula = store.load(policyURI)
    rdf = policyFormula.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
    p = policyFormula.newSymbol('http://dig.csail.mit.edu/TAMI/2007/rei+/policy')
    u = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/s0/university')
    s9 = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-policy')
    s9Log = workingContext.newSymbol('http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-log')
    
    rules = [Rule.compileFromTriples(eventLoop, formulaTMS, policyFormula, x)
                      for x in policyFormula.each(pred=rdf['type'], obj=p['Policy'])]
    ruleAssumptions = []
    for rule in rules:
        a  = formulaTMS.getThing(rule)
        ruleAssumptions.append(a)
        a.assume()

    while eventLoop:
        eventLoop.next()

# See how long it took (minus output)
    totalTime = time.time() - startTime
    print 'time reasoning took=', totalTime

#    rete.printRete()
    triples = list(workingContext.statementsMatching(pred=p['compliantWith']))
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
##    print testPolicy('http://dig.csail.mit.edu/TAMI/2007/s0/log.n3',
##                     'http://dig.csail.mit.edu/TAMI/2007/s0/mit-policy.n3')
    print testPolicy('http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-log.n3',
                     'http://dig.csail.mit.edu/TAMI/2007/s9/run/s9-policy.n3')
