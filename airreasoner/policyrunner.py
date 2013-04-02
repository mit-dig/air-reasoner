#!/usr/bin/env python
"""Amord.py

an attempt at an amord implementation built on cwm

"""

import os

import weakref
#WVD = weakref.WeakValueDictionary
WVD = dict
from collections import deque
from itertools import chain

import llyn
from formula import Formula, StoredStatement
from term import List, Env, Symbol, Term, BuiltIn, SUBJ, PRED, OBJ

import uripath

import diag
progress = diag.progress

import tms
import rete
import treat

MM = rete # or it could be treat

OFFLINE = [False]

airstatementWarnings = set()

from prooftrace import (supportTrace,
                        removeFormulae,
                        removeBaseRules,
                        simpleTraceOutput,
                        rdfTraceOutput)

from py25 import all, any, defaultdict
                        

workcount = defaultdict(int)

GOAL = 1

debugLevel = 0

# Need to extend the List and Tuple types to do x.substitution()
def baseSub(value, bindings):
    if value is not None:
        return value.substitution(bindings)
    else:
        return None

class SubstitutingList(list):
    """A list that responds to the substitution method"""
    pass

SubstitutingList.substitution = \
    lambda self, bindings: \
        SubstitutingList(map(lambda x: baseSub(x, bindings), self))

class SubstitutingTuple(tuple):
    """A tuple that responds to the substitution method."""
    pass

SubstitutingTuple.substitution = \
    lambda self, bindings: \
        SubstitutingTuple(map(lambda x: baseSub(x, bindings), self))

class FormulaTMS(object):
    """This is the interface between the TMS and the rdf side of things
It keeps a Formula of all facts currently believed.
The job of activating rules also goes on this
"""
    tracking = True
    def __init__(self, workingContext):
        self.tms = tms.TMS('FormulaTMS', self.event)
        self.nodes = WVD()
        self.workingContext = workingContext
        workingContext.tms = self
        self.NS = workingContext.newSymbol('http://dig.csail.mit.edu/2007/cwmrete/tmswap/amord')
        self.formulaContents = self.NS['FormulaContents']
        self.parseSemantics = workingContext.store.semantics
        self.premises = set()
        self.falseAssumptions = set()
        self.contexts = {}

        self.assumedPolicies = []
        self.assumedURIs = []
        self.assumedStrings = []
        self.assumedClosedWorlds = []
        
        # Stow some environments associated with things on the side.
        self.envs = {}

    def getAuxTriple(self, auxid, subject, predicate, object, variables):
        """An aux triple is a triple supported for something other than belief
This is currently only used for goals
"""
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
    
    def getThingWithEnv(self, thing, env):
        if thing not in self.envs:
            self.envs[thing] = env
        return self.getThing(thing)
    
    def getStatement(self, (subject, predicate, object, variables)):
        return self.workingContext.statementsMatching(subj=subject, pred=predicate, obj=object)[0]

    def getAuxStatement(self, (auxid, subject, predicate, object, variables)):
        return self.getContext(auxid).statementsMatching(subj=subject, pred=predicate, obj=object)[0]

    def event(self, node, justification):
        if isinstance(justification, tms.Premise):
            if isinstance(node.datum, tuple) and len(node.datum) == 2:
                pass # Better than the alternative?
            else:
                self.premises.add(node)
        if justification is False:
            if isinstance(node.datum, Rule):
                pass # not worth the work
            if isinstance(node.datum, tuple):
                if len(node.datum) == 4:
                    self.workingContext.removeStatement(self.getStatement(node.datum))
#                    self.getContext(GOAL).removeStatement(self.getStatement(node.datum))
                else:
                    self.getContext(GOAL).removeStatement(self.getAuxStatement(node.datum))
        if isinstance(node.datum, Rule):
            if debugLevel >= 3:
                if node.datum.goal:
                    progress('\tNow supporting goal rule %s because of %s' % (node, justification))
                else:
                    progress('\tNow supporting rule %s because of %s' % (node, justification))
            if self.tracking:
                if node.datum.goal:
                    workcount['goal-rule'] += 1
                else:
                    workcount['rule'] += 1
            node.datum.compileToRete()
            if debugLevel >= 4:
                progress('\t\t ... built rule')
        if isinstance(node.datum, Symbol):
            if debugLevel >= 2:
                progress('Now supporting %s because of %s' % (node, justification))
            f = _loadF(self, node.datum.uriref())
            self.getThing(f).justify(self.parseSemantics, [node])
        if isinstance(node.datum, Formula):
            if debugLevel >= 2:
                progress('Now supporting %s because of %s' % (node, justification))
            self.workingContext.loadFormulaWithSubstitution(node.datum)
        if isinstance(node.datum, tuple):
#            print '\t ... now supporting %s because of %s' % (node, justification)
            if len(node.datum) == 2:
                pass # signal data
            elif len(node.datum) == 4:
                if isinstance(node.datum[1], BuiltIn) and node.datum[1] is not node.datum[1].store.sameAs:
                     # Hackety hack...  Dun like it, but it avoids
                     # inserting a (wrong) built-in fact...
                     return
                if self.tracking:
                    workcount['fact'] += 1
                triple = node.datum[:3]
                variables = node.datum[3]
                if variables is None:
                    self.workingContext.add(*triple)                
#                    self.getContext(GOAL).add(*triple)
                else:  # slow path --- do we need it?
                    s, p, o = triple
                    s1 = self.workingContext._buildStoredStatement(subj=s,
                                                                 pred=p,
                                                                 obj=o,
                                                                why=None)
                    if isinstance(s1, int): # It is possible for cwm to not directly add things
                        raise TypeError(node)
                    s1.variables = v
                    result = self.workingContext. _addStatement(s1)
                    
#                    s2 = getContext(GOAL)._buildStoredStatement(subj=s,
#                                                                 pred=p,
#                                                                 obj=o,
#                                                                why=None)
#                    if isinstance(s2, int):
#                        raise TypeError(node)
#                    s2.variables = v
#                    result = self.getContext(GOAL). _addStatement(s1)
            else:
                if self.tracking:
                    workcount['goal'] += 1
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
    """Canonicalize all variables in statement to be URIs of the form
    http://example.com/vars/#variable(digits).  Returns a tuple
    corresponding to the subject, predicate, and object following
    canonicalization, and a frozenset including the URIs of all
    variables that were canonicalized.
    
    """
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
            # Commenting this out for log:includes.  What side-effects
            # does this have?
#            if node.occurringIn(variables):
#                raise ValueError(node)
#            return node
            
            # log:includes uses external scope to canonicalize
            # variables...?
            f = None
            for statement in node.statements:
                subj, pred, obj = statement.spo()
                if subj is not canNode(subj) or pred is not canNode(pred) or obj is not canNode(obj):
                    f = node.store.newFormula()
            if f:
                for statement in node.statements:
                    subj, pred, obj = statement.spo()
                    f.add(canNode(subj), canNode(pred), canNode(obj))
                f.close()
                return f
        return node
    return (canNode(subj), canNode(pred), canNode(obj)), frozenset(varMapping.values())

class Assertion(object):
    """An assertion can be asserted. It tracks what its support will be when asserted
"""
    def __init__(self, pattern, support=None, rule=None, validToRename=None):
        self.pattern = pattern
        self.support = support
        self.rule = rule
        
        if isinstance(pattern, Formula):
            if validToRename is None:
                self.needsRenaming = frozenset(pattern.existentials())
            else:
                self.needsRenaming = frozenset(pattern.existentials()).intersection(validToRename)
        else:
            self.needsRenaming = frozenset()

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

        newBlankNodesBindings = dict([(x, self.pattern.newBlankNode()) for x in self.needsRenaming]) # if invalid, will not be run
        bindings.update(newBlankNodesBindings)

        return Assertion(self.pattern.substitution(bindings), support, self.rule, validToRename=newBlankNodesBindings.values())

    def __repr__(self):
        return 'Assertion(%s,%s,%s)' % (self.pattern, self.support, self.rule)

    def __eq__(self, other):
        return isinstance(other, Assertion) and self.pattern == other.pattern

    def __hash__(self):
        return hash((self.pattern, self.__class__)) 

    
        

class AuxTripleJustifier(object):
    """A thunk, to separate the work of creating aux triples from
building the rules whose support created them.
These are then passed to the scheduler
"""
    def __init__(self, tms, *args):
        self.tms = tms
        self.args = args

    def __call__(self, eventLoop):
        self.tms.justifyAuxTriple(*self.args)

class RuleName(object):
    def __init__(self, name, descriptions, prompts):
        assert isinstance(name, Term)
        assert all(isinstance(x, Term) for x in descriptions)
        assert all(isinstance(x, Term) for x in prompts)
        self.name = name
        self.descriptions = descriptions
        self.prompts = prompts

    def __repr__(self):
        return 'R(%s)' % (self.name,)

    def uriref(self): # silly
        return self.name.uriref() + '+'.join(''.join(str(y) for y in x) for x in self.descriptions)


class RuleFire(object):
    """A thunk, passed to the scheduler when a rule fires
"""
    def __init__(self, rule, triples, env, penalty, result, alt=False):
        self.rule = rule
        self.args = (triples, env, penalty, result, alt)

    def __call__(self, eventLoop):
        triples, env, penalty, result, alt = self.args
        self = self.rule
        if alt and self.success: # We fired after all
#            raise RuntimeError('we do not have any alts yet')
            return
        if debugLevel > 12:
            if alt:
                progress('%s failed, and alt is being called' % (self.label,))
            else:
                progress('%s succeeded, with triples %s and env %s' % (self.label, triples, env))
        triplesTMS = []
        goals = []
        unSupported = []
        # Iterate through each triple of this RuleFire event, and
        # classify it as supported (triplesTMS), a goal triple
        # (goals), or unsupported (unSupported)
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
            # Goal-rule stuff below.
            if not self.goal:
                raise RuntimeError('how did I get here?\nI matched %s, which are goals, but I don\'t want goals' % goals)
#                print 'we goal succeeded! %s, %s' % (triples, result)
            envDict = env.asDict()
            for triple, _ in goals:
                assert not triple.variables.intersection(env.keys())
                newVars = triple.variables.intersection(envDict.values())
                if newVars:
                    raise NotImplementedError("I don't know how to add variables")
            
            for r in result:
                # Do any substitution and then extract the description
                # and r12 from the particular r's tuple.
                r12 = r.substitution(env.asDict())
                prompt = r12[2]
                desc = r12[1]
                r12 = r12[0]
                
                r2 = r12.pattern
                support = r12.support
                ruleId = r12.rule
                assert isinstance(r2, Rule) or not r2.occurringIn(self.vars), (r2, env, penalty, self.label)
#            print '   ...... so about to assert %s' % r2
                r2TMS = self.tms.getThingWithEnv(r2, env)
                if support is None:
                    if isinstance(r2, Rule):
                        r2TMS.justify(self.sourceNode, triplesTMS + [self.tms.getThing(self)])
                    else:
                        # Delay the justification of assertions in else clauses.
                        eventLoop.addAssertion(lambda: r2TMS.justify(self.sourceNode, triplesTMS + [self.tms.getThing(self)]))
                else:
                    supportTMS = reduce(frozenset.union, support, frozenset())
                    if isinstance(r2, Rule):
                        r2TMS.justify(ruleId, supportTMS)
                    else:
                        eventLoop.addAssertion(lambda: r2TMS.justify(ruleId, supportTMS))
                        eventLoop.addAssertion(lambda: r2TMS.justify(RuleName(ruleId, desc, prompt), supportTMS))
#                assert self.tms.getThing(self).supported
#                assert r2TMS.supported                
#                raise NotImplementedError(goals) #todo: handle goals
        elif unSupported:
            raise RuntimeError(triple, self) # We should never get unsupported triples
        else:
            if self.goal:
                return
#                print 'we succeeded! %s, %s' % (triples, result)
            if alt:
                # Close the world over what we've currently assumed if
                # this RuleFire event is an alternate one (else)
#                closedWorld = self.tms.getThing(('closedWorld', self.tms.workingContext.newList(list(self.tms.premises))))
                closedWorld = self.tms.getThing(('closedWorld',
                                                 self.tms.workingContext.newList(self.tms.assumedPolicies +
                                                     self.tms.assumedURIs +
                                                     self.tms.assumedStrings +
                                                     self.tms.assumedClosedWorlds)))
                closedWorld.assumeByClosingWorld(self.tms.assumedPolicies,
                                                 self.tms.assumedURIs,
                                                 self.tms.assumedStrings,
                                                 self.tms.assumedClosedWorlds)
                self.tms.assumedClosedWorlds.append(closedWorld)
                altSupport = [closedWorld]
#                desc = self.altDescriptions
            else:
                altSupport = []
#                desc = [x.substitution(env.asDict()) for x in self.descriptions]

            for r in result:
                # Do any substitution and then extract the description
                # and r12 from the particular r's tuple.
                r12 = r.substitution(env.asDict())
                prompt = r12[2]
                desc = r12[1]
                r12 = r12[0]
                
                r2 = r12.pattern
                support = r12.support
                ruleId = r12.rule
                assert isinstance(r2, Rule) or not r2.occurringIn(self.vars), (r2, env, penalty, self.label)
#            print '   ...... so about to assert %s' % r2
                # Justify r2's TMS node with the triples in
                # triplesTMS, and us as a rule (and any closed world)
                r2TMS = self.tms.getThingWithEnv(r2, env)
                if support is None:
                    if isinstance(r2, Rule):
                        r2TMS.justify(RuleName(self.sourceNode, desc, prompt), triplesTMS + [self.tms.getThing(self)] + altSupport)
                    else:
                        # Delay the justification of assertions in else clauses.
                        eventLoop.addAssertion(lambda: r2TMS.justify(RuleName(self.sourceNode, desc, prompt), triplesTMS + [self.tms.getThing(self)] + altSupport))
                else:
                    supportTMS = reduce(frozenset.union, support, frozenset()).union(altSupport)
                    if isinstance(r2, Rule):
                        r2TMS.justify(RuleName(ruleId, desc, prompt), supportTMS)
                    else:
                        eventLoop.addAssertion(lambda: r2TMS.justify(RuleName(ruleId, desc, prompt), supportTMS))
#                assert self.tms.getThing(self).supported
#                assert r2TMS.supported


class Rule(object):
    """A Rule contains all of the information necessary to build the rete
for a rule, and to handle when the rule fires. It does not care
much how the rule was represented in the rdf network
"""

    baseRules = set()
    
    def __init__(self, eventLoop, tms, vars, label,
                 pattern, contextFormula, result, alt, sourceNode,
                 goal=False, matchName=None, base=False, elided=False,
                 generated=False, goalWildcards={}):
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
        self.contextFormula = contextFormula
        self.result = result
#        self.descriptions = descriptions
        self.alt = alt
#        assert isinstance(altDescriptions, list), altDescriptions
#        self.altDescriptions = altDescriptions
        self.goal = goal
        self.matchName = matchName
        self.sourceNode = sourceNode
        self.generated = generated
        self.isBase = base
        self.isElided = elided
        self.goalWildcards = goalWildcards
        self.goalEnvironments = set()
        self.discoverReachableGoals()
        if base:
            self.baseRules.add(sourceNode)
        if debugLevel > 15:        
            print '''just made a rule, with
        tms=%s,
        vars=%s
        label=%s
        pattern=%s
        result=%s
        alt=%s
        matchName=%s''' % (tms, self.vars, label, pattern, result, alt, matchName)

    def discoverReachableGoals(self):
        """Find all goals reachable from this rule."""
        # We now have THIS rule, but not the goal rules it should be
        # contingent on.

        # Find all of the goals of this rule.
        goalFilter = set()

        # Find all goals this rule may ultimately match and add
        # them to the goals to use as a trigger.

        # Collect unbound vars with each result
        seenStatements = set()
        possibleResults = [(possibleResult, self.vars)
                           for possibleResult in self.result + self.alt]
        while len(possibleResults) > 0:
            possibleResult, vars = possibleResults.pop()
            if isinstance(possibleResult[0].pattern, Rule):
                # We will need to traverse descendants.
                possibleResults.extend([(newResult, possibleResult[0].pattern.vars)
                                        for newResult in possibleResult[0].pattern.result + possibleResult[0].pattern.alt])
            else:  # isinstance(possibleResult[0].pattern, Formula)
                # We have an assertion formula.  Statements in it
                # are reachable goals.
                for statement in possibleResult[0].pattern.statements:
                    # Eugh.  hash(StoredStatement) is by id, not contents.
                    if statement.spo() not in seenStatements:
                        goalFilter.add(statement)
                        seenStatements.add(statement.spo())
        # POST: goalFilter now contains a set of all goal-patterns
        # (with variables set to None) reachable from this rule.
        self.reachableGoals = goalFilter

    def __eq__(self, other):
        return isinstance(other, Rule) and \
               self.eventLoop is other.eventLoop and \
               self.tms is other.tms and \
               self.goal == other.goal and \
               self.vars == other.vars and \
               self.patternToCompare == other.patternToCompare and \
               self.result == other.result and \
               self.alt == other.alt and \
               self.matchName == other.matchName

    def __hash__(self):
        assert not isinstance(Rule, list)
        assert not isinstance(self.eventLoop, list)
        assert not isinstance(self.tms, list)
        assert not isinstance(self.vars, list)
        assert not isinstance(self.pattern, list)
        assert not isinstance(self.sourceNode, list)
        assert not isinstance(self.goal, list)
        assert not isinstance(self.matchName, list)
        return hash((Rule, self.eventLoop, self.tms, self.vars, self.pattern, self.sourceNode, self.goal, self.matchName))

    def __repr__(self):
        return '%s with vars %s' % (self.label.encode('utf_8'), self.vars)

    def compileToRete(self):
        patterns = self.pattern.statements
        if self.goal:
            workingContext = self.tms.getContext(GOAL)
        else:
            workingContext = self.tms.workingContext
        index = workingContext._index
#        buildGoals = False  # If true, goals will be matched first.
        self.goalBottomBeta = MM.compileGoalPattern(self.tms.getContext(GOAL)._index, patterns, self.vars, self.goalWildcards, self.tms.getContext(GOAL), self.reachableGoals, supportBuiltin=self.supportBuiltin)
        goalBottom = MM.ProductionNode(self.goalBottomBeta, self.assertNewGoals, lambda: True)

    def supportBuiltin(self, triple):
        # Create the TMS node representing this triple's extraction.
        self.tms.getTriple(*triple.spo()).assumeBuiltin()
    
    def addTriple(self, triple):
        self.tms.getTriple(*triple.spo()).assume()
    def retractTriple(self, triple):
        self.tms.getTriple(*triple.spo()).retract()

    def assertNewGoals(self, (triples, environment, penalty)):
        # Assert new goals of this rule by substituting in the matched
        # environments of goals this rule can satisfy.
        if environment not in self.goalEnvironments:
            # Only ever assert goals for a given environment once.
            self.goalEnvironments.add(environment)
            patterns = self.pattern.statements
            if self.goal:
                workingContext = self.tms.getContext(GOAL)
            else:
                workingContext = self.tms.workingContext
            index = workingContext._index
            for triple in patterns:
                triple = triple.substitution(environment)
                (s, p, o), newVars = canonicalizeVariables(triple, self.vars)
                self.eventLoop.add(AuxTripleJustifier(self.tms, GOAL, s, p, o, newVars, self.sourceNode, [self.tms.getThing(self)]))

            # TODO: Pass the environment.
            # TODO: This isn't triggering for the right things.
            def reallyCompileRete(eventLoop):
                bottomBeta = MM.compilePattern(index, patterns, self.vars, self.contextFormula, supportBuiltin=self.supportBuiltin)
                trueBottom =  MM.ProductionNode(bottomBeta, self.onSuccess, self.onFailure)
#            print "push", reallyCompileRete, "from", patterns
            self.eventLoop.pushPostGoal(reallyCompileRete)

    def onSuccess(self, (triples, environment, penalty)):
        self.success = True
        self.eventLoop.add(RuleFire(self, triples, environment, penalty, self.result))

    def onFailure(self):
        assert not self.success
        if self.alt:
            self.eventLoop.addAlternate(RuleFire(self, [], Env(), 0, self.alt, alt=True))

    def substitution(self, env):
        if not env:
            return self
        pattern = self.pattern.substitution(env)
        result = [x.substitution(env) for x in self.result]
        alt = [x.substitution(env) for x in self.alt]
#        descriptions = [x.substitution(env) for x in self.descriptions]
#        altDescriptions = [x.substitution(env) for x in self.altDescriptions]
        if self.generatedLabel:
            label = None
        else:
            label = self.label
        return self.__class__(self.eventLoop, self.tms, self.vars,
                              label, pattern, self.contextFormula, result, alt,
                              self.sourceNode, self.goal, self.matchName, base=self.isBase, elided=self.isElided, generated=True)

    @classmethod
    def compileFromTriples(cls, eventLoop, tms, F, ruleNode, goal=False,
                           vars=frozenset(), preboundVars=frozenset(),
                           base=False, goalWildcards={}):
        """Compiles a Rule object which makes use of the specified eventLoop
        and TMS.  The rule is identified by the RDF node ruleNode
        contained in the Formula F.  If goal is True, the Rule is to
        be considered a goal-rule.  vars contains the set of defined
        variables (both bound and unbound) prior to the execution of
        this rule, while preboundVars contains only the set of bound
        variables.  If base is True, the rule being compiled is from
        the base AIR rule set (which contains basic RDFS and OWL
        rules); output of base rules are hidden when justifications
        are constructed.

        NOTE: This function does NOT compile the Rete tree for the
        Rule.  That is done by Rule.compileToRete."""

        # Define namespaces.
        assert tms is not None
        rdfs = F.newSymbol('http://www.w3.org/2000/01/rdf-schema')
        rdf = F.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
        p = F.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/air')

        # Get the pattern for the rule (we'll need it for testing
        # which variables are bound in this rule)
        try:
            pattern = F.the(subj=ruleNode, pred=p['if'])
        except AssertionError:
            raise ValueError('%s has too many air:if clauses, being all of %s'
                             % (ruleNode, F.each(subj=ruleNode, pred=p['if'])))
        if pattern is None:
            raise ValueError('%s must have an air:if clause. You did not give it one' % (ruleNode,))
        
        # Find the variables used in this rule and determine if any
        # variables are newly bound when matching the pattern.
        vars = vars.union(F.universals())
        # ASSUMPTION: variables will never be a predicate(!)
        varsUsed = set([var for var in vars
                        if pattern.contains(subj=var) or pattern.contains(obj=var)])
        varBinding = len(varsUsed - preboundVars) > 0
        preboundVars = preboundVars.union(F.universals())

        realNode = ruleNode
        nodes = [realNode]

        # Get the air:then and air:else nodes.
        thenNodes = F.each(subj=ruleNode, pred=p['then'])
        elseNodes = F.each(subj=ruleNode, pred=p['else'])
        if varBinding and len(elseNodes) > 0:
            raise ValueError('%s has an air:else clause even though a variable is bound in its air:if, which is unsupported (did you mean to use @forSome instead of @forAll?)'
                             % (ruleNode))
#        if altNode:
#            nodes.append(altNode)
#            altDescriptions = list(F.each(subj=altNode, pred=p['description']))
#        else:
#            altDescriptions = []

        # Get the air:label value.
        # TODO: get this annotated on the ontology.
        label = F.the(subj=ruleNode, pred=p['label'])
        
        # Is the rule an air:Hidden-rule?
        base = base or (F.contains(subj=ruleNode, pred=F.store.type, obj=p['Hidden-rule']) == 1)
        # air:Elided-rule?
        elided = (F.contains(subj=ruleNode, pred=F.store.type, obj=p['Elided-rule']) == 1)
#        descriptions = list(F.each(subj=node, pred=p['description']))

        # Collect all air:then or air:else actions...
        resultList  = []
        
        # For each air:then node...
        subrules = []
        goal_subrules = []
        assertions = []
        goal_assertions = []
        for node in thenNodes:
            actions = []
            
            # Get any description...
            try:
                description = F.the(subj=node, pred=p['description'])
                if description == None:
                    description = SubstitutingList()
                else:
                    description = SubstitutingList([description])
            except AssertionError:
                raise ValueError('%s has too many descriptions in an air:then, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['description'])))
            try:
                prompt = F.the(subj=node, pred=p['prompt'])
                if prompt == None:
                    prompt = SubstitutingList()
                else:
                    prompt = SubstitutingList([prompt])
            except AssertionError:
                raise ValueError('%s has too many prompts in an air:then, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['prompt'])))
            
            # Get any subrule...
            subrule = None
            try:
                subruleNode = F.the(subj=node, pred=p['rule'])
                if subruleNode is not None:
                    subrule = Assertion(cls.compileFromTriples(eventLoop, tms, F, subruleNode, vars=vars, preboundVars=preboundVars, base=base, goalWildcards=goalWildcards))
            except AssertionError:
                raise ValueError('%s has too many rules in an air:then, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['rule'])))
            if subrule is not None:
                subrules.append(SubstitutingTuple((subrule, description, prompt)))
                actions.append(subrule)
            
            # Get any goal-subrule...
            goal_subrule = None
            try:
                goal_subruleNode = F.the(subj=node, pred=p['goal-rule'])
                if goal_subruleNode is not None:
                    goal_subrule = Assertion(cls.compileFromTriples(eventLoop, tms, F, goal_subruleNode, goal=True, vars=vars, preboundVars=preboundVars, base=base, goalWildcards=goalWildcards))
            except AssertionError:
                raise ValueError('%s has too many goal-rules in an air:then, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['goal-rule'])))
            if goal_subrule is not None:
                goal_subrules.append(
                    SubstitutingTuple((goal_subrule, description, prompt)))
                actions.append(goal_subrule)
            
            # Get any assertion...
            try:
                assertion = F.the(subj=node, pred=p['assert'])
            except AssertionError:
                raise ValueError('%s has too many assertions in an air:then, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['assert'])))
            if assertion is not None:
                assertions.append(SubstitutingTuple((assertion, description, prompt)))
                actions.append(assertion)
            
            # Get any goal-assertion...
            try:
                goal_assertion = F.the(subj=node, pred=p['assert-goal'])
            except AssertionError:
                raise ValueError('%s has too many goal-assertions in an air:then, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['assert-goal'])))
            if goal_assertion is not None:
                goal_assertions.append(
                    SubstitutingTuple((goal_assertion, description, prompt)))
                actions.append(goal_assertion)
            
            # Make sure there was exactly one of the above.
            if len(actions) != 1:
                raise ValueError('%s has more than one of {air:rule, air:goal-rule, air:assert, air:assert-goal} in an air:then, being all of %s'
                                 % (ruleNode, actions))
            
        # Get the data from the assertions.
        assertionObjs = []
        for assertion in assertions + goal_assertions:
            prompt = assertion[2]
            description = assertion[1]
            statement = assertion[0]
            if F.any(subj=statement, pred=p['statement']) is not None:
                if ruleNode not in airstatementWarnings:
                    print "WARNING: %s has an air:statement clause inside an air:assert clause.  This is no longer supported in AIR 2.5, and will not work with future versions of the reasoner." % (ruleNode)
                    airstatementWarnings.add(ruleNode)
                statement = F.the(subj=statement, pred=p['statement'])
            assertionObjs.append(SubstitutingTuple(
                    (Assertion(statement),
                     description,
                     prompt)))
        resultList.append(subrules + assertionObjs + goal_subrules)
        
        # Now do what we did to collect the assertions and such for
        # any air:else actions.
        subrules = []
        goal_subrules = []
        assertions = []
        goal_assertions = []
        for node in elseNodes:
            actions = []
            
            # Get any description...
            try:
                description = F.the(subj=node, pred=p['description'])
                if description == None:
                    description = SubstitutingList()
                else:
                    description = SubstitutingList([description])
            except AssertionError:
                raise ValueError('%s has too many descriptions in an air:else, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['description'])))
            try:
                prompt = F.the(subj=node, pred=p['prompt'])
                if prompt == None:
                    prompt = SubstitutingList()
                else:
                    prompt = SubstitutingList([prompt])
            except AssertionError:
                raise ValueError('%s has too many prompts in an air:else, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['prompt'])))

            # Get any subrule...
            subrule = None
            try:
                subruleNode = F.the(subj=node, pred=p['rule'])
                if subruleNode is not None:
                    subrule = Assertion(cls.compileFromTriples(eventLoop, tms, F, subruleNode, vars=vars, preboundVars=preboundVars, base=base, goalWildcards=goalWildcards))
            except AssertionError:
                raise ValueError('%s has too many rules in an air:else, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['rule'])))
            if subrule is not None:
                subrules.append(SubstitutingTuple((subrule, description, prompt)))
                actions.append(subrule)
            
            # Get any goal-subrule...
            goal_subrule = None
            try:
                goal_subruleNode = F.the(subj=node, pred=p['goal-rule'])
                if goal_subruleNode is not None:
                    goal_subrule = Assertion(cls.compileFromTriples(eventLoop, tms, F, goal_subruleNode, goal=True, vars=vars, preboundVars=preboundVars, base=base, goalWildcards=goalWildcards))
            except AssertionError:
                raise ValueError('%s has too many goal-rules in an air:else, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['goal-rule'])))
            if goal_subrule is not None:
                goal_subrules.append(
                    SubstitutingTuple((goal_subrule, description, prompt)))
                actions.append(goal_subrule)
            
            # Get any assertion...
            try:
                assertion = F.the(subj=node, pred=p['assert'])
            except AssertionError:
                raise ValueError('%s has too many assertions in an air:else, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['assert'])))
            if assertion is not None:
                assertions.append(SubstitutingTuple((assertion, description, prompt)))
                actions.append(assertion)
            
            # Get any goal-assertion...
            try:
                goal_assertion = F.the(subj=node, pred=p['assert-goal'])
            except AssertionError:
                raise ValueError('%s has too many goal-assertions in an air:else, being all of %s'
                                 % (ruleNode, F.each(subj=node, pred=p['assert-goal'])))
            if goal_assertion is not None:
                goal_assertions.append(
                    SubstitutingTuple((goal_assertion, description, prompt)))
                actions.append(goal_assertion)
            
            # Make sure there was exactly one of the above.
            if len(actions) != 1:
                raise ValueError('%s has more than one of {air:rule, air:goal-rule, air:assert, air:assert-goal} in an air:else, being all of %s'
                                 % (ruleNode, actions))
            
        # Get the data from the assertions.
        assertionObjs = []
        for assertion in assertions + goal_assertions:
            prompt = assertion[2]
            description = assertion[1]
            statement = assertion[0]
            if F.any(subj=statement, pred=p['statement']) is not None:
                if ruleNode not in airstatementWarnings:
                    print "WARNING: %s has an air:statement clause inside an air:assert clause.  This is no longer supported in AIR 2.5, and will not work with future versions of the reasoner." % (ruleNode)
                    airstatementWarnings.add(ruleNode)
                statement = F.the(subj=statement, pred=p['statement'])
            assertionObjs.append(SubstitutingTuple(
                    (Assertion(statement),
                     description,
                     prompt)))
        resultList.append(subrules + assertionObjs + goal_subrules)
        
        node = ruleNode
        matchedGraph = F.the(subj=node, pred=p['matched-graph'])
        
        # Construct the rule object.
        self = cls(eventLoop, tms,
                   vars, unicode(label),
                   pattern,
                   F,
                   resultList[0],
#                   descriptions=descriptions,
                   alt=resultList[1],# altDescriptions=altDescriptions,
                   goal=goal, matchName=matchedGraph, sourceNode=node, base=base, elided=elided, goalWildcards=goalWildcards)
        return self

    @classmethod
    def compileCwmRule(cls, eventLoop, tms, F, triple):
        assert tms is not None
        label = "Rule from cwm with pattern %s" % triple.subject()
        pattern = triple.subject()
        assertions = [(Assertion(triple.object()), None)]
        vars = frozenset(F.universals())
        self = cls(eventLoop, tms,
                   vars, unicode(label),
                   pattern,
                   assertions,
                   alt=[],
                   goal=False,
                   matchName=None,
                   sourceNode=pattern,
                   base=True,
                   elided=False)
        return self


    @classmethod
    def compileFormula(cls, eventLoop, formulaTMS, pf, base=False, goalWildcards={}):
        rdf = pf.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
        p = pf.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/air')
        # New AIR terminology.
        policies = pf.each(pred=rdf['type'], obj=p['RuleSet'])
        policies += pf.each(pred=rdf['type'], obj=p['Policy'])
#        globalVars = frozenset(pf.each(pred=rdf['type'], obj=p['Variable']))
        globalVars = frozenset(pf.universals())
        cwm_rules = [cls.compileCwmRule(eventLoop,
                                        formulaTMS,
                                        pf,
                                        x)
                     for x in pf.statementsMatching(pred=pf.store.implies)]
        rules = reduce(list.__add__, [[cls.compileFromTriples(eventLoop,
                                        formulaTMS,
                                        pf,
                                        x,
#                                        vars=globalVars.union(pf.each(subj=y, pred=p['variable'])),
                                        vars=globalVars,
                                        base=base,
                                        goalWildcards=goalWildcards)
                        for x in pf.each(subj=y, pred=p['rule'])]
                    for y in policies], [])
        goal_rules = reduce(list.__add__, [[cls.compileFromTriples(eventLoop,
                                                       formulaTMS,
                                                       pf,
                                                       x,
#                                                       vars=globalVars.union(pf.each(subj=y, pred=p['variable'])),
                                                       vars=globalVars,
                                                       base=base,
                                                       goalWildcards=goalWildcards)
                        for x in pf.each(subj=y, pred=p['goal-rule'])]
                    for y in policies], [])
        return policies, rules, goal_rules, cwm_rules               





uriGenCount = [0]
def nameRules(pf, uriBase):
    rdf = pf.newSymbol('http://www.w3.org/1999/02/22-rdf-syntax-ns')
    p = pf.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/air')
    bindings = {}
    for statement in chain(pf.statementsMatching(pred=p['rule']),
                                        pf.statementsMatching(pred=['goal-rule'])):
        node = statement.subject()
        if node in pf.existentials():
            bindings[node] = uriBase + str(uriGenCount[0])
            uriGenCount[0] += 1
    return pf.substitution(bindings)


class EventLoop(object):
    """The eventloop (there should only be one)
is a FIFO of thunks to be called.

Note that this eventloop support altevents (for else clauses) which
fire only when there are no events to fire.
"""
    PHASE_OPEN = 0
    PHASE_CLOSED = 1
    PHASE_REOPEN = 2
    
    def __init__(self):
        self.events = deque()
        self.alternateEvents = deque()
        self.postGoalEvents = deque()
        self.phase = EventLoop.PHASE_OPEN
        self.assertionEvents = deque()
        self.newAlternateEvents = deque()

    def add(self, event):
#        if hasattr(event, 'rule'):
#            print "add", event.rule
        self.events.appendleft(event)

    def addAlternate(self, event):
#        print "addAlternate", event.rule
        if self.phase != EventLoop.PHASE_CLOSED:
            self.alternateEvents.appendleft(event)
        else:
            self.newAlternateEvents.appendleft(event)

    def pushPostGoal(self, event):
        # Only ever run this event once we're done with normal
        # events. (i.e. once all necessary goal-rules have been
        # matched.)

        # Also, this runs as a stack.  Goals matched later will
        # execute first.
        self.postGoalEvents.append(event)
    
    def addAssertion(self, event):
#        print "addAssertion", event
        if self.phase != EventLoop.PHASE_OPEN:
            self.assertionEvents.appendleft(event)
        else:
            event()

    def next(self):
        if self.phase == EventLoop.PHASE_OPEN and self.events:
            return self.events.pop()(self)
        elif self.phase <= EventLoop.PHASE_CLOSED and self.alternateEvents:
#            print "close!"
            self.phase = EventLoop.PHASE_CLOSED
            return self.alternateEvents.pop()(self)
        elif self.phase <= EventLoop.PHASE_REOPEN and self.assertionEvents:
            self.phase = EventLoop.PHASE_REOPEN
            if len(self.newAlternateEvents) > 0:
                self.alternateEvents = self.newAlternateEvents
                self.newAlternateEvents = deque()
            return self.assertionEvents.pop()()
        elif self.events:
#            print "open!"
            self.phase = EventLoop.PHASE_OPEN
            if len(self.newAlternateEvents) > 0:
                self.alternateEvents = self.newAlternateEvents
                self.newAlternateEvents = deque()
            return self.events.pop()(self)
        elif self.postGoalEvents:
            event = self.postGoalEvents.pop()
#            print "pop", event
            return event(self)
        else:
            if len(self.newAlternateEvents) > 0:
                self.alternateEvents = self.newAlternateEvents
                self.newAlternateEvents = deque()
            return None

    def __len__(self):
        return len(self.events) + len(self.alternateEvents) + len(self.assertionEvents) + len(self.postGoalEvents)


            

def setupTMS(store):
    workingContext = store.newFormula()
    workingContext.keepOpen = True
    formulaTMS = FormulaTMS(workingContext)
    return formulaTMS
    

def loadFactFormula(formulaTMS, uri, closureMode=""): #what to do about closureMode?
##    We're not ready for this yet!
##    store = formulaTMS.workingContext.store
##    s = store.newSymbol(uri)
##    assert isinstance(s, Symbol)
##    formulaTMS.getThing(s).assume()
##    return s
    f = _loadF(formulaTMS, uri, closureMode)
    formulaTMS.getThing(f).assumeByExtraction(uri)
    formulaTMS.assumedURIs.append(formulaTMS.workingContext.newSymbol(uri))
    return f

def _loadF(formulaTMS, uri, closureMode=""):
    if loadFactFormula.pClosureMode:
        closureMode += "p"
    store = formulaTMS.workingContext.store
    f = store.newFormula()
    f.setClosureMode(closureMode)
    f = store.load(uri, openFormula=f)
    return f

def parseN3(store, f, string):
    import notation3
    p = notation3.SinkParser(store, f)

    p.startDoc()
    p.feed(string)
    f = p.endDoc()

    f = f.close()
    return f


def loadFactFormulaObj(formulaTMS, f, closureMode=""):
    if loadFactFormula.pClosureMode:
        closureMode += "p"
    fCopy = store.newFormula()
    fCopy.setClosureMode(closureMode)
    fCopy.loadFormulaWithSubstitution(f, Env())
    formulaTMS.getThing(fCopy).assume()
    formulaTMS.assumedStrings.append(formulaTMS.workingContext.newLiteral(f.n3String(), dt=n3NS))
    return fCopy


def loadFactN3(formulaTMS, string, closureMode=""):
    if loadFactFormula.pClosureMode:
        closureMode += "p"
    store = formulaTMS.workingContext.store
    f = store.newFormula()
    f.setClosureMode(closureMode)    
    f = parseN3(store, f, string)
    formulaTMS.getThing(f).assumeByParsingN3(f)
    formulaTMS.assumedStrings.append(formulaTMS.workingContext.newLiteral(string, dt=n3NS))
    return f    

loadFactFormula.pClosureMode = False



baseFactsURI = 'http://dig.csail.mit.edu/TAMI/2007/amord/base-assumptions.ttl'
baseRulesURI = 'http://dig.csail.mit.edu/TAMI/2007/amord/base-rules.air_2_5.ttl'

#baseFactsURI =
#baseRulesURI = 'data:text/rdf+n3;charset=utf-8,' # quite empty

store = llyn.RDFStore()

n3NS = store.newSymbol('http://www.w3.org/2000/10/swap/grammar/n3#n3')

def testPolicy(logURIs, policyURIs, logFormula=None, ruleFormula=None, filterProperties=['http://dig.csail.mit.edu/TAMI/2007/amord/air#compliant-with', 'http://dig.csail.mit.edu/TAMI/2007/amord/air#non-compliant-with'], verbose=False, customBaseFactsURI=False, customBaseRulesURI=False):
    trace, result = runPolicy(logURIs, policyURIs, logFormula=logFormula, ruleFormula=ruleFormula, filterProperties=filterProperties, verbose=verbose, customBaseFactsURI=customBaseFactsURI, customBaseRulesURI=customBaseRulesURI)
    return trace.n3String()

goalWildcards = {}

def runPolicy(logURIs, policyURIs, logFormula=None, ruleFormula=None, filterProperties=['http://dig.csail.mit.edu/TAMI/2007/amord/air#compliant-with', 'http://dig.csail.mit.edu/TAMI/2007/amord/air#non-compliant-with'], logFormulaObjs=[], ruleFormulaObjs=[], store=store, verbose=False, customBaseFactsURI=False, customBaseRulesURI=False):
    global baseFactsURI, baseRulesURI
    if OFFLINE[0]:
        baseFactsURI = uripath.join(uripath.base(),
                                      baseFactsURI.replace('http://dig.csail.mit.edu/TAMI',
                                                           '../../..'))
        baseRulesURI = uripath.join(uripath.base(),
                                      baseRulesURI.replace('http://dig.csail.mit.edu/TAMI',
                                                           '../../..'))
        logURIs = map(lambda x: uripath.join(uripath.base(), x), logURIs)
        policyURIs = map(lambda x: uripath.join(uripath.base(), x), policyURIs)
    elif customBaseFactsURI or customBaseRulesURI:
        baseFactsURI = customBaseFactsURI
        baseRulesURI = customBaseRulesURI
    import time
    formulaTMS = setupTMS(store)
    workingContext = formulaTMS.workingContext

## We are done with cwm setup
    startTime = time.time()
    
    logFormulae = []
    if logFormula is not None:
        logFormulae.append(loadFactN3(formulaTMS, logFormula, ""))
    for logURI in logURIs:
        logFormulae.append(loadFactFormula(formulaTMS, logURI, "")) # should it be "p"?
    for logFormulaObj in logFormulaObjs:
        logFormulae.append(loadFactFormulaObj(formulaTMS, logFormulaObj, ""))

#    baseFactsFormula = loadFactFormula(formulaTMS, baseFactsURI)

    eventLoop = EventLoop()


    policyFormulae = []
    if ruleFormula is not None:
        policyFormulae.append(parseN3(store, store.newFormula(), ruleFormula))
    for policyURI in policyURIs:
        policyFormulae.append(store.load(policyURI))
    for ruleFormulaObj in ruleFormulaObjs:
        fCopy = store.newFormula()
        fCopy.loadFormulaWithSubstitution(ruleFormulaObj, Env())
        policyFormulae.append(fCopy)
#    baseRulesFormula = store.load(baseRulesURI)

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


    # Add the filterProperties as goals through AuxTripleJustifier
    goalWildcards = {
        SUBJ: store.newSymbol(store.genId()),
        PRED: store.newSymbol(store.genId()),
        OBJ: store.newSymbol(store.genId())
        }
    for p in filterProperties:
        s = goalWildcards[SUBJ]
        p = store.newSymbol(p)
        o = goalWildcards[OBJ]
        eventLoop.add(AuxTripleJustifier(formulaTMS, True, s, p, o, frozenset([s, o]), None, []))

    allRules = []
    allGoalRules = []
#    # We need to 'flatten' the policy formulae before we can compile it.
    policyFormula = store.mergeFormulae(policyFormulae)
    for pf in [policyFormula]: # + [baseRulesFormula]:
#    for pf in policyFormulae + [baseRulesFormula]:
#        if pf is baseRulesFormula: ## Realy bad hack!
#            base=True
#        else:
#            base=False
        base = False
        policies, rules, goal_rules, cwm_rules = Rule.compileFormula(eventLoop, formulaTMS, pf, base=base, goalWildcards=goalWildcards)
        formulaTMS.assumedPolicies.extend(policies)
        allRules += rules
        allRules += cwm_rules
        allGoalRules += goal_rules
    if verbose:
        print 'rules = ', allRules
        print 'goal rules = ', goal_rules
    ruleAssumptions = []
    for rule in rdfsRules + allRules + allGoalRules:
        a  = formulaTMS.getThing(rule)
        ruleAssumptions.append(a)
        a.assume()

    eventStartTime = time.time()
    Formula._isReasoning = True
    FormulaTMS.tracking = False
    while eventLoop:
        eventLoop.next()
    Formula._isReasoning = False
    if verbose:
        print workcount

# See how long it took (minus output)
    now = time.time()
    totalTime = now - startTime
    if verbose:
        print 'time reasoning took=', totalTime
        print '  of which %s was after loading, and %s was actual reasoning' % (now-compileStartTime, now-eventStartTime)
        print '  additionally, %s was in log:semantics, %s of which was parsing' % (llyn.total_time, llyn.load_time)

#    rete.printRete()
    if len(filterProperties) > 0:
        triples = list(reduce(lambda x, y: x + y, [workingContext.statementsMatching(pred=workingContext.newSymbol(property)) for property in filterProperties]))
    else:
        triples = workingContext.statements
    if verbose:
        if triples:
            print 'I can prove the following compliance statements:'
        else:
            print 'There is nothing to prove'
        
    tmsNodes = [formulaTMS.getTriple(triple.subject(), triple.predicate(), triple.object(), None) for triple in triples]
    reasons, premises = supportTrace(tmsNodes)
    reasons, premises = removeFormulae(reasons, premises)
    strings = simpleTraceOutput(tmsNodes, reasons, premises)
    if verbose:
        print '\n'.join(strings)
    f = rdfTraceOutput(store, tmsNodes, reasons, premises, formulaTMS.envs, Rule)
#    import diag
#    diag.chatty_flag = 1000
    return f, workingContext 


knownScenarios = {
    's0' : ( ['http://dig.csail.mit.edu/TAMI/2007/s0/log.n3'],
             ['http://dig.csail.mit.edu/TAMI/2007/s0/mit-policy.n3'] ),
    's0Local' : ( ['../../s0/log.n3'],
                  [  '../../s0/mit-policy.n3'] ),
    's9var2Local' : (['../../s9/variation2/log.n3'],
                     ['../../s9/variation2/policy.n3']),
    's9var1Local' : (['../../s9/variation1/log.n3'],
                     ['../../s9/variation1/policy1.n3', '../../s9/variation1/policy2.n3']),
#                     ['../../s9/variation1/policy.n3']),
#                     ['../../s9/variation1/demo-policy.n3']),
    'arl1Local' : (['../../../../2008/ARL/log.n3'],
                     ['../../../../2008/ARL/udhr-policy.n3']),    
     'arl2Local' : (['../../../../2008/ARL/log.n3'],
                     ['../../../../2008/ARL/unresol-policy.n3']),    
    's4' : (['http://dig.csail.mit.edu/TAMI/2006/s4/background.ttl',
'http://dig.csail.mit.edu/TAMI/2006/s4/categories.ttl',
'http://dig.csail.mit.edu/TAMI/2006/s4/data-schema.ttl',
'http://dig.csail.mit.edu/TAMI/2006/s4/fbi-bru.ttl',
'http://dig.csail.mit.edu/TAMI/2006/s4/fbi-crs.ttl',
'http://dig.csail.mit.edu/TAMI/2006/s4/fbi-tsrs.ttl',
'http://dig.csail.mit.edu/TAMI/2006/s4/purposes.ttl',
'http://dig.csail.mit.edu/TAMI/2006/s4/s4.ttl',
'http://dig.csail.mit.edu/TAMI/2006/s4/tsa-sfdb.ttl',
'http://dig.csail.mit.edu/TAMI/2006/s4/usms-win.ttl'
],
            ['http://dig.csail.mit.edu/TAMI/2006/s4/privacy-act.ttl']),
    'ucsd' : (['http://dig.csail.mit.edu/2008/Talks/0513-UCSD/simple/policy-explicit.n3'],
            ['http://dig.csail.mit.edu/2008/Talks/0513-UCSD/simple/data1.n3']),
    'arl1' : (['http://dig.csail.mit.edu/2008/ARL/log.n3'],
              ['http://dig.csail.mit.edu/2008/ARL/udhr-policy.n3']), 
    'arl2' : (['http://dig.csail.mit.edu/2008/ARL/log.n3'],
             ['http://dig.csail.mit.edu/2008/ARL/unresol-policy.n3']),
    'dhs' : (['http://dig.csail.mit.edu/2009/DHS-fusion/samples/request.n3'],
             ['http://dig.csail.mit.edu/2009/DHS-fusion/samples/uri-content.n3']),
    'dhs2' : (['http://dig.csail.mit.edu/2009/DHS-fusion/samples/request.n3'],
             ['http://dig.csail.mit.edu/2009/DHS-fusion/Mass/MGL_6-172/MGL_temp_1112.n3']),
    'privacy' : (['http://dig.csail.mit.edu/2009/DHS-fusion/PrivacyAct/log.n3'], ['http://dig.csail.mit.edu/2009/DHS-fusion/PrivacyAct/policy.n3']),
    'idm' : (['http://dig.csail.mit.edu/2010/DHS-fusion/MA/rules/MGL_6-172_ONT.n3',
              'file://' + os.path.abspath(os.path.join(os.path.realpath(__file__), '../../tests/mia_analysa.rdf')),
              'file://' + os.path.abspath(os.path.join(os.path.realpath(__file__), '../../tests/frederick_agenti.rdf')),
              'http://dice.csail.mit.edu/xmpparser.py?uri=http://dice.csail.mit.edu/idm/MA/documents/Fake_MA_Request.pdf',
              'http://dice.csail.mit.edu/idm/MA/rules/mgl_sameAs.n3',
              'file://' + os.path.abspath(os.path.join(os.path.realpath(__file__), '../../tests/idm_nonce.n3'))],
             ['http://dice.csail.mit.edu/idm/MA/rules/MGL_6-172.n3']),
    'millie' : (['http://dig.csail.mit.edu/2010/DHS-fusion/MA/rules/MGL_6-172_ONT.n3',
              'http://dig.csail.mit.edu/2010/DHS-fusion/MA/profiles/MiaAnalysa',
              'http://dig.csail.mit.edu/2010/DHS-fusion/MA/profiles/MillieRecruiting',
              'http://dice.csail.mit.edu/xmpparser.py?uri=http://dig.csail.mit.edu/2010/DHS-fusion/MA/documents/Fake_Recruiter_Response.badxmp.pdf',
              'http://dig.csail.mit.edu/2010/DHS-fusion/MA/rules/MGL_66A-1_ONT.n3',
              'http://dig.csail.mit.edu/2010/DHS-fusion/common/fusion_ONT.n3',
              'http://dig.csail.mit.edu/2010/DHS-fusion/MA/rules/mgl_sameAs.n3',
              'file://' + os.path.abspath(os.path.join(os.path.realpath(__file__), '../../tests/millie_nonce.n3'))],
             ['http://dig.csail.mit.edu/2010/DHS-fusion/MA/rules/MGL_6-172.alt.n3']),
}

def runScenario(s, others=[], verbose=False, customBaseRulesURI=False, customBaseFactsURI=False):
    if s[-5:] == 'Local':
        OFFLINE[0] = True
    if s == 'test':
        rules = others[0:1]
        facts = others[1:]
    elif s == 'list':
        for el in others:
            if el[0:5] == 'rules': rules = el[7:-1].replace(',',' ').split()
            elif el[0:4] == 'data': facts = el[6:-1].replace(',',' ').split()
    elif s not in knownScenarios:
        facts = ['http://dig.csail.mit.edu/TAMI/2007/%s/log.n3' % s]
        rules = ['http://dig.csail.mit.edu/TAMI/2007/%s/policy.n3' % s]
 #       raise ValueError("I don't know about scenario %s" % s)
    else:
        facts, rules = knownScenarios[s]
    return testPolicy(facts, rules, verbose=verbose, customBaseRulesURI=customBaseRulesURI, customBaseFactsURI=customBaseFactsURI)

def main():
    global MM
    from optparse import OptionParser
    usage = "usage: %prog [options] scenarioName\n"
    usage + "       %prog [options] test rulesFile logsFile+"
    parser = OptionParser(usage)
    parser.add_option('--profile', dest="profile", action="store_true", default=False,
                      help="""Instead of displaying output, display profile information.
 This requires the hotshot module, and is a bit slow
""")
    parser.add_option('--psyco', '-j', dest='psyco', action="store_true", default=False,
                      help="""Try to use psyco to speed up the program.
Don't try to do this while profiling --- it won't work.
If you do not have psyco, it will throw an ImportError

There are no guarentees this will speed things up instead of
slowing them down. In fact, it seems to slow them down quite
a bit right now
""")
    parser.add_option('--full-unify', dest='fullUnify', action="store_true", default=False,
                      help="""Run full unification (as opposed to simple implication)
of goals. This may compute (correct) answers it would otherwise miss
It is much more likely to simply kill your performance at this time
""")
    parser.add_option('--lookup-ontologies', '-L', dest="lookupOntologies", action="store_true", default=False,
                      help="""Set the cwm closure flag of "p" on all facts loaded.
This will load the ontologies for all properties, until that
converges. This may compute (correct) answers it would otherwise miss
It is much more likely to simply kill your performance at this time.
It may even cause the computation to fail, if a URI 404's or is not RDF.
""")
    parser.add_option('--reasoner', '-r', dest="reasoner", action="store", default="rete",
                      help="""Which reasoner to chose. Current options are
'rete' and 'treat' (without the quotes). The default is 'rete',
which seems faster right now. 'treat' is likely more extensible
for the future, but may still be buggy.
""")
    parser.add_option('--verbose', '-v', dest="verbose", action="store_true", default=False,
                      help="""\"Oh policyrunner, why don't you talk to me the way you used to?\"""")
    parser.add_option('--base-rules', '-R', dest="customBaseRulesURI", action="store", default=False,
                      help="""Set the base rules URI.""")
    parser.add_option('--base-facts', '-F', dest="customBaseFactsURI", action="store", default=False,
                      help="""Set the base facts URI.""")

    (options, args) = parser.parse_args()
    if not args:
        args = ['s0']
    call = lambda : runScenario(args[0], args[1:], options.verbose, options.customBaseRulesURI, options.customBaseFactsURI)
    MM = eval(options.reasoner)
    if options.lookupOntologies:
        loadFactFormula.pClosureMode = True
    if options.fullUnify:
        rete.fullUnify = True
    if options.psyco:
        if options.profile:
            raise ValueError("I can't profile with psyco")
        import psyco
        psyco.log()
        psyco.full()
##        psyco.profile(0.05, memory=100)
##        psyco.profile(0.2)
    if options.profile:
        import sys
        stdout = sys.stdout
        import hotshot, hotshot.stats
        import tempfile
        fname = tempfile.mkstemp()[1]
        if options.verbose:
            print fname
        sys.stdout = null = file('/dev/null', 'w')
        profiler = hotshot.Profile(fname)
        profiler.runcall(call)
        profiler.close()
        sys.stdout = stdout
        null.close()
        if options.verbose:
            print 'done running. Ready to do stats'
        stats = hotshot.stats.load(fname)
        stats.strip_dirs()
        stats.sort_stats('cumulative', 'time', 'calls')
        stats.print_stats(60)
        stats.sort_stats('time', 'cumulative', 'calls')
        stats.print_stats(60)
    else:
        print call().encode("utf-8")

        


if __name__ == '__main__':
    main()

