"""Rete.py

a rete implementation independant of pychinko, that uses IndexedFormula


This is based heavily on RETE-UL from
   http://reports-archive.adm.cs.cmu.edu/anon/1995/CMU-CS-95-113.pdf
Some inspiration for this came from pychinko; though not enough


"""

import weakref
WKD = weakref.WeakKeyDictionary
from collections import deque
import itertools

from term import unify, Env
from formula import Formula, StoredStatement, WME

from py25 import dequeRemove
VAR_PLACEHOLDER = object()

fullUnify = False

def compilePattern(index, patterns, vars, buildGoals=False, goalPatterns=False, builtinMap={}):
    """This builds the RETE network"""
    current = EmptyRoot
    patterns.sort()
    for pattern in sortPatterns(patterns):
        alpha = AlphaFilter.build(index, pattern, vars, builtinMap=builtinMap)
        current = JoinNode(current, alpha, buildGoals)
        current = BetaMemory(current)
    return current
    
#### Dealing with builtins
## We need code to do a sort of sort here.
## A naive topological sort may not work
## Triples will rely on variables only --- but we are sorting triples, not variables

class CyclicError(ValueError): pass

def sortPatterns(patterns):
    """return a better order for the patterns, based on a topological - like sort"""
    return patterns # This is not used right now
    requires = {}
    provides = {}
    for pattern in patterns:
        for var in pattern.requires:
            requires.setdefault(var, set()).add(pattern)
        for var in pattern.provides:
            provides.setdefault(var, set()).add(pattern)


    def getTopologically():
        nodes = patterns
        inDegrees = {}
        for node in nodes:
            inDegrees[node] = len(node.requires)
        zeros = deque()
        for node in nodes:
            if inDegrees[node] == 0:
                zeros.appendleft(node)
        provided = set()
        while zeros:
            top = zeros.pop()
            yield top
            for var in top.provides:
                if var in provided:
                    continue
                else:
                    for node in requires.get(var, []):
                        inDegrees[node] = inDegrees[node] - 1
                        if inDegrees[node] == 0:
                            zeros.appendleft(node)
                    provided.add(var)
        if max(inDegrees.values()) != 0:
            raise CyclicError

    return list(getTopologically())

    

### end builtins

class BogusTripleError(RuntimeError):
    pass

class BogusTriple(StoredStatement):  
    def __init__(self, triple):
        raise BogusTripleError('The building of BogusTriples should have been stopped')
        if hasattr(triple, 'quad'):
            triple = triple.quad
        StoredStatement.__init__(self, triple)

    def __repr__(self):
        return 'BogusTriple(%s)' % (self.quad,)


#WMEData = WKD()



def removeStatement(s):
    W = s.WME
    for item in W.alphaMemItems:
        item.remove(s)
        if not item:
            item.empty = True
            for node in item.successors:
                if isinstance(node, JoinNode):
                    node.parent.children.remove(node)
        while W.tokens:
            t = W.tokens.pop()
            t.delete()



class TripleWithBinding(object):
    """A (triple, binding) pair to pass from an alpha node to a beta node
"""
    def __init__(self, triple, env):
        self.triple = triple
        self.env = env
        self.WME = WME()

    def __eq__(self, other):
        if isinstance(other, TripleWithBinding):
            return self.triple == other.triple and self.env == other.env
        return self.triple == other


    def __repr__(self):
        return '%s(%s,%s)' % ('TWB', self.triple, self.env)


class AlphaMemory(list):
    """An alpha memory node matched triples against one triple of the pattern.
This base class only knows variables, and is part of the IndexedFormula.
"""
    def __init__(self):
        self.successors = deque()
        self.empty = True
        list.__init__(self)

    def add(self, s):
        self.append(s)
        W = s.WME
        W.alphaMemItems.append(self)
        for c in self.successors:
            c.rightActivate(s)
        self.empty = False


class AlphaFilter(AlphaMemory):
    """An alphaFilter connects an alpha node to a join node. It has the full pattern, and
generates variable bindings
"""
    def __init__(self, pattern, vars):
        self.penalty = 10
        self.pattern = pattern
        freeVariables = vars
        def findExistentials(x):
            if hasattr(x, 'spo'):
                return findExistentials(x.spo())
            elif hasattr(x, 'existentials'):
                ex = frozenset(x.existentials())
                for s in x.statements:
                    ex = ex | findExistentials(s)
                return ex
            elif hasattr(x, '__iter__'):
                ex = frozenset()
                for n in x:
                    ex = ex | findExistentials(n)
                return ex
            else:
                return frozenset()
        existentialVariables = findExistentials(pattern)
        self.vars = pattern.occurringIn(freeVariables | existentialVariables)
        AlphaMemory.__init__(self)

    @property
    def provides(self):
        return self.vars

    @property
    def requires(self):
        return frozenset()

    def buildVarIndex(self, successor):
        return tuple(sorted(list(self.vars & successor.vars)))


    varCounter = itertools.count()
    def rightActivate(self, s):
        if s.variables:
            var_bindings = {}
            for var in s.variables:
                newVar = s.context().newSymbol('http://example.com/alphaFilter#var%s' % self.varCounter.next())
                var_bindings[var] = newVar
                newVar.isVariable = True
            try:
                s2 = s.substitution(var_bindings)
            except TypeError:
                raise ValueError(s, type(s))
            s2.variables  = frozenset(var_bindings.values())
        else:
            s2 = s
        for  unWantedBindings, env in unify(s2, self.pattern, vars = self.vars | s2.variables): #
            if s2.variables.intersection(env.asDict().values()):
                print 'we have trouble with %s' % s2.variables.intersection(env.asDict().values())
                # We are in trouble here!
            if fullUnify or not frozenset(unWantedBindings.asDict().values()).difference(self.vars): # bad, but speeds things up
                self.add(TripleWithBinding(s, env))

    @classmethod
    def build(cls, index, pattern, vars, builtinMap):
        def replaceWithNil(x):
            if isinstance(x, Formula) or x.occurringIn(vars):
                return None
            return x
        masterPatternTuple = tuple(replaceWithNil(x) for x in (pattern.predicate(),
                                                         pattern.subject(),
                                                         pattern.object()))
        
        secondaryAlpha = cls(pattern, vars)
        p, s, o = masterPatternTuple
        V = VAR_PLACEHOLDER
        pts = [(p, s, o)]
        for loc in 0, 1, 2:
            if masterPatternTuple[loc] is not None:
                newpts = []
                for t in pts:
                    newtuple = list(t)
                    newtuple[loc] = V
                    newtuple = tuple(newtuple)
                    newpts.append(t)
                    newpts.append(newtuple)
                pts = newpts
        for patternTuple in pts:
            primaryAlpha = index.setdefault(patternTuple, AlphaMemory())
            for secondaryAlpha2 in primaryAlpha.successors:
                if secondaryAlpha2.pattern == pattern:
                    return secondaryAlpha2
            primaryAlpha.successors.appendleft(secondaryAlpha)
            for triple in primaryAlpha:
                secondaryAlpha.rightActivate(triple)
        return secondaryAlpha

    def triplesMatching(self, successor, env, includeMissing=False): # This is fast enough
        retVal = self   # No reason to do additional work here
        if includeMissing:
            return retVal + [TripleWithBinding(BogusTriple(self.pattern), Env())]
        return retVal


class Token(object):
    """A token is a partial match, stored in a beta node
"""
    def __init__(self, node, parent, current, env, penalty=0):
        """It is not the job of this function to compute
        the new env; indeed, because that operation
        could fail.


        """
        self.penalty = penalty + parent.penalty
        self.parent = parent
        assert not isinstance(current, TripleWithBinding)
        self.current = current
        self.node = node
        self.children = set()
        self.env = env
        parent.children.add(self)
        current.WME.tokens.add(self)

    def delete(self):
        self.parent.children.remove(self)
        while self.children:
            t = self.children.pop()
            t.delete()
        self.node.removeItem(self)
        W = self.current.WME

    def fail(self):
        self.parent.children.remove(self)
        self.current.WME.tokens.remove(self)

    def flatten(self):
        retVal, _, __ = self.parent.flatten()
        retVal.append(self.current)
        return (retVal, self.env, self.penalty)
                


class NullTokenClass(object):
    """There is one empty null token, representing an unstarted match.
"""
    __one__ = None
    def __new__(cls):
        if cls.__one__:
            return cls.__one__
        self = object.__new__(cls)
        cls.__one__ = self
        self.children = set()
        self.env = Env()
        self.penalty = 0
        return self

    def flatten(self):
        return ([], self.env, 0)
NullToken = NullTokenClass()


class ReteNode(object):
    def __new__(cls, parent):
        self = object.__new__(cls)
        self.parent = parent
        self.children = set()
        self.parent.children.add(self)
        if hasattr(parent, 'allChildren'):
            parent.allChildren.add(self)
        return self

class EmptyRootClass(ReteNode):
    """There is one empty root node, the root of the tree of rete nodes
It has nothing matched yet.
"""
    __one__ = None
    def __new__(cls):
        if cls.__one__:
            return cls.__one__
        self = object.__new__(cls)
        cls.__one__ = self
        self.items = set([NullToken])
        self.empty = False
        self.children = set()
        self.allChildren = set()
        self.vars = frozenset()
        self.varTuple = ()
        return self
EmptyRoot = EmptyRootClass()


class BetaMemory(ReteNode):
    """A beta memory stores Tokens, received from the one parent join node
"""
    def __new__(cls, parent):
        for B in parent.children:
            if isinstance(B, cls):
                return B  # A join node should only have one child!
        self = ReteNode.__new__(cls, parent)
        self.items = set()
        self.allChildren = set()
        self.empty = True
        self.vars = self.parent.vars
        self.updateFromAbove()
        return self

    def leftActivate(self, token, triple, newBinding, penalty=0):
        newToken = Token(self, token, triple, newBinding, penalty=penalty)
        if newToken.penalty > 10:
            newToken.fail()
            return
        self.items.add(newToken)
        for c in self.children.copy():
            c.leftActivate(newToken)
        self.empty = False


    def updateFromAbove(self):
        parent = self.parent
        parentChildren = parent.children
        parent.children = set([self])
        for item in parent.parent.items.copy():
            parent.leftActivate(item)
        parent.children = parentChildren

    def removeItem(self, item):
        try:
            self.items.remove(item)
        except KeyError:
            raise ValueError(item.flatten(), [x.flatten() for x in self.items])
        if not self.items:
            self.empty = True
            for c in self.children:
                if isinstance(c, JoinNode):
                    dequeRemove(c.alphaNode.successors, c)

class JoinNode(ReteNode):
    """A join node combines matches from a beta memory and an alphaFilter
to get larger matches.
"""
    def __new__(cls, parent, alphaNode, buildGoals=False):
        for child in parent.allChildren:
            if isinstance(child, cls) and child.alphaNode is alphaNode:
                return child
        self = ReteNode.__new__(cls, parent)
        self.alphaNode = alphaNode
        self.vars = self.parent.vars | self.alphaNode.vars
        if not parent.empty:
            self.alphaNode.successors.appendleft(self)
            if alphaNode.empty:
                parent.children.remove(self)
        self.varIndex = self.alphaNode.buildVarIndex(self)
        if buildGoals:
            raise BogusTripleError('Goal building is dead. Long live goal building')
        self.makesGoals = buildGoals
        return self

    def leftActivate(self, token):
        if self.parent.empty:
            self.relinkAlpha()
            if self.alphaNode.empty:
                self.parent.children.remove(self)
        matchedSomething = False
        for i in self.alphaNode.triplesMatching(self, token.env, self.makesGoals):
            triple = i.triple
            env = i.env
            newBinding = self.test(token, env)
            if newBinding is not None:
                matchedSomething = True
                for c in self.children:
                    c.leftActivate(token, triple, newBinding)


    def test(self, token, env2):  # Not good enough! need to unify somehow....
        env = token.env
        newEnv = env
##        newEnvs = [Env()]
##        allKeys = frozenset(env1.keys()) | frozenset(env2.keys())
##        for key in allKeys:
##            val1, source1 = env1.dereference(key)
##            val2, source2 = env1.dereference(key)
##            oldNewEnvs = newEnvs
##            newEnvs = []
##            for newEnv in oldNewEnvs:
##                newEnvs.extend([x[0] for x in unify(val1, val2, vars=self.vars, bindings=newEnv, n1Source=source1, n2Source=source2) ])
##        print newEnvs
##        if not newEnvs:
##            return None
##        return newEnvs[0]
                    


        
        for var, (val, source) in env2.items():
            if var in env:
                if env[var] == val:
                    pass
                else:
                    return None
            else:
                newEnv = newEnv.bind(var, (val, source))
        return newEnv

    def rightActivate(self, triple_holder):
        if self.alphaNode.empty:
            self.relinkBeta()
            if self.parent.empty:
                dequeRemove(self.alphaNode.successors, self)
        triple = triple_holder.triple
        env = triple_holder.env
        for token in self.parent.items:
            newBinding = self.test(token, env)
            if newBinding is not None:
##                if token in self.falseMatches:
##                    falseTriple = self.falseMatches[token]
##                    del self.falseMatches[token]
##                    if False and self.retractTriple is not None:
##                        self.retractTriple(falseTriple)
                for c in self.children:
                    c.leftActivate(token, triple, newBinding)
        

    def relinkAlpha(self):
        self.alphaNode.successors.appendleft( self)
    def relinkBeta(self):
        self.parent.children.add(self)



    
class ProductionNode(ReteNode):
    """A production node sits at the leaf of the node tree,
with a method to call when the match succeeds
"""
    def __new__(cls, parent, task, alternative = None):
        self = ReteNode.__new__(cls, parent)
        self.items = set()
        self.task = task
        self.alternative = alternative
        self.updateFromAbove()
        if not self.items:
            self.alternative()
        return self

    def leftActivate(self, token):
        token = Token(self, token.parent, token.current, token.env)
        self.items.add(token)
        self.task(token.flatten())

    def updateFromAbove(self):
        for token in self.parent.items:
            self.leftActivate(token)

    def removeItem(self, item):
        self.items.remove(item)
        if not self.items:
            if self.alternative:
                self.alternative()



#####=================

def compilePatternTester(parentFormula, patternFormula):
    index = parentFormula._index
    patterns = patternFormula.statements
    vars = parentFormula.universals()
    bottomBeta = compilePattern(index, patterns, vars)
    def onSuccess((triples, env)):
        print 'success, pattern=%s, triples=%s, env=%s' % (patterns, triples, env)
    def onFailure():
        print 'failure, pattern=%s' % patterns
    trueBottom = ProductionNode(bottomBeta, onSuccess, onFailure)
    return trueBottom

def test():
	socrates = store.newSymbol('http://www.example.com/#socrates')
	ty = store.first.resource['type']
	man = store.newSymbol('http://www.example.com/#Man')
	X = workingContext.newUniversal('http://www.example.com/#X')
	f = store.newFormula()
	f.add(X, ty, man)
	f = f.close()
	b = rete.compilePatternTester(workingContext, f)
	workingContext.add(socrates, ty, man)
	workingContext.removeStatement(workingContext.statementsMatching(subj=socrates, pred=ty, obj=man)[0])
	return b


def test2():
	socrates = store.newSymbol('http://www.example.com/#socrates')
	ty = store.first.resource['type']
	man = store.newSymbol('http://www.example.com/#Man')
	X = workingContext.newUniversal('http://www.example.com/#X')
	f = store.newFormula()
	f.add(X, ty, man)
	f = f.close()
	workingContext.add(socrates, ty, man)
	b = rete.compilePatternTester(workingContext, f)
	workingContext.removeStatement(workingContext.statementsMatching(subj=socrates, pred=ty, obj=man)[0])
	return b


def test3():
	socrates = store.newSymbol('http://www.example.com/#socrates')
	aristotle = store.newSymbol('http://www.example.com/#Aristotle')
	ty = store.first.resource['type']
	man = store.newSymbol('http://www.example.com/#Man')
	greek = store.newSymbol('http://www.example.com/#Greek')
	X = workingContext.newUniversal('http://www.example.com/#X')
	f = store.newFormula()
	f.add(X, ty, man)
	f.add(X, ty, greek)
	f = f.close()
	workingContext.add(socrates, ty, greek)
	workingContext.add(aristotle, ty, man)
	b = rete.compilePatternTester(workingContext, f)
	workingContext.add(socrates, ty, man)
	workingContext.removeStatement(workingContext.statementsMatching(subj=socrates, pred=ty, obj=man)[0])
	return b


def printRete():
    knownNodes = set([EmptyRoot])
    alreadyPrinted = set()
    while knownNodes.difference(alreadyPrinted):
        node = knownNodes.difference(alreadyPrinted).pop()
        alreadyPrinted.add(node)
        print 'node %s' % node
        print '  of type %s' % node.__class__.__name__
        print '  ---> children %s' % node.children
        if hasattr(node, 'items'):
            print '  ----> items : %s' % [x.flatten() for x in node.items]
        if hasattr(node, 'alphaNode'):
            print ' ----> alphaNode %s' % node.alphaNode
            print ' ----------> pattern %s' % node.alphaNode.pattern
            print ' ----------> vars %s' % node.alphaNode.vars
        if hasattr(node, 'allChildren'):
            print ' ----> allChildren %s' % node.allChildren
            for c in node.allChildren:
                knownNodes.add(c)
        for c in node.children:
            knownNodes.add(c)

        
        
    

if __name__ == '__main__':
    from tmswap import rete
    from tmswap import llyn
    store = llyn.RDFStore()
    workingContext = store.newFormula()
    workingContext.stayOpen = True
    test()
    test2()
    test3()
