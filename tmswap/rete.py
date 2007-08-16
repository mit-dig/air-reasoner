"""Rete.py

a rete implementation independant of pychinko, that uses IndexedFormula


This is based heavily on {}
Some inspiration for this came from pychinko; though not enough


"""

import weakref
WKD = weakref.WeakKeyDictionary
from collections import deque

from term import unify, Env
from formula import Formula

from py25 import dequeRemove

def compilePattern(index, patterns, vars):
    current = EmptyRoot
    patterns.sort()
    for pattern in patterns:
        alpha = AlphaFilter.build(index, pattern, vars)
        current = JoinNode(current, alpha)
        current = BetaMemory(current)
    return current
    

WMEData = WKD()

class WME(object):
    def __init__(self):
        self.alphaMemItems = []
        self.tokens = set()


def removeStatement(s):
    W = WMEData[s]
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
    def __init__(self, triple, env):
        self.triple = triple
        self.env = env

    def __eq__(self, other):
        if isinstance(other, TripleWithBinding):
            return self.triple == other.triple and self.env == other.env
        return self.triple == other


    def __repr__(self):
        return '%s(%s,%s)' % ('TWB', self.triple, self.env)


class AlphaMemory(list):
    def __init__(self):
        self.successors = deque()
        self.empty = True
        list.__init__(self)

    def add(self, s):
        self.append(s)
        W = WMEData.setdefault(s, WME())
        W.alphaMemItems.append(self)
        for c in self.successors:
            c.rightActivate(s)
        self.empty = False


class AlphaFilter(AlphaMemory):
    def __init__(self, pattern, vars):
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
        self.vars = freeVariables | existentialVariables
        AlphaMemory.__init__(self)
    def rightActivate(self, s): # Badly named, but ...
        for env, _ in unify(self.pattern, s, vars = self.vars):
            self.add(TripleWithBinding(s, env))

    @classmethod
    def build(cls, index, pattern, vars):
        def replaceWithNil(x):
            if isinstance(x, Formula) or x.occurringIn(vars):
                return None
            return x
        patternTuple = tuple(replaceWithNil(x) for x in (pattern.predicate(),
                                                         pattern.subject(),
                                                         pattern.object()))
        primaryAlpha = index.setdefault(patternTuple, AlphaMemory())
        for secondaryAlpha in primaryAlpha.successors:
            if secondaryAlpha.pattern == pattern:
                return secondaryAlpha
        secondaryAlpha = cls(pattern, vars)
        primaryAlpha.successors.appendleft(secondaryAlpha)
        for triple in primaryAlpha:
            secondaryAlpha.rightActivate(triple)
        return secondaryAlpha


class Token(object):
    def __init__(self, node, parent, current, env):
        """It is not the job of this function to compute
        the new env; indeed, because that operation
        could fail.


        """
        self.parent = parent
        assert not isinstance(current, TripleWithBinding)
        self.current = current
        self.node = node
        self.children = set()
        self.env = env
        parent.children.add(self)
        WMEData[current].tokens.add(self)

    def delete(self):
        while self.children:
            t = self.children.pop()
            t.delete()
        self.node.removeItem(self)
        W = WMEData[self.current]

    def flatten(self):
        retVal, _ = self.parent.flatten()
        retVal.append(self.current)
        return (retVal, self.env)
                


class NullTokenClass(object):
    __one__ = None
    def __new__(cls):
        if cls.__one__:
            return cls.__one__
        self = object.__new__(cls)
        cls.__one__ = self
        self.children = set()
        self.env = Env()
        return self

    def flatten(self):
        return ([], self.env)
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
        return self
EmptyRoot = EmptyRootClass()


class BetaMemory(ReteNode):
    def __new__(cls, parent):
        for B in parent.children:
            if isinstance(B, cls):
                return B  # A join node should only have one child!
        self = ReteNode.__new__(cls, parent)
        self.items = set()
        self.allChildren = set()
        self.empty = True
        self.updateFromAbove()
        return self

    def leftActivate(self, token, triple, newBinding):
        newToken = Token(self, token, triple, newBinding)
        self.items.add(newToken)
        for c in self.children:
            c.leftActivate(newToken)
        self.empty = False


    def updateFromAbove(self):
        parent = self.parent
        parentChildren = parent.children
        parent.children = set([self])
        for triple in parent.alphaNode:
            parent.rightActivate(triple)
        parent.children = parentChildren

    def removeItem(self, item):
        self.items.remove(item)
        if not self.items:
            self.empty = True
            for c in self.children:
                if isinstance(c, JoinNode):
                    dequeRemove(c.alphaNode.successors, c)

class JoinNode(ReteNode):
    def __new__(cls, parent, alphaNode):
        for child in parent.allChildren:
            if isinstance(child, cls) and child.alphaNode == alphaNode:
                return child
        self = ReteNode.__new__(cls, parent)
        self.alphaNode = alphaNode
        if not parent.empty:
            self.alphaNode.successors.appendleft( self)
            if alphaNode.empty:
                parent.children.remove(self)
        return self

    def leftActivate(self, token):
        if self.parent.empty:
            self.relinkAlpha()
            if self.alphaNode.empty:
                self.parent.children.remove(self)
        for i in self.alphaNode:
            triple = i.triple
            env = i.env
            newBinding = self.test(token, env)
            if newBinding is not None:
                for c in self.children:
                    c.leftActivate(token, triple, newBinding)


    def test(self, token, env2):
        env = token.env
        newEnv = env
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
        for token in self.parent.items:
            triple = triple_holder.triple
            env = triple_holder.env
            newBinding = self.test(token, env)
            if newBinding is not None:
                for c in self.children:
                    c.leftActivate(token, triple, newBinding)
        

    def relinkAlpha(self):
        self.alphaNode.successors.appendleft( self)
    def relinkBeta(self):
        self.parent.children.add(self)



    
class ProductionNode(ReteNode):
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
