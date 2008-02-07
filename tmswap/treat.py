"""Treat.py

a TREAT implementation, to see if it performs better / is
 more flexible than rete.py

the interface should be the same!

"""


import weakref
WKD = weakref.WeakKeyDictionary
from collections import deque
import itertools

from term import unify, Env
from formula import Formula, StoredStatement, WME

from py25 import dequeRemove, min

from rete import (fullUnify,
                  VAR_PLACEHOLDER,
                  AlphaFilter)

from operator import or_

def Union(*args):
    return reduce(or_, args, frozenset())

class BindingFilter(AlphaFilter):
    def substitution(self, bindings):
        if not bindings:
            return self
        pattern = self.pattern.substitution(bindings)
        return self.construct(self.index, pattern, self.vars, self.builtinMap)

def compilePattern(index, patterns, vars,
                   buildGoals=False, goalPatterns=False, builtinMap={}):
    """This builds the TREAT"""
    filters = []
    for pattern in patterns:
        filters.append(BindingFilter.build(index,
                                         pattern,
                                         vars,
                                         builtinMap=builtinMap))
    return Matcher(filters)


class Matcher(object):
    def __init__(self, filters):
        self.vars = Union(*[x.vars for x in filters])
        self.children = set()
        self.filters = filters
        for f in filters:
            f.successors.appendleft(Activator(self,
                                              f,
                                              [x for x in filters if x is not f]))


    def match(self, alphas, env=Env(), triples=None):
        if not triples:
            triples = []
        if not alphas:
            self.done((triples, env, 0))
            return
        bindings = env.asDict()
        alphas = [x.substitution(bindings) for x in alphas]
        top = min(alphas, key=len)
        rest = [x for x in alphas if x is not top]
        top.initialize()
        for triple_holder in top.triplesMatching(self, env):
            triple = triple_holder.triple
            env2 = triple_holder.env  
            just = triples + [triple]
            env3 = env.flatten(env2)
            if not rest:
                self.done((just, env3, 0))

            else:
                self.match(rest, env3, just)
            
    def done(self, tok):
        for child in self.children:
            child.leftActivate(tok)

    def run(self, prod):
        children = self.children
        try:
            self.children = set([prod])
            self.match(self.filters)
        finally:
            self.children = children

class Activator(object):
    def __init__(self, matcher, node, others):
        self.matcher = matcher
        self.node = node
        self.others = others

    def rightActivate(self, triple_holder):
        triple = triple_holder.triple
        env = triple_holder.env        
        self.matcher.match(self.others, env, [triple])

class ProductionNode(object):
    """A production node sits at the leaf of the node tree,
with a method to call when the match succeeds
"""
    def __new__(cls, parent, task, alternative = None):
        self = object.__new__(cls)
        self.parent = parent
        parent.children.add(self)
        self.items = set()
        self.task = task
        self.alternative = alternative
        self.updateFromAbove()
        if not self.items:
            self.alternative()
        return self

    def leftActivate(self, token):
        self.items.add(id(token))
        self.task(token)

    def updateFromAbove(self):
        self.parent.run(self)

    def removeItem(self, item):
        self.items.remove(id(item))
        if not self.items:
            if self.alternative:
                self.alternative()

