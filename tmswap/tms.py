"""tms.py

A zeroth order attempt at building a TMS



see http://dig.csail.mit.edu/TAMI/2007/amord/tms.scm
"""

import Queue

from py25 import *


class TMS(object):
    def __init__(self, name, event_handler):
        self.name = name
        self.event_handler = event_handler
        self.contradiction = Node(self, "contradiction")

class Node(object):
    nodeCount = 0
    
    def __init__(self, tms, datum=None):
        self.__class__.nodeCount += 1
        self.count = self.nodeCount
        self.tms = tms
        self.datum = datum
        self.supported = False
        self.justifications = set()
        self.consequents = set()

    def justify(self, rule, antecedents, hypotheses=set()):
        if not isinstance(antecedents, frozenset):
            antecedents = frozenset(antecedents)
        c = ConjunctiveJustification(self, rule, antecedents, hypotheses)
        return None

    @property
    def name(self):
        return 'n%s = %s' % (self.count, self.datum)

    def __repr__(self):
        return self.name

    def signal(self, justification):
        (self.tms.event_handler)(self, justification)

    def isContradicted(self):
        return self is self.tms.contradiction

    def premise(self):
        try:
            return [x for x in self.justifications if isinstance(x, Premise)][0]
        except IndexError:
            return None

    def assumed(self):
        just = self.premise()
        if just is None:
            return False
        return just.supported

    def assume(self):
        just = self.premise()
        if just is not None:
            just.supported = True
        else:
            just = Premise(self)
        self.support(just)

    def support(self, justification):
        if self.supported:
            return
        self.supported = True
        self.signal(justification)
        for just in self.consequents:
            if just.supported:
                just.consequent.support(just)

    def retract(self):
        premise = self.premise()
        if premise is None:
            raise RetractionError('Cannot retract a node that was not assumed in the first place, %s' % self)
        premise.supported = False
        if self.supported:
            self.supported = False
            self.signal(False)
            reSupportNodes(self.propagateRetractions())

    def propagateRetractions(self):
        for just in self.consequents:
            if not just.supported:
                for x in just.propagateRetractions():
                    yield x

    def reSupport(self):
        if self.supported:
            return
        self.supported = True
        for just in self.consequents:
            if just.supported:
                just.consequent.reSupport()

    def hasWellFoundedSupport(self, seen=set(), hypotheses=set()):
        if self in seen:
            return False
        elif self in hypotheses:
            return True
        else:
            return any(just.hasWellFoundedSupport(seen.union(self),
                                                                              hypotheses)
                                   for just in self.justifications)


    def supportingAssumptions(self):
        tree = self.supportTree()
        if tree:
            return tree[2]
        return False

    def supportTree(self):

        def walkNode(node, seen, hypotheses):
            if node in seen:
                return False
            seen = seen.union([node])
            jTrees = []
            support = set()
            for just in node.justifications:
                jTree = walkJust(just, node, seen, hypotheses)
                if jTree:
                    jTrees.append(jTree)
                    support.update(jTree[2])
            if not jTrees:
                return False
            return (node, jTrees, support)

        def walkJust(just, node, seen, hypotheses):
            if isinstance(just, Premise):
                if just.supported or just in hypotheses:
                    return (just, [], set([node]))
                else:
                    return False
            else:
                hypotheses = just.hypotheses.union(hypotheses)
                nTrees = []
                support = set()
                for node in just.antecedents:
                    nTree = walkNode(node, seen, hypotheses)
                    if nTree:
                        nTrees.append(nTree)
                        support.update(nTree[2])
                    else:
                        return False # I don't know if this is right
                return (just, nTrees, support.difference(hypotheses))
            
        return walkNode(self, set(), set())

    ##### printing stuff

    def why(self, port=None):
        def f(consequent, just, antecedents, support): 
            writeComment("""(%s) <== (%s %s) | support = %s """ % (consequent.name,
                                                                                  just.rule or just,
                                                                                  ' & '.join(['(%s)' % x.name for x in antecedents]),
                                                                                  support),
                                     port)
        self.walkSupport(f)

    def walkSupport(self, procedure):
        nTree = self.supportTree()
        assert nTree, 'Bad range argument to %s.walkSupport()' % self
        queue = Queue.Queue()  #should I use this? (overkill)
        seen = set()
        def maybeEnqueue(nt):
            if nt[0] not in seen:
                queue.put(nt)
                seen.add(nt[0])
        maybeEnqueue(nTree)
        while not queue.empty():
            nt = queue.get()
            jTrees = nt[1]
            if jTrees:
                jTree = iter(jTrees).next()  # I don't remember if this is needed
                procedure(nt[0],
                                 jTree[0],
                                 [x[0] for x in jTree[1]],
                                 jTree[2])
                for x in jTree[1]:
                    maybeEnqueue(x)

import sys
def writeComment(obj, port=None):
    if port is None:
        port = sys.stdout
        port.write('; %s \n' % obj)


def reSupportNodes(retracted):
    newSupport = True
    while newSupport:
        newSupport = False
        nodes = retracted
        retracted = []
        for node in nodes:
            if node.supported:
                pass
            elif any(just.supported for just in node.justifications):
                newSupport = True
                node.reSupport()
            else:
                retracted.append(node)
    for node in retracted:
        node.signal(False)



###
##  ====== Justifications =============
###
class Justification(object):
    def __init__(self, consequent):
        self._consequent = consequent

    @property
    def consequent(self):
        return self._consequent

    def attach(self):
        node = self.consequent
        for node2 in self.antecedents:
            if self not in node2.consequents: # I don't think this is right
                node2.consequents.add(self)
        node.justifications.add(self)
        if self.supported:
            node.support(self)

    def propagateRetractions(self):
        node = self.consequent
        if node.supported:
            node.supported = False
            yield node
            for x in node.propagateRetractions():
                yield x

    def hasWellFoundedSupport(self, seen, hypotheses):
        new_hyp = hypotheses.union(self.hypotheses)
        return all(node.hasWellFoundedSupports(seen, new_hyp)
                            for node in self.antecedents)
        
        
class Premise(Justification):
    def __init__(self, consequent):
        Justification.__init__(self, consequent)
        self.supported = True
        self.attach()

    @property
    def rule(self):
        return "Premise"
    @property
    def antecedents(self):
        return set()
    @property
    def hypotheses(self):
        return set()

    def hasWellFoundedSupport(self, seen, hypotheses):
        return self.supported


class ConjunctiveJustification(Justification):
    def __init__(self, consequent, rule, antecedents, hypotheses=set()):
        Justification.__init__(self, consequent)
        self.rule = rule
        self.antecedents = antecedents
        self.hypotheses = hypotheses
        self.attach()

    def __repr__(self):
        return '%s(%s,%s,%s, %s)' % ('ConjunctiveJustification', self.consequent,
                                                                           self.rule,
                                                                           self.antecedents,
                                                                           self.hypotheses)

    @property
    def supported(self):
        if all([x.supported for x in self.hypotheses]):
            return all(x.supported for x in self.antecedents)
        return hasWellFounderSupports(self)

test = """

>>> import tms
>>> Tms = tms.TMS('n', lambda node, just: tms.writeComment('%s %s' % (just and 'supported' or 'unsupported', node.name)))
>>> a = tms.Node(Tms, 'A')
>>> b = tms.Node(Tms, 'B')
>>> c = tms.Node(Tms, 'C')
>>> d = tms.Node(Tms, 'D')
>>> e = tms.Node(Tms, 'E')
>>> f = tms.Node(Tms, 'F')
>>> g = tms.Node(Tms, 'G')
>>> h = tms.Node(Tms, 'H')
>>> i = tms.Node(Tms, 'I')
>>> e.justify('MP', [a,b])
>>> e.justify('X', [c])
>>> g.justify('Y', [e])
>>> h.justify('Z', [e,f])
>>> f.justify('W', [c,d])
>>> c.assume()
; supported n4 = C 
; supported n6 = E 
; supported n8 = G 
>>> c.supported
True
>>> e.supported
True
>>> g.why()
; (n8 = G) <== (Y (n6 = E)) | support = set([n4 = C])  
; (n6 = E) <== (X (n4 = C)) | support = set([n4 = C])  
; (n4 = C) <== (Premise ) | support = set([n4 = C])  
>>> c.retract()
; unsupported n4 = C 
; unsupported n6 = E 
; unsupported n8 = G 
>>> a.assume()
; supported n2 = A 
>>> b.assume()
; supported n3 = B 
; supported n6 = E 
; supported n8 = G 
>>> c.assume()
; supported n4 = C 
>>> d.assume()
; supported n5 = D 
; supported n7 = F 
; supported n9 = H 
>>> a.retract()
; unsupported n2 = A 
>>> h.why()
; (n9 = H) <== (Z (n6 = E) & (n7 = F)) | support = set([n4 = C, n5 = D])  
; (n6 = E) <== (X (n4 = C)) | support = set([n4 = C])  
; (n7 = F) <== (W (n4 = C) & (n5 = D)) | support = set([n4 = C, n5 = D])  
; (n4 = C) <== (Premise ) | support = set([n4 = C])  
; (n5 = D) <== (Premise ) | support = set([n5 = D])  
>>> c.retract()
; unsupported n4 = C 
; unsupported n6 = E 
; unsupported n8 = G 
; unsupported n9 = H 
; unsupported n7 = F 
>>> c.assume()
; supported n4 = C 
; supported n6 = E 
; supported n8 = G 
; supported n7 = F 
; supported n9 = H 
>>> d.retract()
; unsupported n5 = D 
; unsupported n7 = F 
; unsupported n9 = H 
>>> i.justify('U', [f])
>>> i.justify('Q', [g])
; supported n10 = I 
>>> d.justify('R', [i])
; supported n5 = D 
; supported n7 = F 
; supported n9 = H 
>>> h.why()
; (n9 = H) <== (Z (n6 = E) & (n7 = F)) | support = set([n4 = C])  
; (n6 = E) <== (X (n4 = C)) | support = set([n4 = C])  
; (n7 = F) <== (W (n4 = C) & (n5 = D)) | support = set([n4 = C])  
; (n4 = C) <== (Premise ) | support = set([n4 = C])  
; (n5 = D) <== (R (n10 = I)) | support = set([n4 = C])  
; (n10 = I) <== (Q (n8 = G)) | support = set([n4 = C])  
; (n8 = G) <== (Y (n6 = E)) | support = set([n4 = C])  
>>> c.retract()
; unsupported n4 = C 
; unsupported n6 = E 
; unsupported n8 = G 
; unsupported n9 = H 
; unsupported n7 = F 
; unsupported n10 = I 
; unsupported n5 = D 
>>> a.assume()
; supported n2 = A 
; supported n6 = E 
; supported n8 = G 
; supported n10 = I 
; supported n5 = D 
>>> d.why()
; (n5 = D) <== (R (n10 = I)) | support = set([n2 = A, n3 = B])  
; (n10 = I) <== (Q (n8 = G)) | support = set([n2 = A, n3 = B])  
; (n8 = G) <== (Y (n6 = E)) | support = set([n2 = A, n3 = B])  
; (n6 = E) <== (MP (n2 = A) & (n3 = B)) | support = set([n2 = A, n3 = B])  
; (n2 = A) <== (Premise ) | support = set([n2 = A])  
; (n3 = B) <== (Premise ) | support = set([n3 = B])  
>>> c.assume()
; supported n4 = C 
; supported n7 = F 
; supported n9 = H 
>>> c.retract()
; unsupported n4 = C 
; unsupported n7 = F 
; unsupported n9 = H 

"""

__test__ = {'tms' : test}
    
if __name__ == '__main__':
    import doctest
    doctest.testmod()
