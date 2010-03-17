#! /usr/bin/python
"""


$Id: cwm_list.py,v 1.13 2007/06/26 02:36:15 syosi Exp $

List and set built-ins for cwm
http://www.w3.org/2000/10/swap/cwm_list.py

See cwm.py and the os module in python

"""


from term import LightBuiltIn, RDFBuiltIn, Function, ReverseFunction, \
    MultipleFunction, MultipleReverseFunction, Term, \
    CompoundTerm, N3Set, List, EmptyList, NonEmptyList, Node, ListBuiltIn
import types

from set_importer import Set

from diag import verbosity, progress
import uripath

from RDFSink import List_NS, Logic_NS, N3_first, N3_rest, N3_nil

from formula import Formula

ListOperationsNamespace = "http://www.w3.org/2000/10/swap/list#"

####################################################################
#
#                    List handling   B U I L T - I N s
#
#
#   Light Built-in classes


class BI_first(RDFBuiltIn, Function, ListBuiltIn):
    def evalObj(self, subj, queue, bindings, proof, query):
        if isinstance(subj, NonEmptyList): return subj.first
#        elif isNonEmptyListTerm(subj): return listify(subj).first
        else: return None

class BI_rest(RDFBuiltIn, Function, ListBuiltIn):
    def evalObj(self, subj, queue, bindings, proof, query):
        if isinstance(subj, NonEmptyList): return subj.rest
#        elif isNonEmptyListTerm(subj): return listify(subj).rest
        else: return None

class BI_last(LightBuiltIn, Function, ListBuiltIn):
    def evalObj(self, subj, queue, bindings, proof, query):
#        if isNonEmptyListTerm(subj): subj = listify(subj)
#        elif not isinstance(subj, NonEmptyList): return None
        if not isinstance(subj, NonEmptyList): return None
        x = subj
        while 1:
            last = x
            x = x.rest
            if isinstance(x, EmptyList): return last.first

##class BI_map(LightBuiltIn, Function):
##    def evalObj(self,subj, queue, bindings, proof, query):
##        print subj
##        store = self.store
##        genID = store.genId()
##        print genID
##        hash = genID.rfind("#")
##        print genID[hash+1:]
##        symbol = genID[:hash]
##        mapped = store.symbol(symbol)
##        class Map(LightBuiltIn, Function):
##            def evalObj(self, subj, queue, bindings, proof, query):
##                print 'hi'
##                return subj
##        
##        mapped.internFrag(genID[hash+1:], Map)
##        return store.symbol(genID)

class BI_in(LightBuiltIn, MultipleReverseFunction, ListBuiltIn):
    """Is the subject in the object?
    Returnes a sequence of values."""
    def eval(self, subj, obj, queue, bindings, proof, query):
#        print isNonEmptyListTerm(obj)
        if isinstance(obj, CompoundTerm): return subj in obj
#        elif isNonEmptyListTerm(obj): return subj in listify(obj)
        else: return None
        

    def evalSubj(self, obj, queue, bindings, proof, query):
        def fixTerm(x):
            if isinstance(x, Term):
                return x
            elif isinstance(x, types.StringTypes):
                return obj.store.intern(x)
        
#        print isNonEmptyListTerm(obj)
#        if not isinstance(obj, NonEmptyList) and not isinstance(obj, N3Set) and not isNonEmptyListTerm(obj): return None
#        elif isNonEmptyListTerm(obj): obj = listify(obj)
        if not isinstance(obj, NonEmptyList) and not isinstance(obj, N3Set): return None
        rea = None
        return [fixTerm(x) for x in obj]  # [({subj:x}, rea) for x in obj]

class BI_member(LightBuiltIn, MultipleFunction, ListBuiltIn):
    """Is the subject in the object?
    Returnes a sequence of values."""
    def eval(self, subj, obj, queue, bindings, proof, query):
        if isinstance(subj, CompoundTerm): return obj in subj
#        elif isNonEmptyListTerm(subj): return obj in listify(subj)
        else: return None

    def evalObj(self,subj, queue, bindings, proof, query):
        def fixTerm(x):
            if isinstance(x, Term):
                return x
            elif isinstance(x, types.StringTypes):
                return subj.store.intern(x)
        
#        if not isinstance(subj, NonEmptyList) and not isinstance(subj, N3Set) and not isNonEmptyListTerm(subj): return None
#        elif isNonEmptyListTerm(obj): subj = listify(subj)
        if not isinstance(subj, NonEmptyList) and not isinstance(subj, N3Set): return None
        rea = None
        return [fixTerm(x) for x in subj] # [({obj:x}, rea) for x in subj]



class BI_append(LightBuiltIn, Function, ListBuiltIn):
    """Takes a list of lists, and appends them together.


    """
    def evalObj(self, subj, queue, bindings, proof, query):
 #       if isNonEmptyListTerm(subj): subj = listify(subj)
 #       elif not isinstance(subj, NonEmptyList): return None
        if not isinstance(subj, NonEmptyList): return None
        r = []
        for x in subj:
            if not isinstance(x, List): return None
            r.extend([a for a in x])
        return self.store.newList(r)

# TODO: How does this work?
class BI_members(LightBuiltIn, Function, ListBuiltIn):
    """Makes a set from a list

    """
    def evaluateObject(self, subj):
#        if isNonEmptyListTerm(subj): subj = listify(subj)
        return Set(subj)
    
#  Register the string built-ins with the store

def register(store):

#    Done explicitly in llyn
#    list = store.internURI(List_NS[:-1])
#    list.internFrag("first", BI_first)
#    list.internFrag("rest", BI_rest)

    ns = store.symbol(ListOperationsNamespace[:-1])
    ns.internFrag("in", BI_in)
    ns.internFrag("member", BI_member)
    ns.internFrag("last", BI_last)
    ns.internFrag("append", BI_append)
    ns.internFrag("members", BI_members)
##    ns.internFrag("map", BI_map)
# ends

