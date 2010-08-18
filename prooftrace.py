"""prooftrace.py

Given a tms, generate proof traces


"""

import tms
from formula import Formula, StoredStatement
from term import List, Env, Symbol, Fragment, Literal

def supportTrace(tmsNodes):
    """Construct a list of reasons and premises for a set of tmsNodes???"""
    pending = set()
    reasons = {}
    premises = set()
    def nf(self):
        """Recursively populate reasons by seeing if this is a premise, or if
        a justification can be given a reason???"""
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
    """Remove formulae from the lists of reasons, given a set of premises???"""
    newReasons = {}
    premises = premises.copy()
    for node, reason in reasons.items():
        if node in premises:
            newReasons[node] = reason
        else:
            nodes = reasons[node].expression.nodes()
            if len(nodes) == 1:
                parent = list(nodes)[0]
                if isinstance(parent.datum, Formula):
                    newReasons[node] = reasons[parent]
                    if parent in premises:
                        premises.add(node)
                else:
                    newReasons[node] = reason
            else:
                newReasons[node] = reason
    return newReasons, premises

def removeBaseRules(reasons, premises, baseRules):
    """Remove from the reasons anything that is based on a rule in the set
    of baseRules."""
    newExpressions = dict((node, reasons[node].expression)
                          for node in reasons
                          if node not in premises)
    baseNodes = frozenset(node for node in reasons
                          if node not in premises and ((reasons[node].rule in baseRules)
                              or (hasattr(reasons[node].rule, 'name') and reasons[node].rule.name in baseRules)))
    
    changed = True
    doneNewExpressions = {}

    def expressionSubstitutionFunc(expression, bindings):
        """Return the expression with bindings substituted."""
        nodes = []
        for node in expression.args:
            if isinstance(node, tms.BooleanExpression):
                nodes.append(expressionSubstitution(node, bindings))
            else:
                nodes.append(bindings.get(node, node))
        if isinstance(expression, tms.NotExpression):
            return tms.NotExpression(nodes[0])
        return expression.__class__(nodes)
        

    mem = {}
    def expressionSubstitution(expression, bindings):
        """Memoized expressionSubstitutionFunc."""
        bindingsVal = frozenset(bindings.items())
        try:
            return mem[(expression, bindingsVal)]
        except KeyError:
            mem[(expression, bindingsVal)] = expressionSubstitutionFunc(expression, bindings)
            return mem[(expression, bindingsVal)]
    
    # Breadth-first traversal.
    while newExpressions:
        for node in list(newExpressions.keys()):
            expression = newExpressions[node]
            nodes = expression.nodes()
            problemNodes = nodes.intersection(baseNodes)
            if problemNodes:
                replacementExpressions = {}
                for probNode in problemNodes:
                    if probNode in doneNewExpressions:
                        replacementExpressions[probNode] = doneNewExpressions[probNode]
                    else:
                        replacementExpressions[probNode] = newExpressions[probNode]
                newExpressions[node] = expressionSubstitution(expression, replacementExpressions)
            else:
                doneNewExpressions[node] = expression
                del newExpressions[node]
    return doneNewExpressions

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
        elif self in reasons:
            retVal = reasons[self].evaluate(nf2)
            strings.append('%s <= %s(%s)' % (self, reasons[self].rule.uriref(), ', '.join([str(x) for x in reasons[self].expression.nodes()])))
        else:
            # Sometimes when not filtering on the properties when
            # doing AIR reasoning, self may not be in premises or
            # reasons (why???)
            # TODO: find out why.
            retVal = True
            strings.append('%s [assuming to be premise]' % self)
        return retVal
    for tmsNode in tmsNodes:
        nf2(tmsNode)
    return strings

#def eventFragmentGenerator():
#    # Generate a fragment to represent an event uniquely.
#    i = 0
#    while True:
#        i += 1
#        yield "#event%d" % (i)

#mintEventFragment = eventFragmentGenerator().next

#def dataIDGenerator():
#    # Generate a fragment to represent log-file semantics uniquely.
#    i = 0
#    while True:
#        i += 1
#        yield "log%d" % (i)

#mintDataID = dataIDGenerator().next

def rdfTraceOutput(store, tmsNodes, reasons, premises, Rule):
    formula = store.newFormula()
    t = formula.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/tms')
    air = formula.newSymbol('http://dig.csail.mit.edu/2009/AIR/air')
    airj = formula.newSymbol('http://dig.csail.mit.edu/2009/AIR/airjustification')
    pmll = formula.newSymbol('http://www.example.com/pmllite')
    done = set()
    termsFor = {}
    newTermsFor = {}
    expressions = removeBaseRules(reasons, premises, Rule.baseRules)
##    expressions = dict((node, reasons[node].expression)
##                       for node in reasons
##                       if node not in premises)
    for justification in reasons.values():
        termsFor[justification] = formula.newBlankNode()

    def booleanExpressionToRDF(expr):
        if expr in termsFor:
            return termsFor[expr]
        node = formula.newBlankNode()
        termsFor[expr] = node
        newTermsFor[expr] = None
        formula.add(node, store.type, {tms.NotExpression: t['Not-justification'],
                                       tms.AndExpression: t['And-justification'],
                                       tms.OrExpression: t['Or-justification']}[expr.__class__])
        if isinstance(expr, tms.AndExpression):
            #We have a shorthand!
            newFormula = formula.newFormula()
            for arg in expr.args:
                node2 = booleanExpressionToRDF(arg)
                if isinstance(node2, Formula):
                    newFormula.loadFormulaWithSubstitution(node2)
                else:
                    formula.add(node, t['sub-expr'], node2)
            formula.add(node, t['sub-expr'], newFormula.close())
        else:
            for arg in expr.args:
                formula.add(node, t['sub-expr'], booleanExpressionToRDF(arg))
        return node

    def booleanExpressionToNewRDF(expr, hasHiddenAncestor=False):
        if expr in termsFor and expr not in newTermsFor:
            return termsFor[expr]
        elif expr in newTermsFor and newTermsFor[expr] is not None:
            return newTermsFor[expr]
        
        # Are we generating a named node (Belief-node with no
        # Hidden-node ancestor?) or an existential node?
        hideThisNode = False
        if isinstance(expr, tms.AndExpression):
            for arg in expr.args:
                if isinstance(arg.datum, Rule):
                    # Okay, we have the rule then.  Get us the parent.
                    ruleNode = booleanExpressionToNewRDF(arg)
                    node = None
                    if arg.datum.isBase or arg.datum.isElided and hasHiddenAncestor:
                        if arg.datum.isBase:
                            hasHiddenAncestor = True
                        hideThisNode = True
                        node = store.newExistential(formula, store.genId())
                        break
                    elif not hasHiddenAncestor:
                        node = store.newSymbol(store.genId())
                        break
                    elif hasHiddenAncestor:
                        # Don't render this node.
                        return None
        
        newTermsFor[expr] = node
        formula.add(node, store.type, airj['RuleApplication'])
#        formula.add(node, airj['branch'], {tms.NotExpression: air['else'],
#                                           tms.AndExpression: air['then'],
#                                           tms.OrExpression: t['Or-justification']}[expr.__class__])
        if isinstance(expr, tms.AndExpression):
            #We have a shorthand!
            newFormula = formula.newFormula()
            hasCWA = False
            for arg in expr.args:
                node2 = booleanExpressionToNewRDF(arg, hasHiddenAncestor)
                
                # For now, shim in our dataDependency and air:rule.
                # TODO: outputVariableMappingList
                # TODO: clean up nested/dataDependency
                # TODO: built-in functions???
                # TODO: hidden/ellipsed rules
                if arg.fireEvent is not None:
                    formula.add(node, airj['nestedDependency'], arg.fireEvent)
                
                if arg.dataEvent is not None and not hideThisNode:
                    formula.add(node, airj['dataDependency'], arg.dataEvent)
#                    formula.add(node, airj['nestedDependency'], arg.dataEvent)
                elif isinstance(arg.datum, Rule) and not hideThisNode:
                    formula.add(node, air['rule'], node2)
                elif isinstance(arg.datum, tuple) and len(arg.datum) == 2 \
                        and arg.datum[0] == 'closedWorld':
                    formula.add(node, airj['dataDependency'], node2)
                    formula.add(node, airj['flowDependency'], node2)
                    hasCWA = True
            if hasCWA and not hideThisNode:
                formula.add(node, airj['branch'], air['else'])
            elif not hideThisNode:
                formula.add(node, airj['branch'], air['then'])
        else:
            for arg in expr.args:
                formula.add(node, t['sub-expr'], booleanExpressionToRDF(arg))
        return node

    premiseFormula = formula.newFormula()
    
    def nf2(self, recurse=True):
        if self in done:
            return True
        done.add(self)
        if hasattr(self, 'datum'):
            datum = self.datum
        elif isinstance(self, (Formula, Symbol, Fragment, Literal)):
            datum = self
        else:
            raise TypeError(self)
        if isinstance(datum, Rule):
            #datum is a rule!
            if datum.generated:
                newNode = formula.newBlankNode()
                formula.add(newNode, air['instanceOf'], datum.sourceNode)
                termsFor[self] = newNode
            else:
                termsFor[self] = datum.sourceNode
        elif isinstance(datum, tuple):
            if len(datum) == 2:
                if datum[0] == 'closedWorld':
                    ####print datum, [x for x in datum[1]]
                    newNode = formula.newBlankNode()
                    for x in datum[1]:
                        nf2(x, False)
                    formula.add(newNode, air['closed-world-assumption'], formula.newList([termsFor[x] for x in datum[1]]))
##                    formula.add(newNode, air['closed-world-assumption'], formula.newList([x for x in datum[1]]))
                    termsFor[self] = newNode
                    
                    # And now the ClosingTheWorld event
                    newNode = formula.newSymbol(store.genId())
                    formula.add(newNode, store.type, airj['ClosingTheWorld'])
                    for term in datum[1]:
                        if term in newTermsFor:
                            if isinstance(newTermsFor[term], tuple):
                                formula.add(newNode, pmll['flowDependency'],
                                            newTermsFor[term][0])
                                formula.add(newNode, pmll['dataDependency'],
                                            newTermsFor[term][0])
                            else:
                                formula.add(newNode, pmll['flowDependency'],
                                            newTermsFor[term])
                                formula.add(newNode, pmll['dataDependency'],
                                            newTermsFor[term])
                        elif term in self.assumedURIs:
                            # Generate any needed extraction events,
                            # or find the corresponding one.
                            
                            event = formula.any(pred=airj['source'], obj=term)
                            if event:
                                log = formula.any(subj=event, pred=airj['outputdata'])
                                if log:
                                    newTermsFor[term] = (event, log)
                            if term not in newTermsFor:
#                                event = mintEventFragment()
                                log = store.newSymbol(store.genId())
                                if not event:
#                                    log = mintDataID()
                                    event = store.newSymbol(store.genId())
                                newTermsFor[term] = (event, log)
                                formula.add(event, airj['source'], term)
                                formula.add(event, store.type,
                                            airj['Dereference'])
                                formula.add(event, airj['outputdata'], log)
                            formula.add(newNode, pmll['flowDependency'],
                                        event)
                            formula.add(newNode, pmll['dataDependency'],
                                        event)
                    newTermsFor[self] = newNode
                else:
                    raise RuntimeError(self)
            elif len(datum) == 4:
                newFormula = store.newFormula()
                newFormula.add(*self.datum[:3])
                newFormula = newFormula.close()
                termsFor[self] = newFormula
            else:
                raise RuntimeError(self)
        elif isinstance(datum, (Formula, Symbol, Fragment, Literal)): # We failed to remove it!
            termsFor[self] = datum # represents itself
        else:
            raise TypeError(datum)
        if recurse:
            if self in premises:
                retVal = True
                if isinstance(termsFor[self], Formula):
                    premiseFormula.loadFormulaWithSubstitution(termsFor[self])
                else:
                    formula.add(termsFor[self], t['justification'], t['premise'])
                # We need to generate extraction events.
                if self.extractedFrom is not None:
                    symb = store.newSymbol(self.extractedFrom)
                    event = formula.any(pred=airj['source'], obj=symb)
                    if event:
                        log = formula.any(subj=event, pred=airj['outputdata'])
                        if log:
                            newTermsFor[self] = (event, log)
                    if self in newTermsFor:
                        (self.dataEvent, self.dataID) = newTermsFor[self]
                    else:
#                        self.dataEvent = mintEventFragment()
                        self.dataEvent = store.newSymbol(store.genId())
#                        self.dataID = mintDataID()
                        self.dataID = store.newSymbol(store.genId())
                        newTermsFor[self] = (self.dataEvent, self.dataID)
                        
                    formula.add(self.dataEvent, airj['source'],
                                store.newSymbol(self.extractedFrom))
                    formula.add(self.dataEvent, store.type,
                                airj['Dereference'])
                    formula.add(self.dataEvent, airj['outputdata'], self.dataID)
            elif self.assumed():
                retVal = True
                formula.add(termsFor[self], t['justification'], t['premise'])
            elif self in expressions:
                retVal = expressions[self].evaluate(nf2)
                antecedents = expressions[self].nodes()
                rule = reasons[self].rule
                antecedentExpr = booleanExpressionToRDF(expressions[self])
                selfTerm = termsFor[self]
                justTerm = termsFor[reasons[self]]
                
                # Generate the event for this particular expression's
                # RuleApplication event.
                
                # NOTE: This can only be a known symbol if it is a
                # Belief-rule, and we have no Hidden-rule ancestor.
                self.fireEvent = booleanExpressionToNewRDF(expressions[self])
                if isinstance(selfTerm, Formula):
                    formula.add(self.fireEvent, airj['outputdata'], selfTerm)
                
                # Back to the old-school stuff.
                if hasattr(rule, 'descriptions'):
                    desc = rule.descriptions
                    rule = rule.name
                    for d in desc:
                        formula.add(selfTerm, t['description'], d)
                formula.add(selfTerm, t['justification'], justTerm)
                formula.add(justTerm, t['rule-name'], rule)
                assert formula.contains(subj=justTerm, pred=t['rule-name'], obj=rule)
                formula.add(justTerm, t['antecedent-expr'], antecedentExpr)
    #            print 'adding (%s, %s, %s), (%s, %s, %s)' % (selfTerm, t['rule-name'], rule, selfTerm, t['antecedent-expr'], antecedentExpr)
            else:
                # We really shouldn't get here, but right now not
                # having a filter means that we sometimes can.
                # TODO: Find out why we get here.
                retVal = True
                if isinstance(termsFor[self], Formula):
                    premiseFormula.loadFormulaWithSubstitution(termsFor[self])
                else:
                    formula.add(termsFor[self], t['justification'], t['premise'])
        else:
            retVal = False # it does not matter
        return retVal
    
    for tmsNode in tmsNodes:
        nf2(tmsNode)
        formula.add(*tmsNode.datum[:3])

    formula.add(premiseFormula.close(), t['justification'], t['premise'])
    return formula.close()
