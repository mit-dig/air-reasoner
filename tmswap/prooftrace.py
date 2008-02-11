"""prooftrace.py

Given a tms, generate proof traces


"""

import tms
from formula import Formula, StoredStatement
from term import List, Env, Symbol, Fragment, Literal

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
    newExpressions = dict((node, reasons[node].expression)
                          for node in reasons
                          if node not in premises)
    baseNodes = frozenset(node for node in reasons
                          if node not in premises and ((reasons[node].rule in baseRules)
                              or (hasattr(reasons[node].rule, 'name') and reasons[node].rule.name in baseRules)))
    
    changed = True
    doneNewExpressions = {}

    def expressionSubstitutionFunc(expression, bindings):
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
        bindingsVal = frozenset(bindings.items())
        try:
            return mem[(expression, bindingsVal)]
        except KeyError:
            mem[(expression, bindingsVal)] = expressionSubstitutionFunc(expression, bindings)
            return mem[(expression, bindingsVal)]
    
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
        else:
            retVal = reasons[self].evaluate(nf2)
            strings.append('%s <= %s(%s)' % (self, reasons[self].rule.uriref(), ', '.join([str(x) for x in reasons[self].expression.nodes()])))
        return retVal
    for tmsNode in tmsNodes:
        nf2(tmsNode)
    return strings


def rdfTraceOutput(store, tmsNodes, reasons, premises, Rule):
    formula = store.newFormula()
    t = formula.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/tms')
    air = formula.newSymbol('http://dig.csail.mit.edu/TAMI/2007/amord/air')
    done = set()
    termsFor = {}
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
            elif self.assumed():
                retVal = True
                formula.add(termsFor[self], t['justification'], t['premise'])
            else:
                retVal = expressions[self].evaluate(nf2)
                antecedents = expressions[self].nodes()
                rule = reasons[self].rule
                antecedentExpr = booleanExpressionToRDF(expressions[self])
                selfTerm = termsFor[self]
                justTerm = termsFor[reasons[self]]
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
            retVal = False # it does not matter
        return retVal
    
    for tmsNode in tmsNodes:
        nf2(tmsNode)
        formula.add(*tmsNode.datum[:3])

    formula.add(premiseFormula.close(), t['justification'], t['premise'])
    return formula.close()
