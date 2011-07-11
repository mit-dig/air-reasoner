"""
Function creates a cwm instance and checks whether a file contains a formula
"""
# $Date: 2011-07-07 17:25:04 -0400 (Thu, 07 Jul 2011) $
# $Revision: 31083 $
# $Author: lkagal $


def inferenceChecker(file, inferenceDict):
    """
    Given a file, checks if inference is contained
    """

    #import openid
    #from openid.cryptutil import randomString

    # Pieces of cwm we need for this
    try:
        from swap import myStore
        from swap import query
        import os
    except ImportError:
        print "Make sure this module has access to cwm. Place a symlink named 'swap'"
        print "in the current directory, pointing to 'swap' inside the cwm folder."
        sys.exit(1)

    # Create a store for cwm's rdf information
    reasoningStore = myStore._checkStore()

    # loading the output
    outputFormula = reasoningStore.load(file)

    result = outputFormula.contains(subj=outputFormula.newSymbol(inferenceDict['subj']), pred=outputFormula.newSymbol(inferenceDict['pred']), obj=outputFormula.newSymbol(inferenceDict['obj']))

    print "File: %s" % file
    print "Inference: %s" % str(inferenceDict)
    print "Result of searching for inference: %s" %  (repr(result))

    return result

if __name__ == "__main__":
    # correct example
    inferenceDict = {'subj':"http://tw.rpi.edu/proj/tami/Special:URIResolver/Alice", 'pred':"http://dig.csail.mit.edu/TAMI/2007/amord/air#compliant-with", 'obj':"http://tw.rpi.edu/proj/tami/Special:URIResolver/ny_state_residency_and_id_policy"}
    inferenceChecker("<http://dig.csail.mit.edu/2009/AIR/tutorial/test-justification.n3>", inferenceDict)

    # incorrect example - triple is a pattern of a rule and not an inference
    inferenceDict = {'subj':"http://tw.rpi.edu/proj/tami/Special:URIResolver/Troy", 'pred':"http://tw.rpi.edu/proj/tami/Special:URIResolver/Property-3AHas_state", 'obj':"http://tw.rpi.edu/proj/tami/Special:URIResolver/NY"}
    inferenceChecker("<http://dig.csail.mit.edu/2009/AIR/tutorial/test-justification.n3>", inferenceDict)


