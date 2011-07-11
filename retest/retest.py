#! /bin/python
"""Regression test harness for new versions of AIR

python retrest.py   <options>  <inputURIs>
Options:

--testsFrom=uri -f uri      Take test definitions from these files (in RDF/XML or N3 format)
                            Or just by themselves at end of command line after options
--normal        -n          Do normal tests, checking output NOW DEFAULT - NOT NEEDED
--start=13      -s 13       Skip the first 12 tests
--verbose       -v          Print what you are doing as you go
--ignoreErrors  -i          Print error message but plough on though more tests if errors found
                            (Summary error still raised when all tests have been tried)
--air=../policyrunner.py    AIR command is ../policyrunner.py
--help          -h          Print this message and exit

You must specify some test definitions.

Example:    python retest.py -n cases.n3

"""
# You can also specify locations for reference, data, and rules.

# Example: python retest.py --ref=/path/to/reference.n3 --data=http://example.com/data.rdf --rules=http://example.com/rules.n3

# """

from os import system, popen3
import os
import sys
import urllib

# From PYTHONPATH equivalent to http://www.w3.org/2000/10

from swap import llyn
from swap.myStore import load, loadMany, Namespace
from swap.uripath import refTo, base
from swap import diag
from swap.diag import progress
from swap.term import AnonymousNode


rdf = Namespace("http://www.w3.org/1999/02/22-rdf-syntax-ns#")
test = Namespace("http://www.w3.org/2000/10/swap/test.n3#")
n3test = Namespace("http://www.w3.org/2004/11/n3test#")
rdft = Namespace("http://www.w3.org/2000/10/rdf-tests/rdfcore/testSchema#")
triage = Namespace("http://www.w3.org/2000/10/swap/test/triage#")

sparql_manifest = Namespace("http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#")
sparql_query = Namespace("http://www.w3.org/2001/sw/DataAccess/tests/test-query#")
dawg_test = Namespace("http://www.w3.org/2001/sw/DataAccess/tests/test-dawg#")

import getopt
import sys
import re


normal = 1
chatty = 0
proofs = 0
verbose = 0
no_action = 0

def localize(uri):
    """Get URI relative to where this lives"""
    from swap import uripath
    return uripath.refTo("http://www.w3.org/2000/10/swap/test/retest.py", uri)

def problem(str):
    global ploughOn
    global problems
    sys.stderr.write(str + "\n")
    problems.append(str)
    if not ploughOn:
        sys.exit(-1)

#       raise RuntimeError(str)

def usage():
    print __doc__

from subprocess import Popen, call, PIPE

def execute(cmd1, noStdErr=False):
    global verbose, no_action
    if verbose: print "    "+cmd1
    if no_action: return
    if noStdErr:
        stderr = file('/dev/null', 'w')
    else:
        stderr = None
    result = call(cmd1, shell=True, stderr=stderr)
    if result != 0:
        raise RuntimeError("Error %i executing %s" %(result, cmd1))

def diff(case, ref=None, prog="diff -Bbwu"):
    global verbose
    if ref == None:
        ref = "ref/%s" % case
    if diag.print_all_file_names:  #for use in listing all files used in testing
        a = open('testfilelist','a')
        a.write(ref)
        a.write('\n')
        a.close()
    diffcmd = """%s %s temp/%s >diffs/%s""" %(prog, ref, case, case)
    if verbose: print "  ", diffcmd
    if no_action: result = 0
    else: result = system(diffcmd)
    if result < 0:
        raise problem("Comparison fails: result %i executing %s" %(result, diffcmd))
    if result > 0: print "Files differ, result=", result
    d = urllib.urlopen("diffs/"+case)
    buf = d.read()
    if len(buf) > 0:
        if just_fix_it == 0:
            print "#  If this is OK,   cp temp/%s %s" %(case, ref)
            print "######### Differences from reference output:\n" + buf
            return 1
        else:
            os.system("cp temp/%s %s" %(case, ref))
            return 0
    return result

def infCheck(file, infFile):
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

    result = 0
    
   # Create a store for cwm's rdf information
    reasoningStore = myStore._checkStore()

    # loading the output
    outputFormula = reasoningStore.load(file)

    kb = load(infFile)
    for i in kb.each(pred=rdf.type, obj=test.InfReference):
        s = kb.the(i, test.subj)
        p = kb.the(i, test.pred)
        o = kb.the(i, test.obj)
        
        if not s == None: s = outputFormula.newSymbol(str(s))
        if not p == None: p = outputFormula.newSymbol(str(p))
        if not o == None: o = outputFormula.newSymbol(str(o))
        								
        if not outputFormula.contains(subj=s,pred=p,obj=o): result = 1

        # print "File: %s" % file
        # print "Inference: %s" % str(inferenceDict)
        # print "Result of searching for inference: %s" %  (repr(result))

    return result

# def rdfcompare3(case, ref=None):
#     "Compare NTriples fieles using the cant.py"
#     global verbose
#     if ref == None:
#         ref = "ref/%s" % case
#     diffcmd = """python ../cant.py -d %s -f temp/%s >diffs/%s""" %(ref, case, case)
#     if verbose: print "  ", diffcmd
#     result = system(diffcmd)
#     if result < 0:
#         raise problem("Comparison fails: result %i executing %s" %(result, diffcmd))
#     if result > 0: print "Files differ, result=", result
#     d = urllib.urlopen("diffs/"+case)
#     buf = d.read()
#     if len(buf) > 0:
# #       print "#  If this is OK,   cp temp/%s %s" %(case, ref)
#         print "######### Differences from reference output:\n" + buf
#         return 1
#     return result
# 
# def rdfcompare2(case, ref1):
#         """Comare ntriples files by canonicalizing and comparing text files"""
#         cant = "python ../cant.py"
#         ref = "temp/%s.ref" % case
#         execute("""cat %s | %s > %s""" % (ref1, cant, ref))
#         return diff(case, ref)
# 
# 
# def rdfcompare(case, ref=None):
#     """   The jena.rdfcompare program writes its results to the standard output stream and sets
#         its exit code to 0 if the models are equal, to 1 if they are not and
#         to -1 if it encounters an error.</p>
#     """
#     global verbose
#     if ref == None:
#         ref = "ref/%s" % case
#     diffcmd = """java jena.rdfcompare %s temp/%s N-TRIPLE N-TRIPLE  >diffs/%s""" %(ref, case, case)
#     if verbose: print "  ", diffcmd
#     result = system(diffcmd)
#     if result != 0:
#         raise problem("Comparison fails: result %s executing %s" %(result, diffcmd))
#     return result



def main():
    global verbose, proofs, chatty, normal, no_action
    start = 1
    cwm_command='../airreasoner/policyrunner.py'
    python_command='python'
    usingN3 = 1 # default: use N3 for list of test
    desc = None
    global ploughOn # even if error
    ploughOn = 0
    global verbose
    verbose = 0
    global just_fix_it
    just_fix_it = 0
    if diag.print_all_file_names:
        a = file('testfilelist','w')
        a.write('')
        a.close()
    try:
        opts, testFiles = getopt.getopt(sys.argv[1:], "h?s:nNcipf:v",
            ["help", "start=", "testsFrom=", "no-action", "No-normal", #"chatty",
                "ignoreErrors", #"proofs",
		"verbose","overwrite","air="])#,"ref=","data=","rules=","desc="])
    except getopt.GetoptError:
        # print help information and exit:
        usage()
        sys.exit(2)
    output = None
    for o, a in opts:
        if o in ("-h", "-?", "--help"):
            usage()
            sys.exit()
        if o in ("-v", "--verbose"):
            verbose = 1
        if o in ("-i", "--ignoreErrors"):
            ploughOn = 1
        if o in ("-s", "--start"):
            start = int(a)
        if o in ("-f", "--testsFrom"):
            testFiles.append(a)
        if o in ("-n", "--no-action"):
            no_action = 1
        if o in ("-N", "--No-normal"):
            normal = 0
        #if o in ("-c", "--chatty"):
        #    chatty = 1
        #if o in ("-p", "--proofs"):
        #    proofs = 1
        if o in ("--overwrite",):
            just_fix_it = 1
        if o in ("--air", "--the_end"):
            cwm_command=a
##        if o in ("--desc", "--description"):
##            desc=a
        # All opts below if not usingN3
##        if o in ("--ref", "--reference"):
##            ref_location, usingN3=a, 0
##        if o in ("--data"):
##            data_location, usingN3=a, 0
##        if o in ("--rules"):
##            rules_location, usingN3=a, 0

    
    assert system("mkdir -p temp") == 0
    assert system("mkdir -p diffs") == 0
    if proofs: assert system("mkdir -p proofs") == 0
    
    tests=0
    passes=0
    global problems
    problems = []
    
    REFWD="http://dig.csail.mit.edu/TAMI/2007/amord"
    WD = base()[:-1] 
    
    #def basicTest(case, desc, args)

    if verbose: progress("Test files:", testFiles)
    
    kb = loadMany(testFiles, referer="")
    testData = []
#    RDFTestData  = []
#    RDFNegativeTestData = []
#    perfData = []
#    n3PositiveTestData = []
#    n3NegativeTestData = []
#    sparqlTestData = []
#    for fn in testFiles:
#       print "Loading tests from", fn
#       kb=load(fn)

#    if usingN3:
    ruleDataError = 0
    ruleDataErrorURI = []
    infRefError = 0
    infRefErrorURI = []
    for t in kb.each(pred=rdf.type, obj=test.AirTest):
        cFlag = 0 # Flag if errors
        verboseDebug = kb.contains(subj=t, pred=rdf.type, obj=test.VerboseTest)
        u = t.uriref()
        ref = kb.the(t, test.referenceOutput)
        inf = kb.the(t, test.inferenceOutput) # Inference output
        rn = kb.the(t, test.rules)
        dn = kb.the(t, test.data)
        
        if ref == None and inf == None:
            infRefError, cFlag = 1, 1
            infRefErrorURI.append(refTo(base(), t.uriref()))
        if rn == None or dn == None:
            ruleDataError, cFlag = 1, 1
            ruleDataErrorURI.append(refTo(base(), t.uriref()))

        if cFlag: continue
        
##        if ref == None:
##            case = str(kb.the(t, test.shortFileName))
##            refFile = "ref/%s" % case
##        else:
        if not ref == None:
            refFile = refTo(base(), ref.uriref())
            case  = ""
            for ch in refFile:
                if ch in "/#": case += "_"
                else: case += ch  # Make up test-unique temp filename
        else:
            refFile = 0
            caseName = refTo(base(), t.uriref())
            case  = ""
            for ch in caseName:
                if ch in "/#.": case += "_"
                else: case += ch  # Make up test-unique temp filename            

        if not inf == None:
            infFile = refTo(base(), inf.uriref())
        else: infFile = 0
                
        description = str(kb.the(t, test.description))
        if description == 'None': description = "No description specified."
        environment = kb.the(t, test.environment)
        rules = str(rn).split()
        data = str(dn).split()
        rstring = "rules=["
        dstring = "data=["
        for rl in rules:
            rstring = rstring + rl
            if not rules[-1] == rl: rstring += ','
        for dl in data:
            dstring = dstring + dl
            if not data[-1] == dl: dstring += ','
        arguments = "list " + rstring + '] ' + dstring + ']'
        if environment == None: env=""
        else: env = str(environment) + " "
        testData.append((t, t.uriref(), case, refFile, infFile, description, env, arguments, verboseDebug))
    if ruleDataError:
        print "Error: ruleDataError"
        print "Test definitions must have at least one argument for both rules and data."
        print "Please check the following for missing arguments in rules and data (not included in test):"
        for uri in ruleDataErrorURI:
            print uri,
        print '\n'
    if infRefError:
        print "Error: infRefError"
        print "Test definitions must have at least either a referenceOutput or an inferenceOutput, or both."
        print "Please check the following for missing referenceOutput and inferenceOutput (not included in test):"
        for rUri in infRefErrorURI:
            print rUri,
        print '\n'
##    else:
##        try:
##            verboseDebug = 0
##            refFile = ref_location
##            case  = ""
##            for ch in refFile:
##                if ch in "/#": case += "_"
##                else: case += ch  # Make up test-unique temp filename
##            if desc == None: description = "No description specified."
##            else: description = desc
##            arguments = "test %s %s" % (rules_location, data_location)
##            env = ""
##            testData.append((0, rules_location, case, refFile, description, env, arguments, verboseDebug))
##        except:
##            print "\n If test definitions in RDF/XML or N3 is not used for test, retest must have valid values for ref, data, and rules." + "\n" + \
##                  "E.g. python retest.py --ref=/path/to/reference.n3 --data=http://example.com/data.rdf --rules=http://example.com/rules.n3 \n"
##            sys.exit(2)

    testData.sort()
    cwmTests = len(testData)
    if verbose: print "Air tests: %i" % cwmTests
#    RDFTestData.sort()
#    RDFNegativeTestData.sort()
#    rdfTests = len(RDFTestData)
#    rdfNegativeTests = len(RDFNegativeTestData)
#    perfData.sort()
#    perfTests = len(perfData)
#    n3PositiveTestData.sort()
#    n3PositiveTests = len(n3PositiveTestData)
#    n3NegativeTestData.sort()
#    n3NegativeTests = len(n3NegativeTestData)
#    sparqlTestData.sort()
#    sparqlTests = len(sparqlTestData)
    totalTests = cwmTests #+ rdfTests + rdfNegativeTests + sparqlTests \
                 #+ perfTests + n3PositiveTests + n3NegativeTests
    #if verbose: print "RDF parser tests: %i" % rdfTests

    for t, u, case, refFile, infFile, description, env, arguments, verboseDebug in testData:
        tests = tests + 1
        if tests < start: continue

        #if t:
        urel = refTo(base(), u)
        #else: urel = u
        
        print "%3i/%i %-30s  %s" %(tests, totalTests, urel, description)
    #    print "      %scwm %s   giving %s" %(arguments, case)
        assert case and description and arguments
        cleanup = """sed -e 's/\$[I]d.*\$//g' -e "s;%s;%s;g" -e 's;%s;%s;g'""" % (WD, REFWD,
                                                                                                      cwm_command, '../airreasoner/policyrunner.py')
        if normal:
            execute("""CWM_RUN_NS="run#" %s %s %s %s | %s > temp/%s""" %
                (env, python_command, cwm_command, arguments, cleanup , case))  
            if refFile:
                if diff(case, refFile):
                    problem("######### from normal case %s: %spolicyrunner.py %s" %( case, env, arguments))
                    continue
                else: print "\tReference Check: Passed"
            else: print "\tReference Check: Not Checking"
            if infFile:
                if infCheck("temp/"+case, infFile):
			print "\tInference Check: Failed"
                else: print "\tInference Check: Passed"
            else: print "\tInference Check: Not Checking"
            #else: print "\t Passed: %-30s" % urel

        if chatty and not verboseDebug:
            execute("""%s %s %s --chatty=100  %s  &> /dev/null""" %
                (env, python_command, cwm_command, arguments), noStdErr=True)   

##        if proofs and kb.contains(subj=t, pred=rdf.type, obj=test.CwmProofTest):
##            execute("""%s %s %s --quiet %s --base=a --why  > proofs/%s""" %
##                (env, python_command, cwm_command, arguments, case))
##            execute("""%s ../check.py < proofs/%s | %s > temp/%s""" %
##                (python_command, case, cleanup , case)) 
##            if diff(case, refFile):
##                problem("######### from proof case %s: %scwm %s" %( case, env, arguments))
#       else:
#           progress("No proof for "+`t`+ " "+`proofs`)
#           progress("@@ %s" %(kb.each(t,rdf.type)))
        passes = passes + 1
        
    if problems != []:
        sys.stderr.write("\nProblems:\n")
        for s in problems:
            sys.stderr.write("  " + s + "\n")
        raise RuntimeError("Total %i errors in %i tests." % (len(problems), tests))

    #else: print "Done: %i tests with %i errors." % (tests, len(problems))

if __name__ == "__main__":
    main()


# ends
