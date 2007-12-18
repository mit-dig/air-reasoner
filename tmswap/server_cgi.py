#!/usr/bin/env python
"""server cgi

An attempt to get a cgi interface to amord.py

"""

ctype = 'text/rdf+n3'

import cgi
import cgitb; cgitb.enable()  # Comment me out later
from StringIO import StringIO

def send_header(outfile, keyword, value):
    """Send a MIME header."""
    outfile.write("%s: %s\r\n" % (keyword, value))

def end_headers(outfile):
    """Send the blank line ending the MIME headers."""
    outfile.write("\r\n")


def main():
    import sys
    outfile = sys.stdout
    sys.stdout = StringIO()
    form = cgi.FieldStorage()
    logURIs = form.getlist('logFile')
    ruleURIs = form.getlist('rulesFile')
    log = form.getfirst('log')
    rules = form.getfirst('policy')
    from tmswap import amord
    testPolicy = amord.testPolicy
    returnString = testPolicy(logURIs, ruleURIs, log, rules)
    returnString = returnString.encode('utf_8')
    print ('ran testPolicy(%s, %s, %r, %r)\n' % (logURIs, ruleURIs, log, rules))
    print (str(form.keys()) + '\n')
    send_header(outfile, "Content-type", ctype)
    send_header(outfile, "Content-Length", str(len(returnString) + len(sys.stdout.getvalue())))
#    print ctype
    end_headers(outfile)
    outfile.write(sys.stdout.getvalue())
    outfile.write(returnString)
    sys.stdout = outfile


if __name__ == '__main__': # What else would it be?
    main()
