#!/usr/bin/env python
"""server cgi

An attempt to get a cgi interface to policyrunner.py

"""
DEBUG = False

ctype = 'text/rdf+n3'

if DEBUG:
    ctype = 'text/plain'

import cgi
import urllib
import traceback
# instead of cgi.FieldStorage, can we use  paste.wsgiwrappers.WSGIRequest(env).params, 
# as documented in
# http://pythonpaste.org/class-paste.wsgiwrappers.WSGIRequest.html and 
# http://pythonpaste.org/class-paste.util.multidict.MultiDict.html
# connecting to cgi using wsgiref would be a first start
# but I would need a wsgi interface
# FieldStorage seems incompatible --- this is a problem
# It seems (although the docs do not say this) that you
# can run
# stdin = environ['wsgi.input']
# 
if DEBUG:
    import cgitb; cgitb.enable()  # Comment me out later
from StringIO import StringIO


def main_wsgi():
    import wsgiref.handlers
    wsgiref.handlers.CGIHandler().run(wsgi_app)

## instead of using main_wsgi (which is for cgi)
## we might want to just serve directly
##    from paste import httpserver
##    httpserver.serve(wsgi_app, host='127.0.0.1', port='8080')
## (change port, change host to something external)


def wsgi_app(environ, start_response):
    import sys
    outfile = sys.stdout
    sys.stdout = StringIO()
    form = cgi.FieldStorage(fp=environ['wsgi.input'], environ=environ)
    logURIs = form.getlist('logFile')
    ruleURIs = form.getlist('rulesFile')
    log = form.getfirst('log')
    rules = form.getfirst('policy')
    filterProperties = form.getlist('filterProperties')
    if len(filterProperties) == 0:
        filterProperties = ['http://dig.csail.mit.edu/TAMI/2007/amord/air#compliant-with', 'http://dig.csail.mit.edu/TAMI/2007/amord/air#non-compliant-with']
    import policyrunner as amord
#    from tmswap import amord
    testPolicy = amord.testPolicy
    try:
        returnString = testPolicy(logURIs, ruleURIs, log, rules, filterProperties)
        returnString = returnString.encode('utf_8')
        print ('ran testPolicy(%s, %s, %r, %r)\n' % (logURIs, ruleURIs, log, rules))
        print (str(form.keys()) + '\n')
        if DEBUG:
            length = str(len(returnString) + len(sys.stdout.getvalue()))
        else:
            length =  str(len(returnString))
        start_response('200 OK', [('Content-Type',ctype),
                                  ("Content-Length", length)])
        if DEBUG:
            yield sys.stdout.getvalue()
        yield returnString
    except:
        returnString = ''.join(traceback.format_exception(sys.exc_type, sys.exc_value, sys.exc_traceback))
        length = str(len(returnString))
        start_response('500 Internal Server Error', [('Content-Type','text/plain'),
                                                     ("Content-Length", length)])
        yield returnString
    sys.stdout = outfile



### not using wsgi

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
    filterProperties = form.getlist('filterProperties')
    if len(filterProperties) == 0:
        filterProperties = ['http://dig.csail.mit.edu/TAMI/2007/amord/air#compliant-with', 'http://dig.csail.mit.edu/TAMI/2007/amord/air#non-compliant-with']
    import policyrunner as amord
    testPolicy = amord.testPolicy
    try:
        returnString = testPolicy(logURIs, ruleURIs, log, rules, filterProperties)
        returnString = returnString.encode('utf_8')
        print ('ran testPolicy(%s, %s, %r, %r, %s)\n' % (logURIs, ruleURIs, log, rules, filterProperties))
        print (str(form.keys()) + '\n')
        send_header(outfile, "Content-type", ctype)
        if DEBUG:
            length = str(len(returnString) + len(sys.stdout.getvalue()))
        else:
            length =  str(len(returnString))
        send_header(outfile, "Content-Length", length)
#        print ctype
        end_headers(outfile)
        if DEBUG:
            outfile.write(sys.stdout.getvalue())
        outfile.write(returnString)
    except:
        returnString = ''.join(traceback.format_exception(sys.exc_type, sys.exc_value, sys.exc_traceback))
        send_header(outfile, "Content-type", 'text/plain')
        length = str(len(returnString))
        send_header(outfile, "Content-Length", length)
        end_headers(outfile)
#        start_response('500 Internal Server Error', [('Content-Type','text/plain'),
#                                                     ("Content-Length", length)])
        outfile.write(returnString)
    sys.stdout = outfile


if __name__ == '__main__': # What else would it be?
    main_wsgi()
