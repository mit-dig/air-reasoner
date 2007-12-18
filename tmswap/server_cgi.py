"""server cgi

An attempt to get a cgi interface to amord.py

"""


import cgi
import cgitb; cgitb.enable()  # Comment me out later


def send_header(outfile, keyword, value):
    """Send a MIME header."""
    outfile.write("%s: %s\r\n" % (keyword, value))

def end_headers(outfile):
    """Send the blank line ending the MIME headers."""
    outfile.write("\r\n")


def main():
    form = cgi.FieldStorage()
    logURIs = form.getlist('log')
    ruleURIs = form.getlist('rules')
    from amord import testPolicy
    returnString = testPolicy(logURIs, ruleURIs)
    returnString = returnString.encode('utf_8')
    print ctype
    send_header(outfile, "Content-type", ctype)
    send_header(outfile, "Content-Length", str(len(retVal)))
    end_headers(outfile)
    outfile.write(retVal)


if __name__ == '__main__': # What else would it be?
    main()
