"""py25.py

import this to insure you have functions
that were created for python 2.5

"""


try:
    all
except NameError:
    def all(iterable):
        for element in iterable:
            if not element:
                return False
        return True

try:
    any
except NameError:
    def any(iterable):
        for element in iterable:
            if element:
                return True
        return False


from collections import deque
try:
    deque.remove
except AttributeError:
    def dequeRemove(d, item):
        k = len(d)
        noneYet = True
        for i in xrange(k):
            x = d.popleft()
            if noneYet and x == item:
                noneYet = False
            else:
                d.append(x)
        return d
else:
    dequeRemove = deque.remove

