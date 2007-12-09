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

try:
    from collection import defaultdict
except ImportError:
    class defaultdict(dict):
        __slots__ = ['__weakref__']
        def __init__(self, default_factory=None, *a, **kw):
            if (default_factory is not None and
                not callable(default_factory)):
                raise TypeError('factory must be callable')
            dict.__init__(self, *a, **kw)
            self.default_factory = default_factory
        def __getitem__(self, key):
            try:
                return dict.__getitem__(self, key)
            except KeyError:
                return self.__missing__(key)
        def __missing__(self, key):
            if self.default_factory is None:
                raise KeyError(key)
            self[key] = value = self.default_factory()
            return value
        def __repr__(self):
            return 'defaultdict(%s, %s)' % (self.default_factory,
                                            dict.__repr__(self))


