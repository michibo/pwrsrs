#! /usr/bin/env python
"""
Copyright (C) 2011 by Peter A. Donis.
Released under the open source MIT license:
http://www.opensource.org/licenses/MIT
"""

from itertools import count


class MemoizedGenerator(object):
    """Memoize a generator to avoid computing any term more than once.
    
    Generic implementation of a "memoized" generator for cases where each
    term of the generator is expensive to compute, but it is known that
    every realization of the generator will compute the same terms. This
    class allows multiple realizations of the generator to share a
    single computation of each term.
    
    This class can be used to wrap a generator directly, but it only
    works for ordinary functions (i.e., not methods). For ease of use
    and flexibility, it is recommended that the ``memoize_generator``
    decorator be used instead, since that automatically handles both
    ordinary functions and methods.
    
    This class was written for use by the ``PowerSeries`` class, but
    the implementation is general. For example, it correctly handles
    finite-length generators, even though all ``PowerSeries`` instances
    will look infinite as far as this class is concerned (i.e., a
    wrapped ``PowerSeries`` generator will never set the class's
    internal ``__empty`` flag to ``True``).
    
    Functional programming types will note that this implementation
    is done using a class, not a function. Doing it as a function in
    Python would require some inelegant hacks with mutable containers
    since Python does not allow a closure's inner function to mutate
    variables in the closure's outer function. (Python 2.7 adds the
    ``nonlocal`` keyword to allow such behavior, but I didn't want to
    require 2.7 for this since many Linux distributions are still at
    2.6 as of this writing.) Lisp hackers will of course make smug
    comments on this limitation of Python's, but I don't care. :-)
    """
    
    def __init__(self, gen):
        # The underlying generator
        self.__gen = gen
        # Memoization fields
        self.__cache = []
        self.__iter = None
        self.__empty = False
    
    def __call__(self, *args, **kwargs):
        """Direct function call syntax support.
        
        This makes an instance of this class work just like the underlying
        generator function when called directly.
        """
        if not (self.__empty or self.__iter):
            self.__iter = self.__gen(*args, **kwargs)
        for n in count():
            if n < len(self.__cache):
                yield self.__cache[n]
            elif self.__empty:
                break
            else:
                try:
                    term = next(self.__iter)
                except StopIteration:
                    self.__empty = True
                    break
                else:
                    self.__cache.append(term)
                    yield term
