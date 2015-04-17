
from fractions import Fraction as F
from itertools import count, islice, izip, chain, repeat
from functools import partial

from MemoizedGenerator import MemoizedGenerator

class PowerSeries(object):
    testlimit = 7

    def __init__(self, g=None):
        self.__g = g

    def __eq__(self, entry):
        return all(s == e for s,e in islice(izip(self,entry), self.testlimit))

    def __iter__( self ):
        return chain(self.__g(), repeat(0)) if self.__g else repeat(0)

    def __str__(self):
        return self.getstr()

    def getstr(self, num=None):
        def gen_str():
            is_pps = any( isinstance(term, PowerSeries) for term in islice(self, num or self.testlimit ) )
            for term in islice(self, num if num else self.testlimit):
                if is_pps:
                    yield term.getstr(num) + "\n"
                else:
                    yield str(term) + ", "

        return "".join(gen_str()) + "..."

    def deep_apply( self, func, n=1 ):
        if n == 0:
            return func(self)

        if n == 1:
            def _deep_apply():
                for term in self:
                    yield func(term)
        else:
            def _deep_apply():
                for term in self:
                    yield term.deep_apply( func, n-1 )

        return PowerSeries( _deep_apply )

    def deep_map( self, func ):
        def _deep_map():
            for term in self:
                if not isinstance(term, PowerSeries):
                    yield func(term)
                else:
                    yield term.deep_map( func )
    
        return PowerSeries(_deep_map)

    def get_zero( self ):
        for term in self:
            return term

    def get_tail( self ):
        def _tail():
            for term in islice(self, 1, None):
                yield term

        return PowerSeries(_tail)

    @property
    def zero(self):
        return self.get_zero()

    @property
    def tail(self):
        return self.get_tail()

    @property
    def xmul(self):
        def _xmul():
            yield 0
            for term in self:
                yield term

        return PowerSeries(_xmul)

    def __add__(self, entry):
        if is_powerseries(entry):
            def _add():
                for term1, term2 in izip(self, entry):
                    yield term1 + term2
        else:
            def _add():
                it = iter(self)
                yield next(it) + entry

                for term in it:
                    yield term

        return PowerSeries(_add)

    def __mul__(self, entry):
        if not is_powerseries(entry):
            return self.deep_apply( lambda x: x*entry )

        @MemoizedGenerator
        def _mul():
            f0 = self.zero
            g0 = entry.zero
            yield f0 * g0

            F = self.tail
            G = entry.tail

            r1 = 0
            mterms = [F * G]
            if is_powerseries(f0) or f0 != 0:
                f0G = G.deep_apply( lambda x: f0*x )
                r1 += f0G.zero
                mterms.append(f0G.tail)
            if is_powerseries(g0) or g0 != 0:
                g0F = F.deep_apply( lambda x: g0*x )
                r1 += g0F.zero
                mterms.append(g0F.tail)
            
            yield r1

            for terms in izip(*mterms):
                yield sum(terms)

        return PowerSeries(_mul)

    def __rdiv__(self, entry):
        """

        >>> B = 1 / (1 - X - X*Y)

        """

        if is_powerseries(entry):
            return entry * (1/self)

        def _rdiv():
            f0 = self.zero
            if is_powerseries(f0):
                recip = entry / f0
            elif f0 == 1:
                recip = entry
            else:
                recip = F(entry, f0)

            yield recip

            for term in ( (self.tail * R).deep_apply( lambda x: -x*recip ) ):
                yield term

        R = PowerSeries(_rdiv)
        return R

    def __radd__(self, entry):
        return self + entry

    def __sub__(self, entry):
        return self + (- entry)

    def __rsub__(self, entry):
        return entry + (-self)

    def __neg__(self):
        return self.deep_apply( lambda x: -x )

    def __rmul__(self, entry):
        return self * entry

    def __div__(self, entry):
        if is_powerseries(entry):
            return self * (1 / entry)
        elif entry == 1:
            return self
        else:
            return self * F(1, entry)

    def __call__( self, *args ):
        

def is_powerseries( entry ):
    return isinstance(entry, PowerSeries)

def D( f ):
    def _D():
        for n,term in enumerate(f.tail):
            yield (n+1) * term

    return PowerSeries(_D)

def integral( f, const=0 ):
    def _int():
        yield const
        for n, term in enumerate(f):
            yield F(1,n+1)*term

    return PowerSeries(_int)

def tensor( f1, f2 ):
    return f1.deep_map( lambda x: f2*x )

def exp( f ):
    """

    >>> e = exp(X)
    >>> e == D(e)
    True
    >>> e == integral(e, 1)
    True
    >>> log(e) == X
    True
    >>> d = exp(3*X*X)
    >>> d*e == exp(X + 3*X*X)
    True

    """
    f0 = f.zero
    if is_powerseries( f0 ):
        c0 = exp(f0)
    elif f0 == 0:
        c0 = 1
    else:
        raise ValueError("Can't take exp of powerseries with non-zero constant term")

    def _exp():
        for term in integral( E * D(f), c0 ):
            yield term

    E = PowerSeries(_exp)
    return E

def log( f ):
    """

    >>> l = log(1+X) 
    >>> 3*l == log((1+X)*(1+X)*(1+X))
    True
    >>> D(l) == 1/(1+X)
    True

    """
    f0 = f.zero
    if is_powerseries( f0 ):
        c0 = log(f0)
    elif f0 == 1:
        c0 = 0
    else:
        raise ValueError("Can't take log of powerseries with non-unit constant term")

    def _log():
        for term in integral( D(f)/f, c0 ):
            yield term

    return PowerSeries(_log)

I = 1 + PowerSeries()
X = I.xmul
Y = tensor(I, X)
Z = tensor(I, Y)

if __name__ == '__main__':
    import doctest
    doctest.testmod()

