
from fractions import Fraction as F
from itertools import count, islice, izip, chain, repeat, imap
from functools import partial
from math import floor

from MemoizedGenerator import MemoizedGenerator

def repeated(func, n):
    def ret(x):
        return reduce( lambda x,func: func(x) , repeat(func, n), x )
    return ret

class PowerSeries(object):
    testlimit = 5

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
            @MemoizedGenerator
            def _deep_apply():
                for term in self:
                    yield func(term)
        else:
            @MemoizedGenerator
            def _deep_apply():
                for term in self:
                    yield term.deep_apply( func, n-1 )

        return PowerSeries( _deep_apply )

    def deep_map( self, func ):
        @MemoizedGenerator
        def _deep_map():
            for term in self:
                if not isinstance(term, PowerSeries):
                    yield func(term)
                else:
                    yield term.deep_map( func )
    
        return PowerSeries(_deep_map)

    def get_tail( self ):
        @MemoizedGenerator
        def _tail():
            for term in islice(self, 1, None):
                yield term

        return PowerSeries(_tail)

    @property
    def zero(self):
        return get_zero(self)

    @property
    def tail(self):
        return self.get_tail()

    @property
    def xmul(self):
        @MemoizedGenerator
        def _xmul():
            yield 0
            for term in self:
                yield term

        return PowerSeries(_xmul)

    def __add__(self, entry):
        if is_powerseries(entry):
            @MemoizedGenerator
            def _add():
                for term1, term2 in izip(self, entry):
                    yield term1 + term2
        else:
            @MemoizedGenerator
            def _add():
                it = iter(self)
                yield next(it) + entry

                for term in it:
                    yield term

        return PowerSeries(_add)

    def __mul__(self, entry):
        if not is_powerseries(entry):
            if entry == 1:
                return self
            elif entry == 0 and not is_powerseries(self.zero):
                return PowerSeries()
            else:
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
        >>> 1/B == 1-X-X*Y
        True

        """

        if is_powerseries(entry):
            return entry * (1/self)

        @MemoizedGenerator
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
        return self + (-entry)

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

    def __pow__( self, alpha ):
        """

        >>> X*X == X**2
        True
    
        >>> log((1/(1+X))**(F(3,2))) == -F(3,2)*log(1+X)
        True

        >>> exp( X + 3*Y )**F(-4,7) == exp( -F(4,7) * (X + 3*Y) )
        True

        """
            
        f0 = self.zero
        if not is_powerseries(f0) and f0 == 0:
            if floor(alpha) == alpha:
                @MemoizedGenerator
                def _pow():
                    for e in repeat(0, alpha):
                        yield e
                    for term in self.tail ** alpha:
                        yield term
                
                return PowerSeries(_pow)
            else:
                raise ValueError("Can't raise powerseries with vanishing first term to non integer power")

        c0 = self.zero**alpha if is_powerseries(self.zero) or self.zero != 1 else 1

        @MemoizedGenerator
        def _pow():
            for term in integral(alpha * P * D(self)/ self, c0 ):
                yield term

        P = PowerSeries(_pow)
        return P

    def __call__( self, *args ):
        """

        >>> (1/(1-X-X*Y))(X,X) == 1/(1-X-X**2)
        True

        >>> A = exp(X)
        >>> B = log(1/(1-X)) 
        >>> A(B) == 1/(1-X)
        True

        >>> (1/(1-X-X*Y))(Y,X) == 1/(1-Y-Y*X)
        True

        >>> (1/(1-X-X*Y))(Y) == 1/(1-Y-Y*X)
        True

        >>> (1/(1-X-Z))(X,Y,X*Y) == 1/(1-X-X*Y)
        True

        >>> (1/(1-X))(Y) == 1/(1-Y)
        True

        """

        n = len(args)

        try:
            k,a = next( ( (k,a) for k,a in enumerate(args) if not is_powerseries(a) ) )

            if a == 0:
                if n > 1:
                    return self.deep_apply( get_zero, k )( *(args[:k] + args[k+1:]) )
                else:
                    return self.zero
            else:
                raise ValueError("Can't calculate powerseries at non-zero value")

        except StopIteration:
            pass

        @MemoizedGenerator
        def _compose():
            c0 = self.deep_apply(get_zero, n)( *map( get_zero, args ) )

            G = ( self.deep_apply( D, k ) for k in xrange(n) )
            F = imap( D, args )

            r = sum( g.deep_apply(lambda x, f=f: f*x, n) for g,f in izip(G, F) ) + self.deep_apply( D, n )
            for term in integral(r(*args), c0):
                yield term

        return PowerSeries(_compose)

def is_powerseries( entry ):
    return isinstance(entry, PowerSeries)

def get_zero( d ):
    if is_powerseries(d):
        for term in d:
            return term
    else:
        return d

def D( f ):
    if not is_powerseries(f):
        return 0
    @MemoizedGenerator
    def _D():
        for n,term in enumerate(f.tail):
            yield (n+1) * term

    return PowerSeries(_D)

def linsolve( M, B ): 
    for n,b in enumerate(B):
        print "b"
        print b
    for n,e in enumerate(M):
        inv = 1/e[n]
        s = [ u*inv for u in e ]
        for m,d in enumerate(M):
            if m == n:
                continue

            M[m] = [ t - r*d[n] for t,r in izip(d, s) ]
            B[m] = B[m] - inv*B[n]

    for n,e in enumerate(M):
        for m, r in enumerate(e):
            print "n, m", n, m
            print r

    for n,b in enumerate(B):
        print "b"
        print b

    return B

def solve( *args ):
    """
        

    """
    n = len(args)

    get_n_zero = repeated( get_zero, n )

    print "START"
    for a in args:
        print a
    print "START ENDE"

    if any( not is_powerseries(get_n_zero(a)) for a in args ):
        if all( get_n_zero(a) == 0 for a in args ):
            return (PowerSeries(),)*n
        else:
            raise ValueError("No solution")
    
    c0s = solve( *[ a.deep_apply( get_zero, n ) for a in args ] )
    print "REC RES: "
    for c in c0s:
        print c

    m = [ [ a.deep_apply( D, k ) for k in xrange(n) ] for a in args ]
    b = [   -a.deep_apply( D, n ) for a in args ]
    
    dfs = linsolve( m, b )
    print "DFS"
    for df in dfs:
        print df
        print df(-Y)
    print "DFS ENDE"

    SOL = []
    for i in xrange(n):
        def _solve(i=i):
            for term in integral( dfs[i](*SOL), c0s[i] ):
                yield term

        SOL.append(PowerSeries(_solve))

    return tuple(SOL)

def integral( f, const=0 ):
    @MemoizedGenerator
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

    @MemoizedGenerator
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

    @MemoizedGenerator
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

