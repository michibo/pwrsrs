
from fractions import Fraction as F
from itertools import count, islice, izip, chain, repeat, imap
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
    
    def shuffle( self, k ):
        if k == 0:
            return self

        def _shuffle():
            def _f0():
                for term in self:
                    if isinstance(term, PowerSeries):
                        yield term.zero
                    else:
                        yield term

            yield PowerSeries(_f0).shuffle(k-1)

            def _f():
                for term in self:
                    if isinstance(term, PowerSeries):
                        yield term.tail
                    else:
                        yield PowerSeries()

            for term in PowerSeries(_f).shuffle(k):
                yield term

        return PowerSeries(_shuffle)

    @property
    def flip( self ):
        return self.shuffle(1)

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

    def compose(self, *args):
        """

        >>> (1/(1-X-X*Y)).compose(X,X) == 1/(1-X-X**2)
        True

        >>> A = exp(X)
        >>> B = log(1/(1-X)) 
        >>> A.compose(B) == 1/(1-X)
        True

        >>> (1/(1-X-X*Y)).compose(Y,X) == 1/(1-Y-Y*X)
        True

        >>> (1/(1-X-X*Y)).compose(Y) == 1/(1-Y-Y*X)
        True

        >>> (1/(1-X-Z)).compose(X,Y,X*Y) == 1/(1-X-X*Y)
        True

        >>> (1/(1-X)).compose(Y) == 1/(1-Y)
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
            for term in integral(r.compose(*args), c0):
                yield term

        return PowerSeries(_compose)

    def __call__( self, *args ):
        return self.compose(*args)

def is_powerseries( entry ):
    return isinstance(entry, PowerSeries)

def get_zero( d ):
    if is_powerseries(d):
        for term in d:
            return term
    else:
        return d

def D( f, n=1 ):

    if n > 1:
        return repeated(D, n)(f)

    if not is_powerseries(f):
        return 0

    @MemoizedGenerator
    def _D():
        for n,term in enumerate(f.tail):
            yield (n+1) * term

    return PowerSeries(_D)

def linsolve( M, B ): 
    """
    >>> W = [ [ exp(X+2*Y), log(1+Y) ], [ X**2 - exp(Y*(exp(X)-1)), 1/(1-X*Y-X) ]  ]
    >>> B = [  X + Y*3 ,  1/(1-X*Y) ]
    >>> W2 = W[:]
    >>> B2 = B[:]

    >>> R = linsolve( W, B )
    >>> R[0]*W2[0][0] + R[1]*W2[0][1] - B2[0] == tensor(ZERO, ZERO)
    True

    >>> R[0]*W2[1][0] + R[1]*W2[1][1] - B2[1] == tensor(ZERO, ZERO)
    True

    """
    n = len(M)
    for i in range(n):
        inv = 1/M[i][i]
        M[i] = [ u*inv for u in M[i] ]
        B[i] = inv*B[i]

        for j in range(n):
            if i == j:
                continue

            d = M[j][i]
            B[j] = B[j] - B[i]*d
            M[j] = [ t - r*d for t,r in zip(M[j], M[i]) ]

    return B

def solve( *args ):
    """
        
    >>> solve( Y-1 + exp(X))[0] == log(1-X)
    True

    >>> T = [ log(1+X) + exp(Y)-1 + Z, 1/(1-X-X*Y) - 1 + Z ]
    >>> all( t.compose( solve(t)[0] ) == tensor(ZERO, ZERO) for t in T )
    True

    >>> W = [ X + Y + 2*Z + Y*Y - Y*Y*Y, X + Z +X*X ]
    >>> R = solve(*W)

    >>> W[0](*R) == ZERO
    True
    >>> W[1](*R) == ZERO
    True

    """
    n = len(args)

    get_n_zero = repeated( get_zero, n )

    if any( not is_powerseries(get_n_zero(a)) for a in args ):
        if all( get_n_zero(a) == 0 for a in args ):
            return (0,)*n
        else:
            raise ValueError("No solution")
    
    c0s = solve( *[ a.deep_apply( get_zero, n ) for a in args ] )

    m = [ [ a.deep_apply( D, k ) for k in xrange(n) ] for a in args  ]
    b = [  -a.deep_apply( D, n ) for a in args ]

    dfs = linsolve( m, b )

    def make_solver( df, c0 ):
        @MemoizedGenerator
        def _solve():
            for term in integral( df(*SOL), c0 ):
                yield term
        return PowerSeries(_solve)

    SOL = tuple( make_solver( df, c0 ) for df, c0 in zip(dfs, c0s) )

    return SOL

def integral( f, const=0 ):
    @MemoizedGenerator
    def _int():
        yield const
        for n, term in enumerate(f):
            yield F(1,n+1)*term

    return PowerSeries(_int)

def tensor( *args ):
    if len(args) == 1:
        return args[0]
    elif len(args) > 2:
        return tensor( args[0], tensor( *args[1:] ) )
    elif len(args) == 2:
        return args[0].deep_map( lambda x: args[1]*x )
    else:
        return 0

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

ZERO = PowerSeries()
I = 1 + ZERO
X = I.xmul
Y = tensor(I, X)
Z = tensor(I, Y)

if __name__ == '__main__':
    import doctest
    doctest.testmod()

