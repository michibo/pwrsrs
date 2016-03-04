from fractions import Fraction as F
from itertools import count, islice, repeat, chain, starmap
import math

pstestlimit = 5

def memoizedGenerator( gen ):
    _iter = gen()
    _cache = []

    def _gen():
        for n in count():
            if n < len(_cache):
                yield _cache[n]
            else:
                term = next(_iter)
                _cache.append(term)
                yield term

    return _gen

def num_to_str( term ):
    if isinstance(term, float):
        return "\t% .3e" % term
    else:
        return "\t"+str(term)

class PowerSeries(object):
    def __init__(self, g=None):
        self.__g = g

    def __eq__(self, entry):
        print("Warning: comparing powerseries!")
        return Equal( self, entry )

    def __iter__( self ):
        return self.__g() if self.__g else repeat(0)

    def __str__(self):
        return self.getstr()

    def getstr(self, nums=[], term_to_str=num_to_str):
        def gen_str():
            if isinstance(nums, int):
                n = nums
                r = nums
            else:
                n = nums[0] if nums else pstestlimit
                r = nums[1:] if nums else []
            
            is_pps = isinstance(self.zero, PowerSeries)

            for term in islice(self, n):
                if is_pps:
                    yield term.getstr(r) + "\n"
                else:
                    yield term_to_str(term) + ", "

        return "".join(gen_str()) + "..."

    def __getitem__(self, key):
        if isinstance(key, slice):
            return islice(self, key.start, key.stop, key.step)
        else:
            return next(islice(self, key, None))

    def deep_apply( self, func, n=1 ):
        if n == 0:
            return func(self)

        if n == 1:
            @memoizedGenerator
            def _deep_apply():
                return map( func, self )

            return PowerSeries( _deep_apply )
        else:
            return self.deep_apply( lambda x: x.deep_apply(func, n-1) )

    @property
    def ord2exp(self):
        """
        >>> Equal((1/(1-X)).ord2exp, exp(X))
        True
        """
        def _ord2exp(f=1):
            for n,term in enumerate(self):
                yield F(term, f)
                f*= n+1

        return PowerSeries(_ord2exp)

    @property
    def exp2ord(self):
        """
        >>> Equal(exp(X).exp2ord, 1/(1-X))
        True
        """
        def _exp2ord(f=1):
            for n,term in enumerate(self):
                yield term * f
                f*= n+1

        return PowerSeries(_exp2ord)

    @property
    def zero(self):
        for term in self:
            return term

    @property
    def tail(self):
        def _tail():
            return islice(self, 1, None)

        return PowerSeries(_tail)

    @property
    def xmul(self):
        def _xmul():
            return chain( ( self.zero*0,), self )

        return PowerSeries(_xmul)

    def __add__(self, entry):
        if is_powerseries(entry):
            @memoizedGenerator
            def _add():
                return starmap( lambda a,b: a+b, zip( self, entry ) )
        else:
            def _add():
                return chain( map( lambda a: a+entry, islice(self, 0, 1) ), islice(self, 1, None) )

        return PowerSeries(_add)

    __radd__ = __add__

    def __sub__(self, entry):
        return self + (-entry)

    def __rsub__(self, entry):
        return entry + (-self)

    def __neg__(self):
        return self.deep_apply( lambda x: -x )

    def __mul__(self, entry):
        """
        >>> Equal((exp(X-Z)/(1-X)) * (exp(Y+Z)/(1-Y)), exp(X+Y)/(1-X-Y+X*Y))
        True
        """
        if not is_powerseries(entry):
            if entry == 1:
                return self
            elif entry == 0:
                if is_powerseries(self.zero):
                    z = self.zero*0
                    def _z():
                        return repeat( z )

                    return PowerSeries(_z)
                else:
                    return PowerSeries()
            else:
                return self.deep_apply( lambda x: x*entry )
        
        @memoizedGenerator
        def _mul():
            f0 = self.zero
            g0 = entry.zero
            yield f0 * g0

            F = self.tail
            G = entry.tail

            mterms = [(F * G).xmul]
            if is_powerseries(f0) or f0 != 0:
                f0G = G.deep_apply( lambda x: x*f0 )
                mterms.append(f0G)
            if is_powerseries(g0) or g0 != 0:
                g0F = F.deep_apply( lambda x: x*g0 )
                mterms.append(g0F)
            
            for terms in zip(*mterms):
                yield sum(terms)

        return PowerSeries(_mul)

    __rmul__ = __mul__

    def __truediv__(self, entry):
        if is_powerseries(entry):
            return entry.__rtruediv__(self)
        elif entry == 1:
            return self
        elif entry == 0:
            raise ValueError("Zero division error")
        else:
            return self * (F(1, 1) / entry)

    def __rtruediv__(self, entry):
        """
        >>> A = 10/ (1 - X)
        >>> Equal(A, 1/(1-X) * 10 )
        True

        >>> B = 1 / (1 - X - X*Y)
        >>> Equal(1/B, 1-X-X*Y)
        True

        >>> C = 100*solve( Y - X*exp(X) )[0].tail
        >>> Equal( C/C, 1 )
        True

        """

        @memoizedGenerator
        def _rdiv():
            f0 = self.zero
            if isinstance(f0, int):
                recip = F(1, f0)
            else:
                recip = 1 / f0

            if not is_powerseries(entry):
                yield entry * recip

                for term in ( (self.tail * R).deep_apply( lambda x: -x*recip ) ):
                    yield term
            else:
                yield entry.zero * recip

                for term in ( (entry.tail-self.tail * R).deep_apply( lambda x: x*recip ) ):
                    yield term

        R = PowerSeries(_rdiv)
        return R

    def __pow__( self, alpha ):
        """
        >>> Equal(X**0, I)
        True

        >>> Equal(X*X, X**2)
        True
    
        >>> Equal( log((1/(1+X))**(F(3,2))), -F(3,2)*log(1+X))
        True

        >>> Equal(exp( X + 3*Y )**F(-4,7), exp( -F(4,7) * (X + 3*Y) ))
        True

        """
            
        f0 = self.zero
        if not is_powerseries(f0) and f0 == 0:
            if isinstance(alpha, int) and alpha >= 0:
                if alpha == 0:
                    return self*0 + 1
                    
                @memoizedGenerator
                def _pow():
                    for e in repeat(0, alpha):
                        yield e
                    for term in self.tail ** alpha:
                        yield term
                
                return PowerSeries(_pow)
            else:
                raise ValueError("Can't raise powerseries with vanishing first term to non positive integer power")

        c0 = self.zero**alpha if is_powerseries(self.zero) or self.zero != 1 else 1

        @memoizedGenerator
        def _pow():
            for term in integral(alpha * P * D(self) / self, c0 ):
                yield term

        P = PowerSeries(_pow)
        return P

    def compose(self, *args):
        """

        >>> Equal((1/(1-X-X*Y)).compose(X,X), 1/(1-X-X**2))
        True

        >>> A = exp(X)
        >>> B = log(1/(1-X)) 
        >>> Equal( A.compose(B), 1/(1-X) )
        True

        >>> Equal((1/(1-X-X*Y)).compose(Y,X), 1/(1-Y-Y*X))
        True

        >>> Equal((1/(1-X-X*Y)).compose(Y), 1/(1-Y-Y*X))
        True

        >>> Equal((1/(1-X-Z)).compose(X,Y,X*Y), 1/(1-X-X*Y))
        True

        >>> Equal((1/(1-X)).compose(Y), 1/(1-Y))
        True

        """

        n = len(args)

        try:
            k,a = next( ( (k,a) for k,a in enumerate(args) if not is_powerseries(a) ) )

            if a == 0:
                if n > 1:
                    return self.deep_apply( lambda x: x.zero, k )( *(args[:k] + args[k+1:]) )
                else:
                    return self.zero
            else:
                raise ValueError("Can't calculate powerseries at non-zero value")

        except StopIteration:
            pass

        get_zero = lambda d: d.zero if is_powerseries(d) else d
        get_D    = lambda d: D(d)   if is_powerseries(d) else 0

        @memoizedGenerator
        def _compose():
            G = ( self.deep_apply( D, k ) for k in range(n) )
            F = map( D, args )

            r = sum( g.deep_apply(lambda x, f=f: x*f, n) for g,f in zip(G, F) ) + self.deep_apply( get_D, n )

            z = self.deep_apply( get_zero, n )

            c0 = z.compose( *map( lambda x: x.zero, args ) )

            for term in integral(r.compose(*args), c0):
                yield term

        return PowerSeries(_compose)

    def __call__( self, *args ):
        return self.compose(*args)

    def exp( self ):
        if not is_powerseries(self):
            if self == 0:
                return 1
            else:
                raise ValueError("You can't calculate exp of %d with the powerseries package" % self)

        """

        >>> e = exp(X)
        >>> Equal( e, D(e) )
        True
        >>> Equal( e, integral(e, 1) )
        True
        >>> Equal( log(e), X )
        True
        >>> d = exp(3*X*X)
        >>> Equal(d*e, exp(X + 3*X**2))
        True

        """
        f0 = self.zero
        if is_powerseries( f0 ):
            c0 = exp(f0)
        elif f0 == 0:
            c0 = 1
        else:
            raise ValueError("Can't take exp of powerseries with non-zero constant term")

        @memoizedGenerator
        def _exp():
            for term in integral( E * D(self), c0 ):
                yield term

        E = PowerSeries(_exp)
        return E

    def log( self ):
        """

        >>> l = log(1+X) 
        >>> Equal( 3*l, log((1+X)*(1+X)*(1+X)) )
        True
        >>> Equal( D(l), 1/(1+X) )
        True

        """
        f0 = self.zero
        if is_powerseries( f0 ):
            c0 = log(f0)
        elif f0 == 1:
            c0 = 0
        else:
            raise ValueError("Can't take log of powerseries with non-unit constant term")

        @memoizedGenerator
        def _log():
            for term in integral( D(self)/self, c0 ):
                yield term

        return PowerSeries(_log)

    def D( self, n=1 ):
        if n == 1:
            @memoizedGenerator
            def _D():
                return starmap( lambda n,x: (n+1)*x, enumerate(self.tail) )

            return PowerSeries(_D)
        elif n == 0:
            return f
        elif isinstance(n, int) and n > 1:
            return D( D(self), n-1 )
        else:
            raise ValueError("Can't take %d-th derivative" % n)

    def integral( self, const=0 ):
        @memoizedGenerator
        def _int():
            return chain( (const,), starmap( lambda n,x: F(1,n+1)*x, enumerate(self) ) )

        return PowerSeries(_int)

def exp( f ):
    if is_powerseries(f):
        return f.exp()
    else:
        return math.exp(f)

def log( f ):
    if is_powerseries(f):
        return f.log()
    else:
        return math.log(f)

def D( f, n=1 ):
    return f.D(n)

def integral( f, const=0 ):
    return f.integral(const)

def tensor( *args ):
    if len(args) == 1:
        return args[0]
    elif len(args) == 2:
        f0, f1 = args[0], args[1]

        if not is_powerseries(f0) or not is_powerseries(f1):
            return f0 * f1
        else:
            return f0.deep_apply( lambda x: tensor(x, f1) )
    elif len(args) > 2:
        return tensor( args[0], tensor( *args[1:] ) )
    else:
        return 0

def Equal( entry1, entry2, n=pstestlimit ):
    if not is_powerseries( entry1 ) and not is_powerseries( entry2 ):
        return entry1 == entry2
    elif not is_powerseries( entry1 ):
        return Equal(entry2.zero, entry1) and Equal(entry2.tail, PowerSeries())
    elif not is_powerseries( entry2 ):
        return Equal(entry1.zero, entry2) and Equal(entry1.tail, PowerSeries())
    else:
        return all( Equal( s, e, n) for s,e in islice(zip(entry1, entry2), n) )

def is_powerseries( entry ):
    return isinstance(entry, PowerSeries)

def linsolve( M, b ): 
    """
    >>> W = [ [ exp(X+2*Y), log(1+Y) ], [ X**2 - exp(Y*(exp(X)-1)), 1/(1-X*Y-X) ]  ]
    >>> B = [  X + Y*3 ,  1/(1-X*Y) ]
    >>> W2 = W[:]
    >>> B2 = B[:]

    >>> R = linsolve( W, B )
    >>> Equal(R[0]*W2[0][0] + R[1]*W2[0][1] - B2[0], tensor(ZERO, ZERO))
    True

    >>> Equal(R[0]*W2[1][0] + R[1]*W2[1][1] - B2[1], tensor(ZERO, ZERO))
    True

    """

    get_deep_zero = lambda d: get_deep_zero(d.zero) if is_powerseries(d) else d

    n = len(M)
    diag = [0]*n
    for i in range(n):
        for k in range(i, n):
            if get_deep_zero(M[k][i]) != 0:
                break
        else:
            raise ValueError("Zero division Error")

        if k != i:
            M[i], M[k] = M[k], M[i]
            b[i], b[k] = b[k], b[i]

        inv = F(1,1)/M[i][i]
        diag[i] = inv

        for j in range(i+1, n):
            d = M[j][i]*inv
            b[j] = b[j] - b[i]*d
            M[j]= [0]*(i+1) + [ t - r*d for t,r in islice(zip(M[j], M[i]), i+1, n) ]

    for i in reversed(range(n)):
        b[i] = diag[i]*(b[i] - sum( M[i][j]*b[j] for j in range(i+1,n) ))

    return b

def solve( *args ):
    """
        
    >>> Equal(solve( Y-1 + exp(X))[0], log(1-X))
    True

    >>> T = [ log(1+X) + exp(Y)-1 + Z, 1/(1-X-X*Y) - 1 + Z ]
    >>> all( Equal(t.compose( solve(t)[0] ), tensor(ZERO, ZERO)) for t in T )
    True

    >>> W = [ X + Y + 2*Z + Y*Y - Y*Y*Y, X + Z + X*X ]
    >>> R = solve(*W)

    >>> Equal( W[0](*R), ZERO )
    True
    >>> Equal( W[1](*R), ZERO )
    True

    """

    get_zero = lambda d: d.zero if is_powerseries(d) else d
    get_D    = lambda d: D(d)   if is_powerseries(d) else 0

    n = len(args)

    a_n_zero = args
    for i in range(n):
        a_n_zero = tuple( a.zero for a in a_n_zero )
    
    if any( not is_powerseries(az) for az in a_n_zero ):
        if all( az == 0 for az in a_n_zero ):
            return (0,)*n
        else:
            raise ValueError("No solution")
    
    c0s = solve( *[ a.deep_apply( get_zero, n ) for a in args ] )

    m = [ [ a.deep_apply( D, k ) for k in range(n) ] for a in args  ]
    b = [  -a.deep_apply( get_D, n ) for a in args ]

    dfs = linsolve( m, b )
    
    def make_solver( df, c0 ):
        @memoizedGenerator
        def _solve():
            for term in integral( df(*SOL), c0 ):
                yield term

        return PowerSeries(_solve)

    SOL = tuple( make_solver( df, c0 ) for df, c0 in zip(dfs, c0s) )

    return SOL

ZERO = PowerSeries()
I = 1 + ZERO
X = I.xmul
Y = tensor(I, X)
Z = tensor(I, Y)

if __name__ == '__main__':
    import doctest
    doctest.testmod()
