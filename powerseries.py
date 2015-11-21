from fractions import Fraction as F
from itertools import count, islice, izip, repeat, imap, chain

from MemoizedGenerator import memoizedGenerator

class PowerSeries(object):
    testlimit = 6

    def __init__(self, g=None):
        self.__g = g
        self.__zero = None

    def __eq__(self, entry):
        #print "Warning: comparing powerseries!"
        return all(s == e for s,e in islice(izip(self,entry), self.testlimit))

    def __iter__( self ):
        return self.__g() if self.__g else repeat(0)

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

    def getstrdeep(self, nums=[]):
        def gen_str():
            n = nums[0] if nums else self.testlimit
            r = nums[1:] if nums else []
            is_pps = any( isinstance(term, PowerSeries) for term in islice(self, n) )
            for term in islice(self, n):
                if is_pps:
                    yield term.getstrdeep(r) + "\n"
                else:
                    yield str(term) + ", "

        return "".join(gen_str()) + "..."


    def __getitem__(self, key):
        return next(islice(self, key, None))

    def deep_apply( self, func, n=1 ):
        if n == 0:
            return func(self)

        if n == 1:
            @memoizedGenerator
            def _deep_apply():
                return imap( func, self )

            return PowerSeries( _deep_apply )
        else:
            return self.deep_apply( lambda x: x.deep_apply(func, n-1) )

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
                return imap( lambda (a,b): a+b, izip( self, entry) )
        else:
            def _add():
                return chain( imap( lambda a: a+entry, islice(self, 0, 1) ), islice(self, 1, None) )

        return PowerSeries(_add)

    def __mul__(self, entry):
        if not is_powerseries(entry):
            if entry == 1:
                return self
            elif entry == 0:
                if not is_powerseries(self.zero):
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
                f0G = G.deep_apply( lambda x: f0*x )
                mterms.append(f0G)
            if is_powerseries(g0) or g0 != 0:
                g0F = F.deep_apply( lambda x: x*g0 )
                mterms.append(g0F)
            
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

        @memoizedGenerator
        def _rdiv():
            f0 = self.zero
            if is_powerseries(f0):
                recip = entry / f0
            elif isinstance(f0, int):
                recip = F(entry, f0)
            else: 
                recip = entry / f0

            yield recip

            for term in ( (self.tail * R).deep_apply( lambda x: x*(-recip) ) ):
                yield term

        R = PowerSeries(_rdiv)
        return R

    __radd__ = __add__

    def __sub__(self, entry):
        return self + (-entry)

    def __rsub__(self, entry):
        return entry + (-self)

    def __neg__(self):
        return self.deep_apply( lambda x: -x )

    __rmul__ = __mul__

    def __div__(self, entry):
        if is_powerseries(entry):
            return entry.__rdiv__(self)
        elif entry == 1:
            return self
        elif entry == 0:
            raise ValueError("Zero division error")
        else:
            return self * F(1, entry)

    def __pow__( self, alpha ):
        """
        >>> X**0 == I
        True

        >>> X*X == X**2
        True
    
        >>> log((1/(1+X))**(F(3,2))) == -F(3,2)*log(1+X)
        True

        >>> exp( X + 3*Y )**F(-4,7) == exp( -F(4,7) * (X + 3*Y) )
        True

        """
            
        f0 = self.zero
        if not is_powerseries(f0) and f0 == 0:
            if isinstance(alpha, int):
                if alpha == 0:
                    return I
                    
                @memoizedGenerator
                def _pow():
                    for e in repeat(0, alpha):
                        yield e
                    for term in self.tail ** alpha:
                        yield term
                
                return PowerSeries(_pow)
            else:
                raise ValueError("Can't raise powerseries with vanishing first term to non integer power")

        c0 = self.zero**alpha if is_powerseries(self.zero) or self.zero != 1 else 1

        @memoizedGenerator
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
                    return self.deep_apply( lambda x: x.zero, k )( *(args[:k] + args[k+1:]) )
                else:
                    return self.zero
            else:
                raise ValueError("Can't calculate powerseries at non-zero value")

        except StopIteration:
            pass

        def get_zero( d ):
            if is_powerseries(d):
                return d.zero
            else:
                return d

        def get_D( d ):
            if not is_powerseries(d):
                return 0
            else:
                return D(d)

        G = ( self.deep_apply( D, k ) for k in range(n) )
        F = imap( D, args )

        r = sum( g.deep_apply(lambda x, f=f: f*x, n) for g,f in izip(G, F) ) + self.deep_apply( get_D, n )
        @memoizedGenerator
        def _compose():
            c0 = self.deep_apply( get_zero, n )( *map( lambda x: x.zero, args ) )

            for term in integral(r.compose(*args), c0):
                yield term

        return PowerSeries(_compose)

    def __call__( self, *args ):
        return self.compose(*args)

def is_powerseries( entry ):
    return isinstance(entry, PowerSeries)

def linsolve( M, b ): 
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
    diag = b[:]
    for i in range(n):
        for k in range(i, n):
            if is_powerseries(M[k][i]):
                if M[k][i].zero != 0:
                    break
            elif M[k][i] != 0:
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
            M[j]= [0*e for e in M[j][:i+1] ] + [ t - r*d for t,r in zip(M[j], M[i])[i+1:] ]

    for i in reversed(range(n)):
        b[i] = diag[i]*(b[i] - sum( M[i][j]*b[j] for j in range(i+1,n) ))

    return b

def solve( *args ):
    """
        
    >>> solve( Y-1 + exp(X))[0] == log(1-X)
    True

    >>> T = [ log(1+X) + exp(Y)-1 + Z, 1/(1-X-X*Y) - 1 + Z ]
    >>> all( t.compose( solve(t)[0] ) == tensor(ZERO, ZERO) for t in T )
    True

    >>> W = [ X + Y + 2*Z + Y*Y - Y*Y*Y, X + Z + X*X ]
    >>> R = solve(*W)

    >>> W[0](*R) == ZERO
    True
    >>> W[1](*R) == ZERO
    True

    """

    def get_D( d ):
        if not is_powerseries(d):
            return 0
        else:
            return D(d)

    n = len(args)

    a_n_zero = args
    for i in range(n):
        a_n_zero = tuple( a.zero for a in a_n_zero )
    
    if any( not is_powerseries(az) for az in a_n_zero ):
        if all( az == 0 for az in a_n_zero ):
            return (0,)*n
        else:
            raise ValueError("No solution")
    
    c0s = solve( *[ a.deep_apply( lambda x: x.zero, n ) for a in args ] )

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

def D( f ):
    @memoizedGenerator
    def _D():
        for n,term in enumerate(f.tail):
            yield (n+1) * term

    return PowerSeries(_D)

def integral( f, const=0 ):
    @memoizedGenerator
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
        f0, f1 = args[0], args[1]

        if not is_powerseries(f0) or not is_powerseries(f1):
            return f0 * f1
        else:
            return f0.deep_apply( lambda x: tensor(x, f1) )
    else:
        return 0

def exp( f ):
    if not is_powerseries(f):
        if f == 0:
            return 1
        else:
            raise ValueError("You can't calculate exp of %d with the powerseries package" % f)

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

    @memoizedGenerator
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

    @memoizedGenerator
    def _log():
        for term in integral( D(f)/f, c0 ):
            yield term

    return PowerSeries(_log)

ZERO = PowerSeries()
I = 1 + ZERO
X = I.xmul
Y = tensor(I, X)
Z = tensor(I, Y)

def benchmark():
    N = 20
    def _fac():
        r = 1
        for n in count():
            yield r
            r*= n+1
    
    fac = PowerSeries( _fac )
    print "fac: ", fac.getstr(N)

    F = fac - 1
    I = F / ( 1 + F)

    Finv = solve( Y - F )[0]
    print "Finv: ", Finv.getstr(N)

if __name__ == '__main__':
    import doctest
    doctest.testmod()

    import cProfile
    cProfile.run('benchmark()')
