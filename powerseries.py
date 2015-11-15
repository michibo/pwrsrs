from fractions import Fraction as F
from itertools import count, islice, izip, repeat, imap
import math
from math import floor
import matrix
from matrix import Matrix

from MemoizedGenerator import memoizedGenerator

def repeated(func, n):
    def ret(x):
        return reduce( lambda x,func: func(x) , repeat(func, n), x )
    return ret

class PowerSeries(object):
    testlimit = 5

    def __init__(self, g=None):
        self.__g = g

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
                for term in self:
                    yield func(term)
        else:
            @memoizedGenerator
            def _deep_apply():
                for term in self:
                    yield term.deep_apply( func, n-1 )

        return PowerSeries( _deep_apply )

    @property
    def ps_exp(self):
        def _g(m=1):
            for i,term in enumerate(self):
                yield m*term
                m = m*(i+1)

        return PowerSeries( _g )

    @property
    def zero(self):
        for term in self:
            return term

    @property
    def tail(self):
        @memoizedGenerator
        def _tail():
            for term in islice(self, 1, None):
                yield term

        return PowerSeries(_tail)

    @property
    def xmul(self):
        @memoizedGenerator
        def _xmul():
            yield self.zero*0
            for term in self:
                yield term

        return PowerSeries(_xmul)

    def __add__(self, entry):
        if is_powerseries(entry):
            @memoizedGenerator
            def _add():
                for term1, term2 in izip(self, entry):
                    yield term1 + term2
        else:
            @memoizedGenerator
            def _add():
                it = iter(self)
                yield next(it) + entry

                for term in it:
                    yield term

        return PowerSeries(_add)

    def __mul__(self, entry):
        if not is_powerseries(entry):
            if not isinstance(entry, Matrix) and entry == 1:
                return self
            elif not isinstance(entry, Matrix) and entry == 0 and not is_powerseries(self.zero):
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
            return 0*self
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
            if floor(alpha) == alpha:
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
                    return self.deep_apply( get_zero, k )( *(args[:k] + args[k+1:]) )
                else:
                    return self.zero
            else:
                raise ValueError("Can't calculate powerseries at non-zero value")

        except StopIteration:
            pass

        @memoizedGenerator
        def _compose():
            c0 = self.deep_apply(get_zero, n)( *map( get_zero, args ) )

            G = ( self.deep_apply( D, k ) for k in range(n) )
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
        return d.zero
    else:
        return d

def get_tail( d ):
    return d.tail

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
    for i in range(n):
        inv = 1/M[i][i]
        M[i] = [ u*inv for u in M[i] ]
        b[i] = inv*b[i]

        for j in range(n):
            if i == j:
                continue

            d = M[j][i]
            b[j] = b[j] - b[i]*d
            M[j] = [ t - r*d for t,r in zip(M[j], M[i]) ]

    return b

def linsolve2( M, b ): 
    """
    >>> W = [ [ exp(X+2*Y), log(1+Y) ], [ X**2 - exp(Y*(exp(X)-1)), 1/(1-X*Y-X) ]  ]
    >>> B = [  X + Y*3 ,  1/(1-X*Y) ]
    >>> W2 = W[:]
    >>> B2 = B[:]

    >>> R = linsolve2( W, B )
    >>> R[0]*W2[0][0] + R[1]*W2[0][1] - B2[0] == tensor(ZERO, ZERO)
    True

    >>> R[0]*W2[1][0] + R[1]*W2[1][1] - B2[1] == tensor(ZERO, ZERO)
    True

    """
    n = len(b)
    if all( all( not is_powerseries( e ) for e in row ) for row in M ):
        M = M[:]
        b = b[:]
        for i in range(n):
            inv = F(1,1)/M[i][i]
            M[i] = [ u*inv for u in M[i] ]
            b[i] = inv*b[i]

            for j in range(n):
                if i == j:
                    continue

                d = M[j][i]
                b[j] = b[j] - b[i]*d
                M[j] = [ t - r*d for t,r in zip(M[j], M[i]) ]

        return b

    M0 = [ [ e.zero for e in row ] for row in M ]
    M1 = [ [ e.tail for e in row ] for row in M ]

    def _linsolve(b=b):
        b0 = [ e.zero for e in b ]

        x0 = linsolve2(M0, b0)
        yield x0

# M0 x0 = b0
# M x1 + M1 x0 = b1
# M x1 = b1 - M1 x0

        b1 = [ e.tail for e in b ]
        r1 = [ eb1 - sum( eM1*ex0 for eM1, ex0 in zip(row, x0) ) for row, eb1 in zip(M1, b1) ]

        for term in _linsolve(r1):
            yield term
    
    SOL = PowerSeries(_linsolve)

    def make_x(k):
        def _xk():
            for term in SOL:
                yield term[k]

        return PowerSeries(_xk)

    return [ make_x(k) for k in range(n) ]

def powerlinsolve( M, b ):
    #"""
    #>>> W = [ [ exp(X+2*Y), log(1+Y) ], [ X**2 - exp(Y*(exp(X)-1)), 1/(1-X*Y-X) ]  ]
    #>>> B = [ [  X + Y*3] , [ 1/(1-X*Y) ] ]
    #>>> W2 = W[:]
    #>>> B2 = B[:]
#
#    >>> R = powerlinsolve( W, B )
#    >>> R[0]*W2[0][0] + R[1]*W2[0][1] - B2[0][0] == tensor(ZERO, ZERO)
#    True
#
#    >>> R[0]*W2[1][0] + R[1]*W2[1][1] - B2[1][0] == tensor(ZERO, ZERO)
#    True
#
#    """
    n = len(b)

    def _Mgen(M):
        if all( all( not is_powerseries( e ) for e in row ) for row in M ):
            return Matrix(M)

        def _M():
            M0 = [ [ e.zero for e in row ] for row in M ]
            yield _Mgen(M0) 

            M1 = [ [ e.tail for e in row ] for row in M ]
            for term in _Mgen( M1 ):
                yield term

        return PowerSeries(_M)

    mM = _Mgen(M)
    mb = _Mgen(b)

    mx = (matrix.identity(n)/mM) *mb

    def proj( M, i, j ):
        if is_powerseries(M):
            def _proj():
                for term in M:
                    yield proj( term, i, j )
            return PowerSeries(_proj)
        else:
            return M._rows[i][j]
        

    def make_x( k ):
        def _xk(k=k):
            for term in mx:
                yield proj( term, k, 0 )

        return PowerSeries(_xk)

    return [ make_x(k) for k in range(n) ]

def solve_vector( n, v ):
    """
    >>> print solve_vector(1, ( Y-1 + exp(X) )*matrix.identity(1))
    """
    v0 = repeated( get_zero, n )(v)
    print v0
    print v

    if not is_powerseries( v0 ):
        if all( e == 0 for (e,) in v0 ):
            return Matrix( tuple( (0,) for i in range(n)) )
        else:
            raise ValueError("No solution")

    c0 = solve_vector( n, v.zero )
    
    args = [ v.deep_apply( D, k ) for k in range(n) ]
    @memoizedGenerator
    def _dmat():
        for m in izip( *args ):
            yield Matrix( tuple( tuple( e for (e,) in row ) for row in zip(*m) ) )

    M = PowerSeries(_dmat)

    b = -v.deep_apply( D, n )

    dfs = b/M

    @memoizedGenerator
    def _sol():
        SOLs = [ SOL.deep_apply( lambda x: x._rows[i][0] ) for i in range(n) ]

        for term in integral( dfs(*SOLs), c0 ):
            yield term

    SOL = PowerSeries( _sol )

    return SOL

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
    n = len(args)

    get_n_zero = repeated( get_zero, n )
    
    if any( not is_powerseries(get_n_zero(a)) for a in args ):
        if all( get_n_zero(a) == 0 for a in args ):
            return (0,)*n
        else:
            raise ValueError("No solution")
    
    c0s = solve( *[ a.deep_apply( get_zero, n ) for a in args ] )

    m = [ [ a.deep_apply( D, k ) for k in range(n) ] for a in args  ]
    b = [  -a.deep_apply( D, n ) for a in args ]

    dfs = linsolve( m, b )
    
    def make_solver( df, c0 ):
        @memoizedGenerator
        def _solve():
            for term in integral( df(*SOL), c0 ):
                yield term
        return PowerSeries(_solve)

    SOL = tuple( make_solver( df, c0 ) for df, c0 in zip(dfs, c0s) )

    return SOL

def D( f, n=1 ):
    if n == 0:
        return f

    if n > 1:
        return repeated(D, n)(f)

    if not is_powerseries(f):
        return 0

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
            return math.exp(f)

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
    if not is_powerseries(f):
        return math.log(f)
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

if __name__ == '__main__':

    W = [ [ exp(X+2*Y), log(1+Y) ], [ X**2 - exp(Y*(exp(X)-1)), 1/(1-X*Y-X) ]  ]
    B = [  X + Y*3 ,  1/(1-X*Y) ]
    W2 = W[:]
    B2 = B[:]

    A = [ [ 1-X, X*X], [X*0, 1-X] ]
    A1 = [ [ 123, 43], [512, 3] ]

    B3 = [ X.tail*X, X.tail ]
    R2 = linsolve2(A, B3)
    R3 = linsolve2(A1, [ 3, 4] )
    print R3[0]*A1[1][0] + R3[1]*A1[1][1]
    print A[0][0]
    print B3[0]
    print R2[0]*A[0][0] + R2[1]*A[0][1]


    R = linsolve2( W2, B )
    print R[0]
    print R[1]
    print B2[0]

    print R[0]*W2[0][0] + R[1]*W2[0][1]
    
    #print solve_vector(1, ( Y-1 + exp(X) )*matrix.identity(1))
    
    #import doctest
    #doctest.testmod()

