
from fractions import Fraction as F

def hilbert(N):
    return Matrix( tuple( tuple( F(1, i+j+1) for j in range(N)) for i in range(N) ) )

def identity(N):
    return Matrix( tuple( tuple( 1 if i==j else 0 for j in range(N) ) for i in range(N)) )

def unit_vec(N, k):
    return Matrix( tuple( (1,) if k==i else (0,) for i in range(N) ) )

class Matrix(object):
    def __init__( self, rows ):
        self._N = len(rows)
        self._M = len(rows[0])
        self._rows = rows

    def __str__(self):
        return "[%s]" % ",".join("(%s)" % ",".join( str(e) for e in row ) for row in self)

    def __iter__(self):
        return iter(self._rows)
       
    def __eq__(self, entry):
        return  self._N == entry._N and \
                self._M == entry._M and \
                all( all(e1==e2 for e1,e2 in zip(row1,row2)) for row1,row2 in zip(self, entry) )

    def __add__(self, entry):
        if not is_matrix(entry):
            if isinstance(entry, int) and entry == 0:
                return self
            else:
                raise
        else:
            if self._N != entry._N or self._M != entry._M:
                raise ValueError("Cannot add incompatitible matrices!")
            return Matrix( tuple( tuple( e1+e2 for e1,e2 in zip(row1,row2) ) for row1,row2 in zip(self,entry) ) )

    __radd__ = __add__

    def __mul__(self, entry):
        if not is_matrix(entry):
            return Matrix( tuple( tuple( e*entry for e in row ) for row in self ) )

        if self._M != entry._N:
            raise ValueError("Cannot multiply incompatitible matrices!")

        return Matrix( 
            tuple( tuple( sum( self._rows[i][k]*entry._rows[k][j] for k in range(self._M) ) 
            for j in range(entry._M) )
            for i in range(self._N) ) )

    __rmul__ = __mul__

    def __neg__(self):
        return Matrix( tuple( tuple( -e for e in row ) for row in self ) )
        
    def __div__(self, entry):
        """
        >>> (identity(5) / hilbert(5)) * hilbert(5) == identity(5)
        True
        >>> (identity(6) / hilbert(6)) * hilbert(6) == identity(6)
        True
        >>> (identity(7) / hilbert(7)) * hilbert(7) == identity(7)
        True

        >>> identity(2) / Matrix( [[ 0, 1], [1, 0]] ) == Matrix( [[ 0, 1], [1, 0]] )
        True
        
        """
        if not is_matrix(entry):
            if hasattr(entry, "__rdiv__"):
                return entry.__rdiv__(self)
            else:
                raise ValueError("can't divide by Matrix")

        if entry._N != entry._M:
            raise ValueError("Matrix not invertible!")

        N = entry._N

        M = [ list(row) for row in entry ]
        b = [ list(row) for row in self  ]

        for i in range(N):
# Pivot for float:
#            p = abs(M[i][i])
#            k = i
#
#            for s in range(i, N):
#                if abs(M[s][i]) > p:
#                    k = s
#                    p = abs(M[s][i])

# Pivot for rational:
            for k in range(i, N):
                if M[k][i] != 0:
                    break

            if k != i:
                M[i], M[k] = M[k], M[i]
                b[i], b[k] = b[k], b[i]

            inv = F(1,1)/M[i][i]

            for j in range(N):
                if j == i:
                    continue

                d = M[j][i]*inv
                b[j] = [ t - r*d for t,r in zip(b[j], b[i]) ]
                M[j] = [ t - r*d for t,r in zip(M[j], M[i]) ]

            b[i] = [ e*inv for e in b[i] ]
            M[i] = [ e*inv for e in M[i] ]

        return Matrix( tuple( tuple(row) for row in b ) )
            
def is_matrix( entry ):
    return isinstance(entry, Matrix)

if __name__ == '__main__':
    import doctest
    doctest.testmod()
