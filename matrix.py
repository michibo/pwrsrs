
def gauss(a, b):
    a = [ r[:] for r in a ]
    b = b[:] 
    n = len(a)
    p = len(b[0])
    for i in range(n - 1):
        for j in range(i, n):
            if a[j][i] != 0:
                k = j
                break
        else:
            raise ValueError("Equation System has no (unique) solution")

        if k != i:
            a[i], a[k] = a[k], a[i]
            b[i], b[k] = b[k], b[i]
 
        for j in range(i + 1, n):
            t = a[j][i]/a[i][i]
            for k in range(i + 1, n):
                a[j][k] -= t*a[i][k]
            for k in range(p):
                b[j][k] -= t*b[i][k]
 
    for i in range(n - 1, -1, -1):
        for j in range(i + 1, n):
            t = a[i][j]
            for k in range(p):
                b[i][k] -= t*b[j][k]
        t = 1/a[i][i]
        for j in range(p):
            b[i][j] *= t
    return b
 
def zeromat(p, q):
    return [[0]*q for i in range(p)]
 
def matmul(a, b):
    n, p = len(a), 
    p1 = len(b)
    if len(b) != len(a[0]):
        raise ValueError("Incompatible dimensions")

    return [ sum(em * eb for em,eb in zip(r, b)) for r in a ]
 
 
def mapmat(f, a):
    return [list(map(f, v)) for v in a]
