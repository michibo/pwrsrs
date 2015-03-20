
from powerseries import PowerSeries as ps
from powerseries import nthpower, addindex
from operator import mul
from fractions import Fraction as F

X = nthpower(1)

Y = addindex(X)
Z = addindex(Y)

def f_binomial( n, k ):
    if k < 0:
        return 0
    if n < 0:
        return f_binomial( -n + k - 1, k ) * (-1)**k

    b = 1
    for i in range(k):
        b *= (n-i)
        b /= (1+i)
    return b

def test_binomial():
    print "BINOMIAL TEST"
    
    A = ps(f=f_binomial, dim=2)
    print A

    B = 1 / (1 - X - X*Y)

    if A == B:
        print "1. TEST PASSED"
    else:
        print "1. TEST FAILED"

    def f_fibonacci(n):
        if n == 0:
            return 0
        elif n == 1:
            return 1
        else:
            return f_fibonacci(n-1) + f_fibonacci(n-2)

    C = ps(f=f_fibonacci)

    A = A.contract().xmul

    if A == C:
        print "2. TEST PASSED"
    else:
        print "2. TEST FAILED"

def test_compose():
    print "COMPOSE TEST"
    k = 5
    A = reduce(mul, [1+X]*k)

    B = 1/ (1-X) - 1

    def f_power( n ):
        return f_binomial(n + k - 1, n)
    C = ps(f=f_power)

    D = A(B)

    if C == D:
        print "1. TEST PASSED"
    else:
        print "1. TEST FAILED"

    
    E = (B+1)**k

    if C == E:
        print "2. TEST PASSED"
    else:
        print "2. TEST FAILED"

def test_exp():
    A = (X.exponential()).logarithm()
    if A == X:
        print "1. TEST PASSED"
    else:
        print "1. TEST FAILED"

    B = X.exponential() * X.exponential()
    C = (2*X).exponential()

    if B == C:
        print "2. TEST PASSED"
    else:
        print "2. TEST FAILED"

def test_pow():

    n = F(1,2)
    def f_pow(k):
        return f_binomial(n,k)

    A = ps(f=f_pow)

    B = (1+X)**n
    if A == B:
        print "1. TEST PASSED"
    else:
        print "1. TEST FAILED"

def test_shuffle():
    binomial = 1/(1-Y*X-X)
    if binomial.shuffle(1) == 1/(1-X*Y-Y):
        print "1. PASSED"
    else:
        print "1. FAILED"

    binomial2 = 1/(1-Z*X-X)

    if binomial2.shuffle(2) == addindex(1/(1-X*Y-Y)):
        print "1. PASSED"
    else:
        print "1. FAILED"

def main():
    test_shuffle()
    test_binomial()
    test_compose()
    test_exp()
    test_pow()

if __name__ == "__main__":
    main()

