
from powerseries import PowerSeries as ps
from powerseries import X,Y,Z,I
from operator import mul
from math import factorial
from fractions import Fraction as F
import pdb

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

    A = A(X)

    if A == C.tail:
        print "2. TEST PASSED"
    else:
        print "2. TEST FAILED"

def test_compose():
    print "COMPOSE TEST"
    for k in range(1,20):
        A = (reduce(mul, [1+X]*k)).tensor(I)

        B = 1/ (1-X) - 1

        def f_power( n ):
            return f_binomial(n + k - 1, n)
        C = ps(f=f_power)

        D = A(B)

        if C == D:
            print k, "1. TEST PASSED"
        else:
            print k, "1. TEST FAILED"

        
        E = (B+1)**k

        if C == E:
            print k, "2. TEST PASSED"
        else:
            print k, "2. TEST FAILED"
def test_exp():
    print "EXP Test"

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
    print "POW TEST"

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
    print "SHUFFLE TEST"

    binomial = 1/(1-Y*X-X)
    if binomial.shuffle(1) == 1/(1-X*Y-Y):
        print "1. PASSED"
    else:
        print "1. FAILED"

    binomial2 = 1/(1-Z*X-X)

    if binomial2.shuffle(2) == I.tensor(1/(1-X*Y-Y)):
        print "1. PASSED"
    else:
        print "1. FAILED"

def test_inverse():
    print "INVERSE TEST"

    if (X.exponential()-1) == (1+X).logarithm().inverse():
        print "1. PASSED"
    else:
        print "1. FAILED"

    if (X.exponential()-1-Y) == (1+X+Y).logarithm().inverse():
        print "2. PASSED"
    else:
        print "2. FAILED"


def test_solve():
    print "SOLVE TEST"
    
    A = X + Y.exponential()-1 + Z
    T = Y * X.exponential()
    R = T.solve()

    def f_caylay(n):
        if n == 0:
            return 0
        return F((n)**(n-1), factorial(n))

    if R == ps(f=f_caylay):
        print "1. TEST PASSED"
    else:
        print "1. TEST FAILED"


def main():
    test_shuffle()
    test_inverse()
    test_solve()
    test_binomial()
    test_compose()
    test_exp()
    test_pow()

if __name__ == "__main__":
    main()

