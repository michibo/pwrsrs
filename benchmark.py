
from itertools import count
import pwrsrs
from pwrsrs import PowerSeries, X, Y, Z

def comtet():
    N = 10
    def _fac():
        r = 1
        for n in count():
            yield r
            r*= n+1
    
    fac = PowerSeries( _fac )
    print("Factorial numbers: \n", fac.getstr(N))

    F = fac - 1
    I = F / ( 1 + F)

    Finv = pwrsrs.solve( Y - F )[0]
    print("Compositional inverse of the factorial: \n", Finv.getstr(N))

def trees():
    N = 20
    T_unlab = pwrsrs.solve( X - Y*pwrsrs.exp(X) )[0]
    print("Exponential generating function of trees: \n", T_unlab.getstr(N))

    N = 8
    Tu_unlab = pwrsrs.solve( -X + Y*Z + Y*(pwrsrs.exp(X)-1))[0]
    print("bivariate generating function of trees with n nodes and m leaves: \n", Tu_unlab.getstr(N))

def main():
    comtet()
    trees()

if __name__ == '__main__':
    import cProfile
    cProfile.run('main()')
