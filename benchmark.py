
from pwrsrs import *

def comtet():
    N = 20
    def _fac():
        r = 1
        for n in count():
            yield r
            r*= n+1
    
    fac = PowerSeries( _fac )
    print("fac: ", fac.getstr(N))

    F = fac - 1
    I = F / ( 1 + F)

    Finv = solve( Y - F )[0]
    print("Finv: ", Finv.getstr(N))

def main():
    comtet()

if __name__ == '__main__':
    import cProfile
    cProfile.run('main()')
