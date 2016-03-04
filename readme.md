
pwrsrs - Multivariate Power Series for Python, seriously?
=========================================================

This is a Python implementation of multivariate power series arithmetic. 

It is based on Peter A. Donis Python implementation powerseries, which 
itself is based on a paper by Doug McIlroy 'Squinting at Power Series', 
http://doc.cat-v.org/bell_labs/squinting_at_power_series/squint.pdf. 
See also his paper 'Music of Streams', http://www.cs.dartmouth.edu/~doug/music.ps.gz. 
Doug McIlroy also published a Haskell implementation under the name 
of, 'Power serious: power series in ten one-liners', of the basic power 
series operations: http://www.cs.dartmouth.edu/~doug/powser.html

I liked the highly recursive and functional approach, but missed 
support for multivariate power series in both programs. So, I forked 
Peter A. Donis project and added support for multivariate series. 

Moreover, I implemented functions to solve arbitrary systems of equations 
using power series. 

There is not much left of the original code by Peter, but the general 
functional/generator approach is still the same.

Prerequisites
=============

You need Python 2 or 3 to run *pwrsrs*. 

How to use it
=============

    import pwrsrs
    from pwrsrs import X, Y, Z

The symbols X, Y, Z can be imported to make power series expressions as 
readable as possible.

    # prints the first 5 powers of 2
    geometric = 1/(1-2*X)
    print("Powers of 2\n", geometric)

Multivariate power series are stored as power series of power series. 
The output is in matrix form.

    # We can get the binomial coefficients
    # by using their generating function:
    pascal = 1/(1-X-X*Y)

    # This expands up to order X^10 Y^10
    print("Pascal triangle: \n", pascal.getstr(10))

Pwrsrs' main feature is that it can solve arbitrary equation systems 
in power series. 

    # The exponential generating function T(x) of rooted 
    # trees fulfills T(x) = x e^(T(x))
    # we can solve this using pwrsrs:
    trees = solve( X - Y*pwrsrs.exp(X) )[0]

    print("E.g.f. of rooted trees: \n", trees.getstr(10))

Test
====

You can make a test run of pwrsrs by invoking 

    python pwrsrs.py

or

    python benchmark.py


This software is distributed under the MIT license

Copyright (c) for portions of project *pwrsrs* are held by 

Peter A. Donis, 2011 

as part of project *powerseries*. 

All other copyright for project *pwrsrs* are held by 

Michael Borinsky, 2016.


Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
