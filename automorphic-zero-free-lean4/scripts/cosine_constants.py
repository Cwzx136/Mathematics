"""Outward-rounded constants for the compact cosine test. Requires python-flint >= 0.8."""
from fractions import Fraction as Q
from flint import arb, ctx
ctx.prec = 192

def enclose(q):
    return arb(q.numerator)/q.denominator

def pole(k):
    return k**3 / ((1+k**2)*(k+arb.pi()-k.atan()))

def bracket(p):
    left, right = Q(0), Q(100)
    for _ in range(115):
        mid = (left+right)/2
        v = pole(enclose(mid))
        if v < p:
            left = mid
        elif v > p:
            right = mid
        else:
            raise ArithmeticError('Increase working precision')
    assert pole(enclose(left)) < p < pole(enclose(right))
    return enclose(left).union(enclose(right))

def run(label,p,g):
    k = bracket(enclose(p))
    w = (1+k*k)*enclose(g)
    upper = Q(int(float(w)*1000000)+1,1000000)
    assert w < enclose(upper)
    print(label, 'pole =', p, 'cost =', g)
    print('  k',k,'gain',(1+k*k)**(-1),'reciprocal width',w,'certified ceiling',upper)

run('old sextic convex / Stechkin',Q(462244,1000000),Q(2284863,2000000))
run('quartic square Weyl--Nelson',Q(10521,22436),Q(101085917,110587044))
run('octic Weyl--Nelson',Q(470377,1000000),Q(85398805176211663,94275997200000000))
run('degree twenty rational disk certificate',Q(473580,1000000),Q(219852918901,246450000000))
