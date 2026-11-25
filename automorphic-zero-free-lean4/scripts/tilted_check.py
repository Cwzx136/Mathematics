"""Outward-rounded scalar checks for the prior-strip tilt (python-flint >= 0.8).

Analytic hypotheses, and the meaning of the tested surplus, are given in
tilted-boundary-note.tex. The integrand in the Gauss--Legendre evaluation is
entire, and every parameter outside the integral is an explicit rational.
"""
from fractions import Fraction as Q
from flint import arb, acb, ctx

ctx.prec = 160

def enclose(q):
    return arb(q.numerator) / q.denominator

def test(name, poles, slope, tilt, freq, supp, reciprocal, prior):
    p, G, a, k, S, W = map(enclose, [poles,slope,tilt,freq,supp,1/reciprocal])
    assert 0 < k*S < arb.pi()
    assert tilt <= prior
    c = (k*S).cos()

    def B(t):
        return ((2*S-t)*(c*c+(k*t).cos()/2) + (k*(2*S-t)).sin()/(2*k)
                - (2*c/k)*((k*S).sin()+(k*(S-t)).sin()))

    mass = B(arb(0))
    assert mass > 0

    def H(z):
        integrand = lambda x, _: (-2*S*x*z).exp()*B(2*S*x)
        val = acb.integral(integrand, 0, 1, rel_tol=1e-25, abs_tol=1e-25)
        return (2*S/mass*val).real

    v = a/W
    surplus = H(1-v) - p*H(-v) - W*G
    assert surplus > 0
    print(name, 'P',poles,'G',slope,'a',tilt,'k',freq,'S',supp,
          'denominator',reciprocal,'signed surplus',surplus)

test('degree twenty',Q(473580,1000000),Q(219852918901,246450000000),
     Q(26,1000),Q(235698,100000),Q(78646,100000),Q(6005086,1000000),1/(6*Q(6348,1000)))
test('quartic square',Q(10521,22436),Q(101085917,110587044),
     Q(3937,100000),Q(228308,100000),Q(78777,100000),Q(5943825,1000000),1/(4*Q(6348,1000)))

test('quartic square with diagonal prior',Q(10521,22436),Q(101085917,110587044),
     Q(4283,100000),Q(227057,100000),Q(78539,100000),Q(5923066,1000000),Q(4283,100000))
test('quartic square with Young prior',Q(10521,22436),Q(101085917,110587044),
     Q(51,1000),Q(223970,100000),Q(77992,100000),Q(5874730,1000000),Q(51,1000))
test('degree twenty with Young prior',Q(473580,1000000),Q(219852918901,246450000000),
     Q(35,1000),Q(232689,100000),Q(78016,100000),Q(5950712,1000000),Q(35,1000))
