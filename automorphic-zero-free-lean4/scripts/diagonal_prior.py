"""Directed interval checks for the diagonal and Young trace tests."""
from fractions import Fraction as Q
from flint import arb,ctx
ctx.prec=144
def val(x):
    x=Q(x)
    return arb(x.numerator)/x.denominator

def moment(m,n=65536):
    # Integrate in theta by a validated Darboux-style enclosure on all cells.
    # Since the integrand for odd or even m is invariant under theta -> pi-theta,
    # only the positive quadrant is needed. Evaluate Chebyshev by the
    # sine quotient except at the origin, where its dimension bound applies.
    total=arb(0)
    for i in range(n):
        t = val(Q(2*i+1,4*n)).union(val(Q(i,2*n))).union(val(Q(i+1,2*n)))*arb.pi()
        sine=t.sin()
        if i: mag=abs(((m+1)*t).sin()/sine)
        else: mag=arb((m+1)/2,(m+1)/2)
        total+=abs(sine)**2*(mag*mag.nonnegative_part().sqrt())
    return 2*total/n

def hb(theta):
    # Increasing pole budget, 1/3 to 1, on the smaller-angle branch.
    return (1-theta/theta.tan())/theta.sin()**2

def bound(P,theta):
    # A chosen theta gives the exact HB gain for P0=hb(theta).
    # If P <= P0, H(0)-P H(-1) >= P0*cos(theta)^2 by positivity of H(-1).
    P0 = hb(theta)
    assert P < P0
    return P0*theta.cos()**2

def check_general():
    # theta is just above the 1/sqrt(2) threshold.
    t=val(Q(13221231,10**7))
    g=bound(1/arb(2).sqrt(),t)
    print('general diagonal gain',g,'rank constant',1/(4*g))
    assert 1/(4*g)<val(Q(583671,100000))

def check_m(m,theta,budget,target):
    I=moment(m)
    boundP=(I**2*4/(3*arb.pi())).root(3)
    assert boundP<val(budget)
    gain=bound(val(budget),val(theta))
    # Convexity is already sufficient for these prior widths.
    degree=m+1
    gamma=val(Q(degree,4))*(1-val(Q(2,3*degree**5-2*degree**4-degree**2)))
    prior=gain/gamma
    print('m',m,'moment',I,'pole',boundP,'budget',budget,'gain',gain,'prior',prior)
    assert prior > val(target)
check_general()
check_m(2,Q(1299692,1000000),Q(6881,10000),Q(66,1000))
check_m(3,Q(1293575,1000000),Q(68308,100000),Q(51,1000))
check_m(5,Q(128855,100000),Q(679,1000),Q(35,1000))
