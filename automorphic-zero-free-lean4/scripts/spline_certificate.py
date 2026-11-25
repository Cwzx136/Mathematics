"""Exact positive-definiteness and gain certificate for the degree-twenty cubic spline."""
from fractions import Fraction as F
from math import comb, factorial

# Q(theta) = c[0] + 2 sum_{j>0} c[j] cos(j theta).
c = [1006465526, 987069148, 935748540, 854128173, 753402878, 639792025,
     522713813, 408648335, 303745284, 212579151, 138047603, 81207938,
     41868403, 17252697, 5175321, 0, 0, 0, 926819, 419038, 389327]
N = len(c) - 1
delta = F(1, 10)
P = F(473580, 1000000)
G = F(219852918901, 246450000000)

def bernstein_coefficients():
    """Represent c0 + 2 sum c_j T_j(2s-1) on the unit interval."""
    pol = [c[0]] + [0] * N
    prev, curr = [1], [-1, 2]
    for j in range(1, N+1):
        for i, v in enumerate(curr):
            pol[i] += 2*c[j]*v
        nxt = [0] * (len(curr)+1)
        for i, v in enumerate(curr):
            nxt[i] -= 2*v
            nxt[i+1] += 4*v
        for i, v in enumerate(prev):
            nxt[i] -= v
        prev, curr = curr, nxt
    return [sum(F(pol[j]*comb(i,j), comb(N,j)) for j in range(i+1))
            for i in range(N+1)]

def positive_leaves(coeff, depth=0):
    """Exact de Casteljau subdivision. Positive control coefficients prove positivity."""
    if min(coeff) > 0:
        return 1, depth
    assert depth < 36
    left, right = [coeff[0]], [coeff[-1]]
    while len(coeff) > 1:
        coeff = [(a+b)/2 for a,b in zip(coeff, coeff[1:])]
        left.append(coeff[0])
        right.append(coeff[-1])
    ln, ld = positive_leaves(left, depth+1)
    rn, rd = positive_leaves(right[::-1], depth+1)
    return ln+rn, max(ld,rd)

def truncated_power(m, j):
    """Integral of u^m (u-j)_+^3 on [0,N+2]."""
    R, l = N+2, max(0,j)
    return sum((-j)**(3-i)*comb(3,i)*F(R**(m+i+1)-l**(m+i+1),m+i+1)
               for i in range(4))

def unit_moment(m):
    """Physical variable u=x/delta and the centrally positioned cubic cardinal B-spline."""
    return sum(F(c[abs(j)], 6) * sum((-1)**r*comb(4,r)*truncated_power(m,j+r-2)
                                     for r in range(5)) for j in range(-N,N+1))

mass_at_zero = F(2*c[0]+c[1], 3)
moments = [delta**(m+1)*unit_moment(m)/mass_at_zero for m in range(21)]
R = delta*(N+2)

def gain_lower(W, prior):
    a = prior/W
    assert 0 <= a < 1 and a*R < 22
    damp = sum((a-1)**m * moments[m]/factorial(m) for m in range(20))
    grow = sum(a**m * moments[m]/factorial(m) for m in range(20))
    # For 0 <= x <= R, every successive ratio after order 20 is <= aR/21.
    grow += a**20*moments[20]/factorial(20)/(1-a*R/21)
    return damp-P*grow

if __name__ == '__main__':
    leaves, depth = positive_leaves(bernstein_coefficients())
    gain = gain_lower(F(1), F(0))
    print("Positive Bernstein leaves, maximal depth:", leaves, depth)
    print("Unweighted exact gain lower bound:", gain)
    print("Reciprocal width upper bound:", float(G/gain))
    assert gain > F(14461373, 10**8) and G/gain < F(616871, 10**5)
    for reciprocal in (F(6164,1000), F(61635,10000), F(61633,10000), F(61632,10000), F(6163,1000)):
        trial = 1/reciprocal
        surplus = gain_lower(trial, F(9,10000)) - trial*G
        print("Tilted trial reciprocal and surplus:", str(reciprocal), float(surplus))
