#!/usr/bin/env python3
"""Check every rectangle of the degree-twenty positivity certificate using integers."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import comb
import json
from pathlib import Path

def chebyshev(n, second_kind):
    a, b = [1], [0, 2 if second_kind else 1]
    if n == 0:
        return a
    for degree in range(2, n + 1):
        c = [0] + [2*t for t in b]
        for k, t in enumerate(a):
            c[k] -= t
        a, b = b, c
    return b

@lru_cache(None)
def homogeneous(n, k, second_kind):
    """Coefficients of (a+b)^n C_k((a-b)/(a+b)), increasing in a."""
    row = [0]*(n+1)
    for d, coeff in enumerate(chebyshev(k, second_kind)):
        for i in range(d+1):
            for j in range(n-d+1):
                row[i+j] += coeff*comb(d,i)*(-1)**(d-i)*comb(n-d,j)
    return row

def check(path):
    cert=json.loads(path.read_text())
    tab=cert['entries']
    den=cert['den']
    n=max(max(l,j) for l,j,c in tab)
    root=[[0]*(n+1) for _ in range(n+1)]
    p=Q(0); budget=Q(0)
    for l,j,c in tab:
        if l==j==0: p=Q(c,den)
        if l*j:
            assert c>0
            k=j+1
            gamma=Q(1,3) if j==1 else Q(k,4)*(1-Q(2,3*k**5-2*k**4-k*k))
            budget+=Q(c,den)*gamma
        u=homogeneous(n,j,True); t=homogeneous(n,l,False)
        for i,x in enumerate(u):
            for k,y in enumerate(t):
                root[i][k]+=c*x*y
    assert sum(c for l,j,c in tab if (l,j)==(1,1))==den
    assert len(set((l,j) for l,j,c in tab))==len(tab)
    left=[[(i,2**(n-k)*comb(n-i,n-k)) for i in range(k+1)] for k in range(n+1)]
    right=[[(i,2**k*comb(i,k)) for i in range(k,n+1)] for k in range(n+1)]
    histogram=Counter()
    def recurse(net, depth):
        if all(t>=0 for row in net for t in row):
            histogram[depth]+=1
            return
        assert depth<cert['depth'], f'Unresolved rectangle at depth {depth}'
        # Transpose after each bisection so the next one uses the other coordinate.
        for rule in (left,right):
            recurse([tuple(sum(row[i]*v for i,v in coeffs) for row in net) for coeffs in rule],depth+1)
    # Each row advances the first variable at the initial step.
    recurse(list(zip(*root)),0)
    assert dict(histogram)=={int(k):v for k,v in cert['leaves'].items()},histogram
    gain=Q(13,8)*(Q(95181399549361514143,344366740312739020800)-Q(315,796)*p)
    assert (budget,gain,budget/gain)==tuple(Q(cert[k]) for k in ('slope','gain','ratio'))
    assert budget/gain < Q(616918,100000)
    print(f'PASS: {len(tab)} signed coefficients, {sum(histogram.values())} terminal rectangles, maximum depth {max(histogram)}.')
    print('P =',p,' G =',budget,' J0 =',gain,' G/J0 =',budget/gain)

if __name__=='__main__':
    check(Path(__file__).resolve().parents[1]/'data'/'elliptic-degree20.json')
