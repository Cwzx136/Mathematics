#!/usr/bin/env python3
"""Two-stage elliptic certificate, exact integers and rational arithmetic."""
from collections import Counter
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json
from check_smoothing import certify, root_net, d_j
from certify_tilt import moment

DATA=Path(__file__).resolve().parents[1]/'data'
def read(name): return json.loads((DATA/name).read_text())
def verify_square(rows,degree,expected):
    count=Counter()
    certify(root_net(rows,degree),0,18,count)
    assert sum(count.values())==expected
    assert len(set((ell,j) for ell,j,c in rows))==len(rows)
    assert all(0<=ell<=degree and 0<=j<=degree for ell,j,c in rows)
    assert all(c>0 for ell,j,c in rows if ell*j)
    return count
def budget(rows,target):
    den=sum(c for ell,j,c in rows if (ell,j)==target)
    assert den==10**6
    pole=sum(Q(c,den) for ell,j,c in rows if ell==j==0)
    slope=sum(Q(c,den)*d_j(j) for ell,j,c in rows if ell*j)
    return pole,slope
def upper(z):
    assert 0<=z<=Q(5,6)
    return sum(moment(i)*z**i/factorial(i) for i in range(5))+moment(5)*z**5/100
def lower(z):
    assert z>=0
    return sum(moment(i)*(-z)**i/factorial(i) for i in range(10))

def main():
    settings=read('main-result.json')
    r=Q(settings['elliptic_coefficient']); w=1/r
    d,b,tau=[Q(settings[k]) for k in ('final_d','final_b','square_tau')]
    stage1=read(settings['prior_table']); es=stage1['entries']
    hist1=verify_square(es,stage1['degree'],170)
    assert all((ell,j)==(1,2) for ell,j,c in es if ell*j)
    p,g=budget(es,(1,2))
    assert (p,g)==(Q(325909,500000),Q(139,186))
    prior=tau*(moment(0)-p*upper(tau))/g
    assert prior==Q(46952503706646856803334747,553773220000000000000000000)>d
    assert 1/(2*Q('5.673'))>d
    stage2=read(settings['primary_table']); es=stage2['entries']
    hist2=verify_square(es,stage2['degree'],376)
    assert {(ell,j) for ell,j,c in es if ell*j}=={(1,1),(5,1),(2,2),(8,2)}
    p,g=budget(es,(1,1))
    assert (p,g)==(Q(152703,250000),Q(41475929,93000000))
    surplus=b*(lower(b*(1-d/w))-p*upper(b*d/w))-w*g
    assert surplus>Q(77,100000000)
    print('Square target:',sum(hist1.values()),'terminal rectangles, depth',max(hist1))
    print('Prior lower bound:',prior,'>',d)
    print('Original elliptic target:',sum(hist2.values()),'terminal rectangles, depth',max(hist2))
    print('Final surplus:',surplus,'>',Q(77,100000000))
    print('Certified reciprocal coefficient:',r,'=',float(r))
    # Optional totally real Hilbert-modular corollary, using the sextic table.
    p,g=Q(462242,10**6),Q(2284863,2000000)
    b,d,r=Q(41,25),Q(61,2500),Q(729,100)
    assert d<1/(7*Q('5.840'))
    assert r*b*(lower(b*(1-d*r))-p*upper(b*d*r))-g>Q(1,1000)
    print('Totally real convexity comparison:',r,'times the field degree.')
if __name__=='__main__': main()
