"""Exact verification of the tilted restricted-amplifier certificate.
Supply a coefficient JSON file, and put check_smoothing.py on PYTHONPATH.
"""
from fractions import Fraction as Q
from math import factorial
from collections import Counter
from pathlib import Path
import json, sys
from check_smoothing import certify,root_net,d_j


def moment(n):
    # Polynomial h(x)=(1-x)^3(199+597x+204x²-560x³-120x⁴+75x⁵+25x⁶)/199.
    return sum(Q(w * c,199*(n+i+j+1))
               for i,w in enumerate([1,-3,3,-1])
               for j,c in enumerate([199,597,204,-560,-120,75,25]))


def exp_poly_integral(x, n):
    return sum(moment(j)*x**j/factorial(j) for j in range(n+1))


def gain(data):
    p = Q(data['entries'][0][2],10**6)
    G = sum(d_j(j)*Q(c,10**6) for l,j,c in data['entries'] if l*j)
    a, b, R = map(Q, (data['a'],data['b'],data['R']))
    x, y = b*(a*R-1), b*a*R
    n = 13
    assert 0 <= y < n+2 and p >= 0
    # The odd Taylor polynomial minorizes exp on the whole real line.
    # The positive upper tail is bounded by its leading term times a geometric series.
    A = b*exp_poly_integral(x,n)
    B = b*(exp_poly_integral(y,n) + moment(n+1)*y**(n+1)/factorial(n+1)/(1-y/(n+2)))
    return A,B,G,R*(A-p*B)-G


def verify(data):
    e=data['entries'];D=data['degree'];m=data['rankCut']
    assert e[0][:2]==[0,0] and all(l<=D and j<=D and min(l,j)>=0 for l,j,_ in e)
    assert len({(l,j) for l,j,_ in e})==len(e)
    assert [1,1,10**6] in e and all(j<=m and c>=0 for l,j,c in e if l*j)
    H=Counter();certify(root_net(e,D),0,data['maxDepth'],H)
    A,B,G,J=gain(data);assert J>0,(J,float(J))
    if 'slackLower' in data: assert J>Q(data['slackLower'])
    print('Rank cutoff',m,'degree',D,'R',data['R'],'b',data['b'],'a',data['a'], 'P',Q(e[0][2],10**6),'G',G)
    print('Dual-chart leaves',dict(sorted(H.items())),'surplus',float(J),'exact',J)

if __name__=='__main__':
    for p in sys.argv[1:]: verify(json.loads(Path(p).read_text()))
