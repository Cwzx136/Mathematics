"""Arb verification of uniform level-11 bounds from fixed alternating comparison shifts."""
from fractions import Fraction as Q
from flint import arb, ctx
from functools import lru_cache

W6={(0,0):462244,(0,2):444674,(0,4):47038,(0,6):1191,(1,1):1000000,(1,3):293292,(2,0):433762,(2,2):343537,(2,6):348,(3,1):179116,(3,3):1183,(4,0):33882,(4,6):31,(6,0):439,(6,2):110}
W6={k:Q(v,10**6) for k,v in W6.items()}

def four_weights(a,b,c,d):
    from collections import defaultdict
    pol=[{0:a},{1:b},{0:c,2:d},{1:b},{0:a}]
    w=defaultdict(int)
    for i,xs in enumerate(pol):
        for k in range(i,len(pol)):
            ell=k-i
            for j,x in xs.items():
                for h,y in pol[k].items():
                    for n in range(abs(j-h),j+h+1,2):
                        w[ell,n]+=(1 if ell==0 else 2)*x*y
    return {ij:Q(q,w[1,1]) for ij,q in w.items()}

W4=four_weights(7,20,23,15)
def ball(q):
    q=Q(q)
    return arb(q.numerator)/q.denominator

@lru_cache(None)
def dig(k,mu,plus):
    u=arb('0.02') if plus else arb(0)
    return ((1+k+mu+u)/2).digamma()

def costs(W,m,scalar,base_T=262144):
    P=ball(W[0,0]);Delta=(1-P.sqrt())**2
    N=2*m+1
    w=Q(N,2*N+1);c=1-w
    alpha=[Q((-1)**k) for k in range(N)]+[-w]
    shifts=[(ell,j,v) for (ell,j),v in W.items() if ell and (j or not scalar)]
    g=sum(Q(j+1,2)*v for ell,j,v in shifts)
    h=sum(Q(j,2)*v for (ell,j),v in W.items())
    Z=sum(v for (ell,j),v in W.items() if ell and not j)
    static=P*(ball(c)/N-ball(w)/(N+1+arb('.02')))
    for (ell,j),v in W.items():
        if ell:continue
        mus=[(j//2)%2]+[a for k in range(1,j//2+1) for a in (k,k+1)]
        for mu in mus:
            static+=ball(v)/2*(sum(ball(ak)*dig(k,mu,ak>0) for k,ak in enumerate(alpha))-ball(c)*arb.pi().log())
    static+=ball(c*h)*arb(11).log()
    static+=sum(ball(c*Q(j+1,2)*v)*(arb(ell)/(2*arb.pi())).log() for ell,j,v in shifts)
    H=arb(base_T)
    # sum(abs(alpha)) < N+1; all archimedean shifts are in [0,4].
    E=ball(g)*(N+1)*(2/H+(arb('5.02')+N)**2/(2*H**2))
    if not scalar:
        E+=ball(Z)*(N+1)/H**2
    return P,Delta,ball(c*g),static,E,ball(Z)

def scalar_correction():
    """Elementary Chebyshev bound for all n, and the needed zeta bound at 2."""
    limit=1000
    prime=[True]*(limit+1)
    prime[0]=prime[1]=False
    for integer in range(2,limit+1):
        if prime[integer]:
            for multiple in range(integer*integer,limit+1,integer):
                prime[multiple]=False
    von_mangoldt=[arb(0) for _ in range(limit+1)]
    for integer in range(2,limit+1):
        if prime[integer]:
            n=integer
            while n<=limit:
                von_mangoldt[n]=arb(integer).log()
                n*=integer
    first=arb(0); second=arb(0)
    for n in range(1,limit+1):
        first+=von_mangoldt[n]/n
        second+=von_mangoldt[n]/n**2
        assert first < arb(n).log()+arb('.41')
    assert 2*arb(2).log()-1+(2*arb(limit).log()+1+arb(2).log())/limit < arb('.41')
    assert second+(arb(limit).log()+1)/limit < arb('.58')
    Lmin=arb(13)
    X=Lmin**2/4
    extra=(-2*arb(2).log()+2+arb('.41')+3*(1+(-arb(2)).exp())/2
           +(1+(-arb(4)).exp())/(2*X)+1/(2*arb(262144)**2)+arb('.58'))
    assert extra<ball(Q(10,3))
    print('Perron constant:',extra,'< 10/3')
    return ball(Q(10,3))


def main():
    ctx.prec=192
    bonus=scalar_correction()
    assert W4[0,0] == Q(413,900) and W6[0,0] == Q(115561,250000)
    assert W4[1,1] == 1 and W6[1,1] == 1
    assert sum(Q(j+1,2)*v for (ell,j),v in W4.items() if ell) == Q(9161,3600)
    assert sum(Q(j+1,2)*v for (ell,j),v in W6.items() if ell and j) == Q(2284863,10**6)
    assert sum(v for (ell,j),v in W6.items() if ell and not j) == Q(468083,10**6)
    lower=arb(262144).log()
    data4=costs(W4,160,False)
    data6=costs(W6,256,True)
    P4,delta4,s4,C4,E4,_=data4
    P6,delta6,s6,C6,E6,Z=data6
    upper4=arb('-.77425')
    upper6=arb('-.638')
    assert C4+E4<upper4 and C6+E6<upper6
    assert (s4-ball(Q(322,643)*Q(9161,3600))).contains(0)
    def B4(t):
        return s4*t+upper4
    def B6(t):
        return s6*t+upper6+Z*(2*(t+arb(6).log()).log()+bonus)
    assert (P4.sqrt()-P4)/B4(lower)<arb('.02')
    assert (P6.sqrt()-P6)/B6(lower)<arb('.02')
    assert upper6 + Z*(2*(lower+arb(6).log()).log()+bonus-2)>0
    assert s4/delta4 < arb('12.246')
    print('Quartic static residual, arch/pole error:',C4,E4)
    print('Sixth-degree static residual, arch error:',C6,E6)
    for f,delta,label in [(B4,delta4,'quartic'),(B6,delta6,'sixth-degree')]:
        ratio=f(arb(48))/(48*delta)
        print(label,'split-point denominator:',ratio)
        assert ratio < arb('12.091')
    for t,f,delta,limit in [(arb(524288).log(),B4,delta4,'11.682'),
                            (arb(200),B6,delta6,'11.447'),
                            (arb(1000),B6,delta6,'11.232'),
                            (arb(10000),B6,delta6,'11.169')]:
        ratio=f(t)/(t*delta)
        assert ratio < arb(limit)
        print('log-height',t,'reciprocal width / log-height',ratio,'<',limit)


if __name__=='__main__':
    main()
