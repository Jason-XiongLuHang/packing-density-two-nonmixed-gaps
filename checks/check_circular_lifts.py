"""Exact checks of every step of the new circular-lift proof.

Checks arbitrary legal configurations and exhaustive small instances.
These checks supplement, and do not replace, the written proof.
"""
from pathlib import Path
from itertools import combinations
from math import gcd
from random import Random
import json


def egcd(a,b):
    if not b:return a,1,0
    g,x,y=egcd(b,a%b)
    return g,y,x-(a//b)*y


def check(a,b,k,m,selected):
    D=k*a+m*b;n1=D+b;n2=D+a
    M={i*a+j*b for i in range(k+1)for j in range(m+1)if i+j}
    selected=sorted(selected)
    assert all(0<=z<n2 for z in selected)
    assert all(y-x not in M for i,x in enumerate(selected)for y in selected[i+1:])
    B=sum(z<n1 for z in selected);C=len(selected)
    hceil=(B-b+k-1)//k
    assert C<=a-m*hceil,('staircase',a,b,k,m,selected,B,C)
    if C<2:return 0,0
    _,u,v=egcd(a,b);t=m*u-k*v;g=gcd(k,m)
    assert t*a==m-v*D and t*b==-k+u*D
    assert gcd(t,D)==g
    assert len({t*z%D for z in selected})==C
    ordered=sorted(selected,key=lambda z:t*z%D)
    I=J=gap_sum=P=exception=0
    for z,z1 in zip(ordered,ordered[1:]+ordered[:1]):
        ell=t*(z1-z)%D
        assert 0<ell<D
        gap_sum+=ell
        residue=(z1-z)%D
        if residue not in M:
            p=u*(z1-z);q=v*(z1-z)
            height=m*p-k*q
            assert (ell-height)%D==0
            shift=(ell-height)//D
            p+=shift*b;q-=shift*a
            shift=q//m
            p-=shift*k;q-=shift*m
            assert 0<=q<m and p>=k+1
            p-=k;q-=m
            assert p>=1 and q<=-1
        else:
            lo,hi=sorted((z,z1));delta=hi-lo
            assert delta>D and 0<delta-D<a
            assert (delta-D)%b==0
            j=(delta-D)//b
            assert 1<=j<=m and j<a
            assert hi>=n1 and lo<n1
            if z==hi:
                p,q=0,-j;P+=1
                assert z>=n1 and z1<n1 and ell==j*k
            else:
                p,q=b,j-a
                assert p>=1 and q<=-1 and ell==D-j*k
            exception+=1
        assert (a*p+b*q-(z1-z))%D==0
        assert m*p-k*q==ell
        I+=p;J+=q
    assert gap_sum==D and P<=C-B
    assert I>=B and -J>=C
    assert m*I-k*J==D and (a*I+b*J)%D==0
    h=(a*I+b*J)//D
    assert I==b+k*h and J==-a+m*h
    assert B<=b+k*h and C<=a-m*h and h>=hceil
    return C,exception


def exhaustive(a,b,k,m):
    D=k*a+m*b;n2=D+a
    M={i*a+j*b for i in range(k+1)for j in range(m+1)if i+j}
    future=[sum(1<<(x+d)for d in M if x+d<n2)for x in range(n2)]
    count=edges=exceptions=0
    def visit(start,blocked,selected):
        nonlocal count,edges,exceptions
        e,s=check(a,b,k,m,selected);count+=1;edges+=e;exceptions+=s
        for x in range(start,n2):
            if not(blocked>>x)&1:visit(x+1,blocked|future[x],selected+[x])
    visit(0,0,[])
    return count,edges,exceptions


def main():
    totals=[0,0,0];cases=0
    for a in range(2,8):
        for b in range(1,a):
            if gcd(a,b)>1:continue
            for k in range(1,5):
                for m in range(1,5):
                    values=exhaustive(a,b,k,m)
                    totals=[x+y for x,y in zip(totals,values)];cases+=1
        print('exhaustive a',a,'cases',cases,'configurations',totals[0],flush=True)
    rng=Random(2026102810);random_configs=0
    for _ in range(3000):
        a=rng.randrange(2,81);b=rng.randrange(1,a)
        if gcd(a,b)>1:continue
        k=rng.randrange(1,16);m=rng.randrange(1,16)
        D=k*a+m*b;n2=D+a
        M={i*a+j*b for i in range(k+1)for j in range(m+1)if i+j}
        selected=[];candidates=list(range(n2));rng.shuffle(candidates)
        for x in candidates:
            if all(abs(x-y)not in M for y in selected):selected.append(x)
        check(a,b,k,m,selected);random_configs+=1
    report=dict(exhaustive_parameter_cases=cases,exhaustive_configurations=totals[0],
         circular_edges_checked=totals[1],cyclic_forbidden_edges_checked=totals[2],
         random_maximal_configurations=random_configs,all_checks_passed=True,
         caveat='Exact finite checks supplement a general proof; not an independent human review.')
    (Path(__file__).resolve().parent/'circular_lift_checks.json').write_text(json.dumps(report,indent=2))
    print(report,flush=True)


if __name__=='__main__':main()
