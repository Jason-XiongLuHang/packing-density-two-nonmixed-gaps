"""Check the local lift lemma by a second, direct enumeration algorithm."""
from math import gcd
from pathlib import Path
import json


def egcd(a,b):
    if not b:return a,1,0
    g,x,y=egcd(b,a%b)
    return g,y,x-(a//b)*y


def main():
    parameters=pairs=normal=exceptional=0
    for a in range(2,11):
        for b in range(1,a):
            if gcd(a,b)>1:continue
            for k in range(1,5):
                for m in range(1,5):
                    D=k*a+m*b;n1=D+b;n2=D+a
                    _,u,v=egcd(a,b);t=m*u-k*v
                    M={i*a+j*b for i in range(k+1)for j in range(m+1)if i+j}
                    for low in range(n2):
                        for high in range(low+1,n2):
                            if high-low in M:continue
                            assert (t*(high-low))%D!=0
                            for z,z1 in ((low,high),(high,low)):
                                ell=t*(z1-z)%D
                                # Enumerate a bounded set of possible negative q coordinates.
                                # This does not use the proof's Bezout-normalization construction.
                                found=False
                                for j in range(1,m+1):
                                    rem=ell-k*j
                                    if rem<=0 or rem%m:continue
                                    p=rem//m
                                    if (a*p-b*j-(z1-z))%D==0:
                                        found=True;normal+=1;break
                                if not found:
                                    assert z>=n1 and z1<n1
                                    diff=z-z1-D
                                    assert diff>0 and diff%b==0
                                    j=diff//b
                                    assert 1<=j<=m and j*b<a and ell==j*k
                                    exceptional+=1
                                pairs+=1
                    parameters+=1
        print('pair check a',a,'parameter cases',parameters,'ordered pairs',pairs,flush=True)
    report=dict(parameter_cases=parameters,ordered_legal_pairs=pairs,
                direct_normal_lifts=normal,exceptional_lifts=exceptional,
                all_checks_passed=True,method='Direct enumeration of q=-1,...,-m; separate from the constructive checker')
    (Path(__file__).resolve().parent/'pair_lift_checks.json').write_text(json.dumps(report,indent=2))
    print(report,flush=True)


if __name__=='__main__':main()
