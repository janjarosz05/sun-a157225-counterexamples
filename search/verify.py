# Independent check: m is NOT p + 2^x + 7*2^y with p prime, p = 5 mod 6, x,y >= 1.
import sys, json
from sympy import isprime, factorint
def cells(m,K=7):
    out=[]
    x=1
    while 2**x < m:
        y=1
        while 2**x + K*2**y < m:
            out.append((x,y,m-2**x-K*2**y)); y+=1
        x+=1
    return out
def analyse(m):
    cs=cells(m); rows=[]; reps=[]
    for x,y,r in cs:
        if r%6!=5: rows.append((x,y,r,'mod6',r%6)); continue
        if isprime(r): reps.append((x,y,r)); continue
        d=min(factorint(r)) if r>1 else 1
        rows.append((x,y,r,'div',d))
    return cs,rows,reps
if __name__=="__main__":
    res={}
    for m in [1433987797,45483661477,85305551767,367084269651,1572650032347]:
        cs,rows,reps=analyse(m)
        nm=sum(1 for r in rows if r[3]=='mod6'); nd=[r for r in rows if r[3]=='div']
        divs=sorted(set(r[4] for r in nd))
        print(m,'n=',(m+1)//2,'m%6=',m%6,'cells',len(cs),'mod6-killed',nm,'composite',len(nd),'reps',len(reps),'ndiv',len(divs),'maxdiv',max(divs))
        res[m]=dict(n=(m+1)//2,cells=len(cs),mod6=nm,comp=len(nd),reps=len(reps),divs=divs,rows=[(x,y,r,d) for x,y,r,t,d in nd])
    json.dump(res,open('cert.json','w'))
    # sanity: small exceptions; all odd m in (20, 2*10^5) other than 25,31,1983 representable
    bad=[m for m in range(1,200001,2) if not analyse(m)[2]]
    print('zeros below 2e5:',bad)
