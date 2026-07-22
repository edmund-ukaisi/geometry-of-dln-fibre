#!/usr/bin/env python3
"""Corrected simulator (paper-exact T-indexing). Report min, realized terminal profiles, binding path."""
import copy
from fractions import Fraction
def run(M):
    L=len(M)-1
    def Mrun(S): return min(M[:S])
    def Mval(t):
        v=(M[0]-t[0])*(M[1]-t[0])
        for j in range(2,L+1): v+=(t[j-2]-t[j-1])*(M[j]-t[j-1])
        return v
    def tilde(T): return min(T)
    realized=set(); allexp=[]
    def step(S,J,divs):
        MS=Mrun(S); MS1=M[S] if S<=L else None; capJ=min(MS,MS1)
        if J==capJ:
            if S==L:
                for d in divs:
                    if tilde(d['T'])==0:
                        realized.add((tuple(d['T']),d['M'])); allexp.append(d['M'])
                return
            step(S+1,0,divs); return
        jumps=sorted({tilde(d['T']) for d in divs if J+1<=tilde(d['T'])<=MS-1})
        if not jumps:
            Tn=[(M[k] if k<=S-1 else J) for k in range(1,L+1)]   # t^{(k)}=M^{(k+1)} for k=1..S-1
            Mn=(MS-J)*(MS1-J)
            step(S,J+1,divs+[{'T':Tn,'M':Mn}]); return
        jj=jumps[0]; J1=jj-J
        cand=[d for d in divs if tilde(d['T'])==jj]; ustar=min(cand,key=lambda d:tuple(d['T']))
        d11=copy.deepcopy(divs); u1=next(d for d in d11 if d['T']==ustar['T'] and d['M']==ustar['M'])
        for k in range(S,L+1): u1['T'][k-1]=J
        u1['M']=ustar['M']+J1*(MS1-J); step(S,J,d11)
        d12=copy.deepcopy(divs); Tn=[(ustar['T'][k-1] if k<S else J) for k in range(1,L+1)]
        d12.append({'T':Tn,'M':ustar['M']+J1*(MS1-J)}); step(S,J+1,d12)
    step(1,0,[])
    mn=min(allexp)
    return mn, sorted(realized,key=lambda x:(x[1],x[0])), Mval

for M in [(3,3,4),(3,3,2,2),(2,2,2,2)]:
    mn,realized,Mval=run(M)
    binders=[ (T,Me) for (T,Me) in realized if Me==mn ]
    consistent=all(Me==Mval(T) for (T,Me) in realized)
    print(f"M={M}: min Mexp={mn} rlct={Fraction(mn,2)}  Mexp==Mval(T) for all realized: {consistent}")
    print(f"   realized terminal (T,Mexp): {realized}")
    print(f"   binding (T,Mexp): {binders}\n")
