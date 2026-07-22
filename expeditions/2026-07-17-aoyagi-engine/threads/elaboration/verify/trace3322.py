#!/usr/bin/env python3
"""Print the explicit birth/boost history of the binding divisors for (3,3,2,2) and (3,3,4)."""
import copy
def run(M, want):
    L=len(M)-1
    def Mrun(S): return min(M[:S])
    def Mval(t):
        v=(M[0]-t[0])*(M[1]-t[0])
        for j in range(2,L+1): v+=(t[j-2]-t[j-1])*(M[j]-t[j-1])
        return v
    def tilde(T): return min(T)
    found={}
    def step(S,J,divs):
        MS=Mrun(S); MS1=M[S] if S<=L else None; capJ=min(MS,MS1)
        if J==capJ:
            if S==L:
                for d in divs:
                    if tilde(d['T'])==0 and (tuple(d['T']),d['M']) in want and (tuple(d['T']),d['M']) not in found:
                        found[(tuple(d['T']),d['M'])]=list(d['hist'])
                return
            step(S+1,0,divs); return
        jumps=sorted({tilde(d['T']) for d in divs if J+1<=tilde(d['T'])<=MS-1})
        if not jumps:
            Tn=[(M[k] if k<=S-1 else J) for k in range(1,L+1)]; Mn=(MS-J)*(MS1-J)
            h=[f'(S={S},J={J}) CASE 2: born fresh u_S,{J+1}; block ({MS-J}x{MS1-J}); T={Tn}; Mexp={Mn}; b-tail x u; J->{J+1}']
            step(S,J+1,divs+[{'T':Tn,'M':Mn,'hist':h}]); return
        jj=jumps[0]; J1=jj-J
        cand=[d for d in divs if tilde(d['T'])==jj]; ustar=min(cand,key=lambda d:tuple(d['T']))
        d11=copy.deepcopy(divs); u1=next(d for d in d11 if d['T']==ustar['T'] and d['M']==ustar['M'] and d['hist']==ustar['hist'])
        oT=list(u1['T']); oM=u1['M']
        for k in range(S,L+1): u1['T'][k-1]=J
        u1['M']=ustar['M']+J1*(MS1-J)
        u1['hist']=u1['hist']+[f'(S={S},J={J}) CASE 1(1) BOOST run J1={J1}: reset t^({S}..{L})={J}; T {oT}->{u1["T"]}; Mexp {oM}+{J1}*({MS1}-{J})={u1["M"]}; no J-advance']
        step(S,J,d11)
        d12=copy.deepcopy(divs); Tn=[(ustar['T'][k-1] if k<S else J) for k in range(1,L+1)]; Mn=ustar['M']+J1*(MS1-J)
        h=ustar['hist']+[f'(S={S},J={J}) CASE 1(2) run J1={J1}: new u_S,{J+1} inherits t^(<{S}) from {ustar["T"]}; T={Tn}; Mexp={ustar["M"]}+{J1}*({MS1}-{J})={Mn}; J->{J+1}']
        d12.append({'T':Tn,'M':Mn,'hist':h}); step(S,J+1,d12)
    step(1,0,[])
    return found

print("===== (3,3,4) binding divisor t=(1,0), Mexp=8 =====")
for k,h in run((3,3,4),{((1,0),8)}).items():
    print(f" {k}:")
    for line in h: print(f"   {line}")

print("\n===== (3,3,2,2) binding t=(2,1,0), Mexp=4 (coupled, within-layer descend) =====")
for k,h in run((3,3,2,2),{((2,1,0),4)}).items():
    print(f" {k}:")
    for line in h: print(f"   {line}")

print("\n===== (3,3,2,2) binding t=(3,2,0), Mexp=4 (a CLEAN branch, for contrast) =====")
for k,h in run((3,3,2,2),{((3,2,0),4)}).items():
    print(f" {k}:")
    for line in h: print(f"   {line}")
