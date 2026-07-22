#!/usr/bin/env python3
"""Full branching-tree simulator of Aoyagi's (S,J) fold recursion.
Follows the paper's rules (pp.15-22) literally; collects terminal divisors (tilde_t=0) at every leaf.
Validates: set of emitted exponents = {Mval(t)} over profile lattice; min = known minAdm.
This DECORRELATES the hand trace: if the min matches, the rule-reading is validated end to end.
"""
import sys, copy
from functools import lru_cache
from fractions import Fraction

def run(M):
    L = len(M)-1                      # number of matrices C^{(1..L)}; widths M^{(1..L+1)}=M[0..L]
    def Mrun(S): return min(M[:S])    # M(S)=min{M^{(s)}:1<=s<=S}, S>=1
    def Mval(t):
        v=(M[0]-t[0])*(M[1]-t[0])
        for j in range(2,L+1): v+=(t[j-2]-t[j-1])*(M[j]-t[j-1])
        return v

    leaves_expos=[]                   # list of (frozenset of terminal divisor exponents) per leaf
    all_terms=set()                   # union of all (T,Mexp) terminal divisors seen

    def tilde(T): return min(T)

    def step(S,J,divs):
        # divs: list of dicts {'T':list,'M':int}
        MS=Mrun(S); MS1=M[S] if S<=L else None
        capJ=min(MS,MS1)              # M(S+1)=min(M(S),M^{S+1})
        if J==capJ:                   # layer S done
            if S==L:                  # WHOLE recursion done -> leaf
                terms=[d for d in divs if tilde(d['T'])==0]
                leaves_expos.append(frozenset(d['M'] for d in terms))
                for d in terms: all_terms.add((tuple(d['T']),d['M']))
                return
            else:
                step(S+1,0,divs); return
        # find jumps in [J+1, MS-1]
        jumps=sorted({tilde(d['T']) for d in divs if J+1<=tilde(d['T'])<=MS-1})
        if not jumps:                 # CASE 2 : run to MS
            J1=MS-J
            Tn=[M[i+1] if i< S-1 else J for i in range(L)]   # i<S-1 (0-based i<S-1 <=> layer i+1<S) => t^{(i+1)}=M^{(i+2)}
            # careful indexing: t^{(k)} for k=1..S-1 -> M^{(k+1)}; for k=S..L -> J
            Tn=[ (M[k] if (k+1)<S else J) for k in range(1,L+1)]  # k=layer 1..L ; M^{(k+1)}=M[k]
            Mn=(MS-J)*(MS1-J)
            nd=divs+[{'T':Tn,'M':Mn}]
            step(S,J+1,nd); return
        else:                         # CASE 1 : partial run
            jj=jumps[0]; J1=jj-J
            cand=[d for d in divs if tilde(d['T'])==jj]
            ustar=min(cand,key=lambda d:tuple(d['T']))    # T-minimal
            # chart 1(1): boost u* in place, reset t^{S..L}=J, no J advance, re-eval
            d11=copy.deepcopy(divs)
            u1=next(d for d in d11 if d['T']==ustar['T'] and d['M']==ustar['M'])
            for k in range(S,L+1): u1['T'][k-1]=J          # t^{(S..L)} = J
            u1['M']=ustar['M']+J1*(MS1-J)
            step(S,J,d11)
            # chart 1(2): new divisor inherits t^{<S} from u*, t^{S..L}=J ; advance J
            d12=copy.deepcopy(divs)
            Tn=[ (ustar['T'][k-1] if k<S else J) for k in range(1,L+1)]
            Mn=ustar['M']+J1*(MS1-J)
            d12.append({'T':Tn,'M':Mn})
            step(S,J+1,d12); return

    step(1,0,[])
    # profile lattice + Mval
    @lru_cache(maxsize=None)
    def minAdm(MM):
        MM=tuple(int(x) for x in MM)
        if len(MM)==1: return 0
        if len(MM)==2: return MM[0]*MM[1]
        return min((MM[0]-tt)*(MM[1]-tt)+minAdm((tt,)+MM[2:]) for tt in range(min(MM[0],MM[1])+1))
    # enumerate profiles t1>=..>=tL=0
    profs=[]
    def gen(pre,lo,hi,depth):
        if depth==L:
            if pre[-1]==0: profs.append(tuple(pre))
            return
        for v in range(lo,hi+1): gen(pre+[v],0,v,depth+1)
    for t1 in range(0,min(M[0],M[1])+1): gen([t1],0,t1,1)
    prof_vals=sorted({Mval(t) for t in profs})
    emitted=sorted({e for L_ in leaves_expos for e in L_})
    per_leaf_min=sorted({min(L_) for L_ in leaves_expos if L_})
    overall_min=min(e for L_ in leaves_expos for e in L_)
    return dict(L=L, minAdm=minAdm(M), overall_min=overall_min,
                emitted=emitted, prof_vals=prof_vals,
                n_leaves=len(leaves_expos),
                terms=sorted(all_terms, key=lambda x:(x[1],x[0])),
                binding=[t for t in profs if Mval(t)==overall_min])

for M in [(3,3,4),(3,3,2,2),(2,2,2),(2,2,2,2)]:
    r=run(M)
    print(f"M={M} L={r['L']} : minAdm={r['minAdm']}  sim overall_min={r['overall_min']}  "
          f"rlct={Fraction(r['overall_min'],2)}  MATCH={r['minAdm']==r['overall_min']}")
    print(f"    n_leaves={r['n_leaves']}  emitted exps (tilde t=0) = {r['emitted']}")
    print(f"    Mval over profile lattice        = {r['prof_vals']}")
    print(f"    binding profile(s) t = {r['binding']}")
    print(f"    terminal (T,Mexp) census: {r['terms']}")
    print()
