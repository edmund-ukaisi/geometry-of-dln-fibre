import itertools, math
from fractions import Fraction as F

# ---- LR engine (exactly as in CThetaValue/CThetaDropM), on a MONOTONE (ascending) M : list of len N+1 ----
def qipA(M, l):
    # A_l = sum_{i=0}^l M_i - l * M_l   (clamped index inert for l<=N)
    N = len(M)-1
    s = sum(M[i] for i in range(min(l,N)+1))
    return s - l*M[min(l,N)]
def qipM_(M):
    N = len(M)-1
    # greatest l in 0..N with A_l >= 0
    best = 0
    for l in range(0, N+1):
        if qipA(M,l) >= 0:
            best = l
    return best
def qipS_(M):
    m = qipM_(M); N=len(M)-1
    return sum(M[min(i,N)] for i in range(m+1))
def qipRound_(M):
    m = qipM_(M); S = qipS_(M)
    # (2S+m)//(2m)  Int (floor for nonneg)
    return (2*S+m)//(2*m)
def qipDelta_(M):
    m=qipM_(M); S=qipS_(M); a=qipRound_(M)
    return S - m*a
def cValue_(M):
    m=qipM_(M); S=qipS_(M); a=qipRound_(M); d=qipDelta_(M); N=len(M)-1
    d0=M[0]
    pref = sum((M[min(i,N)]-d0)**2 for i in range(1,m+1))
    num = d0**2 - pref + m*(a-d0)**2 + 2*(a-d0)*d + abs(d)
    assert num % 2 == 0, ("cValue num odd", M, num)
    return num//2

# ---- file's reading of Aoyagi core: ell=qipM, ceiling M, a, displayed core ----
def file_core(M):
    ell=qipM_(M); S=qipS_(M); N=len(M)-1
    # activeWidth i = M[min(i,N)], active i in 0..ell
    aw=[M[min(i,N)] for i in range(ell+1)]
    ceilM = (S + ell - 1)//ell           # ceilingM
    a = S - (ceilM-1)*ell                 # residueA
    pairsum = sum(aw[i]*aw[j] for i in range(ell+1) for j in range(i+1, ell+1))
    core = F(a*(ell-a),4*ell) - F(ell*(ell-1),4)*F(S,ell)**2 + F(1,2)*pairsum
    return 2*core   # 2*lambdaCore, should be cValue if sorry true

# ---- Aoyagi's OWN selection (Definition 3): active set = ell+1 SMALLEST, conditions (ii),(iii) ----
def aoyagi_core(M):
    # M sorted ascending. Search ell in 1..N for valid active-set size.
    N=len(M)-1
    cands=[]
    for ell in range(1, N+1):
        T = sum(M[k] for k in range(ell+1))    # sum of ell+1 smallest
        Mell = M[ell]
        cond_ii  = T > ell*Mell                                  # active binding
        if ell < N:
            cond_iii = T <= (ell-1)*M[ell+1]                     # inactive binding
            cond_gap = M[ell] < M[ell+1]                         # strict separation (i)
        else:
            cond_iii = True; cond_gap = True
        if cond_ii and cond_iii and cond_gap:
            cands.append(ell)
    if len(cands)!=1:
        return ('AMBIG', cands)   # no unique Aoyagi ell
    ell=cands[0]
    T = sum(M[k] for k in range(ell+1))
    aw=[M[k] for k in range(ell+1)]
    ceilM=(T+ell-1)//ell
    a = T-(ceilM-1)*ell
    pairsum=sum(aw[i]*aw[j] for i in range(ell+1) for j in range(i+1,ell+1))
    core=F(a*(ell-a),4*ell) - F(ell*(ell-1),4)*F(T,ell)**2 + F(1,2)*pairsum
    return 2*core

# ---- enumerate monotone M of small length and entries ----
mismatch_file=[]; mismatch_aoyagi=[]; ambig=[]; checked=0
for N1 in range(2, 6):      # length N+1 = 2..5  (N=1..4)
    for tup in itertools.combinations_with_replacement(range(0,7), N1):
        M=list(tup)         # already ascending
        if M[0] < 1:        # need d0>=1 (qip hypotheses); skip degenerate
            continue
        if qipM_(M) < 1:
            continue
        checked+=1
        cv = cValue_(M)
        fc = file_core(M)
        if F(cv) != fc:
            mismatch_file.append((M, cv, fc))
        ac = aoyagi_core(M)
        if isinstance(ac, tuple):
            ambig.append((M, ac))
        elif F(cv)!=ac:
            mismatch_aoyagi.append((M, cv, ac))

print(f"checked {checked} monotone vectors (len 2..5, entries 0..6, d0>=1)")
print(f"\n[A] file's 2*lambdaCore (ell=qipM) vs cValue  -- tests the sorry two_lambdaCore_eq_cValue")
print(f"    mismatches: {len(mismatch_file)}")
for x in mismatch_file[:12]: print("      ", x)
print(f"\n[B] Aoyagi's OWN ell (Def 3) 2*core vs cValue  -- tests qipM == Aoyagi ell  (fidelity)")
print(f"    mismatches: {len(mismatch_aoyagi)}    ambiguous(no unique Aoyagi ell): {len(ambig)}")
for x in mismatch_aoyagi[:12]: print("      MISMATCH", x)
for x in ambig[:12]: print("      AMBIG", x)

print("\n\n==================  CORRECTED Aoyagi inactive condition: T <= ell*M (not (ell-1)*M) ==================")
def aoyagi_ell_corrected(M):
    """Aoyagi ell with inactive condition T <= ell*M^(s); active T > ell*M^(s).
       Sorted ascending; ties handled by prefix (ignore strict-gap (i))."""
    N=len(M)-1
    cands=[]
    for ell in range(1, N+1):
        T=sum(M[k] for k in range(ell+1))
        active_ok = (T > ell*M[ell])                 # binding at largest active
        inactive_ok = True if ell==N else (T <= ell*M[ell+1])  # binding at smallest inactive
        if active_ok and inactive_ok:
            cands.append(ell)
    return cands

# Theorem-1 explicit case rule (3-layer), for cross-validation on len-3 M:
def thm1_ell(M):
    assert len(M)==3
    M1,M2,M3=M  # note: NOT sorted; Aoyagi's M^(1),M^(2),M^(3)
    tot=M1+M2+M3
    if all(2*x < tot for x in (M1,M2,M3)): return 2,{1,2,3}
    if M3 >= M1+M2: return 1,{1,2}
    if M2 >= M1+M3: return 1,{1,3}
    if M1 >= M2+M3: return 1,{2,3}
    return None,None

import itertools
from fractions import Fraction as F
neq_qipM=[]; empty=[]; multi=[]; neq_thm1=[]; checked=0
for N1 in range(2,7):
    for tup in itertools.combinations_with_replacement(range(0,8), N1):
        M=list(tup)
        if M[0]<1: continue
        if qipM_(M)<1: continue
        checked+=1
        cands=aoyagi_ell_corrected(M)
        m=qipM_(M)
        if len(cands)==0: empty.append(M)
        elif len(cands)>1: multi.append((M,cands))
        elif cands[0]!=m: neq_qipM.append((M,cands[0],m))
        # cross-check Thm1 on len-3 (compare on SORTED M, since the engine sorts)
        if N1==3:
            le,_=thm1_ell(sorted(M))
            if le is not None and len(cands)==1 and cands[0]!=le:
                neq_thm1.append((sorted(M),cands[0],le))
print(f"checked {checked}")
print(f"corrected-Aoyagi ell: empty={len(empty)}  multi={len(multi)}  != qipM={len(neq_qipM)}")
for x in empty[:8]: print("   EMPTY",x)
for x in multi[:8]: print("   MULTI",x)
for x in neq_qipM[:8]: print("   !=qipM",x)
print(f"corrected-Aoyagi vs Theorem-1 explicit rule (len3, sorted): mismatches={len(neq_thm1)}")
for x in neq_thm1[:8]: print("   ",x)

print("\n\n==================  DEFINITIVE: does Aoyagi's OWN ell give the same lambda value? ==================")
def core_from_ell(M, ell, T):
    aw=[M[k] for k in range(ell+1)]
    ceilM=(T+ell-1)//ell
    a=T-(ceilM-1)*ell
    pairsum=sum(aw[i]*aw[j] for i in range(ell+1) for j in range(i+1,ell+1))
    return F(a*(ell-a),4*ell) - F(ell*(ell-1),4)*F(T,ell)**2 + F(1,2)*pairsum, ceilM, a

bad_aoyagi=[]; bad_file=[]; bad_sorry=[]; bad_arange=[]; checked=0
for N1 in range(2,7):
    for tup in itertools.combinations_with_replacement(range(0,9), N1):
        M=list(tup)
        if M[0]<1 or qipM_(M)<1: continue
        checked+=1
        cv=cValue_(M)
        # Aoyagi's own ell:
        ell_a=aoyagi_ell_corrected(M)[0]
        T_a=sum(M[k] for k in range(ell_a+1))
        core_a,_,a_a=core_from_ell(M,ell_a,T_a)
        if 2*core_a != F(cv): bad_aoyagi.append((M,cv,2*core_a,ell_a))
        # file's ell=qipM:
        m=qipM_(M); S=qipS_(M)
        core_f,ceilM_f,a_f=core_from_ell(M,m,S)
        if 2*core_f != F(cv): bad_file.append((M,cv,2*core_f,m))
        # sorry: residueA*(ell-residueA) == |qipDelta|*(ell-|qipDelta|), file's objects
        dl=qipDelta_(M)
        lhs=a_f*(m-a_f); rhs=abs(dl)*(m-abs(dl))
        if lhs!=rhs: bad_sorry.append((M,a_f,m,dl,lhs,rhs))
        # residueA range 1..ell (Aoyagi says a in {1..ell})?  check file's a_f
        if not (1<=a_f<=m): bad_arange.append((M,a_f,m))
print(f"checked {checked} (entries 0..8, len 2..6)")
print(f"[Aoyagi-own-ell]   2*core != cValue : {len(bad_aoyagi)}")
for x in bad_aoyagi[:6]: print("   ",x)
print(f"[file ell=qipM]    2*core != cValue : {len(bad_file)}   (sorry two_lambdaCore_eq_cValue)")
for x in bad_file[:6]: print("   ",x)
print(f"[sorry residueA*(ell-residueA)==|qd|*(ell-|qd|)] fails : {len(bad_sorry)}")
for x in bad_sorry[:6]: print("   ",x)
print(f"[file residueA in 1..ell?] violations : {len(bad_arange)}")
for x in bad_arange[:6]: print("   ",x)
