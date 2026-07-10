"""
Case-2 adjudication PART 2:
 (e) extend the never-binds check to wider widths (up to 6, L up to 4).
 (f) find prefix-min-TIGHT examples (M(S)M^{(S+1)} == minAdm, divergence M(S)<M^{(S)} bites) for the
     worked binding-chain example.
 (g) reproduce lessons.md's "negative / sub-2lambda" failure: the exact buggy prefix-min "correction"
     (prefix-min columns inside Mval while keeping the actual-width pivot).
"""
from functools import lru_cache
from itertools import product

def prefmin(M, S): return min(M[:S])

@lru_cache(None)
def minAdm(M):
    M = tuple(M)
    if len(M) == 2: return M[0]*M[1]
    return min((M[0]-t)*(M[1]-t) + minAdm((t,)+M[2:]) for t in range(min(M[0],M[1])+1))

def Mval(M, t):
    L = len(M)-1
    val = (M[0]-t[0])*(M[1]-t[0])
    for j in range(2, L+1):
        val += (t[j-2]-t[j-1])*(M[j]-t[j-1])
    return val

# ---- (e) wider never-binds check --------------------------------------------
print("(e) extended never-binds check (widths up to 6, L up to 4):")
pb=0; cb=0; n=0
for L in [2,3,4]:
    for M in product(range(1,7), repeat=L+1):
        ma = minAdm(M)
        for S in range(1,L+1):
            n+=1
            if M[S-1]*M[S] < ma: pb+=1
            if prefmin(M,S)*M[S] < ma: cb+=1
print(f"    tested {n}: printed M^(S)M^(S+1)<minAdm: {pb};  prefix-min M(S)M^(S+1)<minAdm: {cb}")
print("    => both Case-2 forms are >= minAdm everywhere: Case-2 NEVER binds.\n")

# ---- (f) prefix-min-tight worked examples (divergence bites) -----------------
print("(f) worked binding chains: M(S) < M^(S) AND a Case-2 form equals/nears minAdm:")
shown=0
for L in [2,3]:
    for M in product(range(1,6), repeat=L+1):
        ma = minAdm(M)
        for S in range(2,L+1):
            if prefmin(M,S) < M[S-1]:                      # divergence bites at S
                pref = prefmin(M,S)*M[S]; prin = M[S-1]*M[S]
                if pref == ma and shown < 6:               # prefix-min form is TIGHT (=minAdm)
                    disc = (M[S-1]-prefmin(M,S))*(M[S]-0)
                    print(f"    M={M} S={S}: M(S)={prefmin(M,S)}<M^(S)={M[S-1]};  "
                          f"prefmin-codim={pref}=minAdm={ma} (TIGHT); printed={prin}; "
                          f"discrepancy (n_S-mu_S)(n_(S+1))={disc}")
                    shown+=1
print()

# detailed single worked example: (2,4,4)
print("    --- fully-worked example M=(2,4,4), L=2 ---")
M=(2,4,4); ma=minAdm(M)
print(f"    widths M^(1),M^(2),M^(3) = {M};  prefix-mins M(1)={prefmin(M,1)}, M(2)={prefmin(M,2)}")
print(f"    minAdm = {ma}  (branches: ", end="")
for t1 in range(min(M[0],M[1])+1):
    print(f"t1={t1}->{(M[0]-t1)*(M[1]-t1)+minAdm((t1,)+M[2:])} ", end="")
print(f");  threshold lambda = {ma}/2 = {ma/2}")
S=2
print(f"    Case-2 at S=2: M(2)={prefmin(M,2)} < M^(2)={M[1]}  => divergence BITES")
print(f"       printed  terminal Mval (t^(1)=M^(2)=4, t^(2)=0): Mval={Mval(M,[M[1],0])} = M^(2)M^(3)=16")
print(f"       prefix-min single-step codim M(2)M^(3) = {prefmin(M,2)*M[2]} = 8")
print(f"       both >= minAdm={ma}: Case-2 non-binding; binder is t=(1,0) [rank-1], Mval={Mval(M,[1,0])}=7")
print(f"       discrepancy (M^(2)-M(2))*(M^(3)-0) = {(M[1]-prefmin(M,2))*M[2]} = 16-8")
print()

# ---- (g) reproduce the buggy 'prefix-min correction' negatives ---------------
print("(g) the BUGGY prefix-min 'correction' (prefix-min columns in Mval + actual-width pivot):")
def Mval_buggy(M, t):
    """replace the ACTUAL column widths M^{(j+1)} by prefix-min M(j+1), keep actual pivot t."""
    L=len(M)-1
    val=(prefmin(M,1)-t[0])*(prefmin(M,2)-t[0])
    for j in range(2,L+1):
        val += (t[j-2]-t[j-1])*(prefmin(M,j+1)-t[j-1])     # prefix-min column
    return val
neg=0; ex=[]
for L in [2,3]:
    for M in product(range(1,6), repeat=L+1):
        for S in range(1,L+1):
            t=[ (M[i] if (i+1)<S else 0) for i in range(L) ]  # printed actual-width pivot
            v=Mval_buggy(M,t)
            if v<0:
                neg+=1
                if len(ex)<6: ex.append((M,S,t,v))
print(f"    printed-pivot + prefix-min-columns Mval NEGATIVE count: {neg}")
for (M,S,t,v) in ex:
    print(f"       M={M} S={S} pivot t={t}: buggy Mval={v}  (negative! term M(j+1)-t_j<0 since t_j=M^(j+1)>M(j+1))")
print("    => THIS mixed form is the prior expedition's 'prefix-min fix' failure mode (lessons.md).")
print("       The CLEAN prefix-min single-step codim (f) is fine; the BUGGY column-substitution is not.")
