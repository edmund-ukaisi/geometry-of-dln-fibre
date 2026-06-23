from itertools import product
def Mval(M,t):
    L=len(M)-1; tt=[M[0]]+list(t); return sum((tt[j-1]-tt[j])*(M[j]-tt[j]) for j in range(1,L+1))
def admissible(M,t):
    L=len(M)-1; tt=[M[0]]+list(t)
    if tt[-1]!=0: return False
    for j in range(1,L+1):
        if not(0<=tt[j]<=tt[j-1]): return False
        if tt[j]>M[j]: return False
    return True
def adm(M):
    L=len(M)-1; return [(t,Mval(M,t)) for t in product(*[range(M[0]+1)]*L) if admissible(M,t)]
def minAdm(M): return min(m for _,m in adm(M))

# THE CRUX: is minAdm M = 0 ⟺ (∃ s, M_s = 0)?  Verify exhaustively + find the structural reason.
print("CRUX: minAdm M = 0 ⟺ (∃ s, M_s = 0)?  Exhaustive over L=1..4, widths 0..3:")
bad=[]; n=0
for L in range(1,5):
    for M in product(range(0,4),repeat=L+1):
        n+=1
        lhs = (minAdm(M)==0); rhs = any(x==0 for x in M)
        if lhs!=rhs: bad.append((M, minAdm(M), rhs))
print(f"  {n} M tested; mismatches (minAdm=0 XOR ∃M_s=0): {len(bad)}")
if bad:
    for M,mA,rhs in bad[:20]: print(f"    M={M}: minAdm={mA}, ∃M_s=0:{rhs}")
print()
if not bad:
    print("⟹ minAdm M = 0 ⟺ (∃ s, M_s = 0) EXACTLY. STRUCTURAL REASON:")
    print("  (⇐) if some M_s=0: the all-zero t (after s) — actually t_s=0 forced (t_s≤M_s=0), and t weakly-")
    print("      decr with t_L=0 ⟹ can set t_j=0 for j≥s and saturate before. The width-0 layer makes a")
    print("      zero-codim path exist (the chain bottlenecks through 0). minAdm=0.")
    print("  (⇒) if all M_s≥1: every admissible t with t_L=0 has SOME positive summand. The minimal is the")
    print("      rank-1 incidence (t_1=1,rest 0)-type, Mval = (M_0-1)(M_1-1)+...>0 since all M_s≥1. minAdm>0.")
print()
# So the LEAF TEST minAdm=0 EXACTLY detects the DEGENERATE BOUNDARY (∃M_s=0). Implications for #103:
print("="*68)
print("VERDICT for #108/#103 (the leaf-test adjudication):")
print("="*68)
print("minAdm M = 0 ⟺ ∃ s, M_s = 0 (the DEGENERATE BOUNDARY), EXACTLY. So rs-grind's isLeafNode :=")
print("minAdm M = 0 is DECIDABLE + EXACT for 'degenerate boundary', BUT it is NOT a clean interior")
print("recursion leaf — it's the #70 ⊤-trap boundary, where lambdaCore=½·minAdm=0 ≠ rlctAtOn(dlnLoss M 0)=⊤.")
print()
print("THE GENUINE INTERIOR LEAF (all M_s≥1) NEVER has minAdm=0 — the recursion on the BULK (all M_s≥1)")
print("NEVER bottoms out via minAdm=0; it bottoms when the schurState descent reaches a width-0 (M_s=0),")
print("i.e. the DEGENERATE BOUNDARY. So the recursion base case IS the degenerate boundary (∃M_s=0), and")
print("THERE the value is NOT ½·minAdm (the ⊤-trap) — it's the #70 direct-Morse rlctAt = nReg/2.")
print()
print("⟹ isLeafNode := minAdm M = 0 is EXACT for 'this is the degenerate-boundary base case' (= ∃M_s=0),")
print("and the leaf's VALUE must route through #70 (direct Morse, rlctAt=nReg/2), NOT the additive ½·minAdm")
print("(which gives the wrong 0 = the ⊤-trap). The leaf test is RIGHT (detects the base case); the leaf's")
print("VALUE-handling must be #70, not '½·minAdm=0'. fm3's candidate (b) (schurState-bottomed M_0=0 or M_1=0)")
print("is close but WRONG — the boundary is ANY M_s=0 (incl interior M_2=0 like (2,2,0)), not just M_0/M_1.")
