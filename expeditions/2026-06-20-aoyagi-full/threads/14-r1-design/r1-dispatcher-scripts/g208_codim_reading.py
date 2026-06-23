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
def schur(M): M2=list(M); M2[0]-=1; M2[1]-=1; return tuple(M2)

# RECONCILE: g195 read (2,2,2) codims [4,3] as Mval(ROOT (2,2,2), T) at BOTH nodes. But fm3's type has
# PivotWitness M c at the NODE's M (= split.red chain after recursion). Which gives [4,3]?
print("g195 reading: step-1 T=(0,0) Mval((2,2,2),(0,0))=4; step-2 T=(1,0) Mval((2,2,2),(1,0))=3. ROOT M both.")
print(f"  Mval((2,2,2),(0,0))={Mval((2,2,2),(0,0))}, Mval((2,2,2),(1,0))={Mval((2,2,2),(1,0))}")
print()
print("If step-2's PivotWitness is at the REDUCED node M'=schurState((2,2,2))=(1,1,2):")
M2=schur((2,2,2))
print(f"  M'={M2}, Adm(M')={adm(M2)}")
print(f"  Mval((1,1,2),(1,0))={Mval(M2,(1,0))}, minAdm(M')={minAdm(M2)}")
print()
print("KEY: step-2's codim 3 = Mval(ROOT (2,2,2), (1,0)), NOT Mval(reduced (1,1,2), T). The reduced chain's")
print("Mval gives DIFFERENT (smaller) numbers. So the codim a node contributes is the GEOMETRIC codim in the")
print("ORIGINAL space — Mval(ROOT M, T_cumulative) — where T_cumulative is the rank pattern resolved so far,")
print("NOT Mval(split.red, T_local).")
print()
print("="*68)
print("THE ANSWER TO fm3 (the constructibility resolution):")
print("="*68)
print("PivotWitness M c MUST be witnessed against the ROOT M (the original width vector), NOT the reduced")
print("split.red chain. Two ways to make this sound in the decoupled type:")
print()
print("OPTION A (root-anchored witness): the recursion CARRIES the root M (or the cumulative resolved-rank")
print("context) so each node's PivotWitness is ⟨T_cumulative, hAdm : T_cumulative∈Adm(ROOT M), hCodim :")
print("codim = (Mval ROOT_M T_cumulative).toNat⟩. The codimsOf along a path = [Mval(ROOT, T_k)] for the")
print("rank-descent T_0 ⊃ T_1 ⊃ ... — all ≥ minAdm(ROOT) (every Mval(ROOT,T)≥minAdm by def). foldFamily fires.")
print("  ⟹ split.red is the WIDTH bookkeeping (for termination, Σred<ΣM); the codim/witness is ROOT-anchored.")
print()
print("OPTION B (branch-over-Adm at root, candidate 1): a SINGLE root branch, cells=Adm(ROOT M), each cell")
print("codim=(Mval ROOT M T).toNat, witness=⟨T,...⟩ at ROOT M, split.red=anything terminating. Then leaves")
print("are DEPTH-1, codimsOf(cell T)=[Mval(ROOT,T)] (single entry). foldFamily: all ≥minAdm ✓, achiever cell")
print("T* has minAdm ✓. SIMPLEST + terminating + general. The ⨅-over-Adm IS the ⨅-over-cells directly.")
print()
print("VERDICT: fm3's candidate (1) BRANCH-OVER-Adm is RIGHT and simplest — BUT the codim MUST be Mval(ROOT")
print("M, T), witnessed at the ROOT M (PivotWitness (ROOT M) c). The split.red is decoupled (just needs")
print("Σred<ΣM to terminate — can be a single decrement, or even a trivial leaf-child). The recursion DEPTH")
print("is then 1 (root branches over Adm, each cell → leaf). NO schurState needed as a Lean def. codimsOf")
print("for (2,2,2): cells = Adm((2,2,2)) = {(0,0)→4, (1,0)→3, (2,0)→4}; ⨅ over cells of (Mval/2) = min(2,3/2,2)")
print("= 3/2 = lambdaCore ✓. foldFamily_achiever: cell (1,0) has codim 3 = minAdm ✓.")
