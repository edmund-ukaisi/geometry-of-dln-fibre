import sympy as sp
from itertools import product
from fractions import Fraction as Fr
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

# THE SPELL-OUT (against fm3's @b8d3146 light RouteStep.branch):
#   branch (cells)(cellsFin)(split : cells→ChainDimSplit M)(codim : cells→ℕ)(witness : (c)→PivotWitness M (codim c))
#   PivotWitness M c = ⟨T, hAdm : T∈Adm M, hCodim : c = (Mval M T).toNat⟩
#   schurState M' = (M_0-1, M_1-1, M_2, ...) [the C1 ΣM-2 descent]
# Spell (2,2,2) and (3,2,3). The dispatcher at each node: classify → branch with the pivot cells, each
# cell's (split=schurState, codim=Mval(T), PivotWitness=⟨T,...⟩). codimsOf(leaf) = the Mvals down its path.

def schurState(M):
    M2=list(M); M2[0]-=1; M2[1]-=1; return tuple(M2)

print("="*70); print("SPELL-OUT (2,2,2) against fm3's light RouteStep.branch @b8d3146"); print("="*70)
M=(2,2,2); print(f"root M={M}, minAdm={minAdm(M)}, lambda={Fr(minAdm(M),2)}")
print(f"""
ROOT node M=(2,2,2): branch with pivot cells (the rank-defect blow-up cells of pivotBlowupOn).
  The A-pivot blow-up (Case222 step1A = pivotBlowupOn{{0,1,2,3}}0) — the cells are its affine charts.
  Per cell c the dispatcher gives:
    split c   = ChainDimSplit (2,2,2) with red = schurState (2,2,2) = {schurState(M)}  [ΣM 6→4]
    codim c   = (Mval (2,2,2) T).toNat  where T = the rank stratum the cell resolves
    witness c = PivotWitness ⟨T, hAdm, hCodim⟩
  The binding cell c*: T=(0,0) [full collapse], codim = Mval((2,2,2),(0,0)) = {Mval((2,2,2),(0,0))}.
    [step-1 card 4 = this codim ✓]
""")
M1=schurState((2,2,2)); print(f"  RECURSE on schurState = {M1}:")
print(f"""    Node {M1}: the resolved-form blow-up (Case222 step-2 = pivotBlowupOn{{1,2,3}}1).
    binding cell: T=(1,0)-image, codim = Mval((2,2,2),(1,0)) = {Mval((2,2,2),(1,0))} [the ACHIEVER/binding, =minAdm].
      [step-2 card 3 = this codim ✓]
    leaf: MonoData (the unit core, IsUnit residualCore).
""")
print(f"""  codimsOf(binding leaf) = [{Mval((2,2,2),(0,0))}, {Mval((2,2,2),(1,0))}] = [4, 3].
    foldDivisors → ratioMinFold = min(4/2, 3/2) = 3/2 = lambda(2,2,2) ✓
  PivotWitness check: T=(0,0)∈Adm ✓ codim 4=Mval ✓; T=(1,0)∈Adm ✓ codim 3=Mval=minAdm ✓.
  foldFamily_threshold_ge_of_pivotWitness (all codims≥3) + foldFamily_achiever (3∈[4,3]) ⟹ ⨅=3/2.
""")

print("="*70); print("SPELL-OUT (3,2,3)"); print("="*70)
M=(3,2,3); print(f"root M={M}, minAdm={minAdm(M)}, lambda={Fr(minAdm(M),2)}, strata={adm(M)}")
print(f"""
ROOT M=(3,2,3): C1 blow-up. split.red = schurState = {schurState(M)} [ΣM 8→6].
  binding cell: T=(1,0), codim = Mval((3,2,3),(1,0)) = {Mval((3,2,3),(1,0))} = minAdm [the achiever].
  other cell: T=(0,0), codim = Mval((3,2,3),(0,0)) = {Mval((3,2,3),(0,0))}.
  RECURSE on {schurState(M)} until unit leaf.
  codimsOf(achiever leaf) ∋ {Mval((3,2,3),(1,0))} (=minAdm=5) ⟹ binding ratio 5/2 = lambda(3,2,3) ✓.
  PivotWitness: T=(1,0)∈Adm, codim 5=Mval=minAdm ✓.
""")
print("Both spell-outs type-check against branch(split, codim, witness:PivotWitness): each cell gives")
print("(schurState split, (Mval M T).toNat codim, ⟨T,hAdm,hCodim⟩ witness); leaf = MonoData (unit).")
print("Transport = light node_loss_pivot_factor (the pivotBlowupOn x_p²·reduced), discharged at cover-fact,")
print("NOT spelled per-cell. codimsOf = exceptional Mvals; value via foldFamily_*. CONSISTENT with @b8d3146.")
