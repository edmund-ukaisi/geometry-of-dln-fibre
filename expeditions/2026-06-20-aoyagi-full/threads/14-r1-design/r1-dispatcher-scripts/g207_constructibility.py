import sympy as sp
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

# fm3's question: split.red and T are DECOUPLED in the type. Which construction reproduces codimsOf=[4,3]
# for (2,2,2) so foldFamily_achiever fires with m₀=3?
# KEY: codimsOf(path) = [codim c_node = (Mval M_node T_node).toNat : node along path]. The achiever path
# needs minAdm(root M) ∈ codimsOf. m₀ = minAdm(root (2,2,2)) = 3.
print("THE KEY FACT (settles fm3's question):")
print("foldFamily_achiever needs: ∃ leaf i₀ with m₀=minAdm(root M) ∈ codimsOf(i₀), all codims≥m₀.")
print("codimsOf entries = (Mval M_node T_node).toNat. m₀ = minAdm(ROOT M).")
print()
# CRITICAL INSIGHT: the SIMPLEST construction that fires foldFamily_achiever with m₀=minAdm(root) is:
# a SINGLE branch at the root whose cells = Adm M (or just {T*}), with ONE cell carrying T*=argmin, 
# codim = (Mval M T*).toNat = minAdm, and split.red = ANYTHING strictly smaller (to terminate). Because:
#   - foldFamily_achiever only needs m₀ ∈ codimsOf(i₀) for ONE leaf path. If the ROOT branch has a cell
#     with codim = minAdm (the T* cell), then EVERY leaf under that cell has minAdm in its codimsOf.
#   - foldFamily_threshold_ge needs ALL codims ≥ m₀: every cell's codim = (Mval M_node T).toNat ≥ 
#     minAdm(M_node). BUT m₀ = minAdm(ROOT), and minAdm(M_node) for a SMALLER M_node could be < minAdm(root)!
#     ⟹ THE DECOUPLING RISK: if split.red is arbitrary, a child node M' might have minAdm(M') < minAdm(root),
#     and a cell there with codim = minAdm(M') < m₀ would UNDERSHOOT ⟹ foldFamily_threshold_ge FAILS.
print("THE DECOUPLING RISK (the answer to fm3): codimsOf entries are (Mval M_node T).toNat for the NODE's")
print("M_node (= split.red chain). foldFamily_threshold_ge needs ALL ≥ m₀=minAdm(ROOT). But a child M_node")
print("(smaller) can have minAdm(M_node) < minAdm(root) — a cell there UNDERSHOOTS m₀. So split.red is NOT")
print("free: the codims along the path must ALL be ≥ minAdm(root M). Check whether schurState preserves this.")
print()
# Check: does schurState (M_0-1, M_1-1, M_{≥2}) preserve minAdm ≥ minAdm(root)? Or does minAdm DROP?
print("Does minAdm(schurState M) ≥ minAdm(M)?  (if NOT, the codim at the child could undershoot)")
def schur(M): M2=list(M); M2[0]-=1; M2[1]-=1; return tuple(M2)
for M in [(2,2,2),(3,2,3),(3,3,3),(2,2,2,2)]:
    if min(M[0],M[1])>=1:
        ch = schur(M)
        if all(x>=0 for x in ch) and any(x>0 for x in ch):
            print(f"  M={M}: minAdm={minAdm(M)}; schurState={ch}: minAdm={minAdm(ch) if adm(ch) else 'n/a (terminal)'}")
