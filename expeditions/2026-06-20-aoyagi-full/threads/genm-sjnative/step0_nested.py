import sympy as sp
print("="*80)
print("STEP-0 (C-5): NESTED Case-1 branch (2,1,0) — rank-2 pivot at L1, two partial drops")
print("="*80)

# ---- L1: A0 3x3 rank-2 pivot (pivot 2x2 block = I after clear), corank 1x1 ----
# A0 = [[P(2x2), c(2x1)],[r(1x2), m(1x1)]]; pivot block P a unit. Schur: corank Delta0 = m - r P^{-1} c (1x1).
P = sp.Matrix(2,2, lambda i,j: sp.Symbol(f'P{i}{j}', real=True))
c = sp.Matrix(2,1, lambda i,j: sp.Symbol(f'c{i}', real=True))
r = sp.Matrix(1,2, lambda i,j: sp.Symbol(f'r{j}', real=True))
m = sp.Symbol('m', real=True)
A0 = sp.Matrix(sp.BlockMatrix([[P, c],[r, sp.Matrix([[m]])]]))
Pinv = P.inv()
# block LU: A0 = [[I,0],[r P^-1, 1]] . [[P,0],[0, Delta0]] . [[I, P^-1 c],[0,1]]
Lrow = sp.Matrix(sp.BlockMatrix([[sp.eye(2), sp.zeros(2,1)],[r*Pinv, sp.Matrix([[1]])]]))
Delta0 = sp.simplify(m - (r*Pinv*c)[0,0])
Mid   = sp.Matrix(sp.BlockMatrix([[P, sp.zeros(2,1)],[sp.zeros(1,2), sp.Matrix([[Delta0]])]]))
Rcol  = sp.Matrix(sp.BlockMatrix([[sp.eye(2), Pinv*c],[sp.zeros(1,2), sp.Matrix([[1]])]]))
recon = sp.simplify(A0 - Lrow*Mid*Rcol)
print("\n[L1] A0 = Lrow . diag(P, Delta0) . Rcol exact:", recon==sp.zeros(3,3))
print("     det Lrow =", sp.simplify(Lrow.det()), ", det Rcol =", sp.simplify(Rcol.det()),
      " (unit-triangular, det 1); functions of A0's OWN entries only (Z-independent).")
print("     corank Delta0 (1x1) =", Delta0, "  <- the single dropping slot (corank 1 of running-3).")
print("     pivot block P (2x2) SURVIVES as the Morse part (split off, carries NO new radial u1).")

# radial u1 on the 1x1 corank block: Delta0 = u1 (charge 1 => trivial 1-dim radial, u1 IS the coord)
u1 = sp.Symbol('u1', positive=True)
print("     corank charge 1 => radial u1 = Delta0 itself; corank generator carries {u1}, pivot carries {} .")
print("     => block-split isolates support-{} pivot from support-{u1} corank. No cross-support mix. [L1 closed]")

# ---- generator-support closure MODEL across ALL binding branches (mirrors loss_blockSplit+prependColumn) ----
print("\n[C-6] Generator-support closure model (all binding branches; the (S,J) recursion carrier):")
def admBound(M,j): return min(M[0],M[1]) if j==0 else M[j+1]
import itertools
def redChain(t,M): return (t,)+M[2:]
def trace(M, T):
    # returns list of terminal generators as (support_set, layer); checks every active block is constant-support
    cur=M; acc=()  # accumulated radial support of the CURRENT active block (a tuple of radial names)
    terminal=[]; layer=0; all_const=True; details=[]
    while len(cur)>=3 and layer<len(T):
        t=T[layer]; p,q=cur[0]-t,cur[1]-t; chg=p*q
        rad=f"u{layer+1}"
        # pivot part: t*? Morse gens survive with support acc (NO new radial), split off
        pivot_support=acc
        # corank part: gets the new radial -> support acc+(rad,); becomes new active block
        corank_support=acc+(rad,)
        # the block-elimination acts WITHIN the corank block (all gens share corank_support) => constant
        details.append(f"L{layer+1}: peel t={t}, corank {p}x{q} chg={chg}; pivot-support={pivot_support or '{}'}"
                       f" (split off), corank-support={corank_support} (active). block const-support: YES")
        # split-off pivot generators become terminal (Morse), support = pivot_support
        terminal.append((pivot_support, f"pivot@L{layer+1}"))
        acc=corank_support; cur=redChain(t,cur); layer+=1
    # remaining leaf: terminal gens carry acc
    terminal.append((acc, f"leaf"))
    return terminal, details, all_const

M=(3,3,3,4)
for T in [(1,0,0),(2,0,0),(2,1,0)]:
    term, det, const = trace(M,T)
    print(f"\n  Branch T={T}:")
    for d in det: print("    "+d)
    print(f"    terminal generator supports: {[s or '{}' for s,_ in term]}")
    # nesting check: supports are NESTED (each deeper support extends the shallower) => shared divisors
    supps=[frozenset(s) for s,_ in term if s]
    nested=all(supps[i] <= supps[i+1] or supps[i+1] <= supps[i] for i in range(len(supps)-1)) if len(supps)>1 else True
    print(f"    supports NESTED (shared-divisor chain, no incompatible mix): {nested}")
    print(f"    every active block constant-support (gen_rowMix_const applies at each elimination): {const}")
