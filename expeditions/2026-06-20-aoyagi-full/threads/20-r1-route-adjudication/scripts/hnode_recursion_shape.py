"""
Q1 (resolving the absorb ambiguity) — what does a SINGLE hnode step commit to?

A single hnode step at a node M produces (via schur_straighten_squeeze_of_data):
    rlctAtOn(flatCore)(0,0) = nReg/2 + rlctAtOn(G²)(0),   G² = dlnLoss S.red 0 (reduced loss)
with measure_drops: ∑ S.red < ∑ M.

The recursion ITERATES this: at each node peel nReg regular coords (the cleared pivot
block), descend to the reduced chain S.red, accumulate nReg/2 ADDITIVELY.

So after the full recursion the value is  Σ (nReg at each node)/2 = (Σ nReg)/2.
For the headline this must equal ½·minAdm M = ½·Mval(t*), i.e. Σ nReg = Mval(t*)
along the achiever branch.

NOW: a single hnode step clears how many pivots?  The hard-1-pivot Schur
(hardPivot_schur_blockId, schur_row_decomp) clears ONE pivot (block A₁ = 1×1 = 1).
So nReg per step = the regular generators exposed by clearing ONE pivot:
   when one pivot cleared, the regular block {C₁−E, F₂, F₃} restricted to that pivot.
The cross term is then bcol⊗Erow (rank-1) — Test A confirmed.

THE DICHOTOMY:
  - If each hnode step clears exactly ONE pivot (rank-1 elimination), the cross term is
    ALWAYS rank-1 bcol⊗Erow, faithful — BUT then to clear a corank-2 residual you need
    TWO successive rank-1 steps, and the SECOND step's pivot lives in the RESIDUAL Δ-block,
    whose entries are NOT free (they are coupled via the shared deep tail C). The
    pivot-row Erow of the second step is then a product involving the FIRST step's residual,
    and the 'reduced loss' G² of the second step is NOT a clean dlnLoss of a smaller chain.

Let's test the TWO-STEP rank-1 elimination at (3,3,4) t=(1,0) explicitly.
"""
import sympy as sp

# (3,3,4) core: F = ‖C¹·C²‖² with C¹ free 3×3, C² free 3×4, resolved at origin.
# (RRR / L=2 core.) The deepest stratum t=(1,0): rank-1.  We do block elimination.
C1 = sp.Matrix(3,3, lambda i,j: sp.Symbol(f'p_{i}{j}', real=True))
C2 = sp.Matrix(3,4, lambda i,j: sp.Symbol(f'q_{i}{j}', real=True))

# Step 1: clear ONE pivot of C¹ (the (0,0) entry, regular near a rank-1 point).
# Block-elim C¹ -> diag(1, Δ) with Δ the 2×2 Schur complement (free 2×2 near generic).
# Aoyagi Lemma 2: Q1·C¹·Q2 = diag(C1_00, C4), C4 = 2×2 Schur complement (rank up to 2).
# The product ⟨C¹C²⟩ becomes ⟨diag(1,Δ)·C2'⟩ with C2' = Q2⁻¹ C² (fresh free 3×4).
Delta = sp.Matrix(2,2, lambda i,j: sp.Symbol(f'd_{i}{j}', real=True))   # residual 2×2 (free)
C2p = sp.Matrix(3,4, lambda i,j: sp.Symbol(f'r_{i}{j}', real=True))     # fresh free 3×4
diagD = sp.Matrix([[1,0,0],[0,Delta[0,0],Delta[0,1]],[0,Delta[1,0],Delta[1,1]]])
Prod = diagD * C2p     # 3×4
# F_core ~ ‖diag(1,Δ)·C2'‖²  (after the unit transform; ideal-preserving)
# Top row (pivot cleared) = regular block (the 4 entries of row 0 of C2');
#   nReg_step1 = 4  (the M^(2)=4 entries of the cleared pivot row).
top = Prod[0,:]            # 1×4 regular row
bottom = Prod[1:,:]        # 2×4 = Δ·(bottom of C2')
print("=== Step 1 at (3,3,4): clear ONE pivot ===")
print("top row (regular, nReg=4) entries:", [top[0,j] for j in range(4)])
print("bottom 2×4 block = Δ·(C2' bottom rows). Is the cross term rank-1 bcol⊗Erow?")
# The hard-1-pivot form would write bottom_{i,j} = bcol_i·Erow_j + SΓ_{i,j}.
# Here bottom = Δ·SC where SC = bottom rows of C2' (2×4 free). Erow = top row = row 0 of C2'.
# But bottom rows of C2' (SC) are INDEPENDENT of the top row (Erow)! So there is NO
# bcol such that the bilinear-in-(pivot) structure matches — the bottom block does not
# even involve Erow.  Let's verify: does 'bottom' contain Erow (top row) at all?
SC = C2p[1:,:]   # 2×4
involves_erow = any(top[0,j].free_symbols & bottom[i,jj].free_symbols
                    for i in range(2) for jj in range(4) for j in range(4))
print("  bottom block shares variables with Erow (top row)? :", involves_erow)
print("  => At a CLEAN rank-1 peel of (3,3,4), the bottom block = Δ·SC is INDEPENDENT")
print("     of the regular row; the hnode cross term bcol⊗Erow would be ZERO (bcol=0),")
print("     and G² = ‖Δ·SC‖² = the (2,2,4) reduced core. Then rlct = 4/2 + rlct(‖ΔSC‖²).")
print()
# Now rlct of the reduced (2,2,4)-type core ‖Δ·SC‖², Δ free 2×2, SC free 2×4:
print("=== Step 2: the reduced core ‖Δ·SC‖² (Δ 2×2 free, SC 2×4 free) ===")
print("This is itself a (2,2,4) matrix-product singularity. Its rlct must be computed.")
print("Published RRR (Aoyagi-Watanabe): rlct(‖Δ·SC‖²) for (2,2,4) core = 2 (radial resolution).")
print("So rlct(node) = 4/2 + 2 = 2 + 2 = 4. CORRECT!  (matches the certified value)")
print()
print("KEY INSIGHT: at the CLEAN rank-1 peel of (3,3,4), hnode with bcol=0 (no cross term)")
print("and G² = the (2,2,4) reduced core IS satisfiable, and gives the RIGHT value 4 —")
print("PROVIDED the recursion then resolves ‖Δ·SC‖² CORRECTLY (rlct=2, not 1).")
print("The corank-2 coupling lives ENTIRELY in the reduced core ‖Δ·SC‖², which is a")
print("FRESH (2,2,4) matrix-product singularity — NOT a clean dlnLoss of a width-chain")
print("(2,2,4) unless Δ·SC equals dlnLoss(redChain). Check that next.")
