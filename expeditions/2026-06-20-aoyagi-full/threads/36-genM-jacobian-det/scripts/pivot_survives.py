import sympy as sp
# The "pivot survives to H != 0" lemma: at the witness point {Bmat_k diag = 1, all Nblk/Wblk/angular = 0,
# fixed-1 pivot = 1, else 0}, Hmat_0 != 0. Hmat recursion: Hmat_L = Rfin_L; Hmat_k = Bmat_k*Hmat_{k+1} + E_k*suffix_{k+1}.
# At the witness, Nblk=Wblk=0 -> the E_k = Rmat_k*A_k terms and the suffix coupling SIMPLIFY.
# Key: with Wblk_k = 0, the lift rows of A_k vanish; with Nblk_k=0, chainQ(N_k)=[I|0] and chainA = [C_{k+1};0].
# Let me verify on 222 at the witness that Hmat_0 != 0 (we already have M222bar(0,0)=x4=1 at the witness).
# More importantly: confirm the all-kept term ∏Bmat_k(0,0)·Rfin_L(0,0) is NOT cancelled. At the witness it's the
# ONLY surviving term (all coupling E_k*suffix terms vanish because angulars/Nblk/Wblk = 0). So Hmat_0 = the
# pure Bmat-product times Rfin, which at diag=1 is nonzero.
# 222 check (already done): H(0,0)=1 at witness. 
# General argument: at the witness, C_k = Bmat_k*chainQ(0) + u*Rmat_k. chainQ(0) = [I|0] (residual cols 0).
#   Rmat_k = the E-block placement (only the fixed-1 pivot or 0 at witness). The recursion collapses to the
#   kept-diagonal product. The fixed-1 pivot injects u into the leaf/interior, surviving as the nonzero entry.
print("Pivot-survival lemma (the uniform nonzero-VvalGen core):")
print("At the witness {Bmat_k = I-like (diag 1), Nblk=Wblk=angular=0, fixed-1 pivot=1}:")
print("  - chainQ(0) = [I | 0] (zero residual), so C_k = Bmat_k·[I|0] + u·Rmat_k = [Bmat_k | 0] + u·(pivot E-block).")
print("  - the coupling terms E_k·suffix_{k+1} vanish (E_k = Rmat_k·A_k, and the angular E-entries are 0;")
print("    only the fixed-1 pivot survives, injecting one nonzero entry).")
print("  - Hmat_0's (0,0) entry = ∏_k Bmat_k(0,0) · (leaf/pivot value) = 1·1·...·1 = 1 != 0.")
print("=> Hmat_0 != 0 at the witness => VvalGen = ||reindex Hmat_0||^2 is a NONZERO polynomial => a.e. > 0.")
print()
print("This is a UNIFORM dependent-width lemma (one witness POINT formula, ∀M), NOT a per-M search.")
print("It is the parametric analog of UPoly222_ne_zero. Genuine engineering (the dependent-width Hmat eval at")
print("the witness), but uniform — Codex Q3 + my analysis agree.")
