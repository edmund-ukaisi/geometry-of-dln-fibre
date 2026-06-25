# Question: is the general deep-linear-network Schur resolution chart measure-preserving (det 1), or Jacobian-carrying (blow-up producing monomial weights)?

## Setup (Aoyagi's deep linear network RLCT, general layer widths)

Layer widths M : Fin (L+1) → ℕ. A parameter is a composable matrix tuple
A = (A^(0), ..., A^(L-1)), A^(s) : Matrix (Fin (M s)) (Fin (M (s+1))) ℝ.
The product map: prod A = A^(0) · A^(1) · ... · A^(L-1) : Matrix (Fin (M 0)) (Fin (M L)) ℝ.
The loss at the deepest point B=0: dlnLoss A = ‖prod A‖²_F = Σ_{ij} (prod A)_{ij}².
We want the real log-canonical threshold (RLCT) of dlnLoss at A=0.

We are reducing the RLCT recursively. The claimed "Schur-complement chart" near A=0 is supposed to,
in local coordinates, re-identify the loss as
   dlnLoss(chart(x, A')) = u(x,A') · ( Σ_i x_i²  +  dlnLoss_reduced(A') )
where A' ranges over a strictly-smaller-width REDUCED chain (widths M^s − δ_s), x are nReg "regular"
coordinates, u is a scalar analytic unit. The recursion then gives
   RLCT(dlnLoss, M, 0)  =  nReg/2  +  RLCT(dlnLoss_reduced, M', 0).

## The two candidate chart structures

(A) DET-1 / MEASURE-PRESERVING. The chart is built from unimodular row/column operations
    (Gaussian elimination / a Schur complement with det-1 adapted bases (u_i, ψ_i)). Jacobian ≡ 1.
    Then the recursion is CLEAN: RLCT = nReg/2 + RLCT_reduced, no monomial weights, terminating in a
    pure sum-of-squares smooth leaf with RLCT = (total dim)/2. This would give RLCT = (something)/2,
    a half-integer, with NO blow-up needed.

(B) JACOBIAN-CARRYING BLOW-UP. The chart is a blow-up (like the (2,2,2) case used: a "pivot blow-up"
    x ↦ (x_0, x_0 x_1, ..., x_0 x_{n-1}) with Jacobian det = x_0^{n-1}, a nontrivial monomial). The
    monomial Jacobian becomes a WEIGHT in the RLCT integral, and the RLCT is computed as an infimum
    of monomial thresholds ⨅_i monomialThreshold(d_i, k_i, h_i), NOT a clean nReg/2 + ... chain.

## Hard facts I have

- For (2,2,2) (L=2, all widths 2): the verified Lean proof gives RLCT = 3/2, and it REQUIRED a
  blow-up chart (pivotBlowup, Jacobian (x_0)^n) — structure (B). The 3/2 came out of a ⨅ of monomial
  thresholds, each 3/2, over a 24-leaf cover. A clean det-1 reduction was NOT used for (2,2,2).
- Aoyagi's general formula for the DLN learning coefficient λ is generically NOT a clean (dim)/2 — it
  is a more intricate arithmetic minimum (related to a quadratic integer program over how the rank
  drop δ_s is distributed across layers). This intricacy is hard to reconcile with a purely det-1
  clean nReg/2 + reduced recursion (which would just sum half-dimensions).

## The question (answer decisively, with reasoning)

1. For the GENERAL deep linear network (arbitrary L and widths M), is the resolution chart
   structure (A) det-1/measure-preserving, (B) a Jacobian-carrying blow-up, or (C) BOTH in sequence
   (det-1 Gaussian ops peel off regular blocks, THEN a residual blow-up resolves the singular core)?

2. If the answer involves a blow-up (B or C), then the clean recursion-step
   "RLCT = nReg/2 + RLCT_reduced" is WRONG/unsound as a standalone identity (it omits the monomial
   weight). Is that right? What is the correct shape of the recursion-step identity?

3. Given that (2,2,2) provably needed a blow-up and Aoyagi's λ is not a clean half-dimension sum:
   which structure is mathematically forced for the general case? Is a det-1-only reduction even
   capable of producing Aoyagi's arithmetic-minimum formula, or does the blow-up's monomial-weight
   structure carry that arithmetic content?
