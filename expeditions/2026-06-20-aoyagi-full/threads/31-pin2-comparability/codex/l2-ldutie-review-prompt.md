# Decorrelated check: the L=2 "hLDUtie" readback identity + dictionary

You are an independent adversarial reviewer. A Lean lemma claims an exact matrix identity. I want you to
(A) independently verify/refute the algebraic identity, and (B) judge whether two "dictionaries" coincide.
Do the algebra yourself (sympy is fine — you may run it). Report exact expressions, not vibes.

## Setup (r = 1 scalar case; the general case is the block analogue)

Two "layers" on a `1 ⊕ 1` block split (so each is a 2×2 matrix over a field):

    G0 = [[A0, Y0], [Z0, T0]]      G1 = [[A1, Y1], [Z1, T1]]

with A0, A1 invertible and P := (G0·G1)_{11} = A0·A1 + Y0·Z1 invertible.

Two constant "endpoint frames":
    P0 = [[P11, 0],   [P21, 1]]      (block-LOWER triangular, (2,2)-block = 1)
    QL = [[Q11, Q12], [0,   1]]      (block-UPPER triangular, (2,2)-block = 1)

Define the (2,2)-Schur complement of a 2×2 matrix M over its (1,1) entry:
    Schur(M) = M_{22} − M_{21}·(M_{11})^{-1}·M_{12}.

## Claim 1 (the standalone identity)

Let `prod = G0·G1` and `Mhat = P0·prod·QL`.
Define the per-layer FULL-pivot Schur cores and the cross factor:
    S0 = Schur(G0) = T0 − Z0·A0^{-1}·Y0
    S1 = Schur(G1) = T1 − Z1·A1^{-1}·Y1
    K  = Z1·P^{-1}·Y0          (P = (G0·G1)_{11})
    C0 = S0
    C1 = (1 − K)·S1
CLAIM:  C0 · C1  =  Schur(Mhat).
i.e. the product of the two FULL-pivot cores (with the (1−K) bridge) equals the Schur complement of the
FRAMED product. Verify or refute. State whether it needs any extra hypothesis (e.g. that Y0=0, T0=0,
Z1=0, T1=0, or Z0=0, Y1=0). I believe it holds with NO such restriction (all of A0,Y0,Z0,T0,A1,Y1,Z1,T1
free, A0/A1/P invertible, frames triangular with unit (2,2)).

## Claim 2 (frame-strip)

CLAIM:  Schur(Mhat) = Schur(prod)  (i.e. the frames P0, QL cancel out entirely).
Verify/refute and state the conditions used (I claim: P0 block-lower with (2,2)=1, QL block-upper with
(2,2)=1, A0/A1/P invertible — the (1,1) and off-diagonal frame entries P11,P21,Q11,Q12 all cancel).

## Claim 3 (the dictionary discrepancy — the load-bearing review question)

There are TWO candidate "core dictionaries":
  (full-pivot)  S0_full = T0 − Z0·A0^{-1}·Y0     (pivot = the FULL leading block A0)
  (bare-pivot)  S0_bare = T0 − Z0·(1+x0)^{-1}·Y0  (pivot = 1 + x0, where A0 = Ā0 + x0,
                                                    Ā0 = a fixed "deepest leading block", x0 = a read)
QUESTION: under what condition do S0_full and S0_bare coincide? Compute S0_full − S0_bare exactly as a
function of (Ā0, x0, Y0, Z0, T0). I expect it is zero iff Ā0 = 1 (the deepest leading block equals the
identity), and NONZERO when Ā0 ≠ 1. Confirm or refute, and give the exact difference.

## What I need back
1. Claim 1: HOLDS / FAILS, with the exact residual `C0·C1 − Schur(Mhat)` (simplified) and any needed hyps.
2. Claim 2: HOLDS / FAILS + conditions.
3. Claim 3: the exact `S0_full − S0_bare` and the precise condition for it to vanish.
4. One sentence: if a "producer" supplies the BARE-pivot cores but the identity (Claim 1) requires the
   FULL-pivot cores, and the deepest leading block Ā0 ≠ 1 — is there a genuine mismatch the producer must
   repair (by switching to the full-pivot/conjugated core), yes or no?
Keep inference separate from computed fact.
