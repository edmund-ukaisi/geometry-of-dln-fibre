# G3.2 (Schur-complement recursion, general-M) — WITNESS CERTIFICATE (pp-hall, 2026-06-21)

> **CORRECTION (2026-06-21, task #118, fm-2 stop-before-lines catch — read FIRST).** This cert's
> "the recursion bottoms out at a smooth block leaf" (line 27) + the "det-1 unimodular Q" framing was
> **IMPRECISE for the ZERO-CORE resolution**, and if read as the zero-core Lean contract it is WRONG.
> The det-1 Schur substitution validated here is the **B≠0 rank-r PRODUCT REDUCTION** (Aoyagi Thm 3 /
> `product_reduction`): it peels the `r` regular generators cleanly (measure-preserving, the `nReg/2`
> shift) and requires a leading minor to be a UNIT — which FAILS at the zero-core origin (`P[0,0]=0`).
> It does **NOT** resolve the singular zero-core `‖∏C'‖²`. The zero-core resolution (R1 / #111 / the
> (2,2,2) ladder) is a **BLOW-UP** with nontrivial Jacobian `|u|^{Mval(t)-1}` → `monomialThreshold`.
> **The general-M recursion node is BOTH-IN-SEQUENCE:** (B) blow up the rank-stratum center (codim
> `Mval(t)`, exceptional ratio `Mval(t)/2`, the monomial weight) → THEN (A) the det-1 Schur (unit Jac,
> reduces the chain, no weight) → recurse on the residual zero-core. The headline is `⨅ monomialThreshold`
> (B-flavored), NOT a clean `nReg/2` chain; the terminal leaf is monomial × (unit | smooth block), NOT a
> smooth L=1 block. The Schur SUBSTITUTION ALGEBRA below (all diff=0) is CORRECT and IS the (A) part of
> each node; what was imprecise is the claim it ALONE closes the resolution. Full corrected contract:
> `g118-correction-note.md` (this thread) + `codex/g118-A-vs-B-{prompt,answer}.md`. — pp-hall

**Task #109 (route-before-lines gate).** Validate the G3.2 recursion-closing step decorrelated on the first
non-trivial L=2 case (δ>0 genuinely reduces the chain), before any general-R1 formalisation lines.

**Verdict: WITNESS-CONFIRMED.** The recursion step is exact and threads for arbitrary chain length L. Two
independent legs converge: (1) pp-hall exact symbolic algebra (sympy, generic entries, all diff=0); (2)
Codex (xhigh) conceptual proof via transported line/hyperplane. One Lean caveat flagged (chart-locality).

## The claim (G3.2, restated precisely)
Chain `C = (C^(1),…,C^(L))`, `C^(s) : M^s × M^{s+1}`; product `P = C^(1)·…·C^(L)`. In a pivot chart where
the leading 1×1 minor `P[0,0]` is a UNIT, there are UNIMODULAR (det=1, analytic) `Q^(s)` with the
factor-wise transformed chain `∏_s (Q^(s-1) C^(s) (Q^(s))^{-1})` block-diagonalizing:
`Q^(0) P (Q^(L))^{-1} = blockdiag[E_1 (regular), Schur(P)]`, and **`Schur(P) = ∏_s C'^(s)`** for the REDUCED
chain `C'^(s)` of sizes `(M^s−1)×(M^{s+1}−1)`. Then (after the S1.5 parameter c-o-v) `‖∏C−B‖² = ‖reg‖² +
‖∏C'‖²`, so `rlctAt(F) = ½·(reg-dim) + rlctAt(‖∏C'‖²)`. Recurse on `C'`; well-founded (ΣM^s strictly drops).

## The certificate (pp-hall, exact symbolic — all diff = 0)
The explicit pivot chart: `Q^(0)=L0` (clears `C^(1)` col0 below the pivot), the threaded right-changes
`R_s` (clear each transformed factor's top row), inner `(R_s)^{-1} R_s` cancel in the product. Verified:
- **L=2, (3,3,3) r=1** → reduced (2,2,2): `core := (L0·P·R2)[1:,1:] = S1·C2' = Schur(P)`, diff=0. C1',C2' are 2×2.
- **L=2, (3,2,3) r=1** (non-square middle) → reduced (2,1,2): diff=0. C1'=2×1, C2'=1×2.
- **L=2, (4,3,2) r=1** (strictly decreasing) → reduced (3,2,1): diff=0.
- **L=3, (3,3,3,3) r=1** → reduced (2,2,2,2): `core = S1·S2·S3 = Schur(P)`, diff=0; the MIDDLE factor S2
  is two-sided-reduced (R1^{-1} left, R2 right) with NO conflict.
- **Multi-step peel, (3,3,3) r=2**: iterates (3,3,3)→(2,2,2)→(1,1,1) leaf; each step diff=0; ΣM 9→6→3.
  The (1,1,1) leaf is the determinant-ratio scalar (a smooth block) — the recursion bottoms out.
- **Reg-count match:** H¹+H^{L+1}−r regular generators; ½·that = `aoyagiLambda`'s regular shift
  `[−r²+r(H¹+H^{L+1})]/2`. For (3,3,3) r=1: 5/2. ✓ (the additivity's regular term is dimension-correct.)

Reproducibles: `/tmp/{g32_L2_333, g32_blockdiag, g32_factorwise, g32_L3, g32_r2, g32_additivity_real}.py`.

## The general-L mechanism (Codex, conceptual — confirms it threads, resolves the middle-factor issue)
Per vertex i, the transported line `u_i = C^(i+1)…C^(L) e_0` and covector `ψ_i = p^{-1} e_0^T C^(1)…C^(i)`
satisfy `ψ_i(u_i)=1`, `C^(i) u_i = u_{i-1}`, `ψ_{i-1} C^(i) = ψ_i`. Choose each `Q^(i)` ONCE from the pair
`(u_i, ψ_i)` (det-1 basis adapted to `R u_i ⊕ ker ψ_i`). Then every transformed factor
`D_i = Q^(i-1) C^(i) (Q^(i))^{-1} = blockdiag[λ_i, C'_i]`, `∏λ_i = p`, `C'_i` of size `(M^i−1)×(M^{i+1}−1)`.
Inner cancellation ⟹ `Q^(0) P (Q^(L))^{-1} = blockdiag[p, ∏C'_i]` and `= blockdiag[p, Schur(P)]`, so
`Schur(P) = ∏C'_i` exactly, for ALL L. **The middle factor is reduced ONCE** (one `Q^(i)` from `(u_i,ψ_i)`),
which simultaneously clears incoming and outgoing off-blocks because `C^(i) u_i = u_{i-1}`, `ψ_{i-1} C^(i)=ψ_i`
— NOT two independent Schur complements fighting. No L≥3 obstruction.

## The additivity is correctly scoped (NOT a norm-preservation of the unimodular Q's)
`‖∏C−B‖² = ‖reg‖² + ‖∏C'‖²` is NOT `‖Q0 P QL^{-1}‖² = ‖P‖²` (the Q's are unimodular, not orthogonal). It is:
G3.2 supplies (a) the chart / regular-E_r split (= `block_elimination` on `P`, the single-matrix case
ALREADY DONE) + (b) the residual core = `∏C'` (verified). The norm split is the **S1.5 smooth-block c-o-v
additivity (already proven)** applied to the chart's separated coordinates. B contributes 0 to the core block
(B's nonzero is the regular E_r), so the recursion's B' = 0 (the singular core). Cleanly factored:
band/regular dependency in S1.5; the chain-factorization in G3.2.

## The Lean caveat (the one structural refinement for the formaliser — Codex-flagged, pp-endorsed)
Do NOT formalise a single GLOBAL polynomial `Q^(i)` on the whole principal open `{P[0,0]≠0}` without a
basis-extension lemma there. The sound target: the transported-line/hyperplane construction, locally
analytic (or after refining to charts where a chosen coordinate of each `u_i` is a unit), where the det-1
adapted bases exist. For the recursion step + the RLCT chart argument, local-analytic suffices (the RLCT is
local at the origin). Define `C'_i := ` the lower-right block of the adapted transformed factor `D_i`.

## Net for the route-before-lines gate
G3.2 is **construction, not open math** — the recursion step is exact and threads for general L (verified
symbolically L≤3 + multi-step, conceptually all-L). The formalisation target is precise: the
transported-line/hyperplane adapted bases (chart-local), `D_i = blockdiag[λ_i, C'_i]`, `Schur(P)=∏C'_i`, +
the S1.5 norm split. REUSES `block_elimination` (single-matrix Schur, DONE) as the L=1 prototype +
`product_reduction`/S1.5 for the additivity. The recursion is well-founded (ΣM strictly drops; base = smooth
block leaf). **GATE: GO** — general-R1 formalisation may proceed on this route, with the chart-locality
caveat baked into the `Q^(i)` construction (local-analytic, not global-polynomial).

Decorrelation: pp-hall exact symbolic (5 scripts, all diff=0) + Codex xhigh conceptual (transported
line/hyperplane, all-L, the middle-factor resolution + the Lean caveat). Converged. Consult banked at
`codex/g32-recursion-{prompt,answer}.md`. (One Codex run hit a sandbox-pdf-read rejection; the reasoning-only
retry succeeded — the symbolic legs are independent of it regardless.)
