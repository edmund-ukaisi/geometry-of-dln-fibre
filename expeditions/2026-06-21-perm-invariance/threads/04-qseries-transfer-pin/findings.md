# Thread 04 — PEEL local transfer identity: PINNED

> Homed by the controller from `pin-transfer`'s report (harness `.md`-write block). Scratch verifier +
> Codex artefacts committed at `6eb7705`. All claims exact-arithmetic verified (0 float).

**VERDICT: PINNED.** The PEEL local transfer identity is **`N` nested applications of the single `N=1`
Durfee identity**, peeled block-by-block, glued by an elementary arithmetic split of the exponent.
**`q`-Vandermonde / `q`-Chu–Vandermonde / Gaussian binomials are NOT load-bearing** — this CORRECTS
thread-03 §4's recorded Codex read ("`q`-Vandermonde over the `b_i` blocks × the `N=1` Durfee"). Only ONE
classical `q`-series primitive is needed. A fresh decorrelated Codex (hypothesis withheld) independently
reached the same conclusion and supplied the cleaner single-induction form + flagged the one subtle Lean step.

## The identity
`P_{d_N} · ∏_{i<N} P_{b_i} = ∑_x q^{Δ_b(x)} · P_{x_N} · ∏_{i<N} (P_{b_i−x_i} · P_{x_i})`,
sum over `x` with `0≤x_i≤b_i` (i<N), `x_N≥0`, `∑_i x_i = d_N`, `Δ_b(x)=∑_{0≤a<u≤N}(b_a−x_a)x_u`, `b_N:=0`.

## Decomposition (confirmed/corrected)
- **(D) the ONLY classical `q`-series input — `N=1` Durfee:**
  `P_a P_b = ∑_{r=0}^{min(a,b)} q^{(a−r)(b−r)} P_{a−r} P_r P_{b−r}`. The transfer at `N=1` IS (D) verbatim
  (`a=d, b=b_0, r=x_0`), so any primitive set must imply it — strictly necessary.
- **(E) exponent split (pure arithmetic — a POLYNOMIAL identity in indeterminates; sympy `expand==0`, N=1..6):**
  `Δ_b(x) = (b_0−x_0)(d−x_0) + Δ'_{b'}(x_1..x_N)`, where `Δ'` is the same functional on the dropped-first-index
  tuple and `d−x_0 = ∑_{u≥1} x_u`. Telescopes the peel.
- **CORRECTION to record:** thread-03 §4's "`q`-Vandermonde × Durfee (INFERENCE)" is wrong — `q`-Vandermonde /
  Gaussian-binomial is confirmed UNUSED here. (The `q`-binomial *inverse* is still needed elsewhere — S3's
  `∑ P_s xˢ` inversion — but NOT for the transfer.)

## Classical-input lemma list (Lean-targetable)
1. **(D) `N=1` Durfee identity** — THE primitive; absent from Mathlib v4.29; the base-case grind (its own
   Durfee-square / `q`-binomial proof is the deepest sub-target).
2. **(E) exponent split** — `ring` after a `Finset` reindex; no `q`-series content.
3. **staged↔flat index-set equivalence** — a `Finset.sum_bij`; THE subtle step (below).
4. **finite distributivity/reindexing** — reuse Mathlib (`Finset.prod_sum`, `Finset.sum_bij`).

## Recommended Lean target (Codex's staged single-induction)
Running residual `s_0=d`, `s_{j+1}=s_j−x_j`; admissible `0≤x_j≤min(s_j,b_j)`; partial exponent
`E_m=∑_{j<m}(b_j−x_j)s_{j+1}`. Induct on `m` (0..N) with invariant `Claim(m)`; base `m=0` trivial; step
applies (D) ONCE to the single unexpanded pair `P_{s_m}P_{b_m}` (`a=s_m,b=b_m,r=x_m`), new exponent
`E_m+(s_m−x_m)(b_m−x_m)=E_{m+1}`; terminal `x_N:=s_N`, `E_N=Δ_b(x)`. One Durfee per step, nothing else.
(Equivalent peel-first list-recursion also verified; staged form preferred — one induction, one invariant.)

## Single most-likely-to-break Lean step
The terminal reindexing — staged admissibility `x_j≤min(s_j,b_j)` indexes the SAME finite sum as flat
`x_i≤b_i, ∑x=d`. De-risked: for any flat non-neg tuple summing to `d`, `s_j=∑_{u≥j}x_u≥x_j` automatically,
so the `x_j≤s_j` cap is FREE given `∑x=d`. Verified as `q`-series AND as sets-of-tuples equality, 0 mismatch.

## Verification (`scratch/verify_transfer_pin.py`, exact integer, 0 float)
- (D) Durfee `a,b∈0..8` — OK.
- (E) symbolic polynomial identity N=1..6 (sympy) — OK; (E) numeric 300 000 random (N≤5,b≤5,x_N≤5) — 0 mismatch.
- Full chain over 28 `(b;d)` incl. wide/non-monotone/zeros/equal-blocks, N=1..4: endpoint LHS==RHS,
  peel-first, IH-step collapse, full recursion — all 0 mismatch.
- Staged form == flat: `q`-series AND index-set equality, same 28 — 0 mismatch.
- No regression: thread-03 `verify_peeling.py` / `verify_induction.py` still PASS.

## Impact on the build ladder
M2 shrinks: the PEEL/transfer (M3) needs ONLY the `N=1` Durfee identity (D) as its classical input, not
`q`-Vandermonde. M2's `q`-Vandermonde is needed (if at all) only for S3's `q`-binomial inversion in M4 —
re-scope M2 to: (D) Durfee [for M3] + (the S3 `q`-binomial inverse) [for M4], and check whether S3 even
needs the named Gaussian-binomial or can be done by its own induction (thread 03 flagged it AVOIDABLE).

Artifacts (committed `6eb7705`): `scratch/verify_transfer_pin.py`, `codex/decompose-{prompt,answer}.md`.
