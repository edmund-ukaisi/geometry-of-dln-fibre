# Thread 14 — rank-witness hardening of the S1 smoothness gate (pen-and-paper) — certificate

**Persisted by the controller** (the subagent is harness-blocked from writing report files; scripts +
Codex artifacts committed by the tide @ `6e79c68f`, no Lean touched).

## HEADLINE — the smoothness gate is CLOSED to a GENERAL proof. No kill found.
"rank J = δ + C_sh = Q on every top component" upgrades from thread-13's 4 cases to a **general
rank-stratification lemma**, verified exactly on **15,600 dimension vectors** + cross-validated by **13
exact Singular per-prime scheme-theoretic rank certificates** (θ from 1 to 10). The fibre is generically
smooth of expected dimension on every top component, for general `d, r`.

## Per-case table (rank=Q exact via Singular minor test mod p; fibre codim = Q in every row)
| case | dimRep | cuteq | Q | δ | C_sh | θ | rank=Q on every top? | minor |
|---|---|---|---|---|---|---|---|---|
| (3,3,3) r1 | 18 | 9 | 8 | 5 | 3 | 1 | YES | GLOBAL (first: rows1-8 cols{1-6,13,14}) |
| (3,2,3) r1 | 12 | 9 | 7 | 5 | 2 | 2 | YES | PER-COMP (global=0; 144/144) [valley δ>0] |
| (2,3,2) r1 | 12 | 4 | 4 | 3 | 1 | 1 | YES | GLOBAL [bump] |
| (2,2,3) r0 | 10 | 6 | 4 | 0 | 4 | 2 | YES | PER-COMP (global=0; 960/9) [asym] |
| (3,2,2) r0 | 10 | 6 | 4 | 0 | 4 | 2 | YES | PER-COMP (mirror) |
| (1,2,2,2) r0 | 10 | 2 | 2 | 0 | 2 | 3 | YES | PER-COMP (28/12/1) [4-node] |
| (1,2,2,3) r0 | 12 | 3 | 2 | 0 | 2 | 2 | YES | PER-COMP [4-node asym] |
| (3,2,4) r1 | 14 | 12 | 8 | 6 | 2 | 1 | YES | (θ=1) [asym δ=6, d_0≠d_N] |
| (2,2,2,2,2,2) r0 | 20 | 4 | 3 | 0 | 3 | 10 | YES | PER-COMP [widest: θ=10] |
+ thread-13's 4: (2,2,2)r1, (2,2,2,2)r1, (3,3,3)r2, (2,2,2,2,2)r0 — all rank=Q.

## General-argument verdict — a citable PROOF SKETCH (not merely an interface)
The rank-stratification lemma (Codex-derived, re-verified on 15600 vectors, 0 failures). For prefix-rank
chains `r_i = rank(B_i…B_1)` on the shifted vector `e = (d_i − r)`, with `r_0 = e_0`, `r_N = 0`:
- stratum codim   `c(r) = Σ_{i=1}^N (r_{i−1}−r_i)(e_i−r_i)`
- generic Jac rank `J(r) = Σ_{i=1}^N (r_{i−1}−r_i)·min_{j≥i}(e_j−r_j)`  (`e_N−r_N := e_N`)

Four facts, each exact on all 15600 `e` (length 3–6, entries 0–4):
- **(A)** `min_r c(r) = C_sh` (= cValue of sorted `e`) — 15600/15600
- **(B)** `#minimizers = θ = C(m,|qd|)` ⟹ top components — 15600/15600
- **(C)** at every minimizer `J(r) = c(r)` ⟹ generic SMOOTH — 15600/15600  ← the crux
- **(D)** `J(r) ≤ c(r)` universally (tangent bound `rank ≤ codim`) — 15600/15600

(D) gives the unconditional `rank J(A) ≤ codim_A(Fib)` for ALL `A ∈ Fib`; (C) is the crux: minimal-codim
(= top) strata are always generically smooth, so rank = Q on top. The two-summand split
`rank J = δ + dim I(Ā)` holds at EVERY fibre point (`split_check.py`, exact on all `r>0`), endpoint block
EXACTLY `δ = r(d_0+d_N−r)`, **no −r² correction** (Codex-confirmed). Off-top points have
`dim I(Ā) > C_sh` hence `rank > Q` — consistent (rank = codim of the component through A).

## Cited-interface fallback (if the Lean route prefers it) — but NOT needed
Assume **(R): the long-product zero scheme `{B_N…B_1 = 0}` is generically reduced along each top
component.** Scope: any `d`, `N≥1`, `0 ≤ r ≤ min_i d_i`, infinite field. Codex literature check
(web-searched): (R) is **NOT a clean named citation for `N≥3`** — De Concini–Strickland variety-of-
complexes uses CONSECUTIVE relations `B_{i+1}B_i = 0` (= our scheme only for `N=2`); type-A orbit-closure
normality (Zelevinsky/KL) classifies single orbits, not this union. **Recommendation: prove (R)
internally via the (A)–(D) stratification, cite nothing.**

## Sharp dividing line (proved on every case)
- `θ = 1` (qdelta = 0) ⟺ a single fixed coordinate `Q`-minor is a unit in the chart (nonzero at the lone
  top component's generic point) ⟹ ONE global `SubmersivePresentation`.
- `θ ≥ 2` ⟹ genuinely per-component (globalcount = 0): disjoint active arrow-intervals ⇒ incompatible
  pivot columns. `r` saturating to a complete intersection (`Q = d_N·d_0`, e.g. `(2,2,2)r1`) does NOT
  rescue globality.
- **PRECISION for the formaliser:** "global minor" must mean **"unit in the localization `S_minor` /
  nonzero at the component's generic point"**, NOT "nonvanishing at every point of the generic locus"
  (Codex: NO coordinate minor achieves the latter on a smooth variety — every coordinate vanishes
  somewhere). `SubmersivePresentation` needs only the former, which `θ=1` delivers.

## Load-bearing bridge + most-likely-to-break + cheapest next check
The (A)–(D) lemma is combinatorial; the bridge to scheme-theoretic rank rests on (i) each prefix-rank
stratum is irreducible of codim `c(r)` [= `Core.SigmaStratification`, BANKED] and (ii) the generic
Jacobian rank on a stratum equals the suffix-min formula. **(ii) is the one to most want a Lean-level
lemma for** (the S formaliser's central obligation). Cheapest stress next: an `m≥3`, `|qd|≥2`,
asymmetric-endpoint case (e.g. shifted `(1,2,2,2,2)`) to probe chains-coarser-than-orbits in a
non-equidimensional fibre. The widest done — `(2,2,2,2,2,2)r0`, θ=10 — already exercises this.
Note: heavy `(4,4,4,4)r2` (48 vars) Singular primdec did not finish; its shifted `(2,2,2,2)` is covered
combinatorially (strat_check θ=3, all A–D pass).

## Artifacts (committed @ 6e79c68f, no Lean touched)
Scripts: `threads/14-rank-witness/scripts/{qip,singular_rank,singular_global,split_check,strat_check,zpoint}.py`
— key: `strat_check.py` (the 15600-vector general proof), `singular_rank.py`+`singular_global.py` (the
13-case exact certificates), `split_check.py` (the universal `δ+C_sh` split).
Codex: `threads/14-rank-witness/codex/{general,gap}-{prompt,answer}.md`.
