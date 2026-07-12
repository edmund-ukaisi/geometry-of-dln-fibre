# General-width QIP no-collapse — INDEPENDENT soundness hunt (decorrelated adversary)

**Seat:** pen-and-paper, `obstruction` direction. **Date:** 2026-07-12. **NO Lean, NO repo edits**
(only this file; scripts under `/tmp/nocollapse/`). **Charge (controller):** the prior off-sector hunt
(`offsector-independent-hunt.md`) refuted a §7 proof and flagged ONE residual `□`-risk it could not close —
the **general-width QIP no-collapse**. Target: hunt for a chain `M` + binding branch `B` where the true
(coupled) lct `< ½·minAdm(M)` (which would FALSIFY the finiteness result `□ : rlct ≥ ½·minAdm`), OR
establish a scoped structural reason no such collapse binds.

**Discipline.** Exact algebra for load-bearing claims (exact `minAdm`/`Mval` enumeration; exact toric /
monomial-arc upper bound; explicit Jacobian/measure computation on the resolution corner). Monte-Carlo used
ONLY as a guide (calibrated + paired-control), never to certify. Decorrelated `local-codex-consult` fired at
`xhigh`, **conclusion withheld**, framed neutrally ("compute the coupled resolution's lct at these binding
branches; can it fall below ½·codim, and why") — `/tmp/nocollapse/codex/{prompt,answer}.md`.

---

## ★ VERDICT

**NO COLLAPSE (scoped).** Across every design I could make exact or resolve, the true (coupled) lct at the
binding branch equals `½·minAdm` — it never falls below. The mechanism that could have driven it below (a
shared exceptional divisor from compounding corank-≥2 blocks) is computed explicitly and **raises, never
lowers**, the divisor ratio. Two independent lines (my exact algebra + a decorrelated Codex with the
conclusion withheld) converge on `rlct = ½·codim` for the sharpest deep-sharing binders `(4,4,4,4)` and
`(5,5,5,5)`.

The finiteness VALUE `½·minAdm` survives this hunt. The one thing I did **not** independently re-prove (and
name honestly): the **exhaustiveness** of Aoyagi's resolution at arbitrary width — that the disjoint
block-elimination cleanly closes at every peel with no missed divisor. That is the cited Aoyagi content; my
hunt supplies a positive structural reason for it (below) and finds no counterexample, but is not a proof of
it.

`NO COLLAPSE (scoped): the coupled resolution gives rlct = ½·minAdm at every binding branch checked
[all L=2 (AW-rigorous); single-corank-2 (3,3,4)/(2,2,4) exact; deep-sharing binders (3,3,3,4),(4,4,4,4),
(5,5,5,5) via the explicit shared-corner Jacobian + toric-UB + paired-control MC]; structural reason: the
disjoint peel makes F ∼ Σ_i r_i² U_i whose zero locus is the CORNER, so rlct = Σ_i d_i/2 = ½·Mval by
disjoint-sum ADDITIVITY (add, not min), and a shared radial variable r_j=r_1·τ_j carries a coordinate-change
Jacobian r_1^(#shared) that makes the discrepancies ADD — the shared divisor ratio stays Σd_i/2 and cannot
undershoot. Residual, NOT closed: exhaustiveness of the resolution at arbitrary width = cited Aoyagi.`

---

## 0. The object under attack (exact, from the repo)

`Mval M T = Σ_{j=0}^{L-1} (t⁽ʲ⁻¹⁾ − T_j)(M_{j+1} − T_j)` with `t⁽⁻¹⁾ = M₀`, over `Adm M` (weakly-decreasing
`T`, `T_{L-1}=0`, `T₀ ≤ min(M₀,M₁)`, `T_j ≤ M_{j+1}`); `minAdm M = min_{T∈Adm} Mval M T`
(`Foundations/Lambda.lean:35-63`, `Validate/RouteMLayerSplit.lean:51`). The layer-peel `minAdmRec` (same
file `:58`) is `min_t [(M₀−t)(M₁−t) + minAdmRec(t,M₂,…,M_L)]`. `□ = RouteMBoxThresholdFinite` asserts
`∫ ‖prod‖^{−2c'} < ⊤` for `c' < ½·minAdm`, i.e. `rlct ≥ ½·minAdm`. The equality `rlct = ½·minAdm` is the
no-collapse claim; a binding-branch collapse `rlct < ½·minAdm` would make the integral diverge for some
`c' < ½·minAdm` and FALSIFY `□`.

Instrument self-validated: exact `minAdm` (cone enumeration) = `minAdmRec` = all 13 published anchors
(`(2,2,2)→3`, `(3,3,4)→8`, `(4,4,2,2)→4`, `(2,2,4)→4`, `(5,3,4)→11`, `(4,4,4)→12`, …), 0 mismatches
(`/tmp/nocollapse/minadm.py`).

---

## 1. Where a collapse could hide — the census (exact)

The collapse mechanism (prior hunt F4 + R1 thread): a SHARED exceptional divisor. `d²(x²+y²)` has lct `½`
vs `(d₁x)²+(d₂y)²` lct `1` — identical widths, different lct. **Correction I made to the framing (FACT):**
neither is a collapse below `½·codim` — both EQUAL `½·codim` (`{d=0}` is codim-1, `½·codim=½`, matches; the
disjoint one has codim-2, `½·codim=1`, matches). The "collapse" of the prior hunt is relative to a *naive
additive/threshold* recursion, not relative to `½·codim`. A genuine soundness collapse is
`rlct < ½·codim` = genuine **non-mild-singularity** (like the *definite* square `(x²+y²)²`: lct `½ < 1`,
because `{x²+y²=0}` has no real points but the origin). DLN products avoid the definite trap via the
bilinear/indefinite structure (real points on every stratum = the base-field theorem). So the hunt =
a chain where the multilinear product still forces `rlct < ½·codim`.

Census of the collapse-prone binders (corank-≥2 partial-drop = coupled `diag(b)` block; `/tmp/nocollapse/census*.py`):
- **single corank-2** (like `(3,3,4)`): `(3,3,3,4)` minAdm 7, `(3,3,4,4)` minAdm 8, … (75 chains, L=3, w≤5).
- **deep-sharing** (corank-2 block feeding a coupled reduced core): smallest binding case `(4,4,4,4)`
  T=(2,1,0), minAdm 11, n=48; layer-1 residual 2×2 `Δ₁`, layer-2 residual 1×3.
- **strict double-corank-2 compounding** (two consecutive min-corank-≥2 partial layers — the "deep-factor
  sharing" leg the diagb cert flagged **unexercised**): first at `(5,5,4,5)` minAdm 15 and `(5,5,5,5)`
  T=(3,1,0) minAdm 17, n=75; residual 2×2 `Δ₁` at layer1 feeding a 2×4 `Δ₂` at layer2.

These three tiers are the exact targets.

---

## 2. Exact upper-bound probe — no TORIC collapse anywhere (FACT)

Monomial-arc (toric) upper bound `rlct ≤ min_a (Σa)/ord_a(F)`, `ord_a(F) = 2·min_{output entry} min-weight
path` (validated: `(x²+y²)²→½`, `d1²x²→½`; `/tmp/nocollapse/toric_run.py`). If any weight `a` gives
`UB < ½·minAdm`, that CERTIFIES a collapse. Result over all suspects:

    chain          minAdm  half   toricUB   verdict
    (5,5,5,5)        17    8.50   12.500    no toric collapse (UB >= half)
    (5,5,4,5)        15    7.50   10.357    no toric collapse
    (4,4,4,4)        11    5.50    8.000    no toric collapse
    (4,4,3,3)         8    4.00    5.500    no toric collapse
    (3,3,3,4)         7    3.50    4.714    no toric collapse
    (3,3,4,4)         8    4.00    5.500    no toric collapse
    (2,2,2,2)         3    1.50    2.000    no toric collapse
    (3,3,3,3)         6    3.00    4.500    no toric collapse

No monomial arc undershoots `½·minAdm`. (One-sided: toric UB is not tight — the true rlct is achieved
NON-torically, e.g. `(1,2,1)` true `½` < toric `1` — so this rules out only the crudest collapse. The
sharp tool is §4.)

---

## 3. Rigorous & exact no-collapse on the tractable tiers (FACT)

**L=2 (all widths) — rigorous, no collapse.** The L=2 core `‖A₂A₁‖²` is reduced-rank regression at true
rank 0; the learning coefficient is Aoyagi–Watanabe (2005), **proven** mildly singular, `= ½·minAdm`
(perm-invariant closed form `½·(xy − ⌊max(0,x+y−z)²/4⌋)`, `x≤y≤z` sorted; diagb cert cross-checked 11
published RRR values). Independent exact hand-checks I redid, all `= ½·minAdm`, no collapse:
`(1,n,1)`: `F=⟨a,b⟩²`, indefinite rank-`2n` form, rlct `½` = `½·minAdm(1,n,1)=½`;
`(2,1,2)`: `‖ba^T‖²=‖a‖²‖b‖²`, rlct `1`;
`(N,1,M)`: `‖a‖²‖b‖²`, rlct `min(N,M)/2`;
`(2,2,1)`: Morse on the `c^TA₁=0` stratum, rlct `1`;
`(1,4,4)`: `‖Wv‖²`, radial-`v` divisor ratio `2` and residual ratio `2`, rlct `2 = ½·minAdm`.

**Single corank-2 coupling `(3,3,4)` / atom `(2,2,4)` — exact.** The diagb cert (`verify-r1-diagb-334.md`)
resolved `(3,3,4)` to `4 = ½·minAdm` (radial `Δ` ratio `2`, inner shear factor `5/2`, min `2`; plus clean
`‖T‖²` `2`), literature-anchored (AW RRR `(3,3,4)→4`). I re-confirmed the coupling **atom** — the `(2,2,4)`
core `‖ΔS‖²`, `Δ` free 2×2, `S` free 2×4 — with a 2M-sample deep-tail MC: `lamS → 1.91–1.97 ≈ 2 = ½·minAdm`
(`/tmp/nocollapse`, frac 0.002–0.016). Threshold-only (naive) gives `3` at `(3,3,4)` (UNDER, wrong); the
coupled truth is the LARGER `4`. **The naive undershoots; the truth does not.**

---

## 4. The decisive mechanism — the disjoint peel + the shared corner (FACT, derived; Codex-confirmed)

The peel recursion **is** `minAdmRec`: block-eliminate the leading pivot (Aoyagi's ideal-preserving unit
Lemma) to `F ∼ ‖T‖² + ‖ΔS‖²` in **disjoint** variable sets, so by the Watanabe disjoint-sum rule
`rlct(F) = rlct(‖T‖²) + rlct(‖ΔS‖²) = ½·(clean charge) + rlct(reduced core)`. Iterating over layers, at a
branch `T` with per-layer charges `d_1,…,d_L`,

>   `F ∼ Σ_i r_i² U_i`   (disjoint blocks, `U_i = ‖free block of dim d_i‖²` generic, radial `r_i`).

**Why it ADDS, not MINs (the point the naive account gets wrong).** The zero locus is the **corner**
`r_1=⋯=r_L=0`: if only one `r_i=0` while some `r_j≠0`, the term `r_j²U_j` is a nonzero constant and
`F` is bounded away from `0`. So the singularity lives at the corner, where disjoint-sum additivity gives

>   `rlct = Σ_i rlct(r_i² U_i) = Σ_i d_i/2 = ½·Mval(T)`,

and `min_T ½·Mval = ½·minAdm`. Each `rlct(r_i²U_i) = d_i/2` is the Morse-radial value of a **free** `d_i`-dim
block (measure `r_i^{d_i−1} dr_i`, `F∼r_i²`, ratio `(d_i−1+1)/2 = d_i/2`). No `min`-collapse: the pieces are
ADDED (disjoint sum → rlct adds), not multiplied.

**The shared corner (compounding) — computed explicitly.** The collapse fear is that a shared exceptional
variable (one `a` for two coupled blocks) gets only ONE block's Jacobian boost while multiplying a large
sum of squares. Compute it. In the coupled sector `r_j = r_1·τ_j` (the shared radial), the coordinate change
`(r_1,r_2,…)→(r_1,τ_2,…)` has Jacobian `r_1^{(#shared−1)}`, so the measure

>   `∏_i r_i^{d_i−1} dr_i  ⟼  r_1^{(Σ_i d_i) − 1} · ∏_{j shared} τ_j^{d_j−1} · dr_1 ∏ dτ_j`,
>   while  `F ∼ r_1²(U_1 + Σ_j τ_j² U_j) ∼ r_1² · (unit)`.

The shared `r_1`-divisor therefore has `∫ r_1^{Σd_i − 1 − 2c} dr_1 < ∞ ⟺ c < (Σ_i d_i)/2`, i.e.

>   **ratio `= (Σ_i d_i)/2 = ½·Mval(T)`** — the SAME value; sharing MERGES the radial variables but the
>   discrepancy exponents `d_i−1` **ADD**, so the ratio does not drop.

For the sharpest binders (charges `d`):
`(4,4,4,4)` `d=(4,3,4)` → shared ratio `(4+3+4)/2 = 11/2 = ½·minAdm`;
`(5,5,5,5)` `d=(4,8,5)` → `(4+8+5)/2 = 17/2 = ½·minAdm`.
The shared exceptional variable occurs **once** in each generator (loss order stays `k=1`, `F∼a²`), while
its discrepancy accumulates — so sharing RAISES the discrepancy and cannot produce a smaller ratio.

**Decorrelated Codex (conclusion withheld) reached this independently** (`/tmp/nocollapse/codex/answer.md`):
`rlct₀(4,4,4,4)=11/2`, `rlct₀(5,5,5,5)=17/2`, both `= ½·codim`, "no compounding collapse"; its own
shared-corner measure `r^{10}τ₁²τ₂³` / `r^{16}τ₁⁷τ₂⁴` gives ratios `11/2`, `17/2`; verbatim: "sharing does
not make the loss vanish as `a⁴` … its generator order remains `k=1`, while its discrepancy increases.
Therefore no smaller ratio is created." Codex also **corrected my premise** (FACT worth recording): the
minimisers are NOT unique (`(4,4,4,4)`: `(2,1),(3,1),(3,2)`; `(5,5,5,5)`: `(3,1),(3,2),(4,2)`), and
`(4,4,4,4)`'s second residual block is `1×3` (corank-2 in one direction only) — the strict double-corank-2
pattern is genuine only at `(5,5,5,5)`-scale.

---

## 5. Paired-control MC — no collapse signal (GUIDE only)

To distinguish a real collapse from MC's downward bias, I calibrated the bias on **clean-binding controls**
(no partial drops ⟹ provably mildly singular ⟹ true `λ = ½·minAdm`) and checked whether the coupled targets
fall BELOW the control curve. POT-MLE estimator (exponential tail of `−log F` on the unit sphere; near-exact
at small `λ`: `(1,2,1)→0.501`, `(2,1,2)→1.000`). `/tmp/nocollapse/paired.py`:

    CONTROLS (mild; true=half)   half   MC        TARGETS (coupled)      half   MC     vs control curve
    (2,1,2,2)  n=8               1.00   0.85      (3,3,3,4) n=30         3.50   2.65   +0.06 ABOVE
    (3,2,2,3)  n=16              2.00   1.65      (4,4,4,4) n=48         5.50   3.58   +0.13 ABOVE
    (4,2,3,4)  n=26              3.00   2.28      (5,5,5,5) n=75         8.50   4.85   monotone, no dip
    (5,2,4,5)  n=38              4.00   2.90
    (5,3,3,5)  n=39              4.50   3.22
    (6,2,5,6)  n=52              5.00   3.34

Every coupled/deep-sharing target sits **on or slightly ABOVE** the mild-singular control curve at its
claimed `half` — the OPPOSITE of a collapse (a collapse would read noticeably BELOW). MC's bias is toward
UNDER-estimation, so the true values are `≥` MC, i.e. even further from a collapse. (Honest limit: at
`(5,5,5,5)` `half=8.5` MC is saturated — it cannot distinguish true `8.5` from a hypothetical `~6`; the
no-collapse there rests on §4 + toric + Aoyagi, not on independent numerics.)

---

## 6. What survives / most likely to break / next

- **Firmest (the scoped no-collapse).** rlct `= ½·minAdm` at every binding branch checked: all L=2
  (AW-rigorous), single-corank-2 `(3,3,4)`/`(2,2,4)` (exact), deep-sharing `(4,4,4,4)`/`(5,5,5,5)` (explicit
  shared-corner Jacobian ratio `= ½·Mval`, toric-clean, MC-paired no-dip, Codex-confirmed). The structural
  reason — disjoint peel `F∼Σr_i²U_i` (corner ⟹ additivity ⟹ `Σd_i/2`; shared radial ⟹ discrepancies add,
  ratio unchanged) — shows sharing **raises, never lowers** the ratio. **The finiteness VALUE `½·minAdm`
  is not falsified; I could construct no collapse and the mechanism argues one cannot exist.**
- **Most likely to break it / the one thing NOT closed.** The **exhaustiveness** of Aoyagi's resolution at
  arbitrary width — that the ideal-preserving block-elimination cleanly yields the disjoint `Σr_i²U_i` at
  EVERY peel with `Δ` genuinely free, `S` a free reduced product, and **no missed divisor**. §4 assumes this
  (verified exactly only at `(3,3,4)`/`(2,2,4)`); it is the cited Aoyagi content, not re-proved here. A
  falsification of `□` would require exactly such a missed divisor at some deep binder — which the shared-
  corner computation says does not arise, but which I did not prove in general.
- **Next construction that would settle the open part.** (a) An EXACT symbolic resolution of one strict
  double-corank-2 binder (`(5,5,5,5)` or a distilled two-2×2-blocks-in-series core) verifying the disjoint
  decomposition `F ∼ ‖T₁‖²+‖T₂‖²+‖T₃‖²` holds with all three pieces in disjoint variable sets and each `Δ`
  free — this either confirms exhaustiveness at the deep-sharing witness or exposes the first non-disjoint
  peel. (b) Reconcile Aoyagi's `diag(b)` symbolic-support recursion's completeness claim with the shared-
  corner Jacobian accumulation of §4 as a width-uniform lemma (`shared-divisor ratio = ½·Σcharge`), which
  would upgrade this scoped negative toward a proof.

---

## Reproducible scripts (exact; `/tmp/nocollapse/`)

- `minadm.py` — exact `Mval`/`minAdm`/`minAdmRec`/binding branches; 13/13 anchors, 0 mismatch.
- `census.py`, `census2.py` — corank-≥2 / deep-sharing / strict-compounding binder census.
- `toric_run.py` — exact monomial-arc UB collapse detector (no toric collapse on any suspect).
- `fastrlct.py`, `paired.py` — vectorised sphere-MC (POT-MLE), clean-control bias curve vs coupled targets.
- `codex/{prompt,answer}.md` — decorrelated consult (conclusion withheld); independently `rlct=½·codim`,
  shared-corner ratios `11/2`, `17/2`, "no compounding collapse."

Load-bearing exact excerpt (the shared corner — the whole no-collapse mechanism in one line):

    # disjoint peel:  F ~ Σ_i r_i^2 U_i ,  measure ∏ r_i^{d_i-1} dr_i ,  d_i = per-layer charge
    #   zero locus = CORNER r_1=..=r_L=0  ⟹  rlct = Σ_i d_i/2 = ½·Mval   (disjoint-sum ADD, not min)
    # shared sector r_j = r_1·τ_j :  Jacobian r_1^{#shared-1}  ⟹  measure r_1^{(Σ d_i)-1} ∏ τ_j^{d_j-1}
    #   F ~ r_1^2·(unit)  ⟹  shared r_1-divisor ratio = (Σ d_i)/2 = ½·Mval  (SAME; sharing cannot undershoot)
    # (4,4,4,4) d=(4,3,4) → 11/2 = ½·minAdm ;  (5,5,5,5) d=(4,8,5) → 17/2 = ½·minAdm
