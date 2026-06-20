# Rung-0 design spec — foundational definitions + goal skeleton (Aoyagi-Full)

- **Seat:** `pp` (pen-and-paper), thread 01. **No Lean here** — this is the Lean-ready *design*.
- **Source:** Aoyagi 2023 (`aoyagi-2023-neural-networks-preprint.pdf`), read from the page images:
  Definition 1 + Lemma 1 + Definition 2 (pp.5–6), the setup + Definition 3 + Theorem 2 (pp.7–9),
  Lemma 2 / Theorem 3 (pp.10–13), Theorem 4 + Definition 4 + the recursive blow-up (pp.14–21),
  the candidate / minimisation / Lemma 3–5 (pp.22–27). All arithmetic below independently
  re-derived and exact-rational cross-checked (`/tmp/aoyagi_*.py`); numbers are reproducible.
- **Status of each definition:** SOLID (faithful + Lean-ready) unless flagged. Two genuine seams are
  flagged in §7 (the analytic order θ; the Def-3 selection regime).

The spine that everything else rests on (verified, §2/§5):
> `λ = [−r² + r(H⁽¹⁾+H⁽ᴸ⁺¹⁾)]/2 + λ_core`, with **`λ_core = ½·min_T M(T)`** over the genuine
> admissible cone of exponent vectors `T`, and `min_T M(T) = ½(Σqᵢ² − Σmₖ²)` (the clean form).
> Both the value `λ` and the order `θ` are reproduced on every numerical ground-truth case.

---

## 0. Notation and the parameter space

L-layer linear network. **Widths** `H : Fin (L+1) → ℕ`, written `H⁽¹⁾,…,H⁽ᴸ⁺¹⁾`; the model is
`Y = (∏_{s=1}^L A⁽ˢ⁾) X + noise`, so `H⁽¹⁾` is the **output** dimension and `H⁽ᴸ⁺¹⁾` the **input**
dimension (Aoyagi p.8). Layer `s ∈ {1,…,L}` is a matrix `A⁽ˢ⁾` of size `H⁽ˢ⁾ × H⁽ˢ⁺¹⁾`.

> **Lean shape.** A network width vector is `H : Fin (L+1) → ℕ`. A parameter is a dependent tuple
> `A : ∀ s : Fin L, Matrix (Fin (H s.castSucc)) (Fin (H s.succ)) ℝ`. The parameter space is `≅ ℝ^N`
> with `N = Σ_{s} H⁽ˢ⁾·H⁽ˢ⁺¹⁾`; carry it as the dependent tuple and only flatten to `ℝ^N` when the
> measure substrate (S0-measure) needs `EuclideanSpace`.

The matrix product `prod A : Matrix (Fin H⁽¹⁾) (Fin H⁽ᴸ⁺¹⁾) ℝ` is the left-fold
`A⁽¹⁾·A⁽²⁾·…·A⁽ᴸ⁾`. **Reduced widths** `M⁽ˢ⁾ := H⁽ˢ⁾ − r` for `s = 1,…,L+1`, where `r` is the rank
of the true product (these are the only widths that enter the singular core; Theorem 3, p.13).

**Σ_X drops out.** Aoyagi's input covariance `Σ_X ≻ 0` enters the loss only through a fixed positive
weighting; by Lemma 1 (RLCT depends only on the ideal, §S1) the RLCT is unchanged by the regular
change of coordinates that whitens `Σ_X`. *Record this; do not carry `Σ_X` in `dlnLoss`* — the
identity-covariance square-Frobenius loss is RLCT-faithful. (This is the L1-level justification; the
clean statement is the `Σ_X`-elimination corollary of S1.)

---

## 1. `dlnLoss` and `optimalSet`

```text
def dlnLoss (H r) (B : Matrix (Fin H⁽¹⁾) (Fin H⁽ᴸ⁺¹⁾) ℝ) (A : Params H) : ℝ :=
  ∑ i, ∑ j, ((prod A − B) i j)^2          -- square-Frobenius ‖prod A − B‖²_F

def optimalSet (H r) (B) : Set (Params H) := { A | prod A = B }   -- the fibre mult⁻¹(B)
```

- `dlnLoss` is `‖prod A − B‖²_F`, an honest polynomial (hence real-analytic) in the entries of `A`.
  Faithful to Aoyagi's Kullback function `K(w)` for the Gaussian model, which reduces to the
  square-Frobenius distance up to the fixed `Σ_X` weight handled above (p.6, p.8).
- `optimalSet H B = dlnLoss⁻¹{0} = {A | prod A = B}` since the loss is a sum of squares, zero iff
  `prod A = B`. This is the locus over which the global RLCT is the infimum (the fibre).
- **Faithfulness note (caveat-next-to-claim):** the headline takes `B = ∏A^{*(s)}` of rank `r`. The
  theorem holds for any target `B` of rank `r` because the optimal set and the local geometry depend
  on `B` only through its rank (Lemma 2 / Theorem 3 reduce any rank-`r` `B` to the block-normal
  `diag(E_r,0)` by regular row/column operations, which are RLCT-preserving). State `(hB : B.rank = r)`.

**Lean-ready: YES.** Pure polynomial + a set comprehension. No measure theory needed for these two.

---

## 2. `rlctAt` — the real log-canonical threshold (Aoyagi Definition 1)

**Source (Def 1, p.5).** `λ_{w*}(F,φ) = sup{ c : ∫_U |F(w)|^{−kc} φ(w) dw < ∞ }`, with `k = 1` over
ℝ. So over the reals the integrand is `|F|^{−c}`. `φ` is a `C^∞` bump with compact support in a
neighbourhood `U` of `w*`. Stated equal to the largest pole of the zeta function
`Z(z) = ∫_U |F|^{z} φ dw` (`z ∈ ℂ`, analytically continued). For `φ(w*) ≠ 0` the value is
**independent of φ**, written `λ_{w*}(F)`. For an ideal `J = ⟨F₁,…,Fₘ⟩`:
`λ_{w*}(J) = λ_{w*}(F₁²+…+Fₘ²)` (Def 1 last line + Lemma 1).

**Design (the integral-sup form, bump removed via existential neighbourhood).**

```text
def rlctAt (F : Params H → ℝ) (w* : Params H) : ℝ≥0∞ :=
  sSup { (c : ℝ≥0∞) | ∃ c' : ℝ≥0, (c : ℝ≥0∞) = c' ∧
          ∃ U ∈ 𝓝 w*, IntegrableOn (fun w => |F w| ^ (−(c' : ℝ))) U volume }
```

Read: the supremum (in `ℝ≥0∞`) of the down-set of real exponents `c' ≥ 0` for which `|F|^{−c'}` is
locally integrable near `w*`. Value in `ℝ≥0∞` so the locally-nonvanishing case (`F(w*) ≠ 0`, every
`c'` admissible) gives `+∞` and `dlnLoss⁻¹{0}` complement is handled uniformly.

> **Precondition (required, not optional — Codex §6.2).** `rlctAt` is the *standard* RLCT only for `F`
> **real-analytic and `≢ 0` near `w*`**. For an arbitrary measurable `F` whose zero set has positive
> measure the sup collapses to `0` (outside RLCT theory). `dlnLoss B` is polynomial ⇒ real-analytic,
> so the precondition holds for every use in this development; state it on the S1/S2 theorems.

> **Pole-sign convention (Codex §6.1, the "most likely bug").** With the zeta function written
> `Z(z) = ∫_U |F|^z φ`, the largest pole sits at **`z = −λ`** (not `+λ`); `θ` is the order of the pole
> *there*. (Cheap detector: `F = x²` on ℝ gives `λ = 1/2`, pole at `z = −1/2`, since `|x|^{−2c}` is
> integrable near 0 ⟺ `c < 1/2`.) The integral-sup form above avoids the sign hazard entirely; record
> the `z=−λ` reading only when invoking the zeta-pole equivalence (an S1 lemma).

**Why the bump may be dropped for the *value*.** A `C^∞` bump `φ` with `φ(w*) > 0` is, on a small
enough `U₀`, sandwiched `0 < a·𝟙_{U₀} ≤ φ ≤ b·𝟙_{U₁}` (`U₀ ⊂ supp φ ⊂ U₁`, `a,b > 0`). Hence
`∫|F|^{−c}φ` is finite ⟺ `∫_{U₀}|F|^{−c}` is finite, for some neighbourhood. The *existential over
neighbourhoods* `∃ U ∈ 𝓝 w*` recovers exactly the bump-independent threshold (Def 1's `φ`-independence
statement). So `rlctAt F w* = λ_{w*}(F)` of Def 1 for the **value** (the sup). [Standard; submitted
to Codex for audit — §6.]

**`rlctAt` for an ideal / the loss.** Because `dlnLoss B = Σ((prod·−B)ᵢⱼ)²` is *already* the
sum-of-squares of the generators `(prod·−B)ᵢⱼ` of the ideal `⟨prod·−B⟩`, we have
`rlctAt (dlnLoss B) w* = λ_{w*}(⟨prod·−B⟩)` directly — no separate ideal wrapper needed for the
headline. Keep a lemma `rlctAt_ideal : rlctAt (∑ Fᵢ²) = λ(⟨Fᵢ⟩)` as the S1 interface; the headline
uses the `∑Fᵢ²` form, which is what `dlnLoss` *is*.

**Faithfulness checklist (all to confirm in S1 / S2, flagged where not yet certain):**
- *Sign/convention:* `−c` exponent (k=1 real). ✔ matches Def 1 page image.
- *Down-set + sSup:* the admissible `c'` form an interval `[0, λ)` or `[0, λ]`; the sup is the
  threshold; the threshold itself is generically **not attained** (the integral diverges *at* `c = λ`).
  So `sSup` (not `sup` of a max) is the faithful operation. ✔ [Codex audit §6 q1c.]
- *φ-independence:* encoded by the `∃ U ∈ 𝓝 w*` (no φ in the definition). The *theorem* that this
  equals the bumped Def-1 value is an S1 lemma.
- *Measure-zero of `{F=0}`:* `F` real-analytic, `≢ 0` near `w*` ⟹ `{F=0}` has Lebesgue measure 0, so
  `|F|^{−c}` is finite a.e. and `IntegrableOn` is the right predicate. The faithful hypothesis is
  *`F` real-analytic and not locally `≡ 0`*; `dlnLoss B` restricted to the relevant chart is
  polynomial hence analytic. ✔ to encode.

**Lean-ready: YES for the statement; the supporting theory (φ-independence, zeta-pole equivalence) is
S1, not S0.** The S0 deliverable is the `def` above + the typing. The *equality to Def 1* is proven in
S1. Flag: Mathlib has `MeasureTheory.IntegrableOn`, `𝓝`, `sSup` on `ℝ≥0∞`; it does **not** have RLCT,
so this `def` is new (expected per brief standing decision 5).

---

## 3. `rlctOrderAt` — the order θ (Aoyagi's pole multiplicity) — SEAM FLAGGED

**Source (Def 1, p.5).** `θ_{w*}(F,φ)` = the **order** (multiplicity) of the largest pole of the zeta
function `Z(z) = ∫_U |F|^{z} φ` at `z = −λ`. Theorem 2 gives the closed form `θ = a(ℓ−a)+1`.

**Design (faithful analytic definition).**

```text
def rlctOrderAt (F : Params H → ℝ) (w* : Params H) : ℕ :=
  the order of the pole of (z ↦ ∫_U |F|^z φ), meromorphically continued, at z = −(rlctAt F w*)
```

This is the faithful object but is **analytically heavy**: it needs meromorphic continuation of
`∫|F|^z φ` (Atiyah / Bernstein–Gelfand `|f|^s`), which Mathlib lacks entirely.

**SEAM (controller standing decision 6).** The combinatorial order `θ = a(ℓ−a)+1` is the *deliverable*;
the analytic-multiplicity definition is the at-risk item. Two things must NOT be conflated:

1. **`θ` is NOT the number of minimising exponent vectors `T`.** Independently verified
   (`/tmp/aoyagi_theta.py`): for `H = (2,2,2,2,2)`, the genuine admissible cone has **6** distinct
   minimisers of `M(T)`, but `θ = a(ℓ−a)+1 = 5` (ℓ=4, a=2). A naive `Card{argmin T}` over-counts.
   Aoyagi's `θ = max_u Card{ j : (h_j+1)/(2k_j) = λ }` is the per-**chart** count of monomial
   directions that *tie* the minimum ratio — a multiplicity *inside one chart*, proven `= a(ℓ−a)+1`
   by Lemmas 4–5 within the resolution. This is a genuinely different, harder object.
2. **Recommended landing:** define `aoyagiθ H r := a(ℓ−a)+1` combinatorially (total, via the
   minimisation argmin structure / Def-3 data) and prove it equals the **chart-count** `θ` produced by
   the resolution R1 + the S2 chart formula. Carry `rlctOrderAt` (the analytic pole order) as a named
   placeholder and assert `rlctOrderAt = chart-count θ` only as the **S2-order** half of the cited
   interface (the S2 citation already returns the order as `max chart count`, §5). The analytic
   pole-order = chart-count equality is then *inside* the single S2 citation, not a new gap.

**Lean-ready: the combinatorial `aoyagiθ` YES; the analytic `rlctOrderAt` only as a placeholder whose
equality to the chart-count rides inside S2.** Flagged honestly (§7).

---

## 4. `aoyagiλ` — the closed form, defined via the total minimisation

This is the heart. The controller's call (define via the minimisation, total) is **correct**, but the
precise minimisation must be stated carefully — naive "extremise the clean form over ℓ" is WRONG
(verified, §4.3). Here is the faithful, total construction.

### 4.1 The candidate value `M(T)` and the admissible cone (Aoyagi p.22)

For an exponent vector `T = (t⁽¹⁾,…,t⁽ᴸ⁾)` the resolution produces a candidate RLCT contribution
`½·M(T)` (the `½` is the `1/(2k)` of the monomial formula with the Jacobian giving the numerator),
where (Aoyagi p.22, original form, transcribed from the image):

```text
M(T) = (M⁽¹⁾ − t⁽¹⁾)(M⁽²⁾ − t⁽¹⁾)  +  ∑_{j=2}^{L} (t⁽ʲ⁻¹⁾ − t⁽ʲ⁾)(M⁽ʲ⁺¹⁾ − t⁽ʲ⁾)
```

The **genuine admissible cone** `Adm(M)` (the exponent patterns the blow-up actually realises, with
`t̃ = min_layers t = 0`, Def 4 partial order):

```text
T ∈ Adm(M)  ⟺  t⁽¹⁾ ≥ t⁽²⁾ ≥ … ≥ t⁽ᴸ⁾ = 0,   t⁽ʲ⁾ ≥ 0,
               and every factor above is ≥ 0, i.e.
               t⁽¹⁾ ≤ min(M⁽¹⁾, M⁽²⁾)   and   t⁽ʲ⁾ ≤ M⁽ʲ⁺¹⁾  (j = 2,…,L).
```

(The weak-decrease `t⁽ʲ⁻¹⁾ ≥ t⁽ʲ⁾` is Def 4's `T ≤ T'` partial-order discipline reparametrised; the
`t⁽ᴸ⁾ = 0` is the candidate's `t̃ = 0`; the per-factor `≤ M⁽ʲ⁺¹⁾` are the block-size bounds making the
Jacobian-exponent nonnegative. This is the cone over which the resolution's candidate ratios live.)

### 4.2 The definitions

```text
def Mval (M : Fin (L+1) → ℕ) (T : Fin L → ℕ) : ℤ := …            -- the polynomial above
def Adm  (M) : Finset (Fin L → ℕ) := …                            -- the finite admissible set
def lambdaCore (M) : ℚ := (1/2) * (↑(Finset.inf' (Adm M) … (Mval M)))   -- ½·min_T M(T)
def aoyagiλ (H : Fin (L+1) → ℕ) (r : ℕ) : ℚ :=
  (−(r:ℚ)^2 + r*(H 0 + H (L)))/2  +  lambdaCore (fun s => H s − r)
```

`Adm M` is a **finite** set (each `t⁽ʲ⁾` ranges over `0..max M`), so `min_T M(T)` exists
unconditionally — `aoyagiλ` is **total** with no Def-3 dependence. `Finset.inf'` needs `Adm M`
nonempty: `T = 0` (all zeros) is always admissible, so `Adm M ≠ ∅`. ✔

### 4.3 The clean closed form (proven equal where Def 3 applies; this is A1)

```text
lambdaCore (M) = (1/4) ( Σ_{i=1}^{ℓ} qᵢ²  −  Σ_{k=1}^{ℓ+1} mₖ² )      [the clean form]
```
where `m₁ ≤ … ≤ m_{ℓ+1}` are the `ℓ+1` smallest reduced widths (the Def-3 set ℳ), `P = Σ mₖ`, and
`q` is the **balanced ℓ-split** of `P` (`a := P mod ℓ` copies of `⌈P/ℓ⌉`, `ℓ−a` copies of `⌊P/ℓ⌋`).
Equivalently `2·lambdaCore = ½(Σqᵢ² − Σmₖ²)` (the brief's trusted spine).

**Verified (`/tmp/aoyagi_bridge.py`):** over all reduced-width vectors of length ≤4, entries 0..6,
`lambdaCore = ½·min_T M(T)` **equals** the clean form at the Def-3-selected ℓ on **437/437** cases,
zero disagreements; and `aoyagiλ` reproduces every numerical ground truth (§5).

**WARNING — do not state A1 as "extremise the clean form over ℓ".** Verified false
(`/tmp/aoyagi_regime.py`): neither `min_ℓ` nor `max_ℓ` of `¼(Σqᵢ²−Σmₖ²)` reproduces Def-3 (e.g.
`M=(2,2,2)`: Def-3 picks ℓ=2 → core 3/2, but `max_ℓ` picks ℓ=1 → core 2; `min_ℓ` can go **negative**,
e.g. `M=(1,1,1,4)` → −1/2, geometrically impossible). The correct total object is
`½·min_{T∈Adm} M(T)`; the clean form is its *value*, identified only at the genuine minimiser. A1 is
the theorem `½·min_T M(T) = clean form`, proven via Lemma 3 (the integer-balanced-split minimum).

### 4.4 The printed Theorem-2 expression (proven equal to clean; this is part of A1)

Aoyagi Theorem 2 (p.9), where Def 3 selects ℳ and `M = ⌈P/ℓ⌉`, `a = P − (M−1)ℓ`:

```text
λ_Aoyagi = [−r² + r(H⁽¹⁾+H⁽ᴸ⁺¹⁾)]/2  +  a(ℓ−a)/(4ℓ)  −  [ℓ(ℓ−1)/4]·(P/ℓ)²  +  ½ Σ_{1≤i<j≤ℓ+1} m_i m_j
```

**Verified symbolically (`/tmp/aoyagi_symbolic.py`, sympy exact):** the core part
`a(ℓ−a)/(4ℓ) − [ℓ(ℓ−1)/4](P/ℓ)² + ½Σ_{i<j}m_im_j` **= `¼(Σqᵢ² − Σmₖ²)`** identically for all ℓ≤4,
widths 0..6 (`q` = balanced split). So `aoyagiλ` (clean) `=` printed Theorem-2 **where Def 3 applies**.
The Lean lemma: `printed_core ℓ ℳ = clean_core ℓ ℳ` (a finite identity in `m,ℓ,a,M`).

### 4.5 Lean-readiness

**Lean-ready: YES.** `aoyagiλ : ℚ`. `lambdaCore` uses `Finset.inf'` over a finite `Adm M`; totality is
free. The clean-form and printed-form equalities are finite arithmetic identities (`A1`). The clean
form keeps terms small (build-discipline win). **Recommendation:** make `½·min_T M(T)` the *definition*
of `lambdaCore`, prove the clean form as a *theorem* (A1) — this is the robust choice the brief asks for.

---

## 5. Numerical ground-truth table (cross-check — task 2)

All via `λ = reg + ½·min_T M(T)` (the *definition*) and via the clean form and via the printed form;
exact rationals, reproduced in `/tmp/aoyagi_bridge.py`, `/tmp/aoyagi_check4.py`, `/tmp/aoyagi_theta.py`.

| H (widths) | r | reg | argmin T | λ (def=min) | λ (clean) | λ (printed) | θ=a(ℓ−a)+1 | expected (brief) |
|---|---|---|---|---|---|---|---|---|
| (2,2,2)   | 0 | 0 | (1,0)     | **3/2** | 3/2 | 3/2 | **1** | λ=3/2, θ=1 ✔ |
| (2,1,2)   | 0 | 0 | (0,0)     | **1**   | 1   | 1   | **2** | λ=1,   θ=2 ✔ |
| (1,2,2)   | 0 | 0 | (0,0)     | **1**   | 1   | 1   | **2** | λ=1,   θ=2 ✔ |
| (2,2,2,2) | 0 | 0 | (1,0,0)   | **3/2** | 3/2 | 3/2 | **3** | λ=3/2, θ=3 ✔ |
| (3,3,3)   | 0 | 0 | (1,0)     | 7/2 | 7/2 | 7/2 | 2 | (no brief value) |
| (3,3,3,3) | 0 | 0 | —         | 3   | 3   | 3   | 1 | (no brief value) |
| (2,3,4)   | 0 | 0 | (0,0)     | 3   | 3   | 3   | 2 | (no brief value) |

Every brief ground-truth value (λ **and** θ) reproduced exactly. Clean = printed on every case
(including unbalanced (2,3,4), (4,4,2)). The minimisation definition reproduces λ on every case.

---

## 6. Def-3 regime (task 3) — pinned exactly

**Claim (verified `/tmp/aoyagi_def3.py`, `/tmp/aoyagi_regime.py`):**

- Def 3 selects **at most one** set — over 19 600 width-multisets (length 2..5, entries 0..6),
  the count of multisets with **≥2** Def-3 solutions is **0**. So *when it selects, it is unique*.
- Def 3 selects **no** set on a large majority (18 187/19 600) — including the named trap `[1,2,3,4]`
  (sorted `[4,2,1,3]`). The "out" condition `Σ_{ℓ+1 smallest} ≤ (ℓ−1)M⁽ˢ⁾` for non-chosen widths is
  what fails: for short/strictly-increasing/near-equal vectors no ℓ satisfies both thresholds.
- The exact regime where Def 3 succeeds: there exists ℓ with `m := (ℓ+1 smallest)`, `P := Σm`, such
  that **`P > ℓ·max(m)`** (every chosen width strictly under the average-times-ℓ; the "blow-up is
  genuinely needed" condition) **and** `P ≤ (ℓ−1)·min(non-chosen)` (the next width is large enough to
  stay out). These pin ℳ uniquely when satisfiable.

**Resolution of the trap (this is the whole point of defining via the minimisation):** `aoyagiλ` via
`½·min_T M(T)` is **total and Def-3-free**. Where Def 3 succeeds, A1 proves `½·min_T M(T) = clean`.
Where Def 3 fails (e.g. `[1,2,3,4]`), the minimisation still returns the genuine value (`λ_core = 1/2`
for `[1,2,3,4]`), and the printed Theorem-2 expression simply does not apply there — we never claim it
does. The headline theorem uses `aoyagiλ`-via-minimisation as the RHS, so it holds on **all** widths;
the printed-form equality is a *named corollary scoped to the Def-3 regime*, not part of the headline.

> **Lean encoding of the Def-3 regime:** carry `Def3Selects (M) (ℓ) (ℳ) : Prop` as the predicate
> (the two thresholds), prove `Def3Selects → (½·min_T M(T) = clean ℓ ℳ = printed ℓ ℳ)`. Do **not**
> make `aoyagiλ` depend on `Def3Selects`.

---

## 7. The cited interface S2 + the reduction interface D1 — minimal faithful hypotheses

### 7.1 S2 — chart-level normal-crossing → RLCT (THE ONE CITED AXIOM)

**Source (Aoyagi p.6, Hironaka extraction).** If a proper analytic `π : Q → V` resolves `F` to
normal-crossing form on local coordinates `(u₁,…,u_d)`:
`K(π(u)) = u₁^{2k₁}…u_d^{2k_d}` and `π'(u)·φ(π(u)) = u₁^{h₁}…u_d^{h_d}` (`k_j, h_j ≥ 0` integers),
then `λ = min_U min_{1≤j≤d} (h_j+1)/(2k_j)` and `θ = max_u Card{ j : (h_j+1)/(2k_j) = λ }`.

**Minimal faithful hypotheses to PIN (so R1 can feed it and the cited content is exactly the
irreducible monomial-integral fact):**

```text
axiom rlct_of_normalCrossing
  (F : ℝᵈ → ℝ) (w* : ℝᵈ)
  -- the resolution data (PROVED on our side by R1):
  (charts : Finset Chart) (hcover : the images of the charts cover a nbhd of w* ∩ {F=0})
  (hπ : each chart φᵢ : Vᵢ → Uᵢ is an analytic diffeo onto its image, proper)
  (hmono : ∀ chart i, ∀ u ∈ Vᵢ, F(φᵢ u) = unitᵢ(u) · ∏_j |u_j|^{2 k_{i,j}}    -- unitᵢ ≠ 0
                                  ∧ |det Dφᵢ(u)| = unit'ᵢ(u) · ∏_j |u_j|^{h_{i,j}})  -- unit'ᵢ ≠ 0
  -- NB (Codex §6.3): absolute values |u_j| and |det| throughout — signed monomials are wrong.
  (hbump : φ is C∞, compact support, φ(w*) > 0) :
  rlctAt F w* = ⨅ i, ⨅ j, (h_{i,j}+1)/(2 k_{i,j})
  ∧ rlctOrderAt F w* = ⨆ i, Card{ j : (h_{i,j}+1)/(2 k_{i,j}) = rlctAt F w* }
```

The **irreducible cited fact** is the one-variable / monomial convergence criterion (state it so the
algebra is checkable):

> `∫_{[0,ε]^d} (∏_j u_j^{h_j}) · (∏_j u_j^{2k_j})^{−c} du < ∞  ⟺  c < min_j (h_j+1)/(2k_j)`
> (per axis: `∫_0^ε u^{h − 2kc} du` converges ⟺ `h − 2kc > −1` ⟺ `c < (h+1)/(2k)`).

Everything else — the **cover**, the **change-of-variables validity** (`∫_V F(π)^{−c} π'φ = ∫_U F^{−c}φ`),
the **properness/measurability** of `π`, the **unit factors** being bounded away from 0 on compact
charts — stays **on our side** (R1 builds the charts; S1 supplies change-of-variables). The axiom
asserts *only* the monomial extraction. This is the line the brief draws and nowhere else.

**Pin precisely:**
- *"cover"* = the finite union of chart images contains a neighbourhood of `w* ∩ {F=0}` (the singular
  locus), and off `{F=0}` the integrand is locally bounded so contributes a finite, irrelevant amount.
- *bump* = compactly supported `C∞`, `φ(w*)>0`; needed so the pullback Jacobian numerator `h_j` is
  well-defined and the value is φ-independent.
- *units* = `unitᵢ, unit'ᵢ` continuous, nonvanishing on the (compact) chart, so they sit between
  positive constants and do not shift the convergence threshold (only the monomial exponents do).

**Lean-ready: YES as a stated `axiom` (the single permitted citation).** The order half rides inside
the same axiom — this is where `rlctOrderAt = chart-count` is asserted (§3 seam closes here, not as a
new gap).

### 7.2 D1 — reduction to the deepest singular point (Aoyagi 2013 [22], Theorem 4)

**Source (Aoyagi 2023 p.14, Theorem 4).** For homogeneous `F₁,…,Fₘ` and a `C^∞` `φ` with
`φ(0,…,0,w*_{j+1},…) ≥ φ(w*)` and `φ_w` homogeneous near the deepest point,
`λ_{(0,…,0,w*_{j+1},…)}(⟨F⟩,φ) ≤ λ_{(w*_1,…,w*_d)}(⟨F⟩,φ)`. Consequence (p.14): "we can set
`r⁽ˢ⁾ = r` for all `s`" — i.e. the global infimum of the local RLCT over the optimal set is **attained
at the deepest singular point** (all layers at the minimal rank `r`), so the global learning
coefficient = the local RLCT there.

This is the bridge that turns the headline's `⨅_{w ∈ optimalSet} rlctAt` into the *local* RLCT at one
point (which R1+S2 then computes). The brief marks D1 **Proved** (from the 2013 paper, ref [22],
`entropy-15-03714.pdf`). For Rung 0 it is a **named statement placeholder**:

```text
theorem deepest_point_reduction (H r B) (hB : B.rank = r) :
  (⨅ w ∈ optimalSet H B, rlctAt (dlnLoss B) w) = rlctAt (dlnLoss B) w_deepest
-- w_deepest := the parameter with all layers block-normal at rank r (the most degenerate fibre point)
```

**Lean-ready: YES as the statement; the PROOF is D1's job (later rung), not S0.** Faithful hypotheses:
`φ`-monotonicity toward the deepest point + homogeneity; these are automatically met by the
square-Frobenius loss (homogeneous-ish polynomial) and a symmetric bump — to confirm in D1.

---

## 8. The goal skeleton (every named statement; the contract)

```text
-- S0 (this thread): definitions above. All `def`s, total.

-- the ONE cited axiom:
axiom rlct_of_normalCrossing … : rlctAt = ⨅⨅ (h+1)/(2k) ∧ rlctOrderAt = ⨆ chart-count   -- S2

-- S1: RLCT depends only on the ideal; φ-independence; Σ_X elimination; rlctAt = Def-1 value.
theorem rlct_ideal_invariant …                                                            -- S1
theorem rlct_phi_independent …                                                            -- S1
theorem rlct_eq_def1 …                                                                    -- S1

-- L1/L2: block elimination + product reduction (regular ⊕ singular core).
theorem block_elimination …          (Lemma 2, p.10)                                      -- L1
theorem product_reduction …          (Theorem 3, p.11–13): λ(‖∏A−∏A*‖²)
    = [−r²+r(H¹+Hᴸ⁺¹)]/2 + λ(⟨∏C⁽ˢ⁾⟩)                                                    -- L2

-- D1: reduction to the deepest singular point (Aoyagi 2013 Thm 4).
theorem deepest_point_reduction …                                                         -- D1

-- R1 (the mountain): the recursive blow-up as explicit charts → normal-crossing form,
--   producing the (k_{i,j}, h_{i,j}) data with cover + Jacobian-monomial proven.
theorem resolution_charts … : ∃ charts, hcover ∧ hπ ∧ hmono ∧ (exponents give M(T) candidates)  -- R1

-- A1: the arithmetic — ½·min_T M(T) = clean form; clean = printed (Def-3 regime); Lemma 3.
theorem lambdaCore_eq_clean …                                                             -- A1
theorem clean_eq_printed_on_def3 …                                                        -- A1
-- A2: the order count — chart-count = a(ℓ−a)+1 (Lemmas 4–5).
theorem aoyagiθ_eq …                                                                      -- A2

-- T: the headline (the GOAL).
theorem aoyagi_learning_coefficient (H r B) (hB : B.rank = r) :
    (⨅ w ∈ optimalSet H B, rlctAt (dlnLoss B) w) = (aoyagiλ H r : ℝ)
-- assembled: D1 (→ deepest point) ▸ L2 (→ reg + λ_core of ∏C) ▸ R1 (→ charts) ▸ S2 (→ min ratio)
--            ▸ A1 (→ clean form = aoyagiλ).  θ-headline analogously via S2-order ▸ A2.
```

**Sorry-budget:** every line above is a named `sorry` (or the one `axiom`); the count trends down as
each rung closes. No free-floating scaffolding.

---

## 9. Honestly-flagged items (task 5)

1. **The analytic order θ (`rlctOrderAt`) is the genuine seam.** The faithful definition (pole
   multiplicity of `∫|F|^z φ`) needs meromorphic continuation Mathlib lacks; and θ is **not** any
   naive minimiser-count (verified: 6 minimisers but θ=5 for (2,2,2,2,2)). *Plan:* land combinatorial
   `aoyagiθ = a(ℓ−a)+1` fully (total, A2); assert `rlctOrderAt = chart-count` *inside* the S2 axiom
   (the cited extraction returns the order too); prove chart-count `= a(ℓ−a)+1` in A2. The
   analytic-pole-order = chart-count equality is thus **carried by the single S2 citation**, not a new
   gap. If even the chart-count→`a(ℓ−a)+1` proof (A2, Lemmas 4–5) proves disproportionate, θ is the
   named at-risk deliverable per standing decision 6 — λ is unaffected.

2. **`aoyagiλ` via minimisation vs the brief's loose "extremise over ℓ".** Corrected: the faithful
   total object is `½·min_{T∈Adm} M(T)`, NOT min/max over ℓ of the clean formula (both verified wrong;
   min-over-ℓ goes negative). The clean form is the *value* of this minimisation, proven equal at the
   Def-3 ℓ (A1). This is a substantive correction to the brief's phrasing — flagged for the controller.

3. **The admissible cone `Adm(M)`.** I reconstructed it from p.22 (weak-decrease + `t⁽ᴸ⁾=0` +
   per-factor nonnegativity) and verified it reproduces all ground truth and the clean form. But the
   *exact* equivalence between "my `Adm` cone" and "the set of exponent vectors the resolution R1
   literally produces" is only *checked numerically*, not yet proven — it will be pinned precisely when
   R1 is built (R1's output exponents must be shown to range over exactly `Adm`). Until then, `Adm` is
   the faithful-by-construction definition; the R1↔Adm match is an R1-side obligation, flagged.

   > **AMENDED 2026-06-20 (thread 03, controller-integrated).** The set-equality "chart exponents = Adm"
   > is **FALSE** (charts outnumber T-vectors: 24 vs 3 for (2,2,2)) — confirmed by pp + decorrelated
   > Codex. The correct R1 obligation is the **value-match**: resolution's min chart-ratio
   > `= ½·min_{T∈Adm} Mval(T)`. The interpretation: `T` ↔ rank-incidence stratum, `Mval(T) = codim`
   > (proven L=2), so `λ_core = ½·min_strata codim`. `Adm` stays the right *definition* substrate; the
   > R1 obligation shrinks to the value-match (Theorem 3 + resolution existence). See
   > `threads/03-r1-smallcase/thread.md`.

   > **FURTHER AMENDED 2026-06-20 (thread 14 R1-design, controller-integrated).** Even "each minimizing
   > chart ↔ one prefix-stratum `S(t)`" is **too strong** (Codex R1-design consult): charts refine
   > strata by the FULL rank-pattern `r_{ab} = rank(C^a···C^b)` + affine-minor (pivot) choices, not the
   > prefix ranks `t_j`. The R1↔Adm relationship is **VALUE-level only** — `min over charts of the
   > ratios = ½·min_t Mval(t)` — with **no chart↔stratum bijection** of any kind. No formaliser should
   > expect one. The prefix `S(t)` partition is right for the codim-MINIMISATION (the value), too
   > coarse for a literal chart atlas. The full architecture (value/atlas split; the value via codim,
   > NOT via chart bookkeeping; R3b self-contained one-citation route): `threads/14-r1-design/r1-design.md`.

4. **`rlctAt = Def-1 value` (bump removal).** The existential-neighbourhood form is *argued* equal to
   the bumped Def-1 value (sandwich); this is an S1 theorem, not yet proven. The `def` is faithful by
   the standard sandwich argument; submitted to Codex for an independent faithfulness audit (§ below).

---

## 10. Decorrelated Codex audit (task 4)

Fired at `model_reasoning_effort=xhigh` on the *faithfulness* of `rlctAt`/`rlctOrderAt`/S2 to Aoyagi
Def 1 + standard RLCT theory, **withholding my conclusions** (frame + facts in, hypothesis out). Codex
ran its own web searches (Saito 2007 arXiv:0707.2308; arXiv:2501.12747; analytic zero-set measure
fact) — genuinely decorrelated. Prompt/answer: `/tmp/codex-rlct-prompt.md`, `/tmp/codex-rlct-answer.md`.

**Verdict: all six questions FAITHFUL-WITH-CAVEAT — no NOT-FAITHFUL.** Codex independently re-derived
the monomial threshold `∫_0^ε t^{h−2kc} dt < ∞ ⟺ c < (h+1)/(2k)` (matches mine exactly) and the per-
variable convergence story. It **agrees** the existential-neighbourhood form equals the bumped Def-1
value (φ sandwiched between positive constants), the admissible `c` form a down-set, the threshold is
generically not attained, the ideal convention `λ(J)=λ(∑Fᵢ²)` is faithful to Aoyagi, and the
chart-count = analytic pole order *in the positive-amplitude setting with no genericity needed*.

**I judged its algebra independently — it checks.** Its `F(x)=x²` cheap test (λ=1/2, pole at z=−1/2):
`|x²|^{−c}=|x|^{−2c}` integrable near 0 ⟺ −2c>−1 ⟺ c<1/2. ✔.

**Three sharpenings Codex raised that I have folded into the spec (all consistent with my findings,
none overturning a conclusion):**

1. **Pole-sign clarity (Codex's "most likely bug").** For `Z(z)=∫|F|^z φ`, the largest pole is at
   `z = −λ`, *not* `+λ`. My §2/§3 transcribe Aoyagi's wording; the spec now states the sign explicitly
   wherever the zeta-pole reading appears (see §2 amendment). Cheap detector: `F=x²`.
2. **Real-analytic germ is a *required hypothesis*, not optional.** For arbitrary measurable `F` whose
   zero set has positive measure, the sup-definition collapses to threshold 0 (outside RLCT theory).
   The spec now states `rlctAt` is faithful *only under* `F` real-analytic, `≢0` near `w*` — already in
   §2's checklist, now elevated to a precondition on the S0/S1 theorems (`dlnLoss` is polynomial ⇒ OK).
3. **Use `|det Dπ|` and `|u_j|` (absolute values) in S2.** The monomial form should be
   `K(π u)=unit·∏|u_j|^{2k_j}`, `|det Dπ|·φ(π u)=pos·∏|u_j|^{h_j}` — signed Jacobian / signed monomials
   would be wrong. §7.1's axiom uses `|det Dφᵢ|`; the `|u_j|` is now explicit.

Also recorded (convention hygiene, no change needed): some algebraic-statistics papers define the ideal
zeta with a half-exponent `(∑fᵢ²)^{−z/2}`, shifting the value by a factor 2 — we use **Aoyagi's**
convention `λ(J)=λ(∑Fᵢ²)` throughout, which is the source's and which our ground-truth table matches.

**Net:** Codex corroborates the definitions as faithful under the stated hypotheses; it surfaced no
error in the arithmetic spine, and its three caveats are encoding-precision points now pinned.
