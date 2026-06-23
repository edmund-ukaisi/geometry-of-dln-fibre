# r=0 D1≥ — HOMOGENEOUS-SCALING WITNESS CERTIFICATE (pp, 2026-06-23)

**Dispatch.** Adjudicate one truth-value: is the **r=0 case of D1≥** buildable in Lean v4.29 + the
green RLCT toolset, WITHOUT the constant-rank theorem (confirmed absent from Mathlib v4.29)?

**Direction:** `witness`. **VERDICT: WITNESS — build-ready.** The r=0 D1≥ inequality builds from the
green toolset plus exactly **ONE small new lemma** (`rlctAt_const_smul_invariant`, a constant-Jacobian
variant of the existing `rlctAtOn_comp_homeomorph`), classified NEEDS-STANDARD-MATHLIB (not new analytic
input). The constant-rank normal form is NOT needed: global homogeneity replaces it. **No RLCT
lower-semicontinuity, no s→0 limit, no blow-up CoV.** Two decorrelated legs (pp exact-algebra + Codex
xhigh, independent) converged on the identical route.

---

## The target (r=0, B=0 specialisation of `rlctAt_deepest_le_of_optimal`)

`deepestPoint H 0 0 hB hr hL = (fun _ => 0)` — the all-zero tuple / origin (verified:
`deepestPoint_exists`, `Skeleton.lean:872-878`, the `r=0` branch returns `⟨fun _ => 0, …⟩`). So the
`≥` leg of `deepest_point_reduction` at r=0, B=0 is, for every `v ∈ optimalSet H 0` (i.e. `prod H v = 0`):

    rlctAt H (dlnLoss H 0) (0 : Params H)  ≤  rlctAt H (dlnLoss H 0) v.

Write `K := dlnLoss H 0`. Then `K(A) = ‖prod H A‖² = Σᵢⱼ (prod H A) i j ^ 2 ≥ 0` (`Loss.lean:55`,
`dlnLoss_nonneg`). **`K` is globally homogeneous of degree `d = 2L`:**

    K(t • A) = ‖prod H (t•A)‖² = ‖t^L • prod H A‖² = t^{2L} · ‖prod H A‖² = t^{2L} · K(A)    (all t ∈ ℝ),

because `prod H (t•A) = t^L • prod H A` (`prod_smul`, below). Because **B = 0 makes K its own
homogeneous core**, the per-`v` normal-form split (prerequisite (a) of the GENERAL-r certificate
`d1-valuefree-certificate.md`, the constant-rank gap) is not invoked at all here.

---

## The route (the one cleanest; decorrelated-converged)

Two steps. Step 1 is the only one with a measure-theoretic change of variables (the new lemma); step 2
is elementary topology on the `∃ U ∈ 𝓝` witness of `rlctAt`.

### Step 1 — ray-constancy: `rlctAt K (s • A) = rlctAt K A` for every `s > 0`, every `A`.

For `s > 0` the scaling `σ_s : Params H ≃ₜ Params H`, `σ_s A = s • A`, is a homeomorphism
(`Homeomorph.smul`, `continuous_const_smul` both ways). Its volume-pushforward is a POSITIVE FINITE
CONSTANT multiple of volume — `Measure.map σ_s volume = ENNReal.ofReal |s^N|⁻¹ • volume`
(`map_addHaar_smul`, `N = flatDim H`). Then:

    rlctAt K (s • A)
      = rlctAt (K ∘ σ_s) A        [transport: NEW lemma rlctAt_const_smul_invariant]
      = rlctAt (s^{2L} · K) A      [homogeneity: K(σ_s A) = K(s•A) = s^{2L}·K(A), pointwise]
      = rlctAt K A.                [rlct_unit_invariant, constant unit u ≡ s^{2L} > 0]

- Transport line: the existing `rlctAtOn_comp_homeomorph` (`S1Fubini.lean:54`) requires `σ_s`
  **MeasurePreserving** (pushforward ratio EXACTLY 1). `σ_s` has Jacobian `s^N ≠ 1`, so it is only
  QUASI-measure-preserving (constant density). **This is the one gap.** The fix is the constant-Jacobian
  variant (Step-1 lemma, below): the admissible-`c'` integrals on the `e`-image transfer because
  `IntegrableOn f (image) (c • volume) ↔ IntegrableOn f (image) volume` for a positive finite constant
  `c` — exactly Mathlib `integrable_smul_measure (h₁ : c ≠ 0) (h₂ : c ≠ ∞)`.
- `rlct_unit_invariant` line: `u ≡ s^{2L}` is a constant measurable unit with `a = b = s^{2L} > 0`, so
  `rlctAt (s^{2L}·K) A = rlctAt K A` directly (`Skeleton.lean:200` / `rlct_unit_invariant_aux`,
  `S1Local.lean:38`).

### Step 2 — the origin comparison, NO limit (the key sidestep).

`rlctAt K 0 = sSup { c : ∃ c' ≥ 0, c = c', ∃ U ∈ 𝓝 0, IntegrableOn |K|^{-c'} U }`. To show
`rlctAt K 0 ≤ rlctAt K v` it suffices to bound each member `c` of the LHS set:

  Let `c` be admissible at `0`, witnessed by an OPEN `U ∋ 0` with `∫_U |K|^{-c'} < ∞`. Since
  `s • v → 0` as `s → 0⁺` and `U` is an open nbhd of `0`, **choose one fixed `0 < s ≤ 1` with
  `s • v ∈ U`** (`continuous_const_smul` at `0`, or directly: pick `s` with `s·(‖v‖+1) < ε` for an
  `ε`-ball `B(0,ε) ⊆ U`). Then **the SAME `U` is a nbhd of `s • v`** (`s•v ∈ U`, `U` open) with the
  SAME finite integral, so `c'` is admissible at `s • v`, i.e. `c ≤ rlctAt K (s • v)`. By Step 1
  (ray-constancy, `s > 0`), `rlctAt K (s • v) = rlctAt K v`. Hence `c ≤ rlctAt K v`.

  Taking `sSup` over admissible `c`: `rlctAt K 0 ≤ rlctAt K v`. ∎

There is **no s→0 limit and no lower-semicontinuity**: the existential nbhd `U ∋ 0` of `rlctAt K 0`
itself serves as the witness nbhd at the nearby ray point `s•v ∈ U`. (Trying instead to take `s→0` in
the numeric equality `rlctAt K (s•v) = rlctAt K v` WOULD require RLCT lsc at the origin — a known-hard
object needing meromorphic-continuation / Tauberian machinery Mathlib lacks. The witness argument
sidesteps it entirely.)

---

## The ONE new lemma (exact Lean statement — the formaliser's only build target beyond green)

```lean
/-- RLCT transport under a homeomorphism whose volume-pushforward is a POSITIVE FINITE CONSTANT
multiple of volume (constant-Jacobian variant of `rlctAtOn_comp_homeomorph`). -/
theorem rlctAt_const_smul_invariant {M M' : Type*} [MeasureSpace M] [TopologicalSpace M]
    [MeasureSpace M'] [TopologicalSpace M']
    (e : M ≃ₜ M') (hemb : MeasurableEmbedding e)
    (c : ENNReal) (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hmap : Measure.map e volume = c • volume)
    (F : M' → ℝ) (w0 : M) :
    rlctAtOn (fun w => F (e w)) w0 = rlctAtOn F (e w0)
```

Proof is `rlctAtOn_comp_homeomorph`'s proof with the single change: the image-integral step
`he.integrableOn_image` (ratio 1) is replaced by `MeasurableEmbedding.integrableOn_map_iff`/the
`Measure.map e volume = c • volume` rewrite, then `integrable_smul_measure hc0 hctop` discharges the
constant-density. (`integrable_smul_measure : c ≠ 0 → c ≠ ∞ → (Integrable f (c•μ) ↔ Integrable f μ)`,
`L1Space/Integrable.lean:322` — verified present.) Both directions symmetric, as in the green proof.

**The scaling instance feeding it** (the application use-site):
- `e := (Homeomorph.smul (Units s))` on `Params H` — `σ_s`, `s > 0` a unit; `hemb` from the homeo.
- `hmap`: `Measure.map (s • ·) volume = ENNReal.ofReal |s^N|⁻¹ • volume`, `N = flatDim H`,
  `c = ENNReal.ofReal |s^N|⁻¹` (≠ 0, ≠ ∞ for `s > 0`). On `Params H` this transports through the
  already-landed measure-preserving homeomorphism `paramsEquivFlat : Params H ≃ᵐ (Fin N → ℝ)`
  (`ParamsFlat.lean:80-93`, MP + homeo), on which `map_addHaar_smul` (`EqHaar.lean:341`) applies
  because `isAddHaarMeasure_volume_pi` gives `IsAddHaarMeasure (volume : Measure (Fin N → ℝ))`
  (`EqHaar.lean:126`). `paramsEquivFlat` is ℝ-linear (currying + reindex), so it intertwines the two
  scalings: `paramsEquivFlat (s • A) = s • paramsEquivFlat A` (pointwise per coordinate) — a small
  algebraic lemma, the only extra glue.

---

## Green tools consumed (all verified PRESENT on `expedition/aoyagi-full`, signatures read)

| step | tool (exact name) | location | role |
|---|---|---|---|
| homogeneity | `prod_smul` (`prod (t•A) = t^L • prod A`) | **TO BUILD** (trivial induction, see below) | gives `K(t•A) = t^{2L}·K(A)` |
| K ≥ 0 | `dlnLoss_nonneg` | `Loss.lean:91` | the `t^{2L} ≤ 1` comparison side / `\|·\|` cleanup |
| transport (Step 1) | `rlctAt_const_smul_invariant` | **NEW (only build target)** | the constant-Jacobian peel |
| constant-unit (Step 1) | `rlct_unit_invariant` / `_aux` | `Skeleton.lean:200`, `S1Local.lean:38` | drops the constant factor `s^{2L}` |
| flat bridge | `paramsEquivFlat`, `measurePreserving_paramsEquivFlat`, `continuous_paramsEquivFlat(_symm)` | `ParamsFlat.lean:80,91,127,141` | hosts `map_addHaar_smul` on `Fin N → ℝ` |
| Mathlib measure | `map_addHaar_smul`, `isAddHaarMeasure_volume_pi`, `integrable_smul_measure` | `EqHaar.lean:341,126`, `Integrable.lean:322` | the constant-density facts |
| origin step (Step 2) | `rlctAt` def + `mem_nhds_iff`/`IsOpen.mem_nhds` | `Rlct.lean:71` | the `U ∋ 0` witness reused at `s•v ∈ U` |
| deepest = origin | `deepestPoint_exists` r=0 branch | `Skeleton.lean:872-878` | `deepestPoint H 0 0 = (fun _ => 0)` |

**`prod_smul` (the only other build, trivial).** By induction on `k`:
`prodAux H (t•A) k = t^k · prodAux H A k` (each of the `k` matrix factors contributes one `t` via
`Matrix.smul_mul`); base `k=0`: `(1) = t^0 • 1`. Then `prod H (t•A) = prodAux H (t•A) L = t^L • prod H A`.
Pattern mirrors the existing `prodAux_zero`/`prod_zero` (`Skeleton.lean:569-577`). Brief reports it is
already on branch `d1-scope`'s working tree (`Skeleton.lean ~985`); not yet on `expedition/aoyagi-full`.

---

## Why the two failed routes fail (the scoped no-go's, for the obstruction record)

- **`rlctAtOn_comp_homeomorph` as-is (MeasurePreserving) does NOT cover `σ_s`.** `σ_s` has Jacobian
  `s^N ≠ 1`; it is quasi-MP, not MP. This is the precise reason the green peel must be extended by the
  one new lemma. (Not an obstruction to the result — a one-line generalisation.)
- **No-transport (same-point `rlctAt_mono` only) is genuinely impossible.** A same-point domination
  `|K(u)| ≤ C·|K(v+u)|` near `u=0` is FALSE in general (Codex counterexample, exact:
  `K = (y²−xz)²`, `v = (1,0,0)`; for `u = (0,ε,ε²)`, `v+u` lies on the zero cone so `K(v+u)=0` while
  `K(u)=ε⁴≠0` — domination breaks). So the basepoint move `0 ↔ v` (transport) is unavoidable; the
  result is NOT reachable from `rlctAt_mono` alone. This is the honest scope: D1≥-r0 needs transport.
- **The blow-up CoV `Φ(t,u)=t•(v+u)` does NOT help here.** `Φ` collapses `{t=0}` to `0`, so it is not a
  homeomorphism at the only basepoint `(0,0)` where the comparison is non-vacuous (at the regular
  basepoint `(1,0)` the inequality degenerates to `rlctAt K v ≤ rlctAt K v`). The bounded-unit-Jacobian
  peel (#71/#72) needs a LOCAL DIFFEO and so also fails at `(0,0)`. The Step-1/Step-2 route avoids the
  blow-up entirely.

---

## Scope (named for what it is)

This certificate establishes: **for the GLOBALLY-homogeneous loss (the r=0, B=0 slice), the origin is a
deepest point — `rlctAt(K)(0) ≤ rlctAt(K)(v)` for every fibre point `v`** — buildable from the green
toolset + one constant-Jacobian transport lemma, with NO constant-rank theorem and NO RLCT lsc. It does
NOT cover `r > 0` / `B ≠ 0`: there the loss is not globally homogeneous, the per-`v` homogeneous-residual
normal form (constant-rank / IFT split, prerequisite (a) of `d1-valuefree-certificate.md`) returns, and
that split is the genuine gap. The r=0 slice is the one piece of the honest ⨅-form learning-coefficient
headline reachable now without that gap.

## Decorrelation

- pp (this cert): exact-algebra from the `rlctAt` integral-sup definition; verified signatures
  (`rlctAt`, `rlctAt_mono`, `rlctAtOn_comp_homeomorph`, `rlct_unit_invariant_aux`, `paramsEquivFlat`,
  `deepestPoint_exists` r=0); Mathlib lemma existence checked (`map_addHaar_smul`,
  `isAddHaarMeasure_volume_pi`, `integrable_smul_measure`).
- Codex (xhigh, independent; prompt+answer banked `codex/r0-homog-rlct-{prompt,answer}.md`): reached the
  IDENTICAL two-step route — ray-constancy via constant-Jacobian scaling + `rlct_unit_invariant`, then
  the local-`U`-witness origin step with NO limit; named the same minimal lemma
  (`rlctAt_comp_homeomorph_const_smul_measure`); classified it NEEDS-STANDARD-MATHLIB; supplied the R2
  counterexample above; confirmed lsc is sidestepped. Converged.
