# D1 IFT-chart producer — BUILD-READY SPEC (obligation (i), L = 2)

**For: a fresh worktree-isolated `lean-formaliser`.** This is the SINGLE remaining D1 (★) obligation.
Everything upstream (the engine, the wiring, the residual-core interface, the kill-condition + design
adjudications) is BANKED clean-three. Your job: construct the constant-`nReg` IFT chart at a **general**
optimal `v` and supply its outputs to the banked consumers, landing the D1 per-point `≥` leg
`rlctAt_deepest_le_of_optimal` (Skeleton:1172) at L = 2.

Scope **L = 2 only** (`H : Fin 3 → ℕ`, `prod = A⁽¹⁾·A⁽²⁾`). General-L is the named wall **#120** — do NOT
attempt. Branch off `origin/expedition/aoyagi-full`. Commit + push your OWN feature branch; isolation:
worktree; edit ONLY your worktree (a prior leg leaked into the main checkout — be strict).

---

## 0. The target

`rlctAt_deepest_le_of_optimal` (Skeleton:1172) concludes, for any `v ∈ optimalSet H B`:

    rlctAt H (dlnLoss H B) (deepestPoint H r B hB hr hL) ≤ rlctAt H (dlnLoss H B) v.

The BANKED `deepest_le_of_optimal_chart` (Validate/D1ChartProducer.lean) discharges this MODULO three
inputs: `hDeepest` (= #44, the existing Skeleton sorry `deepest_regular_core_normal_form`), the chart
data, and `hCore`. Your deliverable is a producer theorem `GeneralVChartL2` (new file
`Validate/D1ChartProducerL2.lean`) that, for general `v` at L = 2, supplies those inputs and calls
`deepest_le_of_optimal_chart`. So D1's per-point `≥` lands at L = 2.

---

## 1. The mathematics (already adjudicated — DO NOT re-derive, just formalise)

`dlnLoss H B A = ∑ᵢⱼ ((prod A − B)ᵢⱼ)²` — a sum of squares of the smooth product-difference entries
`g_{ij}(A) = (prod A − B)_{ij}`. At an optimal `v` (`prod v = B`), all `g_{ij}(v) = 0`.

Let `m = M_s` the reduced width (`M = H − r`), `a = rank(A₁ at v) − r ≥ 0`, `b = rank(A₂ at v) − r ≥ 0`.
**Peel exactly the CONSTANT `nReg = r(H₀+H₂−r)` independent gradient directions** (the DEEPEST count,
constant on the fibre — NOT the maximal Hessian rank `nReg_v` at `v`; peeling `nReg_v` is the FORBIDDEN
Aoyagi-Thm-2 maximal Morse split and breaks constancy). The slice residual `R` then factors as
(adjudications a97332 / a9a2cf, EXACT, 164-strata exhaustive sweep + Codex):

  * **Deepest-type `v` (`nReg_v = nReg`, i.e. `a = b = 0`):** `R = ‖T₁·(I+G)·T₂‖²_F` with `G` gauge-only,
    `G(0) = 0`, so `R = (core ∘ fst) ∘ Φ` for the bounded-unit local diffeo
    `Φ : (T,g) ↦ ((T₁, (I+G(g))·T₂), g)`, `det DΦ(0) = (det(I+G(0)))^{M₂} = 1`. ⟹ `rlctAtOn R 0 =
    rlctAtOn core 0 = coreDeepest`. (`core = dlnLoss M 0`, `M = H−r`.)

  * **Middle-stratum `v` (`nReg_v > nReg`):** `R ~ (∑_{extra} w_k²) + (degraded core)` via a
    Morse-with-parameters local diffeo, where `extra = m(a+b) − ab` and the degraded core is the deepest
    DLN core of widths `M' = (m−a, m−a−b, m−b)`. ⟹ `rlctAtOn R 0 = extra/2 + lambdaCore(M')` and
    `extra/2 + lambdaCore(M') ≥ coreDeepest` (self-contained `Mval`/`Adm` arithmetic).

Both cases give `hCore : coreDeepest ≤ rlctAtOn R 0`. The deepest-type uses the banked
`hCore_slice_residual_eq` directly; the middle-stratum uses the second-peel route (§4).

---

## 2. Banked consumers (your call targets — exact signatures)

All in `Validate/D1ChartProducer.lean` (+ `Foundations.*`); already clean-three, axiom-clean
`[propext, Classical.choice, Quot.sound]`:

- **`deepest_le_of_optimal_chart`** — the headline wiring. Takes `H r B deepest v F Q R t0 coreDeepest`,
  `hDeepest`, `hchart`, `hF`, `hQ0`, `hFmeas`, `hR`, `hRmeas`, `hRne`, `C`, `hC`, `hcmp`, `hCore`;
  concludes `rlctAt H (dlnLoss H B) deepest ≤ rlctAt H (dlnLoss H B) v`. THIS is your final call.
- **`rlctAt_ge_nReg_add_slice`** — the `hAtV` half (if you want it standalone): `hchart` + the engine ⟹
  `nReg/2 + rlctAtOn R t0 ≤ rlctAt H (dlnLoss H B) v`.
- **`hCore_slice_residual_eq`** — the deepest-type `hCore` discharge: bounded-unit local diffeo `Φ` +
  `hRform : R = (core₀ ∘ fst) ∘ Φ` + a positive-finite gauge nbhd ⟹ `rlctAtOn R (t0,g0) = rlctAtOn core₀ t0`.
- **`rlct_quasiSplit_ge`** (Foundations.S1QuasiSplit) — `F = ∑s² + Q`, `Q ≥ 0`, `R = Q(0,·)` measurable
  a.e.-nonzero, `hcmp : ∑s² + R ≤ C·F` ⟹ `nReg/2 + rlctAtOn R t0 ≤ rlctAtOn F (0,t0)`.
- **`coupled_controls_slice`** (S1QuasiSplit) — `(a−b)² ≤ L²·∑s² ⟹ ∑s² + b² ≤ (2L²+2)(∑s² + a²)`. Build
  `hcmp` by summing this over the inactive index, with `L` from the mean-value bound on the coupled part.
- **`rlctAtOn_boundedUnit_localHomeomorph`** (S1NonMPTransport:292) — strips the chart `Φ` (raw-data
  form: `Φ`, `Φsymm`, `DΦ`, `DΦsymm`, the inverse identities, derivs, bounded-unit det bounds on `V`).
- **`rlctAtOn_spectator_peel`** (S1Spectator:82) — drops the gauge factor (positive-finite gauge nbhd).
- **`rlctAtOn_comp_homeomorph`** (S1Fubini:54) — MP-homeo RLCT transport (for the `Params↔flat` bridge).

---

## 3. The chart-space machinery to REUSE (the deepest-point template to GENERALIZE off `deepestPoint`)

The deepest-point construction is the EXACT template; the producer generalizes it off `deepestPoint`/
`IsDeepLayers` to a GENERAL optimal `v`. Reuse:

- **`paramsEquivFlat H`** (Foundations.ParamsFlat:80) — `Params H ≃ᵐ (Fin (flatDim H) → ℝ)`, with
  `measurePreserving_paramsEquivFlat`, `continuous_paramsEquivFlat(_symm)`. The `Params ↔ flat` bridge
  (so the chart lives on `Fin (flatDim H) → ℝ`, a normed/Haar space for `rlctAtOn_boundedUnit_localHomeomorph`).
- **`DeepestGaugeChart` structure** (DeepestGaugeChart:143) + **`DeepestGaugeChart.ofExactGerm`** (:251) —
  the smart constructor for the deepest chart; build the general-`v` analog.
- **`deepest_regular_core_reduces`** (DeepestGaugeChart:524) — the deepest-point EXACT template producing
  `rlctAt(deepest) = nReg/2 + rlctAtOn(reduced core) 0`. Your producer is its analog at `v`, but EXPOSES
  the post-chart `F = ∑s² + Q` form (so `rlctAt_ge_nReg_add_slice` consumes it) rather than the
  already-reduced equality.
- **`deepest_regular_smooth_split`** (:434), **`deepest_reduced_core_identification`** (:385) — the
  smooth-block split + the `Params↔flat` reduced-core identification (reuse with `M = H−r`).
- The **gauge slice** `C_s = [[I_r+X_s, Y_s],[Z_s, T_s]]` (per-layer `block_elimination` units `P_s, Q_s`)
  — the chart at `v`. The regular coords are the `nReg` directions `P₁₁−I_r, P₁₂, P₂₁`; the reduced core is
  `‖∏ C'_s‖² = dlnLoss M 0`.
- **Mathlib C^r IFT**: `ContDiffAt.toOpenPartialHomeomorph` / `.localInverse` / `.to_localInverse`
  (VERIFIED present); **`Convex.norm_image_sub_le_of_norm_fderiv_le`** (mean-value Lipschitz, for `hcmp`).

`dlnLoss`/`prod` are polynomial ⟹ `ContDiff ℝ ⊤` (by `fun_prop`); `measurable_dlnLoss` /
`continuous_dlnLoss` are banked.

---

## 4. The two-case `hCore` discharge

`deepest_le_of_optimal_chart` takes `hCore : coreDeepest ≤ rlctAtOn R t0` as a hypothesis. Discharge it
by dispatching on `v`'s rank pattern:

**(A) Deepest-type (`a = b = 0`):** build the bounded-unit diffeo `Φ : (T,g) ↦ ((T₁, (I+G(g))·T₂), g)`
(`G` gauge-only from the gauge slice, `G(0)=0`, so `det DΦ(0)=1` by block-triangularity), verify
`hRform : R = (core₀ ∘ fst) ∘ Φ`, and call **`hCore_slice_residual_eq`** ⟹ `rlctAtOn R t0 = coreDeepest`
(so `hCore` with equality). `core₀ = dlnLoss M 0` on the reduced widths.

**(B) Middle-stratum (`nReg_v > nReg`) — the SECOND-PEEL route (design-pass a9a2cf):** the direct
domination route is DEAD (proven: any `rlctAtOn_mono` dominator must vanish on the Schur zero-set
`{(P+X)Y=0}`, so it already encodes the degraded core). The forced route:
  1. `R ~ (∑_{extra} w²) + (degraded core M')` via a Morse-with-parameters local diffeo (the inner
     straightening `rlctAtOn_boundedUnit_localHomeomorph` + `rlctAtOn_spectator_peel`).
  2. `rlctAtOn R 0 = extra/2 + rlctAtOn(degraded core M') 0` via a SECOND `rlct_quasiSplit_ge` application
     (peel the `extra` Morse squares off the degraded core).
  3. `rlctAtOn(degraded core M') 0 = lambdaCore(M')` — **the R1-resolution-at-`M'` INTERFACE (§5).**
  4. `extra/2 + lambdaCore(M') ≥ coreDeepest` — **the self-contained arithmetic lemma (§6).**
  Chain (2)+(3)+(4) ⟹ `hCore`.

You may bank (A) NOW (it uses only banked machinery). (B) is conditional on the §5 interface (which is
itself a Skeleton obligation — see §5) — so structure (B) to take the interface as a HYPOTHESIS.

---

## 5. The R1-resolution-at-`M'` INTERFACE (named hypothesis — interface-banking pattern)

★ **CONTROLLER PRECISION (bake this in):** the middle-stratum `hCore` consumes R1's resolution THEOREM
at the rectangular `M'`, NOT R1's closed-form value and NOT #44. Structure the producer to take

    hResolveM' : ∀ (M' : Fin 3 → ℕ), (∀ s, 0 < M' s) →
        rlctAtOn (fun A : Params M' => dlnLoss M' 0 A) (fun _ => 0) = ENNReal.ofReal (lambdaCore M')

(or the per-`M'` instance you need) as a **NAMED INTERFACE/HYPOTHESIS**. Then the producer builds + lands
CONDITIONALLY NOW (R1's `resolution_charts` is itself a Skeleton sorry), and `hResolveM'` discharges when
R1's general resolution closes. So the producer is NOT hard-sequenced behind R1 — it builds independently.

The interface is dischargeable from the BANKED `resolution_value_of_atlas` (ResolutionAtlas:197,
`⨅ monomialThreshold = ofReal(lambdaCore M)` for arbitrary `M`) + `resolution_charts` (Skeleton:1228,
the chart family for arbitrary `M`, only `hMid : ∀ s, 0 < M s`). Both are stated for ARBITRARY width `M`
(VERIFIED — NOT square-only), so `M'` is covered.

★ **BINDING CONSTRAINT to state in the spec docstring:** `resolution_charts` (Skeleton:1228) MUST stay
general-width (`hMid` only, NOT narrowed to square-only) so it covers the rectangular `M'`. Record this
as an explicit dependency. (No one is building `resolution_charts` yet — it's gated; this is a constraint
on the future R1 cover-assembly, not a live-front message.)

---

## 6. The self-contained arithmetic lemma (build this — pure `ℚ`/`Mval`/`Adm`, no R1, no analysis)

    extra/2 + lambdaCore(M') ≥ coreDeepest,   where coreDeepest = lambdaCore(M),
    extra = m(a+b) − ab,  M' = (m−a, m−a−b, m−b),  M the deepest reduced widths.

Self-contained over `ℚ`, from the symbolic identity `extra + D_{a,b}(t) = F_m(a+t)`, `F_m(s)=(m−s)²+sm`
(`D` the degraded `Mval`). Reduces to `Mval`/`Adm` algebra (Lambda.lean: `Mval`, `Adm`, `lambdaCore`,
`Mval_nonneg_of_adm`, `zero_mem_Adm`). At L=2 (`M : Fin 3 → ℕ`) `Adm M` is small — `decide +kernel` may
close the per-case inequality, or an explicit `Finset.inf'` bound. This is the cleanest piece to land
first (no chart, no analysis). Verified ZERO violations across 164 strata (`m ≤ 8`); D1 needs only `≥`.

---

## 7. Suggested build order (≤4-attempts-then-bank per piece; clean-three, forced #print axioms)

1. **The arithmetic lemma (§6)** — pure `ℚ`/`Mval`/`Adm`, no dependencies. Land first.
2. **The deepest-type producer (A)** — the chart `Φ` + `hRform` + `hcmp` (via `coupled_controls_slice`)
   + `hchart` (via `rlctAtOn_boundedUnit_localHomeomorph` + the `Params↔flat` bridge), feeding
   `rlctAt_ge_nReg_add_slice` + `hCore_slice_residual_eq` + `deepest_le_of_optimal_chart`. Lands D1 `≥` on
   the deepest-type sub-locus. CLEAN-THREE banked (banked machinery only).
3. **The middle-stratum producer (B)** — the second-peel (§4) + the §5 `hResolveM'` interface hypothesis
   + the §6 arithmetic. Conditional clean-three (the interface is the only open hypothesis).
4. **`GeneralVChartL2`** — dispatch on `v`'s rank pattern (A vs B) ⟹ `rlctAt_deepest_le_of_optimal` at L=2.

DISCIPLINE: at a wall on the chart construction (the gauge slice at general `v` / the Morse-with-params
diffeo for (B)), bank what's clean + surface the PRECISE residual — the controller brings a decorrelated
pen-and-paper. Do NOT grind the whole chart blind. The truth-value is BANKED (adjudications a97332/a9a2cf,
EXACT); your job is the formalisation, not re-deriving the math.

---

## 8. Hand-off checklist for the spawned formaliser

- [ ] New file `Validate/D1ChartProducerL2.lean` (DISJOINT from `D1ChartProducer.lean` — additive).
- [ ] Imports: `D1ChartProducer`, `DeepestGaugeChart`, `DeepestL2Wiring`, `S1QuasiSplit`, `S1Spectator`.
- [ ] NOT wired into `DLNFibre.lean` (single-writer aggregator — the controller wires + AxCheck).
- [ ] Zero `sorry`/`axiom`/`native_decide`/`#exit`; `scripts/sorries` clean; forced `#print axioms` on the
      producer theorems = `[propext, Classical.choice, Quot.sound]` (the §5 interface enters as a
      hypothesis, NOT a sorry).
- [ ] Statement card per `docs/policies/statement-cards.md`.
- [ ] Report: the deepest-type producer (banked unconditionally) + the middle-stratum producer (conditional
      on `hResolveM'`) + the arithmetic lemma; or a precise wall.
