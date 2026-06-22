# Statement card — the CORRECTED per-node SQUEEZE lane (datum + chain + EXISTENCE)

- **Status:** `sorry-free`, per-node lane CLOSED (awaiting fidelity review). Branch
  `origin/fm2/r1-squeeze-complete` @fb80122 (the canonical line: #129/#130/#131 verdict docs + g131 cert
  + chain + datum + existence). File `lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean`. Build
  GREEN (2673 jobs, 0 sorry); ALL decls axiom clean-three (S2-FREE).
- **Supersedes** the retracted clean-MP datum `IsSchurStraighten` / `schur_straighten_of_data` (pp2 #129).
  Implements pp2 #129 (squeeze, not clean MP factor) + #130 (the two transport pins) + #131 (the
  ideal-membership existence content).

## The per-node EXISTENCE (closes the lane)

```text
schur_straighten_squeeze_exists {L nReg} (M) (S : ChainDimSplit M) {Y}[meas/top/zero] {Mblk}[Fintype]
    (flatCore : (Fin nReg → ℝ) × Y → ℝ) (G : Y → ℝ) (redEmbed : Y → Params S.red) (T : ℝ)
    (bcol) (SΓ) (hFmeas) (hGmeas) (hredCore : ∀ y, G y² = dlnLoss S.red 0 (redEmbed y))
    (hGne) (hdrop : ∑ S.red < ∑ M)
    (hnode : ∃ U ∈ 𝓝 (0,0), ∀ w ∈ U,
        flatCore w = (∑ⱼ w.1ⱼ²) + ∑ᵢⱼ (bcol w i · w.1 j + SΓ w i j)²    -- the Schur node form
        ∧ G w.2² = ∑ᵢⱼ (SΓ w i j)²                                      -- reduced core = ‖SΓ‖²
        ∧ ∑ᵢ (bcol w i)² ≤ T²) :                                        -- bounded pivot column
    ∃ c₁ c₂, IsSchurStraightenSqueeze M S flatCore G redEmbed c₁ c₂
```

`c₁ = (2(1+T²))⁻¹ > 0`, `c₂ = 2+2T²`. **Faithfulness (Codex g132):** the `flatCore = ‖Â·A2‖²`
coordinate LAYOUT is the blow-up (B)-lane contract — supplied as the explicit `hnode` interface
hypothesis, NOT asserted as `dlnLoss M 0 coords = ‖Â·A2‖²` (which would smuggle guessed plumbing). The
`squeeze` field is `schur_node_squeeze_unif`; the others are the supplied contracts.

## The lemmas (5 new decls)

```text
rlctAtOn_mono {M} [MeasureSpace M] [TopologicalSpace M] [OpensMeasurableSpace M]
    (F G : M → ℝ) (wstar) (hFmeas : Measurable F)
    (hdom : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, |G w| ≤ |F w| ∧ (G w = 0 → F w = 0)) :
    rlctAtOn G wstar ≤ rlctAtOn F wstar          -- general-domain monotonicity (new bedrock)

rlctAtOn_squeeze {M} … (F Φ : M → ℝ) (wstar) (hFmeas) (hΦmeas) (c₁ c₂) (hc₁ : 0<c₁) (hc₂ : 0<c₂)
    (hsq : ∃ U ∈ 𝓝 wstar, ∀ w ∈ U, 0 ≤ Φ w ∧ c₁*Φ w ≤ F w ∧ F w ≤ c₂*Φ w) :
    rlctAtOn F wstar = rlctAtOn Φ wstar          -- the squeeze RLCT-equality (mono ×2 + unit strip)

schur_recursion_step_squeeze {nReg} {Y} [proper measure instances] [Zero Y]
    (flatCore : (Fin nReg → ℝ) × Y → ℝ) (hFmeas) (G : Y → ℝ) (hGmeas)
    (hGne) (c₁ c₂) (hc₁ : 0<c₁) (hc₂ : 0<c₂) (hsq : squeeze of flatCore by smoothBlockSplitForm G) :
    rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0   -- the per-node rlct split

structure IsSchurStraightenSqueeze {L} {nReg} (M) (S : ChainDimSplit M) {Y} [meas/top/zero]
    (flatCore) (G) (redEmbed : Y → Params S.red) (c₁ c₂) : Prop
  -- fields: Fmeas, Gmeas, redCore_eq (G² = dlnLoss S.red 0 ∘ redEmbed), Gne, c₁pos, c₂pos,
  --         squeeze (c₁·Φ ≤ flatCore ≤ c₂·Φ near (0,0)), measure_drops

schur_straighten_squeeze_of_data … (h : IsSchurStraightenSqueeze …) :
    rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (G²) 0   -- datum ⟹ the split (one-liner via the step)
```

## English gloss

The per-node loss `flatCore` at the deepest point is SQUEEZED by the smooth-block normal form
`Φ = (∑ Eᵢ²) + G²` (`G² =` the reduced-chain loss `dlnLoss S.red 0`): `c₁·Φ ≤ flatCore ≤ c₂·Φ` near
`(0,0)` with `0 < c₁, c₂`. Then the per-node RLCT splits as `nReg/2 + rlctAtOn(G²)` — the regular smooth
block plus the strictly-smaller reduced-chain core. The route compares `flatCore` and `Φ` at the SAME
point: NO change of variables, NO measure Jacobian (the `mp_schur_transvection_vec` MP fact is TRUE but
off this path — the transvection's det-1-ness does not make the loss invariant, pp2 #129).

## Fidelity to pp2 #129/#130 (the two transport pins)

- **(i) anchor at the deepest point** (#130 (i), "χ 0 = 0"): in the chart-free squeeze the basepoint of
  the rlct IS `(0,0)` (the deepest point). `schur_recursion_step_squeeze` concludes `rlctAtOn flatCore
  (0,0) = …` at `(0,0)`. No `χ` field — the anchor is the basepoint. (= controller-confirmed default 1.)
- **(ii) genuine unit, bounded away from 0** (#130 (ii)): the unit role is the positive squeeze constants
  `c₁, c₂` (`c₁pos`, `c₂pos`), bounded away from `0` by construction — exactly
  `rlctAtOn_unit_invariant_aux`'s `a > 0`. NOT an abstract `Measurable u` (which could vanish, the gap
  #130 named). (= default 3.)
- **Φ reduced part** = `dlnLoss S.red 0` via `redCore_eq : G y² = dlnLoss S.red 0 (redEmbed y)`
  (`G = √`, valid by `dlnLoss_nonneg`). (= default 2.)
- **`flatCore − Φ ∈ ideal(E)`** is NOT a field — it is the upstream EXISTENCE obligation (pp2 #11) that
  PRODUCES the squeeze inequality; the datum carries the squeeze, which is what the chain consumes. (= default 4.)

## Honest scope / what is NOT here

- This is the per-node rlct ENGINE (the squeeze → split). The PRODUCER of the `squeeze` field — proving
  `c₁·Φ ≤ flatCore ≤ c₂·Φ` from `flatCore − Φ ∈ ideal(regular gens)` (the bounded-linear-perturbation
  estimate, g128 §"the sound bridge") at a general `m×k` node — is pp2's task #11, NOT discharged here.
- The retracted `IsSchurStraighten` / `schur_straighten_of_data` remain in-file marked SUPERSEDED (true
  conditionals on an unsatisfiable clean-factor hypothesis — kept as the dead-route record, not built on).
- `mp_schur_transvection_vec` (the det-1-is-MP fact) is true reusable bedrock on `fm2/mp-transvection`,
  OFF this path.

## Branch note for integration

`f6fedb1` is on the consolidate base. The canonical integration line is `g129-r1-squeeze-verdict` (pp2
verdict docs @728fbb0/a1dc1e4 + my cherry-picked squeeze chain @48cefc0). The DATUM commit (the +71 in
f6fedb1's re-state) still needs cherry-picking onto the verdict line — or merge `fm2/squeeze-datum`.
