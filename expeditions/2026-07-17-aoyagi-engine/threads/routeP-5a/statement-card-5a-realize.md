# Statement card — RUNG 5a: `AtlasRealizesExponents` discharged for (3,3,4)

- **Status.** sorry-free (pending fidelity review).
- **Module.** `lean/DLNFibre/DLN/Aoyagi/Corank2Realize334.lean`.
- **Lane branch.** `expedition/aoyagi-engine-routeP` (built on 5b @ `6ebe99f79`).
- **Task.** #140 (rung 5a of #130).
- **Axioms.** `#print axioms` (force-elaborated, olean deleted) = `[propext, Classical.choice,
  Quot.sound]` on all four results (clean-three, no `sorryAx`).

## The seam being discharged

`AtlasRealizesExponents d res` (`RecursionAdapter`) — the GEOMETRIC obligation of
`exists_coreResolution` — has two clauses:
- **(i)** `∀ c a, a ∈ bindingAxes ((res.charts c).bexp (res.charts c).k₀) →
  (res.charts c).jac a + 1 ∈ terminalExponents (buildTree d (conOracle d) conRoot)`;
- **(ii)** `∀ l ∈ leaves …, ∀ k, l.divExp k = minAdm d →
  ∃ c a, a ∈ bindingAxes … ∧ (res.charts c).jac a + 1 = l.divExp k`.

For (3,3,4): the chart's binding axes are `{E = coord 0, c11 = coord 20}` (dominant monomial `⟨c11·E⟩`,
part-C `Corank2CoreGenWrap`), with `jac = [E:7, α:3, c11:8]` (5b `Corank2ChartJac`); `α = coord 1` is
NON-binding (`bexp α = 0`). So the binding-axis values are `jac+1 = {E : 8, c11 : 9}`, and
`minAdm ![3,3,4] = 8`.

## The real content — `{8, 9} ⊆ terminalExponents (buildTree ![3,3,4] …)`

`terminalExponents` is the value-support `{(Mval ![3,3,4] a).toNat : a realized in the tree}`
(`leaves_resRank_zero` kills the residual). For M=(3,3,4), L=2, `Adm` forces `T₁ = 0`, `T₀ ∈ {0,1,2,3}`,
`Mval(T₀) = (3−T₀)² + 4T₀`:

| `T₀` | profile | `Mval` |
|---|---|---|
| 1 | `(1,0)` | **8** = minAdm (E-axis) |
| 2 | `(2,0)` | **9** (c11-axis) |
| 0 | `(0,0)` | 9 |
| 3 | `(3,0)` | 12 |

- `8 = minAdm` is the banked minimizer (`o5_core_realized`).
- **`9` is NOT banked** — it is not the minimizer. It is the c11-axis value the controller flagged (the
  fan/orbit worry). Discharged directly: `realize_aux` (the banked cert-§4 descent invariant, GENERAL in
  the profile, sorry-free) run on the CLEARABLE ADMISSIBLE profile `(2,0)` realizes it as an analytic
  leaf divisor; `isFullMonomialization_buildTree_conRoot` reads `(Mval (2,0)).toNat = 9` off that leaf.
  **No R7** (`realizedProfiles_eq_clearableAdm` is a retired off-cone `sorry`) — only its `⊇`-direction
  value-consequence for the single profile `(2,0)`, which `realize_aux` already proves.
- The fan/orbit worry DISSOLVES: `9` is genuinely a terminal exponent (the `(2,0)` leaf), not an
  over-count. `Clearable ![3,3,4] a` is vacuously true for L=2 (the only saturated-descent case `i=0,j=1`
  has conclusion = hypothesis), so `(2,0)` is clearable.

## Lean signatures

- `clearableAdm_mval_mem_terminalExponents (M) (hL : 0 < L) (hMpos : ∀ i, 0 < M i) (a) (ha : a ∈ Adm M)
  (hc : Clearable M a) : (Mval M a).toNat ∈ terminalExponents (buildTree M (conOracle M) conRoot)` —
  the reusable engine-grade bridge (`realize_aux` + `isFullMonomialization`); general-`d` 5a consumes it.
- `mem_terminalExponents_334_eight : (8 : ℕ) ∈ terminalExponents (buildTree ![3,3,4] …)` — via `(1,0)`.
- `mem_terminalExponents_334_nine  : (9 : ℕ) ∈ terminalExponents (buildTree ![3,3,4] …)` — via `(2,0)`.
- `atlasRealizesExponents_334 {D Mgen} {F} (res : Resolution F 0) (aE aC : Fin D)
  (hbind : ∀ c, bindingAxes ((res.charts c).bexp (res.charts c).k₀) = {aE, aC})
  (hjE : ∀ c, (res.charts c).jac aE = 7) (hjC : ∀ c, (res.charts c).jac aC = 8) :
  AtlasRealizesExponents ![3,3,4] res` — the reduction (chart data ⟹ seam). Generic in `D` and the axis
  pair so rung 5d supplies the concrete chart (`aE = ⟨0,_⟩`, `aC = ⟨20,_⟩`).
- Local `instance : Decidable (Clearable M a)` (unfold + `infer_instance`), enabling the `decide`
  discharge of the concrete `Adm`/`Clearable`/`Mval` facts (mirrors `admPred`'s decidability instance).

Numeric anchors (`example … := by decide`): `(Mval ![3,3,4] (1,0)).toNat = 8`,
`(Mval ![3,3,4] (2,0)).toNat = 9`.

## Method / fidelity notes

- Membership constructed with the same plumbing `minAdm_le_terminalExponents` uses in reverse
  (`terminalExponents` unfold → `List.mem_flatMap`/`mem_append`/`mem_map` + `mem_finRange`).
- Clause (ii) collapses to `∃ c a binding, jac a + 1 = minAdm` (the RHS is `l.divExp k = minAdm` under
  the hypothesis), answered by the E-axis (`jac 0 + 1 = 8 = minAdm`); the chart witness comes from
  `res.hne`. No dependency on the leaf multiplicity or how many leaves attain 8.
- 5a is stated as a REDUCTION (res + chart data hypotheses), NOT `∃ res, AtlasRealizesExponents` — the
  concrete `res` is rung 5d (assembly). 5d applies `atlasRealizesExponents_334` then feeds
  `exists_hlb_hattain_of_exists_atlasRealizesExponents` (`RecursionAdapter`).

## Fidelity question for review

Does the Lean match the claim: (a) is `atlasRealizesExponents_334` a faithful discharge of BOTH clauses
of `AtlasRealizesExponents` (not a weakened restatement)? (b) is `9 ∈ terminalExponents` genuinely proved
sorry-free WITHOUT R7 (via `realize_aux` on `(2,0)`), and is `(2,0)` genuinely `Clearable ∩ Adm`?
(c) are the reduction's chart-data hypotheses (`bindingAxes = {aE,aC}`, `jac aE = 7`, `jac aC = 8`) the
correct (3,3,4) 5b/part-C data that rung 5d will actually supply? (d) does clause (ii)'s collapse to the
E-axis witness lose anything the seam intends?
