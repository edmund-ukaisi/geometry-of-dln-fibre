<task>
You are red-teaming a Lean 4 + Mathlib formalisation for a FIDELITY review. I (the reviewer) have a
provisional verdict and want a decorrelated second opinion on THREE soundness/faithfulness judgments.
Do not trust my framing; reason from the structure I give you.

CONTEXT. We formalise the RLCT (real log canonical threshold) of deep-linear-network square loss. There
is a per-node "descent step": at a non-leaf width chain M=(2,2,2), the RLCT of a post-blow-up core
`flatCore` at the deepest point equals `nReg/2 + (RLCT of the reduced-chain loss dlnLoss (1,1,2) 0 at 0)`.
The number is 2/2 + 1/2 = 3/2.

The architecture (all PROVEN, 0 sorry, axioms = [propext, Classical.choice, Quot.sound]):

- `RouteMNodeDescent` is a structure bundling: `flatCore : (Fin nReg → ℝ) × Y → ℝ`, a `ReducedTransport S Y`
  (a measure-preserving homeomorphism `redEmbed : Y ≃ₜ Params S.red` with `redEmbed 0 = 0` and
  `hredCore : ∀ y, G y ^2 = dlnLoss S.red 0 (redEmbed y)`), squeeze constants c₁,c₂, and an
  `IsSchurStraightenSqueeze` proof.

- `descentStep` theorem: `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (dlnLoss S.red 0) 0`. Its proof is:
  `schur_straighten_squeeze_of_data` (gives `nReg/2 + rlctAtOn (G²) 0`, via a TWO-SIDED SQUEEZE
  `c₁·Φ ≤ flatCore ≤ c₂·Φ` where `Φ = (∑ Eᵢ²) + G²` — NO change of variables, NO Jacobian, comparing
  flatCore and Φ at the SAME point) THEN `ReducedTransport.descent` (gives `rlctAtOn (G²) 0 =
  rlctAtOn (dlnLoss S.red 0) 0`, via the MP homeomorphism on the REDUCED ambient Y).

- The constructor `ofNodePresentation` takes a `ReducedTransport`, a `flatCore`, T, `bcol`, `SΓ`,
  measurability, germ-nonvanishing of G, well-foundedness, and an `hnode` existential:
  `∃ U ∈ 𝓝 (0,0), ∀ w ∈ U, flatCore w = (∑ⱼ w.1ⱼ²) + (∑ᵢⱼ (bcol w i · w.1 j + SΓ w i j)²)
     ∧ G(w.2)² = ∑ᵢⱼ (SΓ w i j)² ∧ ∑ᵢ (bcol w i)² ≤ T²`.
  The squeeze field is discharged by `schur_node_squeeze_unif` (a pure Young-inequality estimate:
  `(2(1+T²))⁻¹·Φ ≤ flatCore ≤ (2+2T²)·Φ` whenever `∑bcol² ≤ T²`).

THE SPECIFIC (2,2,2) ANCHOR being reviewed instantiates this with:
- `Y = Fin (flatDim (1,1,2)) → ℝ`, `redEmbed = (paramsEquivFlat (1,1,2)).symm` upgraded to ≃ₜ (the generic
  measure-preserving "flattening" homeomorphism between Params and the flat coordinate vector — PROVEN MP).
- `G y = √(dlnLoss (1,1,2) 0 (redEmbed y))`, so `hredCore` is `Real.sq_sqrt ∘ dlnLoss_nonneg`. (`dlnLoss (1,1,2) 0
   A = (α·β0)²+(α·β1)²` with α=A⁰₀₀, [β0,β1]=[A¹₀₀,A¹₀₁].)
- `nReg = 2`, `Mblk = Unit` (single lower row).
- `SΓ222 w () j = α·βⱼ` where α,βⱼ are read off `redEmbed w.2` (the reduced (1,1,2) tuple). So
  `∑ⱼ SΓ² = (α·β0)²+(α·β1)² = G²`. ✓ exactly the `hredCore` shape.
- `bcol222 w () = w.1 0` — the FIRST REGULAR COORDINATE of the regular block `w.1 : Fin 2 → ℝ`.
- `flatCore222 w := (∑ⱼ w.1ⱼ²) + (∑ᵢⱼ (bcol222 w i · w.1 j + SΓ222 w i j)²)` — DEFINED to be exactly the
  hnode RHS (so the first hnode conjunct is `rfl`).
- `T=1`, `U = {w | (w.1 0)² < 1}`, on which `∑bcol² = (w.1 0)² < 1 = T²`.

THE CERTIFICATE this transcribes says the GENUINE post-blow-up Schur core has `bcol = y2` (a PIVOT-COLUMN
coordinate of the blown-up matrix Â=[[1,y1],[y2,y3]]), `Erow = [x4+y1·x6, x5+y1·x7]` (the pivot-row product),
`SΓ = (y3−y2y1)·[x6,x7]`. The cert notes the genuine `redEmbed` requires a det-1 SHEAR straightening
`(y3−y2y1) ↦ y3'` before the coordinate identification, and calls that shear "the one genuinely-new
construction in the anchor."

THE THREE JUDGMENTS I want your independent read on:

(J3 — SOUNDNESS) The anchor builds at the `flatCore` level (defining flatCore as the Schur normal form) and
goes through the SQUEEZE + the reduced-ambient MP transport — NOT through any "raw dlnLoss (2,2,2) ∘ MP-chart
= squeezable" step (which a sibling file `RouteMO1Bridge` flags as UNSOUND for blow-up nodes, because the
blow-up Jacobian y0³ shifts the threshold and an MP reindex cannot carry it). Question: is the descentStep
conclusion `rlctAtOn flatCore222 (0,0) = 3/2` SOUND as a statement about flatCore222 (the abstract object
literally defined in the file), independent of whether flatCore222 equals the true post-blow-up (2,2,2)
core? I.e. is the theorem honest about WHICH object it computes the RLCT of?

(J4 — FAITHFULNESS / VACUITY) `bcol222 = w.1 0` is a REGULAR coordinate (an Erow slot), not the cert's pivot
column y2. At the deepest point both vanish. Concern: does choosing bcol = (a regular coord that also appears
as Erow=w.1) instead of an INDEPENDENT pivot column collapse the cross-term `bcol·Erow` into something
degenerate (e.g. `w.1 0 · w.1 j`, a product of regular coords) — making the "defect" structure vacuous or
self-referential? Does this matter for what `descentStep` proves? Specifically: the squeeze bound only needs
`∑bcol² ≤ T²` on a neighborhood; the RLCT conclusion is `nReg/2 + rlctAtOn(G²)` REGARDLESS of bcol's value
(bcol enters only via the squeeze, which holds for any bounded bcol). So is bcol's faithfulness load-bearing
for the THEOREM, or is it purely a "does this object resemble the real core" cosmetic question? Rule on
whether this is an honest standalone anchor or a vacuity dressed up as the real core.

(J7 — ReducedTransport via generic flattening) The anchor uses `redEmbed = (paramsEquivFlat (1,1,2)).symm`
(the generic Params↔flat-vector MP homeomorphism) as the ReducedTransport, NOT the cert's explicit det-1
shear. The ReducedTransport contract is exactly: a measure-preserving ≃ₜ `Y ≃ₜ Params S.red` with
`redEmbed 0 = 0` and `G y² = dlnLoss S.red 0 (redEmbed y)`. With `Y := flat-vector` and `G := √(dlnLoss ∘
redEmbed)`, all six fields hold trivially. Question: does using the generic flattening (rather than the
shear) SKIP load-bearing content of the descent, or does it legitimately discharge the ReducedTransport
contract? Note the shear was described as needed to turn `(y3−y2y1)` into a single coordinate — but here
`Y` is ALREADY `Params (1,1,2)` flattened (with α=A⁰₀₀ a genuine single coordinate), and G is DEFINED as
√(dlnLoss∘redEmbed), so hredCore is definitional. Is there a hidden circularity (G defined via the very loss
it is supposed to reduce to) that makes the transport vacuous, or is this a legitimate "the reduced ambient
IS the flattened reduced Params" identification?

Cross-cutting: the descentStep takes `rlctAtOn (dlnLoss (1,1,2) 0) 0` as an OUTPUT (not computed here); the
=3/2 endpoint theorem takes `hred : rlctAtOn (dlnLoss (1,1,2) 0) 0 = 1/2` as a HYPOTHESIS. Is deferring the
reduced-node value to a hypothesis honest (it is the recursion's child value), or does it hand-wave the
headline?
</task>

<output_contract>
For EACH of J3, J4, J7: a one-word verdict (SOUND / UNSOUND / VACUOUS / FAITHFUL / COSMETIC-ONLY /
CIRCULAR), then 3-6 sentences of reasoning. Then a CROSS-CUTTING ruling on the hred hypothesis (1-3
sentences). Then a single overall line: does this constitute an honest decorrelated standalone anchor, or
is it a vacuity? Be precise and adversarial; if you think I am missing a hole, name it. ≤ 600 words total.
</output_contract>

<grounding_rules>
You are reasoning about the LOGICAL STRUCTURE I described, not reading the files. Flag any place where your
verdict DEPENDS on a fact you cannot verify from my description (e.g. "IF paramsEquivFlat is genuinely MP
then ... ELSE ..."). Distinguish (a) what is provably true of the abstract objects as defined, from (b) what
would be needed for the anchor to faithfully mirror the true (2,2,2) blow-up geometry. Do not invent Mathlib
lemma behavior; if a step's soundness hinges on a Mathlib fact, say so.
</grounding_rules>
