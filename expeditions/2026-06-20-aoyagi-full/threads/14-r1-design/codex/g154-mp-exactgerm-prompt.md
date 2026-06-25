<task>
Lean/Mathlib RLCT proof. A SHARP truth-value I must get right before telling a teammate their
constructor is undischargeable (or before I try to discharge it).

SETUP. `Φ_loss : (Fin N → ℝ) → ℝ` is the deep-linear square-Frobenius loss in flat coords (a fixed
polynomial, `‖∏C − B‖²`), with a "deepest point" `w0` (a singular zero of the loss germ). We have a
fixed normal form `NF(reg, core, spec) = (∑ reg_i²) + dlnLoss_M(core)`, where `dlnLoss_M(core)` is a
SMALLER deep-linear loss (a fixed polynomial in the `core` block, = `‖∏(reduced layers)‖²`), and `spec`
are spectator coords the loss ignores. Same total dimension `N = dim reg + dim core + dim spec`.

A teammate's constructor `ofExactGerm` asks for:
  a homeomorphism `split : (Fin N → ℝ) ≃ₜ (reg)×(core)×(spec)`, MEASURE-PRESERVING (volume),
  with `split w0 = 0`, such that the GERM equality holds near w0:
      Φ_loss(w) =ᶠ[𝓝 w0]  (∑ (split w).reg_i²) + dlnLoss_M((split w).core)
  i.e. the loss pulls back EXACTLY (c₁=c₂=1) to the normal form, via a measure-preserving split.

THE CERT (trusted exact algebra). The loss germ at w0 IS analytically equivalent to NF, BUT the change
of variables achieving it (the "gauge slice + regular-residual + Schur/gauge-normalization") has
Jacobian determinant `det(A)^{−(r+M)}·det(B)^{−M0}` where A,B ≈ I near w0 — a bounded UNIT, ≠ 1 in
general. The reduced core is the GAUGE-NORMALIZED chain `T̃ = T·(I−VY)⁻¹·S` (the internal gauge unit
g=(I−VY)⁻¹ absorbed); the RAW core `∏T` is provably WRONG (counterexample: 3 layers, C1C2C3 =
blockdiag[1, −ε⁴] has ∑reg²=0, raw ∏T=0, but loss=ε⁸ ≠ 0).

MY CLAIM (want it checked): `ofExactGerm` is UNDISCHARGEABLE as stated, because:
 - the loss→NF c-o-v has det ≠ 1 (the cert's Jacobian), so the SPECIFIC gauge chart is not MP;
 - I argued: therefore no MP split achieves the exact germ.
BUT I realize the flaw in my own argument: "measure-preserving" for a NONLINEAR homeomorphism means the
Jacobian det is ±1 A.E. (volume-preserving), NOT that it's linear. A different split — volume-preserving
but nonlinear, compensating the g-absorption's local stretching elsewhere (e.g. a shear in the reg/spec
coords) — MIGHT achieve the same NF while staying MP. So my "no MP split" claim may be FALSE.
</task>

<output_contract>
Terse, decisive. Answer:
1. Is `ofExactGerm` (MP split + EXACT germ to NF with the dlnLoss_M core) DISCHARGEABLE or NOT? Give a
   yes/no and the core reason in 1-2 sentences.
2. THE CRUX: can a VOLUME-PRESERVING (det = ±1 a.e.) nonlinear homeomorphism pull the loss germ EXACTLY
   onto `∑reg² + dlnLoss_M(core)` (gauge-normalized core), by compensating the g-absorption's det≠1
   stretching in the reg/spec coords? Or is there an INVARIANT obstruction (an RLCT/multiplicity/Newton-
   polytope invariant) that a volume-preserving map cannot change, forcing det≠1?
3. If DISCHARGEABLE via a volume-preserving nonlinear split: is the compensation construction TRACTABLE
   in Lean (vs the coreEmbed-field alternative where the g-unit is peeled as a bounded unit weight)?
   Which is the cheaper Lean path — (a) build a volume-preserving split absorbing g, or (b) add a
   coreEmbed field + peel the g-unit in the reduced-core transport via a unit-weight-invariance lemma?
4. The single cleanest way to state the TRUE comparability the squeeze needs, given all this.
5. The most likely way I'm still wrong.
</output_contract>

<grounding_rules>
The cert's exact algebra (det = det(A)^{-(r+M)}det(B)^{-M0}, T̃ gauge-normalized core, raw-∏T false) is
TRUSTED. Reason about whether an MP/volume-preserving split can still achieve the exact germ — that's
the open question. Distinguish a genuine invariant obstruction (fact) from "the obvious chart isn't MP"
(weaker). If you assert dischargeable, sketch the volume-preserving compensation; if not, name the invariant.
</grounding_rules>
