DECORRELATED FIDELITY RED-TEAM (Lean 4 / Mathlib v4.29, RLCT formalisation).

CONTEXT. We are formalising a per-node RLCT recursion step for deep-linear-network square loss
(Aoyagi-style resolution of singularities). A per-node "core" function `flatCore` at the deepest
point (0,0) is claimed to have its RLCT split as nReg/2 + rlctAtOn(G²). The route has a 3-WRONG
history: (a) a clean measure-preserving change-of-variables `flatCore∘χ = u·Φ` was proposed, then
RETRACTED — the per-node transvection L·A·R is det-1 (measure-preserving) but the LOSS ‖Â·A2‖² is NOT
invariant under it (L unipotent ≠ orthogonal); (b) a packaging form had a false existence theorem;
(c) the clean-factor hypothesis was unsatisfiable. The CORRECTED route is a two-sided SQUEEZE comparing
flatCore and Φ at the SAME point (no change of variables, no measure Jacobian).

THE CORRECTED DATUM (verbatim, all fields):

  structure IsSchurStraightenSqueeze {L nReg} (M : Fin (L+1) → ℕ) (S : ChainDimSplit M)
      {Y} [MeasureSpace Y][TopologicalSpace Y][Zero Y]
      (flatCore : (Fin nReg → ℝ) × Y → ℝ)   -- per-node core at the deepest point
      (G : Y → ℝ)                            -- reduced-chain core
      (redEmbed : Y → Params S.red) (c₁ c₂ : ℝ) : Prop where
    Fmeas : Measurable flatCore
    Gmeas : Measurable G
    redCore_eq : ∀ y, G y ^ 2 = dlnLoss S.red 0 (redEmbed y)   -- G² = reduced-chain loss
    Gne : ∃ U ∈ 𝓝 (0:Y), ∀ᵐ z ∂(volume.restrict U), G z ≠ 0   -- germ-nonvanishing of G
    c₁pos : 0 < c₁
    c₂pos : 0 < c₂
    squeeze : ∃ U ∈ 𝓝 ((0,0) : (Fin nReg → ℝ) × Y), ∀ w ∈ U,
        0 ≤ Φ w ∧ c₁ * Φ w ≤ flatCore w ∧ flatCore w ≤ c₂ * Φ w   -- where Φ w = (∑ᵢ (w.1 i)²) + (G w.2)²
    measure_drops : ∑ s, S.red s < ∑ s, M s

  -- The consumed split (PROVEN from the datum via a squeeze-RLCT-equality lemma + a smooth-block
  -- additivity lemma `rlctAtOn(∑xᵢ²+G²)(0,y0) = nReg/2 + rlctAtOn(G²)(y0)` guarded by Gne):
  theorem schur_straighten_squeeze_of_data (h : IsSchurStraightenSqueeze M S flatCore G redEmbed c₁ c₂) :
      rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn (fun y => G y^2) 0

The squeeze-RLCT-equality lemma: if F,Φ≥0 near wstar, both measurable, c₁·Φ≤F≤c₂·Φ with c₁,c₂>0, then
rlctAtOn F wstar = rlctAtOn Φ wstar (proved by two-sided monotonicity + stripping the positive constant
units; the F=0⟺Φ=0 vanishing comes from c₁,c₂>0).

THE GEOMETRY THE EXISTENCE PRODUCER (separate, downstream) MUST FILL THE squeeze FIELD FROM:
flatCore is the actual node loss; Φ's regular part ∑Eᵢ² are nReg regular generators (pivot-row entries
after a blow-up made the pivot a hard 1); G² = ‖S·Bred‖² the residual Schur-chain core = dlnLoss S.red 0.
The squeeze c₁·Φ≤flatCore≤c₂·Φ rests on `flatCore − Φ ∈ ideal(regular gens)` (a bounded-linear-
perturbation estimate near 0).

QUESTIONS (mark inference vs fact; be adversarial, hunt a 4th wrong-statement):
1. Is the SQUEEZE the faithful encoding of "compare at same point, no c-o-v"? Does stating the rlct AT
   (0,0) (the literal basepoint) correctly pin "anchor = deepest point" WITHOUT a chart map χ (vs the
   retracted route which needed χ 0 = 0)?
2. Is the genuine-unit pin met by c₁,c₂>0 (positive CONSTANTS), as opposed to an abstract `Measurable u`
   that could vanish? Is `0<c₁` (not just `0≤`) load-bearing for the F=0⟺Φ=0 / RLCT-equality?
3. NON-VACUITY / FILLABILITY: is the squeeze field shaped so the geometric existence proof CAN fill it?
   In particular: is there any tension between `redCore_eq` (G²=dlnLoss S.red 0, forcing G²≥0 and
   G²(redEmbed-image)) and the squeeze (Φ = ∑Eᵢ²+G²)? Could the squeeze be UNSATISFIABLE by the actual
   loss for a structural reason (e.g. flatCore not comparable to Φ because the cross-terms 2G·E·h in the
   true F = ∑Eᵢ²+(G+E·h)² break a two-sided constant bound near 0)?
4. Does the conclusion `rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn(G²) 0` follow GENUINELY (not
   vacuously — e.g. could both sides be ⊤ trivially)? The Gne guard is meant to stop the G≡0⟹⊤
   degeneracy. Is Gne the right guard, and is it consistent with redCore_eq?
5. ANY 4th wrong-statement issue: a field that is either too weak (lets a degenerate datum through) or
   too strong (the producer can't supply it). Flag precisely.
