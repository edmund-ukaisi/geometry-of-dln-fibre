<task>
Lean 4 / Mathlib v4.29. I must BUILD `schur_straighten_squeeze_exists` — the per-node EXISTENCE that
produces an `IsSchurStraightenSqueeze` datum for the actual loss. The MATH is certified (pp2 #131,
decorrelated); I have all the abstract pieces GREEN. I need the cleanest faithful Lean STATEMENT shape
that closes the per-node lane without guessing the blow-up lane's coordinate plumbing. Help me pin it.

WHAT I HAVE GREEN (abstract building blocks, all proven, axiom-clean):
- `schur_row_decomp (a b D β Γ)` : `b*β + D*Γ = b*(1*β + a*Γ) + (D − b*a)*Γ`  (the Schur row decomp;
  lower = b·E_row + S·A2red, S = D−b·a)
- `schur_lossDiff_eq_cofactor (bErow SΓ)` : `(∑ᵢⱼ(bErowᵢⱼ+SΓᵢⱼ)²) − (∑ᵢⱼ SΓᵢⱼ²) = ∑ᵢⱼ bErowᵢⱼ(bErowᵢⱼ+2SΓᵢⱼ)`
- `schur_lossDiff_mem_ideal (F Φ E g) (h : F−Φ = ∑ⱼ Eⱼ·gⱼ)` : `F−Φ ∈ Ideal.span (range E)`
- `squeeze_bounds_abstract (E p s t) (hp : ∑pⱼ² ≤ t²·∑Eᵢ²)` : `(∑Eᵢ²+∑sⱼ²) ≤ 2(1+t²)·(∑Eᵢ²+∑(pⱼ+sⱼ)²)
  ∧ (∑Eᵢ²+∑(pⱼ+sⱼ)²) ≤ (2+2t²)·(∑Eᵢ²+∑sⱼ²)`   ⟹ squeeze c₁=(2(1+t²))⁻¹>0, c₂=2+2t²
- `IsSchurStraightenSqueeze {L}{nReg}(M)(S : ChainDimSplit M){Y}[meas/top/zero](flatCore : (Fin nReg→ℝ)×Y→ℝ)
  (G : Y→ℝ)(redEmbed : Y→Params S.red)(c₁ c₂)` with fields Fmeas, Gmeas, redCore_eq (G y² = dlnLoss S.red 0 (redEmbed y)),
  Gne, c₁pos, c₂pos, squeeze (∃ U∈𝓝(0,0), ∀w∈U, 0≤Φ w ∧ c₁·Φ w ≤ flatCore w ∧ flatCore w ≤ c₂·Φ w,
  Φ = (∑ E²)+G²), measure_drops.
- consumer `schur_straighten_squeeze_of_data (h : IsSchurStraightenSqueeze …) : rlctAtOn flatCore (0,0) = nReg/2 + rlctAtOn(G²) 0`.

THE NODE (g131): after one blow-up, the per-node loss is `flatCore = ‖Â·A2‖²_F`, `Â : m×k` with HARD pivot
`Â[0,0]=1`, `A2 : k×n`. Block: `Â=[[1,a],[b,D]]`, `A2=[[β],[Γ]]`. `E_row=(Â·A2)[0,:]=β+a·Γ` (nReg=n regular
gens), `S=D−b·a`, `A2red=Γ`, reduced core `‖S·Γ‖²=dlnLoss S.red 0`. The `Â·A2` is the analog of the
(2,2,2) anchor's `‖A0·A1‖² = ∑ᵢⱼ(∑ₖ A0ᵢₖ A1ₖⱼ)²`.

THE TENSION (what I must NOT guess): the FULL L-layer `dlnLoss M 0 = ‖A⁽¹⁾···A⁽ᴸ⁾‖²` (L factors), but the
node is a 2-FACTOR `Â·A2`. The reduction (L factors → Â = post-blow-up first factor, A2 = product of the
rest) + the (Fin nReg→ℝ)×Y coordinate split + the redEmbed : Y → Params S.red is the BLOW-UP LANE's
coordinate contract (fm's (B) lane), which I don't have. I do NOT want to hardcode a guessed coordinate
layout for dlnLoss M 0.
</task>

<output_contract>
  1. RECOMMEND the cleanest faithful STATEMENT for `schur_straighten_squeeze_exists` that closes the
     per-node lane. Specifically: should it be stated
     (A) at the 2-FACTOR MATRIX NODE — input the matrices Â (with Â 0 0 = 1), A2 directly, flatCore :=
         ‖Â·A2‖², and CONSTRUCT the IsSchurStraightenSqueeze (the (A)-lane existence; the L-layer→2-factor
         reduction is left to the blow-up lane as a separate, explicit hypothesis/interface)? OR
     (B) attempt the full dlnLoss M 0 with an assumed blow-up-coordinate equality as a hypothesis? OR
     (C) something else.
     Pick one, justify in ≤4 lines. Which keeps me faithful (no guessed plumbing) AND genuinely closes
     the per-node math?
  2. For the WINNER: sketch the Lean statement signature (hypotheses + conclusion), naming which of my
     green lemmas discharge each datum field. Flag the ONE hardest sub-step.
  3. The coordinate bookkeeping: at the 2-factor node, what is the cleanest choice of `Y` (the reduced
     ambient) and the `(Fin nReg → ℝ) × Y` split so flatCore/Φ/E/p/s map cleanly to my abstract lemmas?
     (E.g. Y = Â's non-pivot entries × A2's entries? Is there a clean Matrix↔(Fin _→ℝ) reindex?)
  4. Flag any place I'd be tempted to guess fm's blow-up contract — and how to make it an explicit
     hypothesis instead.
  Under ~450 words. Mark inference vs. fact. Don't invent Mathlib lemma names.
</output_contract>

<grounding_rules>
  My green lemmas + IsSchurStraightenSqueeze are FACT (signatures as given). The blow-up coordinate
  contract is UNKNOWN to me — flag anything that assumes it. Distinguish "closes the per-node math
  faithfully" from "looks closed but smuggles the blow-up plumbing as a guess".
</grounding_rules>
