<task>
Lean 4 + Mathlib v4.29 (DLN-fibre formalisation). I need the cleanest ASSEMBLY route for the geometric
heart `deepest_loss_squeeze`, and whether a sub-obligation needs to be a separate cert. I have a working
build env + the banked bedrock below. Rank the routes; for the top one give the proof skeleton + name the
ONE sub-obligation most likely to need a pen-and-paper cert (vs leaf-provable).

THE GOAL (deepest_loss_squeeze, DeepestGaugeConstruction.lean):
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ U ∈ 𝓝 w0, ∀ w ∈ U,
    0 ≤ Φ(w) ∧ c₁·Φ(w) ≤ dlnLoss H B (paramsSymm w) ∧ dlnLoss H B (paramsSymm w) ≤ c₂·Φ(w)
where:
  - w0 = paramsEquivFlat (deepestPoint H r B hB hr hL); paramsSymm := (paramsEquivFlat H).symm.
  - Φ(w) = (∑ i, (regStraighten (split w)).1 i ^ 2) + deepestCoreF H r (coreAbsorb (split w)).2.1.
  - dlnLoss H B A = ∑ i, ∑ j, ((prod H A − B) i j)^2  (squared-Frobenius).
  - HYPOTHESES given: hregval : ∀ q, (regStraighten q).1 = deepestEPivot H r hr hL (q.1, q.2.2);
    hcoreabs : coreAbsorb = deepestCoreAbsorb H r hr hL; hsplit_base : split w0 = 0.

BANKED (sorry-free, clean-three) — consume, don't rebuild:
  - endpoint_telescoping (JUST PROVEN): ∀ (A C : Params H) frames P Q, (hframe: ∀ s, C s = P s·A s·Q s) →
    (hinterface: interior frames = 1) → ∃ P0 QL, prod H C = P0·prod H A·QL. [endpoint-typed P0:H0×H0, QL:Hlast×Hlast]
  - conjugation_frobenius_comparable (P Q Pi Qi : ...) (hP: Pi·P=1) (hQ: Q·Qi=1) (A) :
    ∑A² ≤ (∑Pi²·∑Qi²)·∑(P·A·Q)²  ∧  ∑(P·A·Q)² ≤ (∑P²·∑Q²)·∑A².  [the endpoint-conjugation two-sided bound]
  - dlnLoss_block_squeeze (N e₁ e₂ P00 P01 P10 P11 t) (hblocks: reindex e₁ e₂ N = fromBlocks (P00−1) P01 P10 P11)
    (Invertible P00) (hleak: ∑leak² ≤ t²·∑E²) :
    (∑E²+‖Rcore‖²) ≤ 2(1+t²)·∑N²  ∧  ∑N² ≤ (2+2t²)·(∑E²+‖Rcore‖²).  [E = (P00−1,P01,P10), Rcore = P11−P10·⅟P00·P01]
  - framedParams q : Params H — each layer = framedLayer of (readX/Y/Z q) + core T_s; ∏(framedParams q) is the
    "framed product". deepestEPivot p reads the reg-residual blocks (P11−I, P12, P21) of reindex(∏(framedParamsReg p)).
  - deepestPoint_frame s : (P_s, Q_s) with P_s·(deepestPoint s)·Q_s = corM (block-normal corner); deepestPoint_frame_invertible
    : IsUnit P_s ∧ IsUnit Q_s. deepestPoint_interior_eq_corM / _layer0_cols_vanish / _layerLast_rows_vanish (#95-I frames).
  - ∑(deepestEPivot p)² is PERMUTATION-INVARIANT over the (opaque) regResidualPack (it's a sum of squares),
    so Φ's reg part = the framed reg-residual energy WITHOUT needing the opaque-pack coord correspondence.

THE OPEN PIECE I'm unsure about: relating dlnLoss H B (paramsSymm w) = ∑(prod(paramsSymm w) − B)² to the
framed blocks. paramsSymm w is the RAW params; framedParams(split w) is the FRAMED reconstruction (gauge-read).
The bridge prod(paramsSymm w) = P0⁻¹·prod(framedParams(split w))·QL⁻¹ (constant deepest-point frame) — is this
(a) an instance of endpoint_telescoping (needs per-w hframe: framedParams(split w) s = P_s·(paramsSymm w) s·Q_s,
which is the framed-vs-raw per-layer relation — is THAT leaf-provable from the def of framedParams/split, or a
cert?), or (b) a separate per-w frame-conjugation obligation, or (c) does dlnLoss_block_squeeze apply DIRECTLY
to N = prod(paramsSymm w) − B reindexed (skipping endpoint_telescoping) since the deepest-point B is itself
gauge-normalized?
</task>

<output_contract>
1. RANK the assembly routes (a)/(b)/(c)/(other) by total Lean effort, with the biggest risk of each.
2. For the TOP route: the proof skeleton (the c₁/c₂ choice, the U choice, the per-w chain endpoint_telescoping
   → conjugation_frobenius_comparable → dlnLoss_block_squeeze → the Φ identification), naming which banked
   lemma each step uses.
3. Name the ONE sub-obligation most likely to need a pen-and-paper/Codex cert (the framed-vs-raw per-w relation,
   or the leak bound, or the block decomposition) vs leaf-provable — and say WHY.
Keep under ~650 words, Lean-concrete.
</output_contract>

<grounding_rules>
Flag any Mathlib/DLNFibre lemma you're unsure exists as "(verify)". Distinguish "this route closes it"
(load-bearing) from "this probably works" (guess). If the framed-vs-raw relation is genuinely a cert (not
leaf-provable), say so plainly — don't paper over it.
</grounding_rules>
