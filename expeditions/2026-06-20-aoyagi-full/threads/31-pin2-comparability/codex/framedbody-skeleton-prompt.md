<task>
Lean 4 / Mathlib v4.29 formalisation. I must fill the body of a theorem
`framedParams_split_eq_frame_raw` in DeepestGaugeConstruction.lean. The DESIGN is complete (a
banked S0–S5 decomposition cert). I need a STRUCTURAL judgement on the cleanest skeleton + on a
soundness issue I spotted, NOT a re-derivation of the math.

CONTEXT — the cert's conclusion (current `sorry`). For dimension vector H : Fin(L+1)→ℕ, rank r,
target B (rank r), `J : Fin r ↪ Fin (H (Fin.last L))`, frame families
`Pf : (s:Fin L) → Matrix (Fin (H s.castSucc)) (Fin (H s.castSucc)) ℝ`,
`Qf : (s:Fin L) → Matrix (Fin (H s.succ)) (Fin (H s.succ)) ℝ`, a homeo
`split : (Fin (flatDim H) → ℝ) ≃ₜ DeepestSplit H r (deepestNGauge H r)`, and
`hsplit : ∀ w, split w = deepestSplit … (paramsEquivFlat (deepestPoint H r B …)) w` (concrete witness),
the theorem produces:
  ∃ P0 QL Pi Qi (t γ₁ γ₂ : ℝ),
    Pi*P0 = 1 ∧ QL*Qi = 1 ∧ 0<γ₁ ∧ 0<γ₂ ∧ 0 < (∑P0²)(∑QL²) ∧ 0 < (∑Pi²)(∑Qi²) ∧
    ∃ U ∈ 𝓝 (paramsEquivFlat (deepestPoint …)), ∀ w ∈ U,
      ∃ P00 P01 P10 P11 (_ : Invertible P00),
        -- (a) hconj: reindex(rThr 0, pivotThr last J)(P0·(prod(paramsEquivFlat.symm w) − B)·QL)
        --            = fromBlocks (P00−1) P01 P10 P11
        ∧ -- (b) reg-energy: ∑ (deepestEFull H r hr hL J Pf Qf (split w))² = ∑(P00−1)²+∑P01²+∑P10²
        ∧ -- (c) leak: ∑(P10·⅟P00·P01)² ≤ t²·(∑(P00−1)²+∑P01²+∑P10²)
        ∧ -- (d) ∑(P11 − P10⅟P00 P01)² ≤ γ₂·deepestCoreF H r (deepestCoreAbsorb … (split w)).2.1
        ∧ -- (e) deepestCoreF H r (deepestCoreAbsorb … (split w)).2.1 ≤ γ₁·∑(P11 − P10⅟P00 P01)²

THE BANKED ATOMS (all sorry-free in the tree, signatures verified):
  - `endpoint_telescoping H hL A C P Q (hframe: ∀ s, C s = P s * A s * Q s)
       (hinterface: ∀ s hs, Q s = 1 ∧ P (s+1) = 1) : ∃ P0 QL, prod H C = P0 * prod H A * QL ∧
       (∀ hP0 hQL, IsUnit P0 ∧ IsUnit QL)`  — telescopes a per-layer frame product.
  - `deepestPoint_frame_pivot_exists H r B hB hr hL hL2 : ∃ Jb Pf Qf, (∀s, IsUnit (Pf s)) ∧
       (∀s, IsUnit (Qf s)) ∧ Qf (firstLayer) = 1 ∧ Pf (lastLayer) = 1 ∧
       (∀ s, s+1≠L → Pf s · deepestPoint s · Qf s = corM) ∧ IsUnit (...Qf last toBlocks₂₂) ∧
       reindex(rThr, pivotThr Jb)(deepestPoint last · Qf last) = fromBlocks 1 0 0 0`.
    The caller `deepest_gauge_construction` obtains THIS bundle, sets J := Jb.trans (finCongr …),
    and passes the resulting J, Pf, Qf to the cert. So at the call site frame facts (units, boundary
    triviality, interior normal form, the B-corner) ARE in scope — but the cert SIGNATURE does NOT
    currently take them (Pf Qf J are bare).
  - `reindex_fromBlocks_reads_eq_deviation H r hr hL wstar w s : reindex(rThr.symm,rThr.symm)
       (fromBlocks (readX (deepestSplit wstar w)) readY readZ (core read)) = (paramsEquivFlat.symm (w−wstar)) s`
    — the readX/Y/Z→raw decode for NON-last layers (both sides rThresholdSplit). Last layer uses
    pivotThresholdSplit on the column → needs a pivot-column variant (cert S1', ~30-40 LoC ext+4case).
  - `framedParamsPivot_of_ne_last`, `framedParamsPivot_last`, `framedParamsPivot_coreZero`,
    `framedLayer` def (= corM + P·reindex(fromBlocks X Y Z T)·Q), `deepestPoint_frame_normal`
    (= P·deepestPoint·Q = corM), `framedParams` def.
  - `deepestEPivot_sq_sum_eq_blocks` (the S4 template, for deepestEPivot — re-prove verbatim for deepestEFull).
  - `core_comparability_squeeze E P11 leak Rcore t (hsplit: P11 = leak+Rcore) (hleak: ∑leak² ≤ t²∑E²)
       : (∑E²+∑Rcore²) ≤ 2(1+t²)(∑E²+∑P11²) ∧ (∑E²+∑P11²) ≤ (2+2t²)(∑E²+∑Rcore²)`.
  - `fullProduct_core_split`, `schur_P11_decomp`, `frobenius_fromBlocks`, `frobenius_mul_le`,
    `leak_frobenius_bound`, `conjugation_frobenius_comparable`.
  - The S5c new atom is ADJUDICATED (germ form): `|∑‖R‖² − ∑‖∏S‖²| ≤ C·∑E²` on 𝓝0, R the GLOBAL Schur
    `P11−P10⅟P00P01`, ∏S = deepestCoreF(coreAbsorb). NOT yet written in Lean.

THE SOUNDNESS ISSUE I SPOTTED: the cert signature takes Pf, Qf, J as BARE (no IsUnit, no boundary
triviality, no hcorner). With fully generic Pf,Qf,J the conclusion is FALSE — P0 = Pf first need not
be a unit (so Pi*P0=1 fails), the corner normalization reindex(P0·B·QL)=fromBlocks 1 0 0 0 fails,
P00 need not be invertible. The frame facts are available at the unique call site
(`deepest_gauge_construction`, same file, editable). The squeeze consumer `deepest_loss_squeeze`
(also same file) is the intermediate caller and would need the facts threaded through too.

WHAT I'M ASKING (structural only):
</task>

<output_contract>
Answer in 4 short sections, terse:

1. SOUNDNESS FIX — confirm or refute that the cert is under-hypothesized as I claim, and state the
   MINIMAL set of extra hypotheses to add to `framedParams_split_eq_frame_raw` (and thread through
   `deepest_loss_squeeze`) so the conclusion becomes true. Express each as a Lean hypothesis
   referencing the bundle components above (e.g. `hPunit : ∀ s, IsUnit (Pf s)`, `hcorner : reindex…
   (deepestPoint last · Qf last) = fromBlocks 1 0 0 0`, `hframe : ∀ s, s+1≠L → …`,
   `hQf0 : Qf first = 1`, `hPfL : Pf last = 1`). Which of the bundle's 7 components are load-bearing
   for which conjunct? (Map each of P0-unit / corner / P00-invertible / S2-interface to a hypothesis.)

2. SKELETON SHAPE — the cleanest `have`-chain so the assembly TYPECHECKS with each S-sub-lemma a
   local `sorry`. Give the Lean `have` SIGNATURE (statement only, `:= sorry`) for S1 (per-layer
   round-trip, non-last), S1' (last-layer pivot variant), S2 (telescope output P0,QL),
   S3b (reindex(P0·B·QL)=fromBlocks 1 0 0 0), S4 (reg-energy = Sreg), S5a (Invertible P00 on a nbhd),
   S5b (leak bound), S5c (the two-sided core ≍). State the order they must be introduced and which
   `refine ⟨…⟩` skeleton assembles the final ∃. Flag any cast/defeq hazard (esp. the J finCongr
   between Fin (H (lastLayer).succ) and Fin (H (Fin.last L)), and pivotJSucc).

3. FILL ORDER & RISK — rank S1,S1',S2,S3b,S4,S5a,S5b,S5c by (banked-ness × LoC). Which are pure
   assembly of banked atoms (fillable now) vs genuinely-new geometry (leave as named sorry)?

4. THE NEIGHBORHOOD U — S5a (Invertible P00) and S5b/S5c (germ bounds) all need a 𝓝 0 / 𝓝(deepest)
   restriction. What is the cleanest way to construct the single U (intersection of: det P00 ≠ 0
   open set, the leak-smallness nbhd, the germ-comparability nbhd) and supply it to the outer ∃ U?
   Is there a continuity obstruction to `det P00` being a function of w through prod(framedParamsPivot)?
</output_contract>

<grounding_rules>
You are reasoning about Lean statement structure and soundness, not running code. Mark any claim
about a specific Mathlib lemma name as INFERENCE unless I gave you the exact name above. Do not
invent banked lemma names. If a sub-lemma genuinely needs unwritten analysis (germ bound,
det-continuity), say so plainly rather than gesturing at a one-liner.
</grounding_rules>
