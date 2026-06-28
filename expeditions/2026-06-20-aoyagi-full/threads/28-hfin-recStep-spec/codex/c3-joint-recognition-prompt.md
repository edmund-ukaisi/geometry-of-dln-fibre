<task>
Lean 4 / Mathlib measure-theory formalisation. I am proving a finiteness lemma `core_schur3_lt_top` (corank-3) by mirroring an existing corank-2 proof `core_schur2_lt_top`. The genuinely-new math is DONE and banked; I am doing the per-chart assembly WIRING. I need the cleanest LEAN STRUCTURE for the inner part of the per-chart lemma `matBox3_chart_lt_top`. NO new mathematics — purely how to organise the integral manipulations to reuse the banked lemmas.

GOAL (mirror of corank-2 `matBox2_chart_lt_top`): for a fixed pivot `p : Fin 9` and `0 < c' < 4`, prove
    ∫_{y ∈ chartDomOn univ p \ pivotZeroOn p}  |y_p|^8 · (flatBox3 T).indicator (gFlat3 c' T) (pivotBlowupOn univ p y)  < ⊤.

The corank-2 template does this:
1. `chart_integrand_factor3` (ALREADY BANKED) rewrites the integrand on the chart to  radInd(y_p) · innerS3 c' T p y, where
     innerS3 c' T p y := ∫_{S ∈ matBox 3 4 T} ofReal( frobSq(rmatMul (Rmat3 p y) S) ^ (−c') )
   and radInd(y_p) = (Icc -T T).indicator (fun a => ofReal(|a|^(8 − 2c'))) (y_p).
   `Rmat3 p y` is the 3×3 angular matrix: entry at p is 1, off-pivot entries are the y-components (|·| ≤ 1 on the chart).
2. piFinSuccAbove p MeasurePreserving + Tonelli splits y into (pivot-axis a) × (8 off-pivot ratios z ∈ [−1,1]^8). innerS3 is `a`-invariant (Rmat3 ignores y_p). So the integral factors as
     (∫_a radInd) · (∫_{z ∈ [−1,1]^8} innerS3 c' T p (e.symm (0,z))).
   The radial axis factor ∫_a is finite for c' < 9/2 (banked `radial_aAxis_divisor_lt_top 3`, since 8 − 2c' > −1 ⟺ c' < 9/2; and 4 < 9/2 so OK).
3. So the whole thing reduces to the "hratiofin" goal:
     ∫_{z ∈ [−1,1]^8} innerS3 c' T p (e.symm (0,z))  < ⊤.   (★)
   In corank-2 this was closed by bounding innerS2 ≤ a UNIFORM constant `schurInnerBnd2` (z-independent), then ∫_z const = const·vol. THAT TRICK FAILS at corank-3 (the inner residual depends on z and there is no uniform bound that integrates the +2 Morse gain). Instead (★) must be closed via the banked JOINT residual lemma.

THE BANKED LEMMAS I MUST USE for (★):

(A) N2b split `schur_minorPivot_split (r:=3)(p:=4) 1 (j=1)`: gives constants c₀,c₁>0 and, for the FIXED angular matrix R := Rmat3 p (e.symm(0,z)) (which has R i₀ j₀ = 1 at the pivot, |R a b| ≤ 1) and every S, the two-sided bound
     c₀·D(R,S) ≤ frobSq(R·S) ≤ c₁·D(R,S),   D(R,S) = frobSq((R·S)_top_row0) + frobSq(Sc(R)·S_bot),
   where (R·S)_top_row0 : Fin 1 → Fin 4 is row 0 of R·S; Sc(R) : 2×2 = M22(R) − M21(R)·M11(R)⁻¹·M12(R); with pivot at (0,0), M11 = R₀₀ = 1, so Sc(R) = M22(R) − M21(R)·M12(R), M22(R) = R restricted to rows/cols {1,2}; S_bot = rows {1,2} of S.
   Inverse-power flip `schurSplit_integrand_le` then `schurSplit_lintegral_le`: ∫_S frobSq(R·S)^{−c'} ≤ ofReal(c₀^{−c'}) · ∫_S D(R,S)^{−c'}.

(B) The split-S integral ∫_{S∈matBox 3 4 T} D(R,S)^{−c'}: split S = (S_row0, S_bot) (piFinSuccAbove 0 on the row index), Tonelli with S_bot outer. Per fixed S_bot, the top block (R·S)_row0 = S_row0 + R₀₁·S_row1 + R₀₂·S_row2 is a SHEAR of S_row0 (4 entries, a Morse block). Translate S_row0 ↦ S_row0 + shift (box-enlarge to radius 3T), then apply the SHIFTED-EXPONENT Morse peel
   `radial_morse_residual_power_le (m:=3) c' (hc' : (3+1)/2 < c') ... (w := frobSq(Sc(R)·S_bot)) (hw : 0 < w)`:
     ∫_{P∈morseBox 4 (3T)} ofReal((∑(P_j)² + w)^{−c'}) ≤ ofReal( Cresid 4 c' · w^{−(c'−2)} ).
   The threshold (3+1)/2 = 2 < c' holds since c' ∈ (2,4) at this stage (we are above 2 here).
   PROBLEM: `radial_morse_residual_power_le` needs w > 0 STRICTLY (Cresid·w^{−(c'−2)} blows up if w=0, and the lemma hypothesis is hw:0<w). The set {S_bot : frobSq(Sc·S_bot)=0} can be positive-measure when Sc is singular (Sc·S_bot = 0). How is the w=0 / Sc-singular edge handled cleanly? In corank-2 the analogous residual was a 1×1 scalar Sc₀₀ and the bound used radial_morse_dominates (crude (∑P²+w)^{−c'} ≤ (∑P²)^{−c'}, no w>0 needed) because c'<2 there. Here we are ABOVE 2 and MUST use the residual-power (w>0). So the w=0 locus needs separate treatment.

(C) The JOINT residual `schurResid2_translate_lt_top (Sh)(B)(hB:∀ i j,|Sh i j|≤B)(c'')(0<c''<2)(T)(0<T)`:
     ∫_{Δ∈matBox 2 2 T} ∫_{S∈matBox 2 4 T} ofReal( frobSq((Δ − Sh)·S)^{−c''} ) < ⊤,  for a FIXED shift Sh.
   The intended recognition: c'' = c'−2 (∈(0,2) since c'∈(2,4)); Sc(R) = M22(R) − Sh(R) where Δ := M22(R) is the free 2×2 block (rows/cols {1,2} of R-angular, ranging over matBox 2 2 1 as z varies) and Sh(R) = M21(R)·M12(R) (depends on the boundary ratios, |Sh| ≤ B for some constant B since all ratios ≤ 1).

THE CRUX I want your design on:
After (A)+(B), goal (★) becomes (roughly)
     ∫_{z∈[−1,1]^8} ofReal(c₀^{−c'}·Cresid 4 c') · ∫_{S_bot∈matBox 2 4 3T} frobSq(Sc(Rmat3 p (e.symm(0,z)))·S_bot)^{−(c'−2)}  < ⊤.
But (C) `schurResid2_translate_lt_top` has the shift Sh FIXED and integrates Δ=M22 over matBox 2 2 T. In my (★) the 8 z-coords split into (the 4 entries forming M22=Δ) and (the 4 entries forming the boundary ratios that determine Sh). The shift Sh(z) VARIES with z. So I need to Tonelli-separate the 8 z-coords into (4 M22-coords) × (4 boundary-coords), apply (C) per fixed boundary-coords (fixed Sh), then integrate over the boundary-coords (a finite box ⟹ finite). Also the S domain in (C) is matBox 2 4 T but I have matBox 2 4 3T after the box-enlarge — fine, just use radius 3T in (C) (it is parametric in T).

Also there is a corank-2 vs corank-3 mismatch worry: in (C) S ranges over matBox 2 4, but Sc·S_bot where S_bot is rows {1,2} of the ORIGINAL S∈matBox 3 4. After Tonelli S_bot ∈ matBox 2 4 — matches (C)'s S (2 rows, 4 cols). Good.

QUESTIONS (rank by how much they de-risk the build):
1. Is the Tonelli-separation of the 8 z-coords into (M22 4-block) × (boundary 4-block) the right move, or is there a cleaner recognition (e.g. integrate over ALL of z directly by a single change of variables)? Note M22 = the {1,2}×{1,2} entries of Rmat3, which under the e.symm(0,·)/matToFlat3 parameterisation are 4 specific z-indices; the boundary {row0-cols, col0-rows} are 4 others. Is reindexing Fin 8 ≃ Fin 4 × Fin 4 the cleanest, or should I keep z:Fin 8→ℝ and just bound the boundary-coords' contribution by a finite-volume factor?
2. THE w=0 / Sc-singular edge in (B): what is the cleanest Lean handling so that `radial_morse_residual_power_le` (which needs w>0) can be applied a.e.? Options: (a) show {S_bot : frobSq(Sc·S_bot)=0} is null for a.e. R — FALSE when Sc singular (then Sc·S_bot=0 on a positive-measure subspace). (b) Don't peel to w; instead keep the FULL D = frobSq(top) + frobSq(Sc·S_bot) and bound ∫_S D^{−c'} differently. (c) Bound the ENTIRE inner-S integral ∫_S frobSq(R·S)^{−c'} by reverting to the corank-2 lemma core_schur2 applied to a 2×2 sub-core after peeling ONLY the top Morse row with the CRUDE bound (∑P²+w)^{−c'} ≤ ... — but crude caps at c'<2 for the 4-entry block, undershooting. Which option is actually sound, and how is the w=0 measure-zero-or-not issue resolved? THIS IS THE KEY RISK — be concrete.
3. Given (C) integrates frobSq((Δ−Sh)·S)^{−c''} and my residual is frobSq(Sc·S_bot)^{−c''} with Sc = Δ − Sh, the integrands match pointwise. But (C)'s OUTER integral is over Δ∈matBox 2 2 T (4 free entries) whereas my M22-coords come from z∈[−1,1]^4 (radius 1). Since matBox 2 2 1 = matBox 2 2 T at T=1, and (C) is parametric in T, I apply (C) at its T-slot = 1 for the Δ-box and 3T for the S-box. But (C) uses the SAME T for both Δ-box and S-box! Is that a problem (I need Δ-radius 1 but S-radius 3T)? Re-examine: can I just enlarge the Δ-box to radius max(1,3T) and the S-box likewise, both bounded, and apply (C) at T_big = max(1,3T)? Confirm (C) at a single large radius dominates both.

Be concrete and Lean-idiom specific (v4.29 Mathlib). I want a STEP LIST for the inner of matBox3_chart_lt_top, flagging the one genuinely-risky step.
</task>

<output_contract>
Three sections:
1. RECOMMENDED STRUCTURE — a numbered step list for the inner of matBox3_chart_lt_top (from goal (★) to ⊤), naming which banked lemma each step uses and the exact Tonelli/reindex move.
2. THE w=0 EDGE — the sound handling of the Sc-singular / w=0 locus (answer Q2 decisively; if option (a)/(b)/(c) each fail say so and give the correct one).
3. RISKS — rank the 1–3 steps most likely to thrash, each with the specific Lean obstacle and a mitigation. Be brief.
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY from the given signatures vs what is INFERENCE about Mathlib behaviour. Flag any lemma you are unsure exists in Mathlib v4.29. Do not invent lemma names — if you need a lemma, describe it and say "needs: …".
</grounding_rules>
