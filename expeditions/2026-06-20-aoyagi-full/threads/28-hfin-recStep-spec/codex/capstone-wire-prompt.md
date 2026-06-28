<task>
Lean 4 + Mathlib v4.29. I am WIRING the final `sorry` of an RLCT-upper-bound capstone — generalizing a
proven corank-3 firing to arbitrary `r ≥ 3`. ALL bricks below are PROVED sorry-free in the file. I need
the EXACT proof skeleton for the target theorem from these bricks, in the right order, with the right
intermediate `have`s. The genuinely-hard sub-step is the "N2b ↔ stepShearG bridge" (expanding a matrix
row-0 product into an explicit shear sum). Tell me precisely how to do it.

TARGET (the sole sorry):
  theorem schurRatioResidGen_mid (r N : ℕ) (hN : r * r = N + 1) (hr : 3 ≤ r)
      (hIH : SchurLowerIH 4 schurLambda r) (c' : ℝ) (hc2 : 2 < c') (hc' : c' < schurLambda r)
      (p : Fin (r * r)) (T : ℝ) (hT : 0 < T) :
      (∫⁻ z in (Set.univ.pi (fun _ : Fin N => Set.Icc (-1 : ℝ) 1)),
          innerSGen r c' T p ((piRatioG r N hN p).symm (0, z))) < ⊤

where:
  schurLambda r = 2*r - 2 (for r ≥ 2), so for r ≥ 3, schurLambda r ≥ 4, and c' ∈ (2, schurLambda r),
  and c'' := c' - 2 ∈ (0, schurLambda (r-1)) since schurLambda(r-1) = 2(r-1)-2 = 2r-4 = schurLambda r - 2.

KEY BRICKS (all PROVED in-file; I quote exact signatures):

(1) innerSGen_eq_norm : innerSGen r c' T p ((piRatioG r N hN p).symm (0, z))
      = ∫⁻ S in matBox r 4 T, ENNReal.ofReal ((frobSq (rmatMul (RmatGnorm r N hN hr p z) S)) ^ (-c'))
    -- RmatGnorm is the pivot-normalised r×r angular matrix; pivot RmatGnorm…⟨0⟩⟨0⟩ = 1.

(2) RmatGnorm_pivot : RmatGnorm r N hN hr p z ⟨0,_⟩ ⟨0,_⟩ = 1
    RmatGnorm_offpivot_le (with hz : z ∈ box) : |RmatGnorm r N hN hr p z a b| ≤ 1   (any a b)

(3) The carve readbacks (M : Fin(r-1)×Fin(r-1)→ℝ, v : Fin(r-1)⊕Fin(r-1)→ℝ):
    RmatGnorm_carve_M22 : RmatGnorm r N hN hr p ((zEG r N hN hr p).symm (M,v)) ⟨a+1,_⟩ ⟨b+1,_⟩ = M (a,b)
    RmatGnorm_carve_g   : RmatGnorm r N hN hr p ((zEG…).symm (M,v)) ⟨a+1,_⟩ ⟨0,_⟩ = v (Sum.inl a)
    RmatGnorm_carve_b   : RmatGnorm r N hN hr p ((zEG…).symm (M,v)) ⟨0,_⟩ ⟨b+1,_⟩ = v (Sum.inr b)
    (pivot ⟨0⟩⟨0⟩ stays 1 by RmatGnorm_pivot.)
    bgShiftG m v : Matrix (Fin m)(Fin m) ℝ := fun a b => v (Sum.inl a) * v (Sum.inr b)
    bgShiftG_entry_le (hv : ∀ s, |v s| ≤ 1) : |bgShiftG m v a b| ≤ 1

(4) measurePreserving_zEG : MeasurePreserving (zEG r N hN hr p)
       (volume : Measure (Fin N → ℝ))
       (volume : Measure ((Fin(r-1)×Fin(r-1)→ℝ) × ((Fin(r-1)⊕Fin(r-1))→ℝ)))
    zEG_symm_apply : (zEG…).symm (M,v) k = Sum.elim M v (zσG r N hN hr p k)
    -- so [-1,1]^N pulls back: z ∈ box ⟺ (M,v) entrywise in [-1,1] (each slot a distinct z-coord).

(5) stepShearG (m : ℕ) (b : Fin m → ℝ) (hb : ∀ a, |b a| ≤ 1) (Sc : Matrix (Fin m)(Fin m) ℝ) (T)(hT:0<T)(c'):
      (∫⁻ S in matBox (m+1) 4 T,
          ofReal (((∑ q, (S 0 q + ∑ a, b a * S a.succ q)^2)
            + frobSq (rmatMul Sc (fun a q => S a.succ q)))^(-c')))
        ≤ ∫⁻ S_bot in matBox m 4 T, ∫⁻ T' in morseBox 4 ((m+1)*T),
            ofReal (((∑ q, (T' q)^2) + frobSq (rmatMul Sc S_bot))^(-c'))

(6) resolvedShiftRG_le (r)(hr:3≤r) (Sh : Fin(r-1)→Fin(r-1)→ℝ) (B)(hB:∀ i j,|Sh i j|≤B) (K)(hK:0<K)(c')(hc2:2<c'):
      (∫⁻ Δ in matBox (r-1)(r-1) K, ∫⁻ S in matBox (r-1) 4 K, ∫⁻ T in morseBox 4 K,
          ofReal ((∑ i, (T i)^2 + frobSq (rmatMul (fun a b => Δ a b - Sh a b) S))^(-c')))
        ≤ ENNReal.ofReal (Cresid 4 c') * coreSchurGenVal (r-1) (c'-2) (K+B)
    coreSchurGenVal_lt_top (hr)(hIH)(c'')(hc0:0<c'')(hclam:c''<schurLambda(r-1))(Kr)(hKr:0<Kr):
        coreSchurGenVal (r-1) c'' Kr < ⊤

(7) ofReal_rpow_le_const_mul (X F c₀ c')(hc0:0<c')(hcc:0<c₀)(hX:0≤X)(hF:0≤F)(hle:c₀*X≤F)(hzero:X=0→F=0):
      ofReal (F^(-c')) ≤ ofReal (c₀^(-c')) * ofReal (X^(-c'))

(8) N2b — schur_minorPivot_split {r p_ : ℕ} (j)(hj:j≤r) :
      ∃ c₀ c₁, 0<c₀ ∧ 0<c₁ ∧ ∀ (R : Matrix (Fin r)(Fin r) ℝ)(S : Fin r → Fin p_ → ℝ),
        (∀ a b, |R a b| ≤ 1) →
        (∀ I J : Fin j → Fin r, |(R.submatrix I J).det| ≤ |(M11 of R).det|) →
        (M11 of R).det ≠ 0 →
        ∃ Sc, Sc = (the genuine Schur complement M22 − M21·M11⁻¹·M12) ∧
          R.det = (M11).det * Sc.det ∧
          c₀ * (frobSq ((R·S)_top j rows) + frobSq (Sc · S_bot)) ≤ frobSq (R·S) ∧
          frobSq (R·S) ≤ c₁ * (frobSq ((R·S)_top) + frobSq (Sc · S_bot))
    -- For j=1: (R·S)_top is the single row 0 of R·S, M11 = [R 0 0] = [1] (pivot), Sc is (r-1)×(r-1).

THE TEMPLATE (proven at r=3, the analog I am generalizing): the (3,3,4)-anchor route bounds the per-z
integral via an EXPLICIT 3×3 `angularR` reconstruction + a `nlinarith`-clean comparability
`frobSq_angularR_ge` — that explicit route does NOT generalize. The generic chain (bricks above) is built
to use N2b (8) + stepShearG (5) + resolvedShiftRG_le (6) instead.

MY CONCERN / the crux: bridging N2b's `frobSq ((R·S)_top)` (for j=1, the single row 0 of R·S =
∑_k R_{0k} S_{kq}) to stepShearG's `∑_q (S_0q + ∑_a b_a S_{a+1,q})^2`. Since RmatGnorm pivot R_{00}=1,
row 0 of R·S at column q is S_{0q} + ∑_{a:Fin(r-1)} R_{0,a+1} S_{a+1,q}, matching b_a = R_{0,a+1}.
But N2b's Sc is M22 − M21·M11⁻¹·M12 with M11=[1], i.e. Sc_{ab} = R_{a+1,b+1} − R_{a+1,0}·R_{0,b+1}; on the
CARVED point (zEG.symm(M,v)) this is M(a,b) − v(inl a)·v(inr b) = (matOf M − bgShiftG v)_{ab}. So
Sh = bgShiftG v, and Sc·S_bot matches resolvedShiftRG_le's `(fun a b => Δ a b - Sh a b)` with Δ=matOf M.
</task>

<output_contract>
Give me, in order:
1. The TOP-LEVEL skeleton: rewrite via innerSGen_eq_norm, CoV via measurePreserving_zEG to split z=(M,v),
   Tonelli to put v outer, then per-(M,v) work, then integrate the bounded v-box. Name each Mathlib lemma
   for the CoV+Tonelli (the bricks use `setLIntegral_comp_preimage_emb`, `Measure.volume_eq_prod`,
   `setLIntegral_prod`, `lintegral_lintegral_swap`).
2. The per-(M,v) chain: how to go from `∫_S ofReal(frobSq(R·S)^(-c'))` (R = RmatGnorm at the carved point)
   to the resolvedShiftRG_le LHS shape. Specifically:
   (a) the N2b instantiation (j=1) — what are hbd, hpivot, hne for RmatGnorm? (pivot=1, |entries|≤1.)
       hpivot for j=1: |det of a 1×1 submatrix R[I 0][J 0]| = |R (I 0)(J 0)| ≤ 1 = |R 0 0| = |M11.det|.
   (b) apply ofReal_rpow_le_const_mul with c₀ from N2b, X = frobSq_top + frobSq(Sc·S_bot), F = frobSq(R·S).
       This gives ofReal(F^-c') ≤ ofReal(c₀^-c')·ofReal(X^-c'). Pull c₀^-c' const out of ∫_S.
   (c) THE BRIDGE: rewrite `frobSq ((R·S)_top)` (j=1, single row) into `∑_q (S_0q + ∑_a b_a S_{a+1,q})^2`
       with b_a = R_{0,a+1}. Give the exact `frobSq`/`rmatMul` unfolding: frobSq of a (Fin 1 → Fin 4 → ℝ)
       single-row family vs the explicit ∑_q (...)^2. How to handle the Fin 1 sum collapse and the
       `R 0 0 = 1` pivot to turn ∑_k R_{0k} S_{kq} into S_{0q} + ∑_{a:Fin(r-1)} R_{0,a+1} S_{a+1,q}
       (the index split Fin r = {0} ⊕ Fin(r-1) via Fin.succ). Is `Fin.sum_univ_succ` the right tool?
   (d) rewrite `Sc` and `Sc·S_bot` at the carved point to `(matOf M − bgShiftG v)·S_bot` using the carve
       readbacks (3). Then apply stepShearG (5) with m=r-1, b = (R 0 · row), Sc = matOf M − bgShiftG v.
   (e) feed resolvedShiftRG_le (6) with Sh = bgShiftG v, B = 1, K = T (radius). Note stepShearG's output
       has morseBox 4 ((m+1)*T) and matBox m 4 T — does resolvedShiftRG_le's K need to be max(T, (m+1)*T)?
       The brief said K = max 1 (r*T). Resolve the radius mismatch precisely (S-box radius T vs T-box
       radius (r)*T): which K to pick so BOTH boxes embed, and whether a `lintegral_mono_set` enlargement
       is needed before resolvedShiftRG_le.
3. The final v-integration: after per-(M,v) ≤ const · resolvedShiftRG_le-bound (a CONSTANT in v), the
   v-integral over the bounded box [-1,1]^{2(r-1)} is const·vol(box) < ⊤. Confirm the bound is v-uniform
   (resolvedShiftRG_le's RHS coreSchurGenVal(r-1)(c'-2)(K+B) is v-independent since B=1 caps |bgShiftG v|).
4. FLAG any step where the bricks DON'T compose (a missing helper I'd need to prove), especially the
   bridge (c) and the radius (e). Be concrete about Mathlib lemma names at v4.29.
</output_contract>

<grounding_rules>
Distinguish what you can VERIFY from the signatures given vs what you INFER. If a brick signature doesn't
match what a step needs (e.g. box radius, the Fin-index shape of stepShearG's `S a.succ` vs N2b's
`S ⟨1+a,_⟩`), FLAG it explicitly as a gap requiring a bridging `have`, do not paper over it. I will build
every line locally; I need the diagnosis of the route + the danger points, not runnable code I trust blind.
</grounding_rules>
