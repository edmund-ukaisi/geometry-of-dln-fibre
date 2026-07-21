import DLNFibre.Core.Aoyagi.PrincipalInv
open DLNFibre.Core.Aoyagi
open scoped Topology

/- Elder's Σw² refutation vs the CURRENT form: Case2Preservation is FALSE.
   State F=(u₀,u₁) (S3-satisfying), g=id, b=1; spec center={0} (|S|=1), δ=true.
   blockBlowupMap {0} 0 = id, so σ=sh; δ=1 forces b'=u₀; child StepInv forces sh≡0 on {u₀=0}∩Vchart;
   an analytic sh with jacDet≡1 cannot (Dsh(0) kills e₁ ⟹ det 0 ≠ 1). -/
example : ¬ Case2Preservation := by
  intro h
  set F : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fun u => u 0, fun u => u 1] with hF
  have hstep : StepInv F id (fun _ => 1) F (fun i j _ => if i = j then (1:ℝ) else 0) Set.univ := by
    refine ⟨fun i j => continuousOn_const, ?_, ?_⟩
    · intro i; fin_cases i <;> simp [hF]
    · intro u _ i
      simp only [Function.comp_apply, id_eq, one_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; rw [if_neg (fun hh => hji hh.symm), zero_mul]
      · intro hcon; exact absurd (Finset.mem_univ i) hcon
  set spec : EdgeSpec 2 := ⟨true, {0}⟩ with hspec
  obtain ⟨p, hp, hchild⟩ :=
    h isOpen_univ (Set.mem_univ 0) hstep (by norm_num) spec ⟨0, by simp [hspec]⟩
  obtain rfl : p = 0 := by simpa [hspec] using hp
  obtain ⟨sh, Vchart, b', nR', resid', q', han, hsh0, hjac1, _hcca, hVopen, hV0, hb'law, hcstep⟩ := hchild
  have hbbu : ∀ u, blockBlowupMap spec.center 0 u = u := by
    intro u; funext j; fin_cases j <;> simp [blockBlowupMap, hspec]
  have hb' : ∀ u, b' u = u 0 := by intro u; rw [hb'law u]; simp [hspec]
  obtain ⟨_, _, hfac⟩ := hcstep
  have hsh_hyp : ∀ u ∈ Vchart, u 0 = 0 → sh u = 0 := by
    intro u hu hu0
    have hmem : u ∈ (fun u => id (sh (blockBlowupMap spec.center 0 u))) ⁻¹' Set.univ ∩ Vchart :=
      ⟨Set.mem_univ _, hu⟩
    have key : ∀ i, F i (sh u) = 0 := by
      intro i
      have hf := hfac u hmem i
      simp only [Function.comp_apply, id_eq] at hf
      rw [hbbu u] at hf
      simp only [hb' u, hu0, zero_mul, mul_zero, Finset.sum_const_zero] at hf
      exact hf
    have h0 : sh u 0 = 0 := by have := key 0; simpa [hF] using this
    have h1 : sh u 1 = 0 := by have := key 1; simpa [hF] using this
    funext j; fin_cases j
    · simpa using h0
    · simpa using h1
  -- CLOSURE
  set e1 : Fin 2 → ℝ := fun j => if j = 1 then (1:ℝ) else 0 with he1def
  set γ : ℝ → (Fin 2 → ℝ) := fun t => t • e1 with hγ
  have hγ0 : γ 0 = 0 := by simp [hγ]
  have hshdiff : HasFDerivAt sh (fderiv ℝ sh 0) 0 :=
    (han 0 (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hγderiv : HasDerivAt γ e1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const e1
  have hgf : HasFDerivAt sh (fderiv ℝ sh 0) (γ 0) := by rw [hγ0]; exact hshdiff
  have hcomp : HasDerivAt (sh ∘ γ) (fderiv ℝ sh 0 e1) 0 := hgf.comp_hasDerivAt 0 hγderiv
  have hev : (sh ∘ γ) =ᶠ[𝓝 0] (fun _ => (0 : Fin 2 → ℝ)) := by
    have hpre : γ ⁻¹' Vchart ∈ 𝓝 (0:ℝ) :=
      hγderiv.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hVopen.mem_nhds hV0)
    filter_upwards [hpre] with t ht
    exact hsh_hyp (γ t) ht (by simp [hγ, he1def])
  have hzero : HasDerivAt (sh ∘ γ) 0 0 := (hasDerivAt_const (0:ℝ) (0:Fin 2→ℝ)).congr_of_eventuallyEq hev
  have hker : fderiv ℝ sh 0 e1 = 0 := hcomp.unique hzero
  set L := (fderiv ℝ sh 0).toLinearMap with hL
  have he1ne : e1 ≠ 0 := by intro hcon; have := congrFun hcon 1; simp [he1def] at this
  have hLe1 : L e1 = 0 := hker
  have hker_ne : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hmem : e1 ∈ LinearMap.ker L := LinearMap.mem_ker.mpr hLe1
    rw [hbot, Submodule.mem_bot] at hmem
    exact he1ne hmem
  have hdet0 : LinearMap.det L = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker_ne
  have hdet1 : LinearMap.det L = 1 := hjac1 0
  rw [hdet0] at hdet1; exact one_ne_zero hdet1.symm
