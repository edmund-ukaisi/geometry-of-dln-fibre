import DLNFibre.DLN.Aoyagi.MonumentAtlas
open DLNFibre.Core.Aoyagi DLNFibre.DLN.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine
open scoped Topology

/- Does the EDGE-INDEXED Case2Preservation d close the gap? NO — the state, center, and ambient Dd
   remain FREE ∀-quantifiers (only δ is tied to the edge). SupportedOn constrains `resid`, but the
   |S|=1 refutation needs F=coords (about F) + a TRIVIAL residual (resid ≡ 1, which is SupportedOn any
   center). With a case-2 edge at cleared=0 (δ=true) and a supplied |S|=1 center {0}, the refutation
   survives: b'=u₀, child StepInv forces sh≡0 on {u₀=0}, contradicting jacDet sh ≡ 1. -/
example {N : ℕ} (d : Fin (N + 1) → ℕ)
    (hedge : ∃ ne ∈ ResolutionTree.stepEdges (buildTree d (conOracle d) (conRoot : ConState N)),
      ne.2.case = StepCase.case2 ∧ ne.1.cleared = 0) :
    ¬ Case2Preservation d := by
  intro h
  obtain ⟨ne, hne, hcase, hcl⟩ := hedge
  set F : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fun u => u 0, fun u => u 1] with hF
  set spec : EdgeSpec 2 := ⟨true, {0}⟩ with hspec
  have hstep : StepInv F id (fun _ => (1:ℝ)) (fun (_ : Fin 1) _ => (1:ℝ)) (fun i (_ : Fin 1) => F i) Set.univ := by
    refine ⟨?_, ?_, ?_⟩
    · intro i j; fin_cases i <;> exact (continuous_apply _).continuousOn
    · intro i; fin_cases i <;> simp [hF]
    · intro u _ i; simp [hF, Fin.sum_univ_one]
  have hsupp : SupportedOn (nR := 1) (fun _ _ => (1:ℝ)) spec.center (Set.univ : Set (Fin 2 → ℝ)) := by
    intro j u _ dd _ t; rfl
  have hδ : spec.δ = decide (ne.1.cleared = 0) := by rw [hcl]; rfl
  have hbc := h ne hne hcase spec 0 hδ (by simp [hspec]) ⟨0, by simp [hspec]⟩
    isOpen_univ (Set.mem_univ 0) hstep (by norm_num) hsupp
  obtain ⟨sh, Vchart, b', resid', q', han, hsh0, hjac1, _hcca, hVopen, hV0, hb'law, _hsupp', hcstep⟩ := hbc
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
  set e1 : Fin 2 → ℝ := fun j => if j = 1 then (1:ℝ) else 0 with he1def
  set γ : ℝ → (Fin 2 → ℝ) := fun t => t • e1 with hγ
  have hγ0 : γ 0 = 0 := by simp [hγ]
  have hshdiff : HasFDerivAt sh (fderiv ℝ sh 0) 0 :=
    (han 0 (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hγderiv : HasDerivAt γ e1 0 := by simpa using (hasDerivAt_id (0:ℝ)).smul_const e1
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
