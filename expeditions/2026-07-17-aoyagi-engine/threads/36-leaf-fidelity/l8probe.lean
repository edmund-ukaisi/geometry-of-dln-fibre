import DLNFibre.DLN.Aoyagi.MonumentAtlas
open DLNFibre.Core DLNFibre.Core.Aoyagi DLNFibre.DLN.Aoyagi DLNFibre.DLN.RLCT DLNFibre.DLN.RLCT.Engine
open scoped Topology

/- L8 `∀ atlas` soundness test: same degenerate atlas, but `jac` chosen ADVERSARIALLY beyond the
   (finite) terminal spectrum. Then clause (i) `jac a + 1 ∈ terminalExponents` FAILS. Refutes
   `leafPath_realizesExponents`'s statement. -/
example {N : ℕ} (d : Fin (N + 1) → ℕ) (e : (Fin (DLNFibre.DLN.Aoyagi.flatDim d) → ℝ) ≃ₜ Tuple (k := ℝ) d)
    (hfd : 0 < DLNFibre.DLN.Aoyagi.flatDim d)
    (hL8 : ∀ atlas : GeoAtlasData d e,
      (∀ (c : Fin atlas.n) (a : Fin (DLNFibre.DLN.Aoyagi.flatDim d)), a ∈ bindingAxes (atlas.bexp c) →
          (atlas.jac c a + 1) ∈
            ResolutionTree.terminalExponents (buildTree d (conOracle d) (conRoot : ConState N))) ∧
        (∀ l ∈ ResolutionTree.leaves (buildTree d (conOracle d) (conRoot : ConState N)),
          ∀ k : Fin l.numDiv, l.divExp k = minAdm d →
            ∃ (c : Fin atlas.n) (a : Fin (DLNFibre.DLN.Aoyagi.flatDim d)),
              a ∈ bindingAxes (atlas.bexp c) ∧ atlas.jac c a + 1 = l.divExp k)) :
    False := by
  set i0 : Fin (DLNFibre.DLN.Aoyagi.flatDim d) := ⟨0, hfd⟩ with hi0
  set L := ResolutionTree.terminalExponents (buildTree d (conOracle d) (conRoot : ConState N)) with hL
  let atlas : GeoAtlasData d e :=
    { n := 1, hn := one_pos, steps := fun _ => [], dom := fun _ => {0}, region := fun _ => Set.univ
      bexp := fun _ => (fun j => if j = i0 then 1 else 0)
      jac := fun _ => (fun _ => L.sum + 1)          -- adversarial: beyond the terminal spectrum
      hregion_open := fun _ => isOpen_univ, hzero_region := fun _ => Set.mem_univ _
      hdom_compact := fun _ => isCompact_singleton, hzero_dom := fun _ => rfl
      hdom_sub := fun _ => Set.subset_univ _
      hbind := fun _ => ⟨i0, by simp [bindingAxes]⟩
      hsqfree := fun _ a ha => by
        simp only [bindingAxes, Finset.mem_filter] at ha
        by_cases h : a = i0
        · simp [h]
        · simp [h] at ha }
  obtain ⟨hclause1, _⟩ := hL8 atlas
  have hbind0 : i0 ∈ bindingAxes (atlas.bexp ⟨0, atlas.hn⟩) := by
    show i0 ∈ bindingAxes (fun j => if j = i0 then (1:ℕ) else 0)
    simp [bindingAxes]
  have hmem : (atlas.jac ⟨0, atlas.hn⟩ i0 + 1) ∈ L := hclause1 ⟨0, atlas.hn⟩ i0 hbind0
  -- atlas.jac _ i0 = L.sum + 1, so L.sum + 2 ∈ L, but every element ≤ L.sum.
  have : L.sum + 1 + 1 ∈ L := hmem
  have hle : L.sum + 1 + 1 ≤ L.sum := List.single_le_sum (by intro x _; exact Nat.zero_le x) _ this
  omega
