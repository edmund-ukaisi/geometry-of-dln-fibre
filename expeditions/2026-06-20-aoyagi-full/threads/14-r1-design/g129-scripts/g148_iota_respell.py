# Re-spell the achiever path i₀ in fm3's EXACT routeMIota encoding (RouteMTree.lean).
# routeMIota S = (routeAtlas S).ι, a Σ/⊕-tree:
#   leaf      → ι = PUnit                                  (a leaf carries MonoData directly)
#   c1 cs dec → ι = Σ c : cs, (routeAtlas (schurState S c.1)).ι     (pick a pivot cell, recurse)
#   c2 c dec  → ι = (routeAtlas (passState S c)).ι                  (descend, same ι)
#   c4 s ..   → ι = AL.ι ⊕ AR.ι                                     (Sum: left/right block)
#   c5 cs p.. → ι = (Σ c:cs, A1.ι) ⊕ A2.ι                           (Sum of C1-Σ and C2)
# So a leaf i : routeMIota S is a NESTED term of Sigma.mk / Sum.inl/inr / PUnit.unit tracing the path.
print("=== Achiever path i₀ in fm3's routeMIota encoding (nested Σ/⊕ term) ===")
print("""
GENERAL i₀ for T* = (t_1,…,t_L): at each node S the dispatcher `classify S` returns a RouteCase; the
achiever path picks the constructor + sub-choice that resolves the active factor to its T*-rank:
  • if classify S = .c1 cs dec  (coupled rank-defect at this layer, T* wants rank t_s < t_{s-1}):
        i₀ at S = ⟨c*, i₀'⟩  : Σ c : cs, (routeAtlas (schurState S c)).ι
        where c* ∈ cs is the PivotChoice exposing rank t_s (the T*-rank pivot cell),
        and i₀' is the achiever path of the residual node (schurState S c*), recursively.
  • if classify S = .c2 c dec  (full-rank pass-through, t_s = t_{s-1}):
        i₀ at S = i₀'  : (routeAtlas (passState S c)).ι   (same ι; descend, no choice)
  • if classify S = .c5 cs p ..  (mixed partial-drop):
        i₀ at S = Sum.inl ⟨c*, i₀'⟩  (the complement-via-C1 branch) — pick the T*-rank pivot cell.
        [or Sum.inr if the survivor branch carries the binding divisor; for a minimiser the binding
         center is the complement's codim-m₀ divisor, so Sum.inl.]
  • if classify S = .c4 s ..  (separating pinch): the minimiser lies in one block;
        i₀ at S = Sum.inl i₀'  (or Sum.inr) — the block containing T*'s binding center.
  • when the residual reaches the binding center (the codim-m₀ leaf):
        i₀ = PUnit.unit  : the leaf whose MonoData has the binding divisor (k,h)=(1, m₀−1).
So i₀ is the finite nested term  ⟨c*₁, ⟨c*₂, … , PUnit.unit⟩⟩ (Σ-nesting through the C1 nodes,
Sum.inl/inr at C4/C5), bottoming at the PUnit leaf carrying (1, m₀−1).
""")
print("=== (2,2,2) CONCRETE (the depth-2 anchor): S₀ = ⟨2, ![2,2,2]⟩ ===")
print("""
T* = (1,0), m₀ = 3. The binding path:
  classify S₀ = .c1 cs dec   (C1: resolve C_1 from rank 2 to rank t_1=1 — the rank-1 coupled defect).
    c* = the PivotChoice exposing the rank-1 incidence locus (the 1×1 pivot; in the banked Case222
         this is the δ-branch → ρ-chart pivot).
    residual S₁ = schurState S₀ c*  (the reduced node carrying the codim-3 binding center, the ρ leaf).
  classify S₁ = .leaf md₁   where md₁ = the MonoData with d, k=![…,1,…], h=![…,2,…] — the ρ binding
    divisor (k,h)=(1,2)=(1,m₀−1).  [In Case222 terms: the ρ-chart, |det Dφ|=|ρ|², F=α²ρ²·[unit].]
  ⟹ i₀ = ⟨c*, PUnit.unit⟩ : Σ c : cs, (routeAtlas (schurState S₀ c)).ι = routeMIota S₀.
  ⟹ routeK S₀ i₀ at the binding coord = 1, routeH S₀ i₀ at it = 2 = m₀−1.
  ⟹ monomialThreshold (routeD S₀ i₀)(routeK S₀ i₀)(routeH S₀ i₀) = (2+1)/(2·1) = 3/2 = ½·m₀. ✓
This is IsResolutionAtlas.achiever for S₀: ⟨i₀, proof threshold = ½·m₀⟩, i₀ = ⟨c*, PUnit.unit⟩.
""")
print("NOTE for fm3: i₀ is BUILT by the same WellFounded.fix recursion as routeAtlas — at each node the")
print("achiever picks classify's constructor + the T*-rank PivotChoice cell. Once classify/PivotChoice are")
print("un-stubbed (the rank-pattern combinatorics), i₀ is `the Σ/Sum term following the T*-rank choices`.")
print("The realizability (T* reached) = classify S returns .c1/.c5 with a cs containing the T*-rank pivot")
print("(nonempty: Core.baseChange_normalForm realizes T*, so the rank-t_s minor is selectable).")
