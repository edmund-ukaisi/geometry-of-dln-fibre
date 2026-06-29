<task>
Confirm the EXPLICIT structure (a Finset membership predicate) of the "radial active" coordinate set for a
de-radialized chart factorization phi = B ∘ pivotBlowupOn(active, p) at chain-depth L=2 (single genuine
boundary), and the squareness/non-degeneracy logic. Lean/Mathlib formalisation. Derive from the structure
given; sympy facts are exact.
</task>

<setup_L2>
Width tuple M=(M0,M1,M2), L=2. Flat space R^N, N = M0·M1 + M1·M2 (the two layer matrices).
Coordinates are addressed via a bijection chartIdxEquiv : Fin N ≃ ChartIdx, where
  ChartIdx = Σ k:Fin L, (Fin (schurDim k) ⊕ Fin (liftDim k)),  schurDim k = Text_k·Wext_k, liftDim k = (Wext_{k+1}-Text_{k+1})·Wext_{k+2}.
At L=2 there is one genuine boundary (k=0, "s=1") and the leaf (k=L-1=1). The schur slot at boundary k
splits via frameSplitEquiv into roles (((K ⊕ X) ⊕ N) ⊕ E): K = Text_{k+1}², X = (Text_k-Text_{k+1})·Text_{k+1},
N = Text_{k+1}·(Wext_k-Text_{k+1}), E = (Text_k-Text_{k+1})·(Wext_k-Text_{k+1}) = r·c  [outermost Sum.inr].
The leaf (k=L-1) schur slot holds the leaf residual Rfin (Text_L·Wext_L coords).

EXACT sympy facts (verified at (2,2,2),(2,3,2),(3,3,3)):
- The radial active set = {structPivot=⟨0,_⟩} ∪ {the E-role coords of boundary k=0} ∪ {the leaf coords
  (excluding ONE fixed anchor)}.  Its card = minAdm exactly.  (minAdm = r·c + Text_L·Wext_L.)
- pivotBlowupOn(active,p) sends x_p -> x_p, and each active coord x_i -> x_p·x_i.
- With this active set, det Dphi = ±u^{minAdm-1} (single monomial), chart square (#coords = flatDim).
- MIS-ALLOCATION (forcing the fixed anchor into a K-core coordinate instead of the leaf, leaving the leaf
  all-free) keeps #coords = flatDim but gives det Dphi ≡ 0 (degenerate).
</setup_L2>

<questions>
1. State the EXPLICIT Finset (Fin N) for `active` at L=2 as a membership predicate over ChartIdx via
   chartIdxEquiv: it should be {chartIdxEquiv.symm of the E-role slots at k=0} ∪ {chartIdxEquiv.symm of the
   leaf slots at k=L-1, minus the anchor} ∪ {structPivot}. Is the cleanest Lean form a union of
   Finset.image (chartIdxEquiv.symm ∘ the role-slot embedding) over the E-role index set and the leaf index
   set (erase anchor), plus {structPivot}? Give the precise set-builder.
2. The squareness/budget pin: explain WHY #active = minAdm EXACTLY (the closed-form r·c + Text_L·Wext_L
   = minAdm at L=2) is equivalent to the chart being square with det ≠ 0. Specifically: det Dphi =
   det(DB)·u^{#active-1}; det(DB) = the engine product (nonzero generically) IFF B is a square local iso.
   Why does a WRONG #active (anchor mis-allocated to a K-core coord) force det ≡ 0? Is it because the
   de-radialized B then loses a DOF (a column of DB becomes dependent) — i.e. B no longer a local iso?
3. Confirm the slot-scaling: each R/Rfin "active" coordinate is, in the chart phi, multiplied by the pivot
   x_p (the u·E and u·Rfin scalings), and pivotBlowupOn supplies exactly that x_p factor (x_i -> x_p·x_i).
   So the chart's "u·(R-block)" = "pivotBlowupOn applied to the active R-coords". Is this the faithful reading
   of phiGen_smul_radial (the pivot u multiplies precisely the R/Rfin blocks)?
</questions>

<output_contract>
Q1: the explicit Finset set-builder over ChartIdx. Q2: the squareness <=> #active=minAdm <=> det≠0 logic
(why mis-allocation kills the det). Q3: confirm/deny the slot-scaling = pivotBlowupOn-on-actives reading.
Mark proof vs heuristic.
</output_contract>

<grounding_rules>
Reason from the ChartIdx role-split + the blow-up structure. sympy facts exact. Don't rubber-stamp; if the
explicit Finset has a subtlety (e.g. the leaf anchor's exact position, or the E-role embedding), flag it.
</grounding_rules>
