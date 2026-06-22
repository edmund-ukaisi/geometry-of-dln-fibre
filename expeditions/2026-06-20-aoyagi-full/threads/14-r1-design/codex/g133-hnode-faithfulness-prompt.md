DECORRELATED FIDELITY RED-TEAM (Lean 4 / Mathlib, RLCT resolution of DLN square loss).

CONTEXT. A per-node RLCT existence theorem `schur_straighten_squeeze_exists` is parametrized over an
explicit interface hypothesis `hnode` (NOT asserting any coordinate identity). The QUESTION is whether
`hnode` is a FAITHFUL presentation of what the hard-pivot blow-up actually produces at a 2-factor Schur
node — i.e. is the interface CORRECT, so the downstream discharge (proving hnode from the actual loss)
isn't chasing a wrong shape.

THE SETUP (math, established/witnessed elsewhere):
- A zero-product matrix-chain core ‖A1·A2‖² at the origin (all bilinear, Jacobian rank 0).
- BLOW UP the rank-stratum center: A1 = x·Â with Â[0,0] = 1 a HARD constant (the pivot). The loss
  becomes x²·‖Â·A2‖². The residual ‖Â·A2‖² is the REDUCED NODE input (x² is a separate monomial weight,
  handled in a different "cover" lane — NOT in this per-node theorem).
- Â = [[1, a],[b, D]] (block: 1×1 hard pivot, row a, col b, block D). A2 = [[β],[Γ]] (rows β, Γ).
- The product Â·A2 has: TOP row = 1·β + a·Γ =: E_row (the "pivot-row product", the REGULAR generators),
  LOWER rows = b·β + D·Γ. A pure ring identity (`schur_row_decomp`, GREEN) rewrites the lower rows as
  b·β + D·Γ = b·(β + a·Γ) + (D − b·a)·Γ = b·E_row + S·Γ, where S = D − b·a is the Schur complement and
  S·Γ is the SMALLER chain core = the reduced loss dlnLoss(reduced) = "G²".
- So ‖Â·A2‖² = ‖E_row‖² + ‖b·E_row + S·Γ‖² = (∑ⱼ E_rowⱼ²) + ∑ᵢⱼ (bᵢ·E_rowⱼ + (S·Γ)ᵢⱼ)².

THE INTERFACE hnode (verbatim; flatCore is the abstract node loss, w.1 the regular coords, w.2 reduced):
  ∃ U ∈ 𝓝 (0,0), ∀ w ∈ U,
     (1) flatCore w = (∑ⱼ (w.1 j)²) + (∑ᵢ ∑ⱼ (bcol w i · w.1 j + SΓ w i j)²)
     (2) G(w.2)² = ∑ᵢ ∑ⱼ (SΓ w i j)²
     (3) ∑ᵢ (bcol w i)² ≤ T²
where bcol, SΓ are arbitrary (point-dependent) functions, T a fixed constant. The theorem then proves
∃ c₁ c₂ > 0, the two-sided squeeze c₁·Φ ≤ flatCore ≤ c₂·Φ holds (Φ = ∑w.1² + G²) with
c₁ = (2(1+T²))⁻¹, c₂ = 2+2T² (via Young's inequality, given ∑(bcol·w.1)² = ‖bcol‖²·∑w.1² and (3)).

QUESTIONS (mark inference vs fact; be adversarial):
1. Is hnode's form (1) FAITHFUL to ‖Â·A2‖²? In particular: the regular block is EXACTLY ∑(w.1 j)²
   (identifying w.1 = E_row, the pivot-row product). Is it correct that the pivot-row product entries
   are the regular generators with unit (coefficient-1) squares — no cross term between regular block and
   lower block, the cross terms living ONLY inside (bcol·w.1 + SΓ)²?
2. (2) sets G² = ∑(SΓ)² = ‖S·Γ‖². Faithful that the reduced core is ‖S·Γ‖² (NOT ‖Â·A2red‖² or some
   other residual)? Is S·Γ a genuine smaller matrix-chain product (the next recursion node)?
3. (3) ‖bcol‖² ≤ T²: bcol = b = the pivot COLUMN Â[1:,0]. At the deepest point b → 0 (the blow-up
   normalizes the pivot to 1, the off-pivot column entries → 0). Is "‖b‖² bounded by a constant T² on a
   nbhd" the RIGHT and SUFFICIENT smallness condition for a UNIFORM (point-independent) two-sided
   constant squeeze? Any hidden requirement (e.g. need b → 0, not merely bounded)?
4. MISSING PIECE: does hnode OMIT anything the blow-up genuinely produces that would BREAK the squeeze
   or the downstream discharge? Candidates: (a) the x² monomial Jacobian weight — correctly excluded
   (separate lane)? (b) a coupling making w.1 (E_row) itself depend on the lower data? (c) the regular
   block possibly having NON-unit coefficients (E_row entries weighted)? (d) the squeeze comparing at a
   point where Φ could vanish faster than flatCore (the c₁>0 needs flatCore not vanishing strictly faster
   — does the form guarantee same zero-set)?
5. Could hnode be SATISFIED by data that is NOT a real Schur node (too weak, lets garbage through), in a
   way that would make the existence theorem misleading? Or is it appropriately tight as a contract?
