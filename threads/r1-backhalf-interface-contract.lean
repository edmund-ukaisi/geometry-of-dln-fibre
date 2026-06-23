/-
#113 R1 BACK-HALF — INTERFACE CONTRACT + 3 SKELETON CONTRACTS (route-before-lines down-payment).
NOT aggregator-wired. Scratch file for the fm-2↔fm interface agreement.
Branch worktree-rung0-defs @9e2faea. Build gated on fm-2's #111 recursion landing.

═══════════════════════════════════════════════════════════════════════════════
THE CRITICAL DELIVERABLE: the recursion-OUTPUT ↔ glue-INPUT interface (fm-2 builds #111 TO this).
═══════════════════════════════════════════════════════════════════════════════

WHAT MY GLUE CONSUMES (the per-node atom, ALREADY GENERAL + DONE — S1G5Charts:g5_pivotNode):

  theorem g5_pivotNode {N : ℕ} (active : Finset (Fin N)) (U : Set (Fin N → ℝ))
      (hUcov : U =ᵐ[volume] ⋃ p ∈ active, argmaxCellOn active p)
      (g : (Fin N → ℝ) → ℝ≥0∞) :
      ∫⁻ x in U, g x ∂volume
        = ∑ p ∈ active, ∫⁻ x in chartDomOn active p \ pivotZeroOn p,
            ENNReal.ofReal |(pivotBlowupOnDeriv active p x).det| * g (pivotBlowupOn active p x) ∂volume

  Recursion shape (Codex (a)): compose g5_pivotNode by recursing on
    g' := fun x ↦ ofReal |det(pivotBlowupOnDeriv active p x)| * g (pivotBlowupOn active p x).
  Each node consumes g, emits a per-p reduced integrand g'; the tree bottoms at monomial×unit leaves.

THEREFORE fm-2's #111 RECURSION OUTPUT must supply, PER NODE n (so my glue composes):
  (I1) active_n : Finset (Fin N_n)         — the node's pivot-coordinate set (g5_pivotNode arg).
  (I2) the cover witness  U_n =ᵐ ⋃ p∈active_n, argmaxCellOn active_n p   (g5_pivotNode hUcov).
       [G3.4: this is the leaves-cover-nbhd obligation. argmaxCellOn_cover gives the univ form;
        the {∏C=0}-nbhd vs univ-minus-null reconciliation is MY G3.4 (openBox-local-witness pattern).]
  (I3) THE STRICT-TRANSFORM FACT (G3.2, fm-2's crux, the recursion-closing datum my glue reads):
         (dlnLoss-core ∘ pivotBlowupOn active_n p) x  =  monomial_n,p(x) · (dlnLoss-core' ∘ ι) x
       *** UPDATED (post-#123 per-node contract, controller-relayed): the REDUCED core is
       specifically `dlnLoss M' 0` for a GENUINE SMALLER MATRIX-CHAIN M' (field-4) — NOT a generic
       polynomial G (the (2,2,2) under-tested this: L=2 bottoms in one step). fm-2 exposes per node:
         - field-3 EXPLICIT DATA: { active : Finset (Fin N_n), pivot p, codim = active.card,
             a center-identification theorem, matching pivotBlowupOn's signature };
         - field-4: the residual reduced chain `dlnLoss M' 0` (the smaller chain, dims M' < M);
         - field-6: ΣM' < ΣM (well-foundedness, fm-2 has it via ChainDimSplit.hdrops).
       So my glue (a) feeds g5_pivotNode the field-3 active/p, (b) DESCENDS on `dlnLoss M' 0` (the
       reduced chain), (c) reads off (k,h) = (1, Mval−1) at the leaf.
  (I4) per-leaf terminus = THE BASE CASE: at a leaf, `dlnLoss M' 0` bottoms in a SMOOTH BLOCK
       (Σ entries², the L=1 terminal `‖C‖²`) → monomial × unit, threshold = monomialThreshold(k,h).
       *** core' may be NON-EMPTY at L≥3 (the recursion is genuine — my glue is a structural
       recursion on ΣM', NOT a flat 1-step; the smooth-block is the well-founded base case). The
       (2,2,2) instance hid this (one step to the smooth block); the general glue recurses.

  *** UPDATED (fm-2's (C) finding, controller-relayed): the per-node chart is a BLOW-UP with an
  EXCEPTIONAL MONOMIAL JACOBIAN ∏u^h (NOT a bare scalar unit). This is what produces the
  monomialThreshold WEIGHTS my g5_pivotNode/argmaxCellOn cover consumes — exactly the (2,2,2)
  pivotBlowup's |det| = (x₀)^n Jacobian pattern (pivotBlowupOnDeriv .det). So the "clean Schur
  recursion (det-1, no exponent shift)" framing was UNSOUND; general-M = the (2,2,2) blow-up
  machinery GENERALIZED = my #113 cover/glue architecture. VINDICATED. I3 refines accordingly:
    (core ∘ pivotBlowupOn active_n p) x = (∏ u^{h_{n,p}})(x) · (core' ∘ ι) x,
  where the monomial is the Jacobian-induced weight (NOT a unit); my glue already handles this
  (it's the (2,2,2) pattern — |det(pivotBlowupOnDeriv)| · g(pivotBlowupOn ·) in g5_pivotNode).

  *** FINAL (C2) ARCHITECTURE — ORDER CORRECTED by #126 (@921d86a, pp-hall + Codex xhigh). The
  per-node composite is BLOW-UP FIRST → STRAIGHTEN → RECURSE (NOT straighten-then-blow-up):
    STAGE 1 (MINE, the blow-up): pivotBlowupOn / g5_pivotNode on the rank-stratum COORDINATE center,
      Jacobian x^{Mval(t)−1} (the monomial weight, (k,h) = (1, Mval−1), ratio Mval/2 →
      ⨅ monomialThreshold). This comes FIRST because at the per-node ZERO-core bilinear origin
      (dlnLoss M' 0, B'=0) the generator-Jacobian rank is 0 — NO regular block, NO unit pivot — so the
      #125 unit-pivot peel has nothing to act on. The blow-up EXPOSES a HARD pivot (e.g. A1 = x·Â,
      Â[0,0] = 1 a hard constant 1).
    STAGE 2 (fm-2's (A) straighten): with the hard pivot, a pure TRANSVECTION (det = ±1, MEASURE-
      PRESERVING) — exactly lemma2Fwd-style (the (2,2,2) anchor, measurePreserving_lemma2, det = −1).
      `schur_straighten_exists` / IsSchurStraighten. NO monomial (det ±1).
    STAGE 3 (MINE, recurse): on the smaller zero-core dlnLoss M' 0 (M' = S.redM, the δ-branch
      residual ‖Â'B'‖²), ΣM' < ΣM. Base case = L=1 smooth block ‖C‖².
  ELEMENTARY (per #126): both the blow-up and the transvection are GREEN; the crux is uniform
  assembly/packaging, no new mechanism. The (2,2,2) IS this composite (one step); the general node
  RECURSES (#123 fields 4 + 6 are exactly the per-node recursion needs the (2,2,2) under-tested).

  THE COMPOSITE NODE (`schur_chart_exists`) = what I ASSEMBLE consuming fm-2's (A) straighten:
    blow-up (STAGE 1, mine) ∘ straighten (STAGE 2, fm-2) → reduced dlnLoss M' 0 → recurse (STAGE 3).
  My glue = structural recursion on ΣM': per node, g5_pivotNode the blow-up center [reads field-3
  active/p] → compose fm-2's straighten (measure-preserving, the factor germ-eq) → DESCEND on dlnLoss
  M' 0 [field-4] → base case at the smooth block. fm-2's IsSchurStraighten interface SIGN-OFF is
  CONDITIONAL on (a) residual named `dlnLoss M' 0` [field-4, for STAGE 3] + (b) explicit center-coord
  field [for STAGE 1's g5_pivotNode] — both = the #123 fields, both NEEDED for the recursion to close.

═══════════════════════════════════════════════════════════════════════════════
THE 3 SKELETON CONTRACTS (example/sorry — durable API the recursion must satisfy + assembly shape).
═══════════════════════════════════════════════════════════════════════════════

-- C1 (G3.4 — the cover): the recursion tree's leaf images cover a nbhd of {∏C=0} up to null.
-- Consumes the per-node (I2) covers; reconciles univ-minus-null ↔ {∏C=0}-nbhd (openBox-local).
-- SHAPE (general-M, generalizes the (2,2,2) argmaxCellOn cover which is ALREADY general):
--   theorem r1_leaf_cover (M : Fin (L+1) → ℕ) (tree : ResolutionTree M) :
--       {x : Params M | corePoly M x = 0}ᶜ-nbhd =ᵐ[volume] ⋃ leaf ∈ tree.leaves, leaf.image := sorry
-- [argmaxCellOn_cover + per-node compose; the genuine residual exhaustiveness work.]

-- C2 (G3.5 — the binding ratio): along the branch to stratum S(t), the leaf threshold = ½ Mval(t).
-- Per-leaf (k,h)=(1, Mval(t)−1) ⟹ monomialThreshold = ½ Mval(t), via S2 (monomial_rlct.1) +
-- unit-absorption (rlct_unit_invariant #30). Arith done (R1.2a/b #49).
--   theorem r1_leaf_threshold (M : Fin (L+1) → ℕ) (leaf : tree.leaf) :
--       monomialThreshold leaf.d leaf.k leaf.h = ENNReal.ofReal (Mval M leaf.t / 2) := sorry
-- [k=1, h=Mval−1 ⟹ axisRatio binding = (Mval−1+1)/(2·1) = Mval/2; ⨅ over axes = ½Mval.]

-- C3 (the assembly): resolution_charts via the recursion-tree glue + cover + ratio + A1.
-- Composes g5_pivotNode over the tree (consuming I3 at each node), then C1 (cover) + C2 (ratios) +
-- ⨅-min over leaves = ½ min_t Mval (R1.2 upper/lower) = lambdaCore (A1, DONE).
--   theorem resolution_charts (M : Fin (L+1) → ℕ) :  -- the Skeleton:1017 contract
--       ∃ (ι)(_ : Fintype ι)(d)(k h), rlctAtOn (dlnLoss-core M) (0:Params M)
--         = ⨅ i : ι, monomialThreshold (d i) (k i) (h i) := sorry
-- [ι = tree.leaves; (d,k,h) = per-leaf binding data; the ⨅ = ½ min Mval = lambdaCore.]

-- G3.6 (θ, folded — B2, post-divisors). REFINED by the #115 certificate: θ is the count of BINDING
-- STRATA (admissible rank vectors attaining min_Adm Mval), NOT a single-stratum divisor count.
-- Multi-achiever: (3,3,3) has 2 (S(1,0),S(2,0), both Mval=7); (2,2,2,2) has 3; (4,3,2) has 2.
--   def thetaGeom (M) := (admissibleStrata M).filter (fun t => Mval M t = minAdmMval M) |>.card
--   theorem aoyagiTheta_eq (M : Fin (L+1) → ℕ) (hL : 1 ≤ L) :
--       thetaGeom M = aoyagiTheta (cAch M) (aTheta M) := sorry
-- [the REAL θ = #{binding strata}. CROSS-CHECK (verified, all cert cases): #{binding strata} =
--  aoyagiTheta (cAch M) (aTheta M) — the geometric count EQUALS the achiever-arithmetic θ. So G3.6
--  is the bridge thetaGeom = aoyagiTheta, and my banked aTheta := Sprefix M (cAch M+1) % cAch M IS
--  the right arithmetic side. (3,3,3): #strata=2 = aoyagiTheta(2,1)=2 ✓; (3,2,3): 1=aoyagiTheta(2,0)
--  ✓; (4,3,2): 2=aoyagiTheta(2,1) ✓; (2,3,2): 2 ✓; (2,2,2,2): 3=aoyagiTheta(3,2) ✓.]

-- ═══════════════════════════════════════════════════════════════════════════════
-- #115 CERTIFICATE FACTS (pp-hall + Codex, decorrelated) — BAKE INTO C1/C2 LINES.
-- ═══════════════════════════════════════════════════════════════════════════════
-- LOAD-BEARING IDENTITY: codim S(t) = Mval(t) EXACTLY (geometric dimension-count codim, NOT the
--   naive generator-Jacobian rank — that undershoots at deep thin strata e.g. (4,3,2) origin:
--   gen-Jac-rank 8 but Mval=12). This bridge makes divisor ratios = Mval(t)/2.
-- G3.4 cover-EXHAUSTIVE: {prod=0} = ⊔_t S(t) (exact partition by t_j=rank(C¹···Cʲ), t_L=0); the
--   FULL pivot atlas (all minors) reaches every stratum via #109 Schur recursion + induction.
-- G3.5 SOUND + A1-INDEPENDENT: ⨅ monomialThreshold = ½·min_Adm Mval EXACTLY, as a resolution+Mval
--   fact; A1 (lambdaCore=closed form) is INDEPENDENT confirmation, NOT a dependency. C2 does NOT
--   need A1; ½·min Mval = lambdaCore is the separate (done) meeting point.
-- THREE CONDITIONS (else a hole — carry into every C1/C2 line):
--   (1) FULL pivot atlas (all minors/flag charts), NOT one fixed pivot — else strata missed (G3.4).
--   (2) FULL terminal block n_block = Mval(t_leaf), NOT a last local summand — else block-ratio ≥
--       m0/2 can fail (G3.5(i)). Option B (smoothBlockND) gives n_block/2 directly.
--   (3) every center = admissible-stratum strict transform (#109 discipline) — NO auxiliary
--       off-stratification blow-up, else an intermediate divisor could undercut (G3.5(ii)).
-- GATE: GO (G3.4+G3.5 are construction, not open math). Build C1/C2/C3/G3.6 against this cert.
-/
