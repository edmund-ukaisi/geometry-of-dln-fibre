You are a decorrelated second-opinion reviewer for a Lean 4 + Mathlib (v4.29) formalisation expedition. I need an adjudication of ONE build-vs-cite verdict. Be skeptical and precise; flag if I am over- or under-claiming.

CONTEXT. We are building a Core (network-free) determinantal rank-geometry + constructive pivot-chart atlas library, re-expressing DLN (deep linear network) matrix-multiplication rank-loci as instances. The capstone goal is a "bare FiberBundle" statement: the rank-=r locus of an affine determinantal scheme is locally trivial with explicit Schur-complement charts over pivot principal-opens U_P = D(det A_P).

THE GATING QUESTION (the "residue-field-rank bridge"). For the charts to cover EVERY scheme point (not just k-rational matrices), we need: at every prime p of the rank-=r coordinate ring, [rank over the residue field κ(p) = r] ⟹ [some r×r pivot minor is a unit at p] ⟹ [p ∈ some chart U_P]. The brief predicted this is "detail-at-scale" (basic-opens D(f_i) cover where the f_i generate the unit ideal, + extend the minor↔rank API over a general residue field), NOT a "monument" (a deep insight that is itself a research achievement, e.g. resolution of singularities).

WHAT I FOUND IN THE REPO (all sorry-free, axiom-free, machine-checked):
1. `Matrix.rank_le_iff_forall_submatrix_det_eq_zero`: over ANY field, A.rank ≤ r ↔ all (r+1)-minors vanish. General, field-level.
2. `RankMinorCover.exists_invertible_minor_of_rank`: over any field, rank-r matrix has an invertible r×r minor (the cover keystone).
3. `FibreRankBridge.mem_rankROpen_iff_rank_universalMatrixResidue_eq`: for a prime P of the coordinate ring, `P ∈ rankROpen ↔ (universal matrix over κ(P)).rank = r`. The proof: ≤ direction is automatic (the (r+1)-minors are baked to vanish in the ring, push to κ(P)); ≥ direction is "some pivot minor ∉ P ⟹ its κ(P)-image ≠ 0 ⟹ that r×r minor invertible over the field κ(P) ⟹ rank ≥ r". `rankROpen := (zeroLocus {pivot minors})ᶜ`, so the cover `iSup_pivot_basicOpen = rankROpen` is DEFINITIONAL.

So the residue-field-rank bridge appears ALREADY PROVED in-repo for the DLN instance, using only standard field-level minor↔rank + residue-field algebra. It is NOT a monument.

THE ACTUAL REMAINING OBSTACLE I FOUND. Mathlib v4.29's `FiberBundle` is PURELY TOPOLOGICAL (needs `[TopologicalSpace B]`); there is NO scheme-theoretic / Zariski-local-triviality `FiberBundle` class in `Mathlib.AlgebraicGeometry`. The repo's entire bundle layer is bespoke ring-level (localization isos, tensor product trivializations). The per-pivot trivializations + base-side cocycle are PROVED; the target-side cocycle ROUND-TRIP is deferred because `AlgEquiv.trans_assoc` is MISSING in v4.29 (only `self_trans_symm`/`symm_trans_self` exist), and the pointwise `ext` route hits a kernel timeout on the @[reducible] double-localized type.

MY DRAFT VERDICT:
(a) The residue-field-rank bridge itself = DETAIL-AT-SCALE, already done in-repo; de-DLN-ifying it to a general determinantal scheme is mechanical (the field-level inputs are already general).
(b) BUT the "bare FiberBundle capstone" as literally stated (a Mathlib `FiberBundle` instance) is NOT reachable, because Mathlib has no algebraic/scheme FiberBundle to instantiate — and putting a topology on Spec to use the topological one would be a category error. So the honest ceiling is: the explicit atlas (charts + Schur trivializations + cover-every-scheme-point via the bridge) + the cocycle, with the target-side cocycle round-trip gated on a Mathlib-gap `AlgEquiv.trans_assoc` spin-out (network-free, detail-at-scale).

QUESTIONS FOR YOU:
1. Is my verdict (a)+(b) right? Specifically: is the "bare FiberBundle" target a category error given Mathlib's only FiberBundle is topological, and is the honest deliverable "explicit atlas + cocycle (cover-every-point via the residue bridge), with the abstract-bundle leap roadmapped"?
2. Is there a scheme-theoretic local-triviality notion I'm missing that IS in Mathlib v4.29 or is cheap to define (e.g. an `IsLocallyTrivial` predicate as "∃ open cover + per-chart AlgEquiv to a product", which sidesteps the topological FiberBundle entirely)? Would defining such a bespoke predicate be the right "bare bundle" target instead?
3. Is `AlgEquiv.trans_assoc` genuinely the blocker for the cocycle round-trip, or is there a standard Mathlib idiom (e.g. proving `e₁.trans e₂ = e₃` via `AlgEquiv.coe_ringEquiv`/`toRingEquiv` injectivity, or `RingEquiv.trans_assoc` which DOES exist via `Equiv.trans_assoc`) that dissolves it without new API?
4. Any sharper kill-condition for the claim "the residue-field-rank bridge is detail-at-scale"?

Answer concisely, numbered. Push back hard if the framing is wrong.
