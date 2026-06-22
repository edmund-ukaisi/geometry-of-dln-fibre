# G1 RouteMTree — FINAL build spec (fm3, all interfaces locked, ready to grind)

Every design + interface question is CLOSED. This is the complete spec for the dispatcher grind.

## Target: ONE unified RouteMAtlas (crux2 @31063ec, headline GREEN given it)
structure RouteMAtlas M F U ι d k h := { isCover : IsRouteMCover F U ι d k h, isValue : IsResolutionAtlas M ι d k h }
routeM_rlctAtOn_eq_lambdaCore (atlas) : rlctAtOn F 0 = ofReal (lambdaCore M)  -- GREEN, one Eq.trans.
My G1 produces ONE (ι,d,k,h); discharge isCover + isValue over the SAME family. Bridge is
MECHANISM-INDEPENDENT — ingests the FINAL accumulated per-leaf (d,k,h), however built.

## Encoding (controller-accepted): WF.fix / NodeChartFamily, Fintype-as-field
RouteState(L,M); routeMeasure = lex(L,ΣM,ncDefect); routeRel_wf. routeAtlas = WellFounded.fix.
NodeChartFamily per-leaf record (crux2 leaf-level): {composite chart φ_i, pullback L∘φ_i=monomial·unit
(pointwise on chartDomOn, unit≥a>0), Jacobian, (d,k,h)}. routeMIota/Fintype/routeD/routeK/routeH banked-shape.
FOUNDATION BANKED: RouteMState.lean @origin/fm3/routem 7c6401a (green, leaf=unit).

## C1 node (triply-converged: my (a)/(b) + pp2 g144 + controller lock): blow-up ⊕ Schur-descent ⊕ recurse
- BLOW-UP: pivotBlowupOn active p → core∘φ = x_p²·(core∘hardPivotAt) (G2 node_loss_pivot_factor),
  Jac (x_p)^(card−1) (node_jacobian_det). x_p² = k=1 weight, ΣM UNCHANGED.
- SCHUR-DESCENT (the ΣM-drop, route-independent): the triangular D↔S+ba peel (det-1, S⁻¹-free) clears
  pivot row+col, Â→blockdiag[1,S], residual ‖S·A2red‖²=dlnLoss M' 0. schurState = M' (M'_0=M_0−1,
  M'_1=M_1−1, M'_s=M_s s≥2). measure_drops = crux2's ChainDimSplit.measure_drops, Σdrop=2 (drop_0=drop_1=1).
  Loss-pullback FACT = Framing A row-split (my schur_node_loss_presentation, ‖Â·A2‖²=‖row0‖²+‖lower‖²).
  {S=0} bilinear center needs the triangular peel (pivotBlowupOn hits coord subspaces only); {Γ=0} direct.
- PRECONDITION M_0,M_1≥2 (else width-1 pinch → C4).
- RECURSE on schurState. lex↓ via Σdrop=2.
Build C1 against g138/g140-BOTH-STEPS (efff7ca/2f80d44), NOT g138-c2c5-fix 5bcac11 (pre-#36, wrong).

## C2/C4/C5 (g140 taxonomy)
- C2 full-rank pass-through: passState (L drops); downstream-descent.
- C4 separating/width-1 pinch: Fubini split, two children (leftState/rightState, L drops). The C4-terminal
  proviso (empty-Schur/width-1 → C4, not C1) is the no-stall guard, baked in classify.
- C5 mixed partial-drop: C1+C2 composite.
- C3 NC-completion: per-leaf (d,k,h) post-pass (k≥2), not a tree node.

## isCover (= IsRouteMCover, crux2's bridge consumer)
- Fmeas/Uopen/Umem (easy: dlnLoss polynomial-measurable; U = bounded open box ∋ 0).
- cover_le: ∫_U |F|^{−c'} ≤ Σ_ι ∫_{unitBox d_i} monomialIntegrand. PROOF = g5_pivotNode/recStep cover
  split (argmaxCellOn cover + aedisjoint) + per-chart CoV (node_loss_pivot_factor + node_jacobian_det
  composed down the path) landing monomial·unit on chartDomOn [−1,1]^d. NORMALIZATION (signed-box [−1,1]^d
  + monomial·unit → bare-monomial [0,1]^d): crux2's STAGED adapter monomialIntegrand_abs_invariant (2^d-
  orthant) + the unit-factor reduction (integrableOn_monomial_mul_unit_iff, banked). crux2 completes on flag.
- cover_ge_div: ε-uniform leaf divergence at/above threshold (generalize Case222 rlctAtOn_myF222_le route,
  cites monomial_rlct/S2 for ≤). monomialIntegrand_lintegral_box_eq_top is the banked atom.

## isValue (= IsResolutionAtlas, cover's S-min @1c4b9b5, via of_mult_and_achiever)
- threshold_ge (C≥): ∀ i, ½·m₀ ≤ monomialThreshold (d i)(k i)(h i). From k=1 mult-control
  (monomialThreshold_ge_of_mult', banked) + admissibility (every center codim = some Mval(T) ≥ minAdm).
- achiever (C=∃): ∃ i₀, monomialThreshold = ½·m₀. = pp2's g147/g148 binding branch (i₀ = the C1 path
  resolving each C_s to T*-rank, j₀ = binding divisor (1,m₀−1)). Transcribe pp2's cert; my routeMIota
  nested-Σ/Sum path is the i₀ shape (depth-2 for (2,2,2): C1@A-pivot → C1@incidence → leaf).

## Banked precedent for every piece
G2/Schur/LossHomog (mine, banked) · schur_lossDiff_mem_ideal + ChainDimSplit.measure_drops (crux2) ·
g5_pivotNode/argmaxCellOn_cover/_aedisjoint/pivotBlowupOn(Deriv_det) (atlas) · monomialThreshold_ge_of_mult'/
_le_regularSeq + monomial_rlct/S2 + monomialIntegrand_integrable_of_lt/_lintegral_box_eq_top (Skeleton/Case222) ·
integrableOn_monomial_mul_unit_iff + integrableOn_Icc_symm_of_even (Case222, the normalization) · pp2 achiever cert.

## NET
No open interface/design questions. The grind = classify (rank-pattern dispatcher) + the 4 reduction
state-maps + descent proofs + the enriched per-leaf accumulation → concrete routeAtlas; the extraction
(routeMAmbient=flatDim/routeMCore=flat dlnLoss/routeMBaseNbhd=bounded box, needs ParamsFlat import); the
isCover facts (Fmeas/Uopen/Umem easy; cover_le the hard one; cover_ge_div) + isValue (threshold_ge + achiever).
crux2 packages into RouteMAtlas on route-m-atlas + completes the normalization adapter. Commit+push each green decl.

## ACHIEVER CERT (pp2 g147, DELIVERED) — the routeM_achiever transcription target
Cert: origin/g147-achiever-cert @6e6b00d, g147-Smin-achiever-CERTIFICATE.md. The (i₀,j₀) witness for
of_mult_and_achiever (encoding-independent; pp2 re-spells i₀ in my routeMIota once it has the signature, sent):
- T* = (Adm M).inf' Mval minimiser; m₀ = Mval(T*).
- i₀ = the routeMIota path resolving each C_s to its T*-rank t_s (nodeC1/C5 pivot, or nodeC2 where t_s=t_{s-1}).
- j₀ = the codim-m₀ binding divisor: (k i₀ j₀, h i₀ j₀) = (1, m₀−1). ⟹ monomialThreshold = m₀/2 = ½·m₀.
- of_mult_and_achiever hk₀ (k i₀ j₀=1) + hh₀ (h i₀ j₀=m₀−1) → monomialThreshold_eq_half_of_binding → achiever.
- (2,2,2) concrete: T*=(1,0) rank-1 incidence codim-3, i₀ = ρ-chart path, j₀ = ρ-divisor, (k,h)=(1,2), 3/2.
- Realizability (why i₀ exists): T* via Core.OrbitKostant/Orbit.baseChange_normalForm (RealizableRank =
  range rankFn; Gabriel normal form hits T*), seam prefix:RealizableRank M→Adm M. Only the MINIMISER need
  be reached (weaker than full surjectivity); the nodeC1/C5 branch picks the T*-rank pivot per node.
- Verified (g147): (2,2,2)→(1,2); (3,3,3)→(1,6); (2,2,2,2)→(1,2); (4,3,2) T*=(2,0)→(1,5); (2,1,2)→(1,1).
ALL UPSTREAM CERTS NOW DELIVERED — the grind has no remaining external dependency.

## ACHIEVER i₀ RE-SPELLED IN MY ENCODING (pp2 g148, zero translation gap)
Cert: origin/g148-iota-respell @febc15a, g148-achiever-iota-respell.md. i₀ built by the SAME WellFounded.fix
recursion as routeAtlas, per-RouteCase:
  .c1 cs dec → i₀@S = ⟨c*, i₀'⟩ : Σ c:cs, (routeAtlas (schurState S c.1)).ι   (c* = the T*-rank PivotChoice cell)
  .c2 c dec  → i₀@S = i₀'                                                     (descend, same ι)
  .c5 cs p   → i₀@S = Sum.inl ⟨c*, i₀'⟩                                       (complement-via-C1, the minimiser's binding center)
  .c4 s      → i₀@S = Sum.inl i₀' | Sum.inr i₀'                               (the block with T*'s binding center)
  .leaf md   → i₀ = PUnit.unit                                               (md = binding divisor (1, m₀−1))
So i₀ = ⟨c*₁, ⟨c*₂, …, PUnit.unit⟩⟩. Wiring: ι := routeMIota ⟨L,M⟩, d/k/h := routeD/K/H; of_mult_and_achiever
(i₀, j₀): j₀ = the binding coord on i₀'s MonoData (routeK _ i₀ j₀=1, routeH _ i₀ j₀=m₀−1) →
monomialThreshold_eq_half_of_binding → achiever.
(2,2,2): i₀ = ⟨c*, PUnit.unit⟩ (c* = ρ-chart pivot, schurState → leaf md₁=(1,2)), threshold 3/2. ✓
DEPENDENCY: classify/PivotChoice stubbed → i₀'s SHAPE wireable now (the recursion selecting the T*-rank
cell), concrete c* lands with #39's rank-pattern un-stub. (2,2,2) anchor wireable immediately. Realizability
(cs nonempty at the T*-rank cell) rides Core.baseChange_normalForm, stub-independent.
pp2's λ-path arc g132→g148 COMPLETE. No remaining translation gap on any consumed cert.

## ACHIEVER FINAL (pp2 g148-222fix2 @34c1d6c) — fully pinned to my encoding, zero gaps
- i₀ = ⟨c*₁, ⟨c*₂, …, PUnit.unit⟩⟩, per-rank-unit nested Σ/⊕ following the T*-rank PivotChoice at each node
  ("resolve C_s to t_s" = (t_{s-1}−t_s) per-rank-unit C1 steps).
- (2,2,2): i₀ = ⟨c*₁(A-pivot rank2→1), ⟨c*₂(incidence), PUnit.unit⟩⟩, TWO C1 nodes. (2-node, authoritative.)
- j₀ = the axis with LARGEST card = m₀ (the C1 step whose pivotBlowupOn center is the full codim-m₀
  stratum); it binds the ⨅ at ½·m₀; other axes (smaller card) have larger ratio (don't lower the ⨅).
- ROUTE (NOT bare single-axis eq): monomialThreshold = ½·m₀ via le_antisymm —
  (≤) monomialThreshold_le_regularSeq at j₀ ((k,h)=(1,m₀−1)); (≥) threshold_ge (all axes, mult-bound).
  of_mult_and_achiever bundles both (hk₀/hh₀ at j₀ + the m₀·k≤h+1 mult-bound).
- Wires once classify/PivotChoice un-stub (the c* lands with the rank-pattern combinatorics; the
  card=m₀-at-binding-step is the (S-min) datum, stub-independent).

=== COORDINATION + DESIGN ARC COMPLETE ===
No open questions: interface (unified RouteMAtlas, crux2), value (cover S-min + of_mult_and_achiever),
achiever (pp2 g147→g148→222fix2, re-spelled in my encoding), cover_le normalization (crux2 adapter),
C1 mechanism (blow-up ⊕ Schur-descent ⊕ recurse, triply-converged), encoding (WF.fix, controller-accepted).
All upstream certs delivered. The grind (classify + reductions + per-leaf accumulation + isCover facts +
isValue) is dependency-free formalisation against this locked spec.

## C1 PEEL TRANSPORT (pp2 g152, pre-answered) — det=1 MP, rides measurePreserving_lemma2, NO new lemma
The per-node C1 triangular peel w := D − ba is MEASURE-PRESERVING, det EXACTLY 1 (a shear/transvection:
Jacobian lower-triangular with 1's on diagonal [[1,−b,−a],[0,1,0],[0,0,1]], det=1 identically, at ANY rank
— I verified the shear is det-1 for matrix S in /tmp/peel_rank_r.py; pp2 g152 confirms). So schurState's
peel rides measurePreserving_lemma2 / rlctAtOn_comp_homeomorph (det=1, no Jacobian weight) — the EASY MP
side, NO new bounded-unit-Jacobian lemma needed.
DISTINCTION (don't conflate): C1 per-node peel = det=1 MP (measurePreserving_lemma2). The g150
deepest-point GAUGE chart (crux2 #51) = det-UNIT non-MP (det(A)^{-(r+M2)}det(B)^{-M0}, bounded unit ≠1,
rides rlctAtOn_unit_invariant_aux + germ-locality) — DIFFERENT transport, because it's the whole-chain
gauge slice accumulating endpoint dets, not a single Schur shear. For nodeC1 I'm on the MP (easy) side.

=== ALL BUILD-RELEVANT DETAILS NOW CLOSED ===
Every interface (RouteMAtlas/IsRouteMCover verbatim), cert (achiever g148, value of_mult_and_achiever),
design (C1 = blow-up ⊕ det-1 triangular peel ⊕ recurse, rank-r = same op iterated), and transport
(C1 peel = det=1 MP / measurePreserving_lemma2; cover_le normalization = banked + crux2 adapter) is pinned.
Zero open questions, zero banked-lemma gaps. The grind is pure formalisation against this spec.

## C1 PEEL det=1 RANK-r CERTIFIED (pp2 g153 @0006f3a, decorrelated with my /tmp/peel_rank_r.py)
The general-rank-r peel W:=D−b·a is det=1 EXACTLY (block shear: ∂(W,a,b)/∂(D,a,b) block-lower-triangular,
identity on the D-block diagonal since ∂W/∂D=I, f(a,b) D-independent). Verified r=1,2,3 × several (m,k)
(pp2 g153) + my rank-r check — CONVERGED. So nodeC1's peel rides measurePreserving_lemma2 (det=1 MP) at
ANY rank, NO bounded-unit lemma, NO rank-dependent unit. Fully de-risked. (The bounded-unit case is ONLY
the g150 deepest-point gauge chart, crux2 #51 — not the per-node C1 peel.)
=== COORDINATION + DESIGN ARC EXHAUSTIVELY CLOSED (g132→g153). The grind is pure formalisation. ===

## ACHIEVER WIRING — eq_half_of_binding bundles the multi-axis le_antisymm (pp2 g154)
of_mult_and_achiever calls monomialThreshold_eq_half_of_binding (d i₀)(k i₀)(h i₀) _ hm₀pos (hmult i₀) j₀ hk₀ hh₀
where (hmult i₀) = the within-chart mult-bound (m₀·k≤h+1 on ALL of chart i₀'s axes, the C≥/≥) and j₀ = the
card=m₀ binding axis (the C=∃/≤). So eq_half_of_binding IS the le_antisymm internally — it does NOT assume a
single-axis chart; it composes for my 2-axis (2,2,2) path directly. WIRE IT AS ONE LEMMA CALL (eq_half_of_binding
@ j₀ + hmult), NOT a manual le_antisymm. (2,2,2): u0 (card4,ratio2) + u2 (card3,ratio3/2), ⨅=3/2, j₀=u2,
the within-chart mult-bound pins the min at u2. Consistent g147/g148/g154. Achiever fully routed, no obstruction.

## C1 measure_drops — CORRECTED (crux2 record-correction + controller; supersedes the ΣM≥1 steer)
nodeC1.measure_drops = the det-1 triangular PEEL's Σdrop=2 (the schurState lemma, w:=D−ba / #37 change),
NOT ΣM≥1 (crux2's earlier "Framing A ΣM≥1" steer was imprecise — controller-flagged, retracted). The peel
is NEEDED because {S=0} is bilinear (pivotBlowupOn only hits coordinate subspaces); it clears pivot row+col,
ΣM−2. schurState's M' = (M_0−1, M_1−1, M_2,…), Σdrop=2 via crux2's ChainDimSplit.measure_drops (or my own
schurState lemma threading D↔S+ba). Loss-pullback FACT still = my green schur_node_loss_presentation (the
row-split ‖row0‖²+‖lower‖² — how I PROVE the pullback); the measure_drops WIRING = Σdrop=2 (the peel). I
already have this (g152/g153-converged + /tmp/peel_rank_r). The VALUE (⨅ monomialThreshold = lambdaCore) is
framing-independent. (Same det-1 triangular peel at BOTH per-node C1 (w:=D−ba) AND crux2's #44 deepest-point
gauge chart (g150 T̃) — one mechanism, two levels.)
(pp2's Σdrop=2 / the det-1 triangular peel is the FULLER per-node Schur clear — available if a node ever
needs the one-step ΣM−2, but A's row-split + recurse is the default; same terminating lex, A is simpler.)

=== ALL WIRING + DESIGN CLOSED. Framing A locked. The grind is pure formalisation against this spec. ===

## NON-DEGENERACY HYPOTHESIS (resolved fidelity finding — controller-accepted)
THE FINDING: the lambdaCore identity rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M) is FALSE for interior
M_s=0 (interior H_s=r): prod_M ≡ 0 (0-dim cut, verified /tmp/interior_zero.py) ⟹ RLCT=⊤ ≠ finite lambdaCore.
So R1 ASSUMES interior M_s≥1 — NOT discharged. Forced by the formula's correctness, not a design choice.
FRAMING (controller-corrected, precision-faithful): this is OUR FORMALISATION CARVE-OUT — refining the
paper's realisability (r≤min(d⃗), NON-strict ≤, Lehalleur–Rimányi main.tex:1874) to exclude the prod≡0
degeneracy the combinatorial lambdaCore can't see. Sound + consistent within Aoyagi's realisable domain,
but NOT a verbatim-stated Aoyagi assumption. FENCE IT next to the claim as "the formalisation's
non-degeneracy carve-out", NOT "Aoyagi-faithful verbatim". (Optional, deferred, not a gate: deep-read the
DLN preprint to pin whether Aoyagi's genericity implicitly excludes it — nice-to-have for the final
fidelity note.)
THREADING (controller-assigned): I thread it through R1's lemmas; crux2 threads L2 + headline
(aoyagi_learning_coefficient + deepest_point_reduction). PREDICATE (coordinating with crux2):
  headline/L2 (A, on H,r): hNonDeg : ∀ s : Fin (L+1), 0 < (s:ℕ) → (s:ℕ) < L → r < H s
  my R1/RouteMTree (B, on M):              ∀ s : Fin (L+1), 0 < (s:ℕ) → (s:ℕ) < L → 0 < M s
  defeq-bridged (M s = H s − r ⟹ r<H_s ⟺ 0<M_s); interior 0<s<L (endpoints free); VACUOUS at L=1
  (no interior s — the leaf/L=1 case needs no condition). resolution_charts + RouteMTree's identity
  lemmas carry (B); classify's domain is already interior M_s≥1 so it's a natural fit. AWAITING crux2's
  form-lock, then thread.

## hMid FORM — CORRECTED to ALL-s (g159, crux2 fidelity catch + controller Decision A)
⚠ The interior-only lock below (g154) was INCOMPLETE — it missed the ENDPOINTS. SUPERSEDED.
CORRECT SHARED FORM (headline + L2 + R1, all-s, endpoints included):
  H-form (headline/L2): hMid : ∀ s : Fin (L + 1), r < H s
  M-form (R1/resolution_charts): hMid : ∀ s : Fin (L + 1), 0 < M s
  bridge: M s = H s − r ⟹ (r < H s ⟺ 0 < M s), all s.
WHY all-s (the fidelity catch): R1's identity rlctAtOn(dlnLoss M 0) 0 = ofReal(lambdaCore M) is FALSE
whenever ANY reduced width M_s=0 — INTERIOR OR ENDPOINT:
  - interior M_s=0 (0<s<L): prod ≡ 0 (zero-dim intermediate cut).
  - ENDPOINT M_0=0 (r=H_0) or M_L=0 (r=H_L): prod M A : Matrix (Fin (M 0)) (Fin (M (Fin.last L))) is an
    EMPTY matrix ⟹ prod ≡ 0. r=H_0/H_L are REACHABLE under hr (r ≤ H, non-strict). So the endpoints break
    R1's identity (and L2's smooth-block) exactly like the interior. The interior-only form left M_0/M_L=0 in.
- R1 CARRIES it (NOT discharged — ⊤≠finite for any M_s=0). DONE @origin/fm3/routem 0cedc7e:
  resolution_charts carries `(hMid : ∀ s : Fin (L+1), 0 < M s)`, docstring fences both interior+endpoint
  degeneracies, green (2671). crux2 re-threads L2/headline to ∀ s, r<H s + builds the hMid⟹hGne bridge.
- NOT vacuous at L=1 anymore (the all-s form constrains M_0,M_1 even at L=1 — correct: a single zero-width
  layer makes the lone matrix empty ⟹ prod≡0). The earlier "vacuous at L=1" was an artifact of the wrong
  interior-only form.

--- SUPERSEDED (g154, interior-only — kept for the finding's history) ---
[Was: hMid : ∀ s : Fin L, 0 < s.val → r < H s.castSucc; "hits interior H_1…H_{L-1}, endpoints free".
 The "endpoints free" was the GAP — r=H_0/H_L break R1's identity. Corrected to all-s above.]

## ARCHITECTURE FINDING (g155, Codex-decorrelated + crux2's own design docstring) — RESHAPES #39
THE FORK on the general-M R1: my RouteMTree.lean re-invents a recursion-state (RouteState/schurState/
classify) that PARALLELS crux2's banked ChainDimSplit + schur_recursion_step_sound (GeneralR1Recursion.lean,
route-m-atlas). Codex xhigh (routeM-division-{prompt,answer}.md) + crux2's OWN docstring converge:
- crux2's GeneralR1Recursion docstring (line 20-22) STATES the intended division: "the general-M chart is
  the det-1 straightening (crux2) THEN a blow-up (monomial Jacobian → ⨅ monomialThreshold, **fm's cover
  lane**, applied to the residual G)." So the seam was crux2-designed: crux2 = straightening phase
  (schur_recursion_step_sound: rlctAtOn(dlnLoss M 0) = nReg/2 + rlctAtOn(dlnLoss Mred 0), MP-chart-gated);
  fm = the blow-up cover lane (⨅ monomialThreshold via the per-node pivotBlowupOn + cover-split).
- TWO orthogonal mechanisms, BOTH needed (refines Codex's "telescoping replaces cover" — too strong):
  (i) ADDITIVE-along-a-path: crux2's per-step nReg/2 descent → each leaf's accumulated value.
  (ii) MIN-over-branches: the ⨅ over leaves = min over reduction paths = MY cover-split (argmaxCellOn pivot
       cells, the branching). The ⨅ is NOT reconstructed by telescoping a single chain — it's the min over
       the BRANCHING the cover-split produces. So cover_le/_ge_div ARE the right vehicle for the min-half.
- PARALLEL-RECURSION HAZARD (Codex #3, AGREE): my standalone RouteState is a liability IF it duplicates
  ChainDimSplit's state-transition. FIX (Codex shape): the recursion DRIVER should be shared (crux2's
  ChainDimSplit step relation); fm owns the leaf MonoData ACCUMULATOR + threshold proofs + the cover
  branching, NOT an independent state-transition system. My routeAtlas should consume crux2's reduction
  state, not re-derive schurState.
- LOAD-BEARING ASSUMPTION (Codex flagged, VERIFIED): schur_recursion_step_sound's chart hypothesis
  (hfactor: dlnLoss M 0 ∘ χ = u·(∑x² + G²)) IS the per-node factorisation — dischargeable from my G2
  node_loss_pivot_factor + crux2's schur_straighten_of_data. Confirmed against the actual signature.
- hGne RE-SURFACES PER-STEP: schur_recursion_step_sound takes (hGne : ∃ U ∈ nhds 0, ∀ᵐ z, G z ≠ 0) on the
  REDUCED core EACH step. This is the hMid⟹hGne crux2 owns — but it's needed at every recursion level, not
  once. Confirms hGne is crux2's (the straightening lane consumes it); my cover lane does not.
DECISION OWED: the controller + crux2 must confirm the seam (straighten=crux2 / branching-cover=fm, both
needed) before I grind. NOT a unilateral call — it sits exactly on the crux2/fm3 boundary. SURFACED.
CONCRETE FORK-INDEPENDENT NEXT STEP (Codex #4, useful in every division): the per-step MonoData→(d,k,h)
threshold-update lemma — `monomialThreshold (addPivotDivisor d k h) = …` relating a node's added pivot
divisor (1, card−1) to its monomialThreshold contribution. Pure (d,k,h) combinatorics, no recursion,
no cover. Stackable now.

## VALUE-SIDE BEDROCK BANKED (fm3, @origin/fm3/routem 870afff) — appendDivisor min-fold
The fork-independent value-side accumulation atoms (RouteMState.lean, green, clean-three + monomial_rlct):
- `MonoData.appendDivisor md c := ⟨md.d+1, Fin.snoc md.k 1, Fin.snoc md.h (c-1)⟩` — snoc the codim-c
  exceptional axis (1, c−1).
- `iInf_fin_succ_eq_min_last` : ⨅ over Fin(d+1) = min(last, ⨅ castSucc-prefix). Generic ℝ≥0∞, clean-three.
- `monomialThreshold_appendDivisor` : monomialThreshold (md.appendDivisor c) = min(c/2, monomialThreshold md).
- `monomialThreshold_appendDivisor_ge` : append codim-≥m₀ ⟹ preserves ≥ m₀/2 (threshold_ge inductive step).
- `monomialThreshold_appendDivisor_le_binding` : append codim-m₀ ⟹ ≤ m₀/2 (achiever upper bound).
These are the per-node folds of IsResolutionAtlas's threshold_ge (C≥) and achiever (C=∃). They compose
along ANY append-recursion, so they survive whatever A/B/C division the seam decision picks. The achiever
transcription (pp2 g148) lands by folding _le_binding at the binding node + _ge elsewhere, down to a ⊤
leaf (leafMonoData_threshold) — le_antisymm gives = m₀/2. The MonoData accumulator is fm's regardless
(Codex #3: fm owns the leaf data accumulator + threshold proofs; only the state-transition DRIVER may
rebase onto crux2's ChainDimSplit).

PER-PATH FOLD BANKED (@origin/fm3/routem a446bcd): the closed-form per-leaf value.
- `MonoData.foldDivisors cs` : fold appendDivisor over a codim list (one path's appends).
- `ratioMinFold cs` (+ _nil/_cons) : ℝ≥0∞ min-fold of the ratios c/2.
- `monomialThreshold_foldDivisors` : monomialThreshold (foldDivisors cs) = ratioMinFold cs.
- `ratioMinFold_le_of_mem` / `ratioMinFold_ge_of_all_ge` : the two list-min bounds.
- `monomialThreshold_foldDivisors_eq_of_binding` : all-codim ≥ m₀ ∧ m₀ ∈ cs ⟹ threshold = m₀/2.
  ⟹ the IsResolutionAtlas achiever VALUE, in Lean, for one reduction path (pp2 g148 transcribed).
SESSION STATE (g155): hMid threaded (6f4e70f) + full value-side bedrock (3b2ba20→a446bcd), all green
sorry-free clean-three(+monomial_rlct). RouteMTree.lean stays UNCOMMITTED (all-stub) pending the seam
decision — do NOT bank the parallel RouteState recursion until controller+crux2 confirm the driver
(rebase onto ChainDimSplit vs standalone). The recursion DRIVER is the only piece blocked.

## SEAM DECIDED + REBASE (controller g156) — DRIVER = crux2's ChainDimSplit; drop RouteState
(a) SEAM: crux2 = per-step straighten / additive nReg/2 descent (ChainDimSplit, value-along-a-path);
    fm = the blow-up cover / ⨅-min-over-pivot-branches (→ ⨅ monomialThreshold). BOTH needed; the cover
    STAYS (it IS the ⨅), on top of crux2's descent. My refinement accepted (telescoping ≠ the cover).
(b) REBASE: YES. Drop the parallel RouteState; rebase the descent-STATE onto crux2's banked ChainDimSplit.
    Keep the cover-branching + the MonoData accumulator + threshold proofs ON TOP (fm's, per Codex #3).
    Coordinate the ChainDimSplit interface with crux2 (my 3 questions → crux2 answers + extends
    ChainDimSplit if the cover-branching needs more). Controller told crux2 to support it.
CONSEQUENCE for my files: RouteMState's RouteState/widthSum/ncDefect/routeMeasure/routeRel/routeRel_wf
become DEAD (superseded by ChainDimSplit + its hdrops/ΣM termination) — but MonoData + leafMonoData +
ALL the appendDivisor/foldDivisors threshold lemmas (3b2ba20→a446bcd) are KEPT (they're on MonoData,
recursion-driver-agnostic). RouteMTree's routeAtlas gets rewritten to recurse over ChainDimSplit
(consume crux2's reduction state), NOT WellFounded.fix on RouteState. AWAITING crux2's reply on the
ChainDimSplit interface shape + whether it carries the per-node pivot-branch data my cover needs (the
argmaxCellOn pivot cells per node = the branching). Until then: stay on fork-independent value-side.

## ChainDimSplit API STUDIED (g157) — the rebase is NOT a mechanical swap; the taxonomy changes
Read crux2's banked ChainDimSplit (GeneralR1Recursion.lean @route-m-atlas). Three findings reshape the rebase:
1. ChainDimSplit M = a SINGLE one-step width split {drop, red, hsum : drop+red=M, hdrops : 0<Σdrop}. NOT a
   branch family, NOT iterated. L is FIXED (it reduces WIDTHS M→red, never depth). Termination = ΣM drops by
   Σdrop≥1. So my old L-dropping C2/C4 taxonomy does NOT map — crux2's recursion is pure ΣM-width-reduction.
2. ChainDimSplit is only ever CONSUMED in GeneralR1Recursion (schur_straighten_of_data / _squeeze /
   rlctAtOn_reduced_transport all TAKE an (S : ChainDimSplit M)); it is NEVER CONSTRUCTED there. So the
   rank-pattern dispatcher (WHICH split at each node = my old classify) is UNPROVIDED — still the producer's
   (my) job. The rebase makes my recursion PRODUCE ChainDimSplits (consume the carrier type) rather than my
   own RouteState; it does NOT hand me a banked recursion.
3. NO banked WF recursion over iterated ChainDimSplit exists. I build the fix myself: recurse M → S.red via a
   per-node ChainDimSplit, terminating on ΣM (hdrops ⟹ ΣS.red < ΣM), base at L=1 / red≡0 (dlnLoss_one_layer_deepest).
SHARPENED QUESTION to crux2 (supersedes Q1/Q2): does crux2 CONSTRUCT the per-node ChainDimSplit (the
rank-pattern → split dispatcher) or do I? If I do, the rebase = (i) swap my RouteState carrier for
(M, ChainDimSplit M); (ii) keep my pivot-branch Finset + the ⨅-min on top (branching is mine — ChainDimSplit
is single-path); (iii) my recursion produces, at each node, a Finset of child ChainDimSplits (one per pivot
cell) + folds MonoData via appendDivisor; (iv) terminate on ΣM. The carrier becomes (M, ChainDimSplit M) not
RouteState, but the RECURSION + BRANCHING + CONSTRUCTION are still mine. The "rebase" narrows to: use crux2's
split TYPE + its transport lemmas, not a fresh state machine — value/cover layers unchanged.

## REBASE FOUNDATION BANKED (g158, @origin/fm3/routem 55db82d) — RouteMRecursion.lean
The construction-agnostic recursion driver, rebased onto ChainDimSplit (replaces the dead RouteState/
routeMeasure/routeRel_wf). New file RouteMRecursion.lean (imports GeneralR1Recursion for ChainDimSplit +
RouteMState for MonoData; NO RouteMBridge/RouteMAtlas — single-writer-safe; green, clean-three):
- `chainWidthSum M := Σ M` — the termination measure.
- `ChainDimSplit.redM_widthSum_lt` : Σ S.red < Σ M (from hsum+hdrops; extracted from crux2's inlined proof).
- `chainRel N M := chainWidthSum N < chainWidthSum M` + `chainRel_wf` (InvImage of < on ℕ) — the WF carrier
  for the iterated Route-M WellFounded.fix.
- `ChainDimSplit.redM_chainRel` : any split descends along chainRel (the recursive-call descent proof).
These hold WHOEVER constructs the per-node split — the recursion skeleton stands. STILL GATED on crux2's
"who builds the per-node ChainDimSplit" reply: the WellFounded.fix BODY (the per-node step: produce the
pivot-cell Finset + child splits + fold MonoData + layer the cover) needs the split-construction interface.
NOT building the fix body until the answer lands (avoids baking a wrong split-construction shape).
NEXT (when crux2 replies): the fix body over chainRel_wf → NodeChartFamily; then the cover-branching
(g5_pivotNode split per node) + wire isCover/isValue → RouteMAtlas.

## SEAM FULLY RESOLVED (crux2 #66) + FIX-BODY SKELETON ROUTE-CHECKED (g160)
crux2 #66 answer: **fm3 CONSTRUCTS the dispatcher.** ChainDimSplit = the consumed minimal width-only
carrier (never constructed in GeneralR1Recursion); the pivot-cell coord-center lives in the paired
IsSchurStraightenSqueeze datum (field 3, COORD-CENTER), NOT in ChainDimSplit. My termination lemma
redM_widthSum_lt = crux2's proposed sum_red_lt (don't double-add). CONSUMER RECIPE (3 transport pieces
my recursion folds per node): schur_straighten_squeeze_of_data (nReg/2 descent, consumes my squeeze datum)
▸ rlctAtOn_reduced_transport (G²→dlnLoss S.red 0 at redZero) ▸ recurse on S.red ▸ dlnLoss_one_layer_deepest
(L=1 leaf).

FIX-BODY SKELETON — ROUTE-CHECKED GREEN (RouteMRecursion.lean, UNCOMMITTED, single sorry = routeStep):
- NodeChartFamily M {ι : Type, fintype, data : ι → MonoData} (Type 1, carries the Type field).
- RouteStep M : Type 1 := leaf (md) | branch (cells : Type) (cellsFin) (split : cells → ChainDimSplit M)
  (codim : cells → ℕ). The dispatcher's output. [Type 1 needed — the Type-valued cells field.]
- routeStep M : RouteStep M := sorry  ← THE substantive dispatcher (rank-pattern → leaf|branch).
- routeAtlas := WellFounded.fix chainRel_wf (leaf↦PUnit chart with md; branch↦Σ over cells of
  rec (split c).red [(split c).redM_chainRel] + ((child).data).appendDivisor (codim c)). Fintype derives.
- routeMIota/Fintype-instance/routeD/routeK/routeH extraction. ALL type-checks around the one sorry.
RouteMTree.lean (old parallel-RouteState stub) DELETED (untracked, superseded).

THE OPEN CORE = routeStep (the rank-pattern dispatcher). FINDING (g160): NO banked construction precedent —
even the (2,2,2) case (Case222Resolution.lean) is hand-built concrete coordinate maps (step1A=pivotBlowupOn
{0,1,2,3} 0, etc.) over Fin 8/Fin 7, NOT a ChainDimSplit instance. So routeStep is from-scratch combinatorial
work: given M, decide leaf-vs-branch + (for branch) the Finset of pivot cells + each cell's (drop,red) split
+ codim, from the rank pattern (Adm cone / pivotBlowupOn argmaxCellOn structure). This is design-space
combinatorics — pp2's lane. CANNOT commit the fix-body until routeStep is filled (sorry-gate). The skeleton
green VALIDATES the rebase shape end-to-end; routeStep is the substantial remaining grind (likely needs a
pp2 split-construction cert: rank-pattern → (drop,red) per node, generalizing the (2,2,2) hand-build).

## CRITICAL SPECIFY FINDING (g161, Codex xhigh routeStep-type-{prompt,answer}.md) — the VACUITY TRAP
The bare `RouteStep.branch (split) (codim)` is TOO WEAK: it gives a SYNTACTIC recursion, not a mathematical
resolution. A routeStep returning ARBITRARY splits TYPE-CHECKS and routeAtlas produces SOME (d,k,h) — but
DISCONNECTED from dlnLoss M 0. The value identity rlctAtOn(dlnLoss M 0) 0 = ⨅ monomialThreshold would then
be UNPROVABLE (the (d,k,h) isn't tied to the loss). Codex CONFIRMS (decisive): filling routeStep with
arbitrary splits is STRICTLY WORSE than the sorry — it manufactures a misleading "resolution" object that
lets downstream prove a false-flavoured identity. THE GUARD: never use routeAtlas M as a resolution unless
paired with a correctness proof built from CERTIFIED steps.
THE FIX (Codex, my SPECIFY corrected): RouteStep.branch must carry (or a ValidRouteStep M predicate must
assert) the per-cell TRANSPORT DATUM — the IsSchurStraightenSqueeze-existence that PROVES each split
factorises the loss (core ∘ φ = unit·(Σx² + dlnLoss S.red 0)). Without it the split is meaningless.
SEPARABILITY (Codex): dispatcher and identity ARE separable AFTER enriching — the clean architecture is
  routeStep : M → RouteStep M        (raw plumbing — termination only)
  ValidRouteStep M (routeStep M)     (the per-cell squeeze/reduced/cover certificates)
then a GENERIC FOLD theorem `routeAtlas_correct_given_valid` : (every branch certified) ⟹ rlctAtOn = ⨅
monomialThreshold, by well-founded induction matching routeAtlas. The dispatcher's REAL obligation is
"construct cells + decreasing splits + the per-cell transport datum", NOT "choose smaller reds".
MY NEXT (the formaliser's lane, INDEPENDENT of pp2's split-construction): build ValidRouteStep + the
generic fold theorem (Codex's minimal-honest-step items 1-2) — the GUARDRAIL + the target shape pp2's #67/#68
designs against ("get target-shape from fm3 first"). pp2 designs the rank-pattern → certified-RouteStep
recipe (#68); I provide the certified type + prove the fold; pp2's construction populates it.

## SCOPING DECISION (g162) — co-design the ValidRouteStep fields with pp2's #68, don't build blind
The ValidRouteStep certificate must carry, per branch cell, crux2's schur_straighten_squeeze_of_data
consumed data: nReg, a reduced ambient Y (+ PseudoMetricSpace/MeasureSpace/ProperSpace/BorelSpace/Zero
instances), flatCore, G, redEmbed (≃ₜ Params S.red), c₁ c₂, the IsSchurStraightenSqueeze datum, the
node-loss-identification (flatCore = the node's dlnLoss in blow-up coords), and the cover fact. This is a
HEAVY dependent structure (the Y/instance/universe bundling — same friction as RouteStep : Type 1). The
EXACT field list depends on pp2's #68 construction (designing it blind = the very wrong-type iteration the
vacuity-trap find just caught — "state the suspect hypothesis as a known unknown, resolve before proving";
the certificate's field list IS that hypothesis, #68 is its resolution-in-flight). So: HOLD the certificate
construction for #68; co-design the fields once pp2's recipe lands. SENT pp2 the target shape (the consumed
data + the additive-vs-min reconciliation the 3 correctness args must satisfy).
BANKED THIS SESSION (all green, @origin/fm3/routem aeca9a3): hMid all-s (0cedc7e); value-side foldDivisors
achiever+threshold_ge (fd4a622); rebase foundation chainWidthSum/redM_widthSum_lt/chainRel_wf/redM_chainRel
(55db82d). UNCOMMITTED route-check artifact: the recursion skeleton (NodeChartFamily/RouteStep/routeAtlas/
extraction, single routeStep sorry) — validates the rebase shape; RouteStep type PROVISIONAL (→ ValidRouteStep
once #68 co-design lands). The recursion DRIVER stands; the dispatcher + certificate are the #68-gated grind.

## CONSISTENCY CONTRACT BANKED (g163, @bef5ba5) — controller's critical item (iii), machine-checked
The value-side ⟹ IsResolutionAtlas bridge — pp2's dispatcher leaf-monomials AGREE with my foldDivisors
achiever BY CONSTRUCTION, no separate consistency proof. RouteMState.lean, green, clean-three+monomial_rlct:
- `foldFamily_threshold_ge` (ι codimsOf m₀ ...) : (∀ i, ∀ c∈codimsOf i, m₀≤c) ⟹ ∀ i, ½·m₀ ≤
  monomialThreshold(foldDivisors (codimsOf i)). [crux2 IsResolutionAtlas.threshold_ge, C≥]
- `foldFamily_achiever` (ι codimsOf m₀ i₀ ...) : (minimiser i₀: ∀ c∈codimsOf i₀, m₀≤c ∧ m₀∈codimsOf i₀) ⟹
  ∃ i, monomialThreshold(foldDivisors (codimsOf i)) = ½·m₀. [crux2 IsResolutionAtlas.achiever, C=∃]
Stated over an ABSTRACT leaf family (ι, codimsOf) — branch-version-independent (my branch's
ResolutionAtlas.lean carries the STALE stratum/threshold_eq form; crux2's route-m-atlas has the
threshold_ge/achiever form; this bridge targets the latter via the two facts directly, not the struct).
THE CONTRACT for pp2's #68 (m₀ = (Adm M).inf' Mval = the min codim; lambdaCore = ½·m₀): design the
dispatcher's per-leaf codims so (a) ∀ path, ∀ pivot codim ≥ m₀ (no undershoot); (b) the min-Mval path's
binding pivot codim = m₀. Then (a)+(b) ⟹ IsResolutionAtlas ⟹ ⨅ monomialThreshold = lambdaCore. (2,2,2):
m₀=3 (codim-3 rank-1 incidence), binding path → (1,2) ratio 3/2 = lambdaCore; others ≥3. SENT pp2.
=== MEANWHILE-WORK (controller i/ii/iii) DONE: interface target shape (i) + consumer recipe (ii) sent;
consistency contract (iii) machine-checked + banked. The dispatcher itself = pp2 #68 → I transcribe. ===
