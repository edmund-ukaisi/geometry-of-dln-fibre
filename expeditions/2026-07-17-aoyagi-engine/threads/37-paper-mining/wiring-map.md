# Thread 37 — paper-mining wiring map (long-range scout)

Scout `paper-mining`, 2026-07-21. Charge (team-lead): comb Aoyagi 2023 (+ `aoyagi-2023-worked.tex`)
against the 8-leaf monument skeleton in BOTH directions (paper→leaves, code→paper); find the REMAINING
instances where the paper already resolves a fork the wave is fighting, BEFORE the seats fight them.

**Method.** All formulas verified against the PAGE IMAGES of
`paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`
(PDF page index = printed page number; confirmed). Mountain pp.14–22 + Lemmas 3–5 pp.24–26 read this
pass. Cross-checked against the reified leaves (`Core/Aoyagi/PrincipalInv.lean`,
`DLN/Aoyagi/MonumentAtlas.lean`), the thread-33/34/35/36 certificates, and `verify-owed-math-audit.md`.

Entry format: **[paper site]** → *content (one sentence)* → **[status]** → **[wiring point]** → **[action]**.
Ranked by load-bearing-ness for the CURRENT wave (L4 first). Known compass/`worked.tex` defects
(Def-3, Lemma-1 direction, T-profile totality T-F, Case-2 raw-width T-E, realization gap, per-step
principality split) are NOT re-flagged — those are settled. Quarry = NEW finds.

**COVERAGE (sweep COMPLETE).** Page images read: pp.14–26 (Thm 4/Def 4, the full inductive statement,
Case 1(1)/1(2), Case 2, the terminal compression + M_{s,k} + boxed rule, p.23 completing-the-square,
Lemmas 3–5). Certificates read: thread-33 (shear-pin), 34 (case1-invariant), 35 (cover-cert), 36
(leaf-fidelity). `verify-owed-math-audit.md` + compass ledger cross-checked. Decorrelated Codex consult
(`codex/delta-answer.md`) run on the sharpest question (the δ-law) — independently confirmed δ=[J=0].

**BASELINE REFRESH (2026-07-21, post-merge tip `ae4067369`; folded into the entries below).** The
controller+elder adjudication landed while this swept: (S1) the step atom is now `blockBlowupMap`
(block-center + spectators), full-ambient `blowupMap` retired; (S2) = A1, the δ=[J=0] fix, now an
`EdgeSpec` field; (S3) `StepInv` carries deepest-point vanishing; L3/L4 are now **EDGE-INDEXED over the
actual `buildTree`** (not ∀-state — the ∀-state form kept admitting sharper refutations; the paper's
Cases are steps of THE construction, not universal facts), leaves move DLN-side; `FoldProduced`'s tie
is now `(bindingAxes bexp).card = numDiv`. CONSEQUENCE for this map: the paper's traversal order + the
per-case (S,J,t̃) transition bookkeeping (pp.15–20) is now **DIRECTLY load-bearing** as the edge-data
source the fold consumes — items B1/B3/B4 are upgraded from "brief fodder" to "edge-spec source".

---

## (a) FINDS THAT COULD CHANGE A REIFIED STATEMENT — stop-on-suspect

### A1. ⟨THE WALL⟩ L4 `Case1Preservation` — the child-dominant δ-law is mis-indexed. **[ADJUDICATED CONFIRMED → FIXED: `EdgeSpec` δ=[J=0], merged `ae4067369`]**
> STATUS UPDATE: reported to `main` (2× msgs); the elder's comb converged on it independently (same
> pp.16/17/20 reading, same [J=0]-vs-branch diagnosis) and went further to S1 (the step-map shape). The
> decorrelated Codex consult (`codex/delta-answer.md`) derived δ=[J=0] from scratch and exhibited a
> concrete reachable witness: existing coords x,y with t̃(x)=1,t̃(y)=2 give (b₁,b₂,b₃)=(1,x,xy); at J=0 a
> length-1 merge with x → (x,x,xy) [(1(1),J=0): true δ=1, hardcode δ=0, WRONG]; advancing to J=1 a
> length-1 split with fresh z → (x,zx,zxy) [(1(2),J=1): true δ=0, hardcode δ=1, WRONG] — the SAME
> advancing run hits both erroneous states. Fix banked: δ supplied by the fold from `ConState.cleared`
> as an `EdgeSpec` field; branch re-pointed to pivot-kind/resid-shape (one-shared-center-two-distinct-
> pivots), 1(1) a genuine `blockBlowupMap` at the old u_{s,k}. Kept below as the record of the find.
- **[paper: pp.16–17 (Case 1(1)/1(2)), p.20 (Case 2); + p.15 b_i recursion; worked.tex:598–601,612–627]**
- *The dominant generator is b₁ = ∏_{t̃_{s,k}=0} u (the smallest in the chain b₁|…|b_M, what `StepInv`
  factors out). Across a Case-1 step with pivot u_p, b₁ picks up u_p (δ=1) iff the pivot's newly-set
  t̃ = J equals 0, i.e. iff **J=0** — and this holds for BOTH sub-cases 1(1) and 1(2) (and Case 2):
  1(1) multiplies only the run b_{J+1}…b_{J+J₁} (contains b₁ iff J=0); 1(2)/Case-2 multiply
  b_{J+1}…b_{M(S)} (contain b₁ iff J=0). So δ = [J=0], state-dependent, NOT sub-case-dependent.*
- **[status: REIFIED-CONTRADICTS-PAPER]** The Lean CODE (`PrincipalInv.lean:192`) hardcodes
  `b' u = (u p)^(if branch then 0 else 1) * b(σ …)` = δ=[branch=1(2)]. Three independent sources say
  δ=[J=0]: the page images (above), the file's OWN docstring line 184 ("δ = [J=0] ∈ {0,1}"), and the
  thread-34 certificate line 16 ("b'₁ = u^δ·φ*b₁ where δ = [J=0]"). Only the code disagrees — a
  regression introduced by rev-leaves "FIX 3".
- **[wiring: `DLNFibre.Core.Aoyagi.Case1Preservation` (PrincipalInv.lean:177–194) → `case1_preserves_stepInv` (L4) → folded by L5/L8]**
- **[action: SEAT-L4 brief — RE-STATE before proving.]** The `∀ branch` fork is right (1(1)/1(2) are two
  charts of one blow-up, both needed for the cover) but the branches must be distinguished by the
  RESIDUAL SHAPE (merge keeps/append vs split clears a pivot: `nR'` differs), NOT by δ. δ must be a
  J=0 indicator threaded through the interior state (the state carries no J today — that absence is why
  the seat used `branch` as a δ-proxy). CAUTION: simply setting δ=[J=0] for both branches without the
  residual-shape distinction would REOPEN the branch-collapse the thread-36 reviewer killed (a single
  witness discharging both) — the residual-shape fork must carry that load instead. Why it bites: at
  (J≥1, 1(2)) — the normal J-advancing step — code demands δ=1 but truth is δ=0 ⟹ FALSE divisibility
  ⟹ L4 unprovable-as-stated; at (J=0, 1(1)) code demands δ=0, truth δ=1 ⟹ provable but WEAKER, L8's
  `jac+1` exponent drops a u_p power ⟹ wrong M_{s,k}. Both states reachable.

*(No other reified statement contradicts the paper. terminal_bezout, L1, L3's existential-b', L5/L6/L7
match; L7/L8's free-atlas falsity is already caught + HELD by thread-36 round-2, see D5.)*

---

## (b) FINDS THAT FEED PROOF PLAYBOOKS — brief fodder for the wave seats

### B1. L4 exact-division mechanism — the Q, P matrices + the key identity are PRINTED verbatim.
- **[paper: p.17 (Q + D_J″), p.18 & p.21 (P + D_J‴ + the assembled chain); worked.tex:614–629]**
- *Case 1(2)/Case 2 fold: unipotent Q = [[1,−d′_{J+1,·}],[0,E]] clears the pivot ROW of the d′-block
  (D_J″ = D_J′·Q, top row → e₁); the next-layer factor absorbs it, C_J′^(S+1) = Q⁻¹C_J^(S+1) (ideal-
  preserving). Then regular P = [[1,0,…],[−(b′_{J+2}/b′_{J+1})d″_{J+2,J+1}, 1,…],…] clears the pivot
  COLUMN, giving the compression D_J‴ = [[1,O],[O,D_{J+1}]] and the exact identity
  **P·diag(b_{J+1},…,b_{M(S)})·D_J·C = u_{S,J+1}·diag(b′_{J+1},…,b′_{M(S)})·D_J‴·C′** (p.21).*
- **[status: TRANSCRIBED in docstring prose (PrincipalInv.lean:70–73, 133–135) but ABSENT as a Lean lemma]**
- **[wiring: the algebraic heart of `case1_preserves_stepInv` (L4); the q′-regeneration]**
- **[action: SEAT-L4 brief.]** P = diag(b′)·(unipotent col-clear)·diag(b′)⁻¹ IS the `Q̂` cofactor the
  docstring names; the `−(b′/b′)·d″` entries are image-verified verbatim. The child quotients
  `q′_ij = (φ*q_ij)/u_p^δ` are EXACT polynomial division (worked.tex/thread-34), no localization. Q
  enters the chart map g (absorbed via C^(S+1)); P/Q₁-type left-recombinations stay as the
  `RegionRepresents` cofactors (shear-pin thread-33 §1: the discriminator is invertibility of the
  induced source map — Schur/Q₂ det-1 → into g; Q₁ det-0 projection → forced cofactor).

### B2. L6 Jacobian ledger — each exceptional u carries power exactly M_{s,k}−1; residual carry 0.
- **[paper: p.15 the `∏∏∏ dc_ij = (∏_{s,k} u_{s,k}^{M_{s,k}−1} du_{s,k})·(∏ dd_ij)(∏ dc_ij)` display; worked.tex:589–607]**
- *The change-of-variables determinant is a pure blow-up monomial ∏ u_{s,k}^{M_{s,k}−1}; residual d_ij
  and unblown c_ij carry power 0 (plain differentials) ⟹ in the boxed rule k_j≡1 on binding axes,
  h_j = M_{s,k}−1, unit ≡ 1.*
- **[status: TRANSCRIBED (image-confirmed this pass; also thread-33 shear-pin cert)]**
- **[wiring: `GeoStep.hσ_jac`/`jexp`, `leafPath_chartGeometry` (L6) `chart.jac`]**
- **[action: brief fodder.]** The shear-pin structural argument (thread-33 §3) is paper-consistent:
  exceptional coords are never touched by later shears (the shears mix only residual/next-layer coords),
  and the one non-unipotent transform (Thm 3's A₁⁻¹, det = (det A₁)^−#) is the r>0 peel — trivial at
  the r=0 deepest point where the whole resolution lives (E_J pivots = identity). So `unit ≡ 1` holds
  ∀ L/width/corank. L6 states g = (unipotent shears)∘(monomial blow-ups), NOT a monomial map.
- **[S1 corroboration — NEW, confirms `blockBlowupMap` vs full-ambient against the paper.]** The
  exceptional Jacobian exponent h = M_{s,k}−1 is exactly (block-center codimension)−1, NOT an
  ambient-dimension count: Case 2 blows up the full residual block {d_ij=0, i,j>J} of codim
  (M(S)−J)(M^(S+1)−J), and the printed exponent is M′_{S,J+1}=(M(S)−J)(M^(S+1)−J) = that codim (p.20);
  Case 1(1)'s printed INCREMENT M′_{s,k}−M_{s,k}=J₁(M^(S+1)−J) (p.16) equals the added sub-block codim
  J₁×(M^(S+1)−J). So the block-center codimension arithmetic reproduces her printed increments — the
  full-ambient `blowupMap` (retired S1) would give the wrong exponent. Confirms the merged
  `blockBlowupMap` atom is the faithful shape; feeds `GeoStep.jexp`/`hσ_jac` under the new baseline.

### B3. L5 fold — the exact roll-over rule (J increments to M(S+1), then S) + the root state.
- **[paper: p.19 "If J+1 ≤ M(S+1) then J increases by one; if J+1 > M(S+1) then S increases by one";
   p.14 M(S)=min{M^(s):1≤s≤S}; p.15 "obvious for S=0, J=0"; p.14 first-step t^(s)_{S,k}=M^(s+1), M_{s,k}=0]**
- *The recursion advances J from 0 to M(S+1)=min{M(S),M^(S+1)} within a layer, then increments S;
   terminates at S=L+1. Root: S=J=0, D₀=∏C, b₀=1.*
- **[status: TRANSCRIBED (image-confirmed) — the running-min M(S) governs exponent accumulation (compass T-E)]**
- **[wiring: `leaf_stepInv_of_path` (L5) fold order + well-foundedness; the root `StepInv F id 1 coreGen` (root_probe.lean)]**
- **[action: EDGE-SPEC SOURCE for the edge-indexed L3/L4/L5 (upgraded from brief fodder).]** Under the
   merged edge-indexed baseline, the fold generates each `EdgeSpec` from the (S,J,t̃) transition of the
   corresponding `buildTree` edge; THIS roll-over rule (p.19) + the per-case t̃ assignments (Case 1(1)
   sets t̃=J on the reused pivot p.16; Case 1(2)/Case 2 set t̃_{S,J+1}=J on the fresh pivot pp.17/20) ARE
   that transition bookkeeping — the paper is the direct source for the edge data. Termination rides the
   FINITE branch (J bounded by M(S+1), S by L+1), NOT a residual measure. BOUNDARY (p.19): when
   J+1 > M(S+1) the residual collapses to D_J‴ = (1,0,…,0) or its TRANSPOSE — the roll-over can
   transpose a single-row/col residual; the fold must handle the residual-becomes-a-vector edge.

### B4. L7 routing — the pivot-selection rule (argmin over the T-order) + coordinate-block centers.
- **[paper: p.15 "Fix u_{s,k} such that t̃_{s,k}=J+J₁ and T_{s,k} ≤ T_{s′,k′}"; p.16/p.19 blow-up
   submanifolds {d_ij=0, u_{s,k}=0} / {d_ij=0}; Def 4 p.14 the componentwise partial order]**
- *The pivot at each step is chosen by the T-order (a minimal T among the equal-run coordinates); the
   blow-up centers are COORDINATE BLOCKS (a d-subblock and/or an exceptional coordinate).*
- **[status: TRANSCRIBED (image-confirmed); cover cert thread-35 mines the argmax lift already]**
- **[wiring: `leafPath_compactCover` (L7) argmax routing; `CenterCoordAligned` (the center is a coord block)]**
- **[action: brief fodder for SEAT-L7.]** The center-is-a-coordinate-block property is the paper's own
   (centers are {d-block=0, u=0}); it discharges the "next center is a coordinate block in the sheared
   coords" INHERITED condition the cover cert (thread-35 gap-2) flags as the sharpest Lean risk. NOTE:
   a real blow-up of a codim-c center has c charts; the paper groups them into the 1(1)/1(2)/Case-2
   representatives — L7's cover must union over ALL charts of each blow-up, matched to the `∀ branch`.

### B5. L8 exponent match — the terminal M_{s,k} = Mval(t) formula + the t̃=0 binding restriction.
- **[paper: p.22 `M_{s,k}=(M^(1)−t^(1))(M^(2)−t^(1)) + Σ_{j=2}^L (t^(j−1)−t^(j))(M^(j+1)−t^(j))` and the
   boxed `½ min{M_{s,k}: t̃_{s,k}=0}`; worked.tex:668–677]**
- *Each terminal divisor's accumulated exponent M_{s,k} equals the codimension Mval(t) of its branch's
   rank-profile; only t̃=0 (terminal) divisors bind the min.*
- **[status: TRANSCRIBED (image-confirmed); = Object D's divExp/minAdm, banked]**
- **[wiring: `leafPath_realizesExponents` (L8) — `jac a + 1 ∈ terminalExponents`, `bindingAxes`, `divExp = minAdm`]**
- **[action: brief fodder for SEAT-L8.]** The `jac + 1` = M_{s,k} identity is the L8 clause-(i) content;
   the min-attainment (some leaf achieves minAdm) is clause (ii). Both are the paper's p.22 read-off.

### B6. terminal_bezout — the terminal compression makes the dominant a bare generator.
- **[paper: p.22 `⟨∏C^(s)⟩ = ⟨diag(b_1,…,b_{M(L+1)})⟩` at S=L+1; worked.tex:575–577]**
- *At the terminal the ideal is generated by the bare diagonal monomials b_1,…,b_M; the dominant b₁ IS
   one generator (F₁∘g = b₁·1), so Bézout b₁ = 1·(F₁∘g) is immediate (the cleared-pivot `unit`=1≠0).*
- **[status: TRANSCRIBED (compression image-confirmed); the Bézout-inversion FRAMING is ours (see D3)]**
- **[wiring: `terminal_bezout` (`TerminalBezout`), consumed by L5 at each leaf]**
- **[action: brief fodder.]** Confirms terminal_bezout is sound + non-vacuous — principality is born
   exactly at S=L+1 (worked.tex:659 "terminal-chart invariant"), matching the thread-34 split.

---

## (c) UNMINED MACHINERY FOR LATER — Object E, Watanabe-upper, Lemma 2

### C1. cited_watanabe_upper_ax — the UPPER bound is the EASY half of the same resolution.
- **[paper: p.22 boxed rule + min-attainment; the ½·codim ≤/≥ split]**
- *rlct = ½·min_charts min_j (h_j+1)/(2k_j). The UPPER bound rlct ≤ ½·codim needs ONE min-attaining
   chart (the leaf where M_{s,k}=minAdm); the LOWER bound needs ALL charts ≥ ½·min. Both come from the
   SAME monument — the min-attaining leaf (L8 clause ii / `hattain`) gives the upper bound; the
   all-charts bound (L8 clause i / `hlb` + the min-over-charts CoV) gives the lower.*
- **[status: ABSENT as a proof (cited axiom); the min-attainment half is what L8-(ii) supplies]**
- **[wiring: `cited_watanabe_upper_ax` (AoyagiCited.lean:57) — proof-target candidate]**
- **[action: later waypoint.]** Both cites (`cited_watanabe_upper_ax`, `cited_aoyagi_lower_ax`) are
   derivable from the monument + the min-over-charts CoV. The upper bound is the cheaper leg (single
   chart's divergence ≥ the min ratio, i.e. the origin-blow-up divergence + R0 that the charter names);
   worth a follow-up waypoint to prove & delete it alongside the lower-bound kill-target.

### C2. Object E (order θ) — Lemmas 3/4/5 give the full combinatorial θ, incl. an explicit construction.
- **[paper: Lemma 3 p.24 (within-set quadratic min A(a−1)=A(a)=aℓ(ℓ−a), tie at b=a−1,a); Lemma 4 p.25
   (binding branch ⟺ envelope T̃≤T_{sk}≤T̃′ AND increment ∈ {M−1,M}); Lemma 5 p.25–26 (θ=a(ℓ−a)+1 via
   the union count |{H:H̃_j≤H≤H̃′_j}| + the explicit t^(S)_{s,k} construction attaining it, eqs (1),(2))]**
- *θ counts the minimising terminal branch-vectors; the a−1/a tie of Lemma 3 is what makes θ>1.*
- **[status: worked.tex-TRANSCRIBED + image-verified; Lean has `boxedOrder`/`aoyagiPoleOrder`/`ThetaOrderDistinction`; the aggregate identity + the analytic pole-order id are ABSENT]**
- **[wiring: Object E (`Core.Aoyagi.Order`, `DLN.Aoyagi.ThetaOrderDistinction`), deferred per charter §1-E]**
- **[action: keep named/reachable.]** The p.26 explicit construction (eqs (1),(2)) is the constructive
   LOWER bound for θ — the paper attains a(ℓ−a)+1 by an explicit local coordinate. Feeds the combinatorial
   `boxedOrder`-aggregate = a(ℓ−a)+1 identity (NAMED-unbuilt). The analytic "count = pole multiplicity"
   needs Mathlib meromorphic continuation (monument, off-path). Do not build now; do not box out.

### C3. Lemma 2 (block elimination) + Theorem 3 (regular peel) — the r>0 machinery, off the kill-path.
- **[paper: Lemma 2 p.13 (Schur C₄=−A₃A₁⁻¹A₂+A₄, Q₁,Q₂ unipotent); Thm 3 pp.11–13 (peel the regular
   r×r block); Thm 4 p.14 (deepest-point domination, method of [22]=Aoyagi 2013); worked.tex:400–553]**
- *Block-elimination peels the rank-r regular part, splitting rlct into a Morse prefactor
   ½(−r²+r(H^(1)+H^(L+1))) + the core rlct; Thm 4 collapses the global inf to the origin.*
- **[status: TRANSCRIBED — Lemma 2 = `RankNormalForm`/`left/right_normal_form_of_*_vanish`; Thm 4's
   instance = `GlobalHomog.rlctGlobal_eq_rlctAt_zero_of_homogeneous`; general-r Thm 3 open on Skeleton]**
- **[wiring: the r=0 corollary path (`coreReduction`, landed); general-r = O3, deferred]**
- **[action: none for the wave.]** The r=0 kill-path needs neither; general-r Thm 2 is the single
   largest additional build (O3), shares no dependency with the kill-path. Named boundary, not a gap.

### C4. O5 (the printed-form / clean q²−m² identity) — the paper HAS a general-L proof: pp.23–24 completing-the-square. **[NEW — elder-flagged, verified independently]**
- **[paper: p.23 the M_{s,k} completing-the-square; p.24 the 2λ_O assembly + Lemma 3; worked.tex:876–910]**
- *p.23 rewrites the terminal branch exponent as
   `M_{s,k} = ½ Σ_{j=1}^{ℓ-1} (F_j − P̄)² + ½ (Σ_{j=1}^{ℓ-1} F_j − ((ℓ-1)/ℓ)·Σ M^(S_j))²`, where P̄ =
   (Σ_{k=1}^{ℓ+1} M^(S_k))/ℓ is the balanced mean — a genuine sum of squared deviations. Minimising over
   the branch (the F_j) is then the balanced-split minimisation of Lemma 3 (p.24, min A(b)=aℓ(ℓ−a)),
   yielding the printed Thm-2 closed form.*
- **[status: image-VERIFIED this pass (the SOS identity is explicit on p.23); currently O5 is DEFERRED and only exact-enumeration-verified (L≤6, `verify-def3-underspec.md` Check 4) — the (F-1) "still-owed theorem"]**
- **[wiring: O5 — the `cCodim = ½·Mval_min = clean q²−m² = printed Thm-2` identity ∀(L,M); `lambdaCore_eq_clean`]**
- **[action: later waypoint — the general-L proof is TRANSCRIBE-ABLE, not enumeration-bound.]** pp.23–24
   (completing-the-square → balanced-split min via Lemma 3) is the whole skeleton; it converts O5 from
   "verified by finite enumeration only" to "the paper proves it generally". A clean self-contained
   pen-and-paper + formalise unit if the operator wants the printed form on the record. Confirms the
   elder's read. NOT on the kill-path (the destination names C = the codimension = `cCodim`, proved);
   this is the downstream printed-form exposition.

---

## (d) PAPER-SILENT OBLIGATIONS — OURS to prove; the paper gives no lemma/guide here

### D1. The min-over-charts change-of-variables (`rlctAt_sumSqFam_eq_iInf_charts`, O1).
- *The paper CITES the boxed rule "min over charts U" (Hironaka) but never proves the joint integral
   realizes the min: the per-point subset-divisor min + compact finite subcover + area-formula
   subadditivity (≥) and the injective-CoV divergence transport (≤) are all OURS.* **[PAPER-SILENT]**
- **[wiring: `Core.Aoyagi.ProductResolution.rlctAt_sumSqFam_eq_iInf_charts` — the boxed equality itself]**
- **[action: the O1 build (scheduled). Heavy proof-engineering, not new math — knowing it is paper-silent prices it as OURS.]**

### D2. L7's compact cover as a Lean measure statement (empty escape).
- *The paper's blow-up "covers" is Hironaka-implicit; the explicit compact-box-in-SOURCE-coordinates
   + argmax routing + finite-depth bound inflation (`R·(1+R)^m`) + `ball ⊆ ⋃ images` is OUR construction
   (cover cert thread-35). The paper gives no compact domains and no cover proof.* **[PAPER-SILENT]**
- **[wiring: `leafPath_compactCover` (L7)]**
- **[action: SEAT-L7. Salvage the retired Engine's kernel-checked tree cover (PivotCover/GeoCoverSpec),
   generalise R=1→R-parametric, bridge to the `Chart`/`Resolution` record. The pathwise-coherence fold is the detail-at-scale burden.]**

### D3. terminal_bezout's Bézout INVERSION (unit⁻¹ continuity, region shrink to {unit≠0}).
- *The paper gives the ideal identity ⟨∏C⟩=⟨diag(b)⟩ but NO Bézout representation b=Σr_i(F_i∘g); the
   inversion (r_{i₀}=1/unit via `ContinuousOn.inv₀`, V′=V∩{unit≠0}) is OUR framing.* **[PAPER-SILENT on the form; content present via the bare diagonal generator]**
- **[wiring: `terminal_bezout`]**
- **[action: SEAT (terminal_bezout). The route is named in the docstring (ContinuousOn.inv₀); it is proof-engineering, paper-silent but strike-able.]**

### D4. a.e.-injectivity of each step map off the exceptional locus (`hσ_inj`/`CenterCoordAligned`).
- *The paper never discusses injectivity of g; `Set.InjOn σ (univ \ {jacWeight=0})` is OUR measure-
   theoretic requirement for the CoV.* **[PAPER-SILENT]**
- **[wiring: `GeoStep.hσ_inj`, `CenterCoordAligned` (L6/L7)]**
- **[action: brief note — birationality of shear∘blow-up (shears bijective, blow-ups injective off exceptional) is standard; paper-silent but strike-able.]**

### D5. L7/L8 atlas-provenance anchoring (already caught; NOT new — recorded for completeness).
- *L7/L8 quantify over a FREE `atlas : GeoAtlasData` with no field tying it to the fold/tree ⟹ FALSE as
   stated (degenerate-atlas + adversarial-jac refutations, thread-36 round-2). The paper's atlas IS the
   fold by construction; the Lean must encode the tie (provenance predicate / `FoldProduced`).*
- **[status: RESOLVED under the merged baseline — L3/L4 edge-indexed over `buildTree`; `FoldProduced`'s
   tie is now `(bindingAxes bexp).card = numDiv` (the earlier branch-length tie was unsatisfiable —
   merges birth no divisors)]**
- **[wiring: `leafPath_compactCover`/`leafPath_realizesExponents` — anchored to the fold/tree]**
- **[action: confirmed — A1's δ fix and this anchoring shared ONE root cause (the interior state carried
   too little provenance: no J, no fold-link); the edge-indexed baseline threads the recursion state +
   the fold anchor together, which is exactly the paper's own frame (see the cross-cut).]**

---

## CERTIFICATE — the edge-indexed EdgeSpec traversal gate for (3,3,4) (commissioned 2026-07-21)

**Battery:** `edgespec_traversal_334.py` (exact integer/`Fraction`, EXIT 0). **Verdict: the fold's
edge-indexed generator reproduces Aoyagi's (S,J,t̃) transition system for the coupled RRR core (3,3,4),
including the p.19 transpose boundary and the only-at-exhaustion guard. NO stop-on-suspect.**

**Decorrelation.** The simulator implements the recursion from my independent page-image reading
(pp.14–22); the dispatch rule is cross-read against `conOracle` (EngineConstruction.lean:2117) and the
outputs asserted against the paper's PRINTED formulas. Agreement of the two encodings on the printed
increments + the (3,3,4) headline is the gate.

**The (3,3,4) full transition table** (paper S = Lean layer+1; profile t=(t⁽¹⁾,t⁽²⁾), t̃=min):
the S=1 layer runs three Case-2 appends building divisors (0,0)/9, (1,1)/4, (2,2)/1; rollover fires at
J=3=M(S+1) (transpose boundary); at (S=2,J=0) a **Case-1(1) merge** bumps (1,1)/4 → **(1,0)/8 =
Mval(1,0)** with δ=[J=0]=1 — exactly the compass landmark "the (1,1)→(1,0) M=8 merge at paper S=2 =
Lean layer=1" (EngineConstruction.lean:85). minAdm=8, rlct_core=½·8=4. 5 leaves, 26 edges.

**Six assertion classes verified (all PASS, exact arithmetic):**
1. **MvalCoh** — every divisor's accumulated exponent = Mval(profile) (p.22 M_{s,k} formula), at every edge.
2. **Case-1(1) increment = J₁·(M^(S+1)−J)** (p.16) and **Case-2 exponent = (M(S)−J)(M^(S+1)−J)** (p.20);
   the bump exactly closes the Mval-gap of the tail-write.
3. **δ = [J=0], UNIFORM across sub-cases** (S2) — every non-rollover edge; both edges of a Case-1 node
   share δ (this is A1's fix, now positively verified on the traversal, not just argued).
4. **Rollover fires EXACTLY at J = M(S+1) = widthMinUpto(layer+1)** — the p.19 transpose boundary /
   only-at-exhaustion guard; verified at every rollover edge.
5. **Center codimension = block dims** (S1): Case-2 center = full (M(S)−J)×(M^(S+1)−J) block; Case-1
   center = J₁×(M^(S+1)−J) d-subblock + the u-hyperplane — matches `blockBlowupMap`, not full-ambient.
6. **Headline** — min over terminal t̃=0 divisors = minAdm (over the t_L=0 admissible lattice); rlct = ½·minAdm.
   Guards PASS: (2,2,2)→3/2, (2,1,2)→1, (2,2,2,2)→3/2, (3,3,2,2)→2, (2,2,3,2) [non-monotone T-E instance].

**Rule-by-rule correspondence to the fold** (`conOracle`): terminal at `L ≤ layer`; rollover at
`widthMinUpto(layer+1) ≤ cleared` (2119); Case-1 iff an occupied t̃-level lies in `(J, M(S))` with
`runLen = target − J = J₁` (2122–2143); else Case-2 (2146). Case-1 emits BOTH charts (merge `case11`
bumps `divExp[f] += runLen·resCols` + tail-writes; split `case12` appends `divExp[f]+runLen·resCols`,
inherited head + tail-write, advances J) (2055–2103); Case-2 appends `resRows·resCols`, `runMinWidth`
head + tail J (1965–1980). EdgeSpec `δ = [J=0]` uniform, `σ = sh ∘ blockBlowupMap center p`
(PrincipalInv.lean rung-c, 126–151).

**A CONFIRMING sub-find (not a suspect): the Case-2 head is the RUNNING-MIN, not the printed raw-width.**
The simulator first tripped MvalCoh at the non-monotone (2,1,2): profile (2,0) with Mval 4 ≠ divExp 2.
Cause: I had encoded the Case-2 profile head as `widthMinUpto M p = min(M[0..p])`, but the fold uses
`runMinWidth M p = min(M[0..p+1])` (EngineDefs.lean:147) — the RUNNING-MIN. With the running-min head the
profile is (1,0), Mval=2=divExp, and MvalCoh holds. This is precisely the T-E-defect resolution in force:
the fold deliberately does NOT reproduce the paper's printed p.20 raw-width head-reset `t^(i)=M^(i+1)`
(defective at non-monotone widths); the running-min head is T-E-immune and makes MvalCoh hold
UNCONDITIONALLY (verified at the non-monotone (2,1,2), (2,2,3,2), (3,3,2,2)). Fidelity point: the fold's
head choice is a documented, correct deviation from the printed label (compass T-E ledger), not a defect.

## Cross-cut observation (for the controller) — CONFIRMED by the merged baseline

A1 (the δ mis-index), D5 (free-atlas falsity), and arch-C's case-2-b′-law open note were the SAME root
cause surfacing three times: the reified interior state (`StepInv`/`Case1Preservation`/`GeoAtlasData`)
carried too little provenance — no recursion index J, no fold-link. The paper's state is (S,J) with a
fully determined b-ledger; every "which b picks up which pivot / which chart came from which branch"
question is answered by (S,J) + the b_i = ∏_{t̃<i} u closed form. The merged baseline (`ae4067369`)
adopted exactly this: edge-indexing L3/L4 over `buildTree` (the fold supplies edge specs from the (S,J,t̃)
transitions), `EdgeSpec` δ=[J=0] from `ConState.cleared`, and the `FoldProduced` `card = numDiv` tie —
all three symptoms dissolve into one frame. **This is the paper's shortcut the wave kept re-deriving: the
state is (S,J), the b-ledger is a function of it, and the Cases are edges of THE construction, not
universal facts.** The remaining paper-silent obligations (D1–D4) are the genuinely OUR-side proof-
engineering; the rest is transcription of pp.14–24 against the edge-indexed / block-center baseline.
