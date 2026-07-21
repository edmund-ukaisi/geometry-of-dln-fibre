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

---

## (a) FINDS THAT COULD CHANGE A REIFIED STATEMENT — stop-on-suspect (reported to `main` already)

### A1. ⟨THE WALL⟩ L4 `Case1Preservation` — the child-dominant δ-law is mis-indexed. **[SUSPECT, near-certain]**
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

### B3. L5 fold — the exact roll-over rule (J increments to M(S+1), then S) + the root state.
- **[paper: p.19 "If J+1 ≤ M(S+1) then J increases by one; if J+1 > M(S+1) then S increases by one";
   p.14 M(S)=min{M^(s):1≤s≤S}; p.15 "obvious for S=0, J=0"; p.14 first-step t^(s)_{S,k}=M^(s+1), M_{s,k}=0]**
- *The recursion advances J from 0 to M(S+1)=min{M(S),M^(S+1)} within a layer, then increments S;
   terminates at S=L+1. Root: S=J=0, D₀=∏C, b₀=1.*
- **[status: TRANSCRIBED (image-confirmed) — the running-min M(S) governs exponent accumulation (compass T-E)]**
- **[wiring: `leaf_stepInv_of_path` (L5) fold order + well-foundedness; the root `StepInv F id 1 coreGen` (root_probe.lean)]**
- **[action: brief fodder for SEAT-L5.]** Termination rides the FINITE branch (J bounded by M(S+1), S by
   L+1), NOT a residual measure — matches `StepInvChild`'s docstring. BOUNDARY (p.19): when
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
- **[status: KNOWN — thread-36 round-2, L7/L8 seats HELD on anchoring; dispatched to arch-C]**
- **[wiring: `leafPath_compactCover`/`leafPath_realizesExponents` — need an atlas-fold anchor]**
- **[action: none new — flagging that A1's δ fix and this anchoring both stem from the interior state
   carrying too little provenance (no J, no fold-link). Consider a single enriched state carrying J +
   the fold anchor to fix A1, D5, and the arch-C brief together.]**

---

## Cross-cut observation (for the controller)

A1 (the δ mis-index), D5 (free-atlas falsity), and arch-C's case-2-b′-law open note are the SAME root
cause surfacing three times: the reified interior state (`StepInv`/`Case1Preservation`/`GeoAtlasData`)
carries too little provenance — no recursion index J, no fold-link. The paper's state is (S,J) with a
fully determined b-ledger; every "which b picks up which pivot / which chart came from which branch"
question is answered by (S,J) + the b_i = ∏_{t̃<i} u closed form. Threading (S,J) — or at least a J=0
indicator + a fold anchor — through the interior state would fix A1 and D5 at once and price the fold
correctly. This is the paper's shortcut the wave keeps re-deriving: **the state is (S,J), and the
b-ledger is a function of it.**
