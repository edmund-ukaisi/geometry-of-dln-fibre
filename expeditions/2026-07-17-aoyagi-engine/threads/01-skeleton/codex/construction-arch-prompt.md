<task>
Lean 4 + Mathlib formalisation architecture review, before I build a multi-increment "construction tide."

CONTEXT. I am transcribing Aoyagi (2023) DLN preprint pp.14–22 — a resolution-of-singularities by
iterated blow-ups — into Lean. The banked CARRIER + BUNDLE already elaborate (sorry-free defs):

  structure StepData (M : Fin (L+1) → ℕ)  -- one blow-up node. Fields: layer S, cleared J, case
    (StepCase = case11|case12|case2), resRows resCols (residual block D_J dims), numDiv, numB,
    bExp : Fin numB → (Fin numDiv → ℕ) (monomial vector), bChain : Monotone bExp (divisibility chain),
    divExp divTilde : Fin numDiv → ℕ (per-divisor exponent M_{s,k} and clearing level t̃), numGen,
    support : Fin numGen → Finset (Fin numDiv)  (the divisor-sharing map — load-bearing at corank≥2).
  structure LeafData (M) -- terminal node: numDiv, divExp, divProfile : Fin numDiv → (Fin L → ℕ),
    numB, bExp, bChain : Monotone bExp, chartDom : Set (Params M).
  inductive ResolutionTree (M) | leaf (LeafData M) | branch (StepData M) (List (ResolutionTree M))
  -- read-offs: leaves, nodes, terminalExponents (all total).

  def CanonicalResolution (M) (t) : Prop :=
    IsFullMonomialization t                              -- ∀ leaf, ∀ k, divExp k = (Mval M (divProfile k)).toNat
    ∧ (∀ n ∈ nodes t, StepInvariant n)                  -- per-node Case recurrence + sharing footprint
    ∧ (∃ n charts, t = branch n charts ∧ n.layer=0 ∧ n.cleared=0)  -- branch-rooted base S=J=0
    ∧ ChartsCover M t                                    -- neighbourhood cover: ∃ U open, {frobSq=0}∩box ⊆ U ⊆ ⋃ chartDom
    ∧ (minAdm M ∈ terminalExponents t ∧ ∀ e ∈ terminalExponents t, minAdm M ≤ e)  -- exponent hooks

I have PROVED `∃ t, CanonicalResolution (![2,2,4]) t` sorry-free (a hand-built branch+leaf tree; divExp=Mval
by kernel decide; minAdm(2,2,4)=4 via the banked minAdmRec recursion; ChartsCover by chartDom=univ).

THE SPEC (Aoyagi pp.14–22, worked-reproduction). Double induction on (S,J), 0≤S≤L, 0≤J≤min(M(S),M(S+1)),
M(S)=min{M^(s):1≤s≤S}. Invariant: ⟨∏C⟩ = ⟨diag(b_1..b_{M(S)})·[E_J 0;0 D_J]·∏_{s>S+1}C⟩, D_J is
(M(S)−J)×(M(S+1)−J); b_i monomials in the exceptional u's, b_0=1, divisibility chain. At (S,J), read the
equal run of b_{J+1}..b_{M(S)}: Case 1 (partial run length J_1 < M(S)−J) blows up a sub-block, splitting
into 1(1) (d-block acquires an EXISTING exceptional factor u; exponent-merge, an inner recursion) and 1(2)
(a NEW pivot u_{S,J+1} introduced, advances J); Case 2 (full run) blows up the full residual, new-divisor
exponent (M(S)−J)(M(S+1)−J). Terminates at S=L+1 in the full diagonal (depth ≤ Σ_s M^(s+1)). Terminal
divisor exponents = Mval(rank-profile); rlct_core = ½·min. The BANKED value side: minAdm = (Adm M).inf' Mval
(RouteMLayerSplit), with minAdmRec the layer-peeling recursion (minAdmRec_eq_minAdm PROVED); deepest-point
domination `deepest_le_of_homogeneous_core` (homogeneity CoV, degree 2L). CONSTRAINTS: exact-steps-only
(any lossy factorization is FALSE at binding cells); the divisor-sharing `support` must not be flattened;
per cert-d3 the "per-blow-up LOCAL COVERING LEMMA" (standard affine charts U_i of each blow-up ↔ the stated
case children, support-preserving) is THE genuine new content, hardest at corank≥2. Coverage must NOT use
rlct=c* (circularity). A separate lane may soon require the chart SUBSTITUTION MAPS be explicit/recoverable
in the leaf/chart structures.

MY PLAN (5 rungs, each a committed green step): (1) recursion State type + step dispatch producing the
Case children + a proof the branch conditions EXHAUST all non-terminal states; (2) termination via the
depth measure; (3) per-case invariant preservation (footprint conjuncts first); (4) exponent hooks by
consuming minAdm/QIP (never rebuild); (5) coverage LAST (real chart maps + the local covering lemma).
</task>

<output_contract>
1. STATE DESIGN: the minimal Lean `State` type for the (S,J) double induction that (a) supports an
   EXHAUSTIVE, decidable branch dispatch into case11/case12/case2 + terminal, and (b) carries enough to
   later attach chart substitution maps. Name the fields; say what NOT to put in it. Flag any field whose
   omission would force a later restructure.
2. TERMINATION: the exact decreasing measure (and on which argument the well-founded recursion should
   descend) — Σ M^(s+1)? (S,J) lexicographic? depth? — and why it strictly decreases on EACH case
   including the 1(1) inner recursion (the exponent-merge that does NOT advance J).
3. RUNG ORDER: is my 1→5 order right, or does something (esp. the chart-map data requirement) force an
   earlier structural commitment? Give the corrected order if so.
4. WALLS: rank the top 3 places this construction will actually wall or thrash in Lean (not the paper
   math — the FORMALISATION), cheapest-diagnostic-first. Be concrete about corank≥2.
5. One thing in my plan that is WRONG or will cause a costly restructure, if any.
Keep to these 5 sections. Terse. This is architecture, not code — pseudocode only where a type signature
is load-bearing.
</output_contract>

<grounding_rules>
Distinguish what follows FROM the spec I gave vs. what is your inference/recommendation — label
inferences. If a claim depends on a Mathlib detail you are unsure exists at v4.29, say so rather than
asserting it.
</grounding_rules>
