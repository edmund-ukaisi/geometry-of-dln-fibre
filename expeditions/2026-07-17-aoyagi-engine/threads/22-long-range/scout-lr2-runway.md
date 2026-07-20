# scout-lr2 — post-spine runway map

*Long-range reconnaissance for expedition 2026-07-17-aoyagi-engine. READ-ONLY seat; one
deliverable. Standing steer honored: the paper (`theory/aoyagi-2023-reproduction/aoyagi-2023-worked.tex`)
is the fidelity touchstone (page/line cites); math-necessity over build-convenience;
Proved/Assumed/Cited/Deferred kept ruthless. Registers tagged.*

Grounded in: `ROADMAP.md`, `compass.md` (forks 11–15 + standing counsel), `priorities.md` (R4–R7),
journal ticks 336–345, `strategy/altitude-2026-07-19.md §3`, the RLCT engine on disk
(`Foundations/{Rlct,Lambda,AoyagiOrder}.lean`, `Engine/*`, `RlctPayoff*`, `AxCheck.lean`),
`threads/12-realization/cert-o5-realization.md`, `threads/21-r4-sharing/cert-r4-sharing-design.md`.

---

## 0. The load-bearing finding (re-frames target [1], and the whole runway)

**`[CLAIM]` The engine expedition IS the native-λ route. "Path B" is not a fresh next-expedition
spine that must build a zeta/pole layer from scratch — the native RLCT value computation is the
engine's own headline, and once `hbox` lands (the current endgame) the singular-locus LOWER bound
is DONE. The residue to discharge the cited axiom is bounded interface/glue, not new geometry.**

Evidence, on disk:

- The engine headline `aoyagi_learning_coefficient` (`Skeleton.lean:1680`) is
  `(⨅ w ∈ optimalSet H B, rlctAt H (dlnLoss H B) w) = ENNReal.ofReal (aoyagiLambda H r)` — the
  **global real RLCT of the DLN loss = Aoyagi's λ**, computed via her own resolution (D1 deepest-point
  ▸ L2 closed form). Its general-L form `aoyagi_learning_coefficient_gen` (`HeadlineGenAssembly`,
  `AxCheck:927`) is **clean-three, conditional only on `hRValue` = the R1 reduced-core gate = `hbox`**.
- `rlctAt` (`Foundations/Rlct.lean:71`) is defined as the **sup-of-finite-`c`** form
  `sSup { c | ∃ U ∈ 𝓝 wstar, IntegrableOn (|F|^(-c)) U }` — Aoyagi Def 1's FIRST equivalent form
  (worked.tex:135-138). **No zeta function, no pole.** The zeta/pole layer lives ONLY in the OPAQUE
  `rlctOrderAt` (`Rlct.lean:124`, the ORDER θ, second deliverable). `[OBS]` So the zeta/pole-order layer
  is greenfield **but is not in the λ-value cone at all** — the value never touches it.
- The geometric side is banked axiom-clean: `minAdm_eq_cCodim` (`MinAdmCCodim:315`, `AxCheck:1182`) gives
  `minAdm M = cCodim M 0`, and `cCodim = codimRepCanonical(fibre)` from Core; with
  `2·lambdaCore = inf' Mval = minAdm` and `aoyagiLambda(·,0) = lambdaCore`, we have
  `aoyagiLambda(M,0) = ½·codimRepCanonical(fibre)` up to the r>0 regular shift — i.e. the arithmetic
  half of `cited_aoyagi_dln` is already proven.
- The singular-locus half — the runway memory's kill-condition — is **built as the resolution, not as a
  smoothness argument**: `o5_realization` is **PROVEN clean-three** (`AxCheck:1311`; crux `o5_core_realized`
  landed, `O5Realization.lean:882`), i.e. `minAdm M ∈ terminalExponents(built tree)` and attained at a
  leaf. Combined with `deepest_le_of_homogeneous_core` (Thm 4 domination, worked.tex:437-458) the global
  `⨅` collapses to the deepest (worst) point and reads off `minAdm/2` — the LOWER bound `rlctAt ≥ minAdm/2`
  is exactly `hbox`/finiteness (altitude §3, elder-verified; the divergence half gives the easy `≤`).

`[OBS]` The runway memory `rlct-runway-target.md` framed the next expedition around a smooth-locus/lci
route (regular sequence → local quadratic model) and flagged "the capstone has NO singular-locus lower
bound" as the kill. That memory **predates the engine** and is now stale: the engine route (Aoyagi's
actual resolution) supersedes the lci route and delivers the singular-locus lower bound directly. This
should be recorded at close.

Consequence for the pricing below: the classically-scary items ("native λ", "singular-locus lower bound")
are *the current spine*; what actually remains post-spine is smaller than the map suggests.

Baseline (distance to `hbox`): **ONE live mathematical hole** — `LeafPullback` (the InvVal value walk over
the α-normalized chart), open at `ChartBridgeFaithful.lean:92` + `GeoAlphaGauge.lean:562`, in flight
(loss-t15), plus the α-atlas transfer re-wire (t14, tasks #1–7). `geoAtlas_cocycle`/`_fold_det`/`_leafJacobian`
and `o5_realization` are already clean-three (ticks 336–338; `AxCheck:1311`). The `≤`-lane
`r1_resolution_general_le` is hbox-free and banked.

---

## Target [1] — the native-λ route / cite discharge  ·  cost **M** (was framed XL)

**NOW.** `aoyagi_learning_coefficient(_gen)` = native `rlct(dlnLoss) = ofReal(aoyagiLambda)` (spine, landing
at mint). `minAdm_eq_cCodim` (banked). `o5_realization` clean-three (the singular-locus realization). The
cited axiom `cited_aoyagi_dln` (`RlctPayoff.lean:297`) = `rlct(lossDLN) = ½·codimRepCanonical(fibre over K)`.

**Paper.** Def 1 sup-of-finite-c (worked.tex:135-138); S2 boxed monomial rule — *the only permitted
citation* (worked.tex:180-189); Thm 4 deepest-point domination (worked.tex:437-458); the value
`rlct_core = ½·min_t Mval(t)` (worked.tex:527-537). LR Thm 8.6 for the codim↔rlct reading.

**Gap (as statements), i.e. the residue to turn `cited_aoyagi_dln` from Cited → Proved** (altitude §3,
elder-verified — none is Aoyagi's resolution, that is the spine):
1. `[gap]` **Interface instantiation:** replace the opaque field `RlctInterface.rlct` with the concrete
   `rlctAt`/`⨅ optimalSet rlctAt`. A DESIGN change (a different `RlctInterface` instance), not a proof.
2. `[gap]` **Localization glue:** `dlnLoss d B` near a fibre minimizer ↔ `routeMCore` (the reduced core the
   engine resolves). The Thm 3 regular peel (worked.tex:363-424) is the content; its VALUE is banked
   (`deepest_regular_core_reduces_frontPivot_front`, `AxCheck:923`), the *localization identity* is the glue.
3. `[gap]` **Neighbourhood bookkeeping:** `rlctAt`-germ nbhd vs `cubeBox ε` / `routeMBaseNbhd`
   (`cubeBox ε ⊆ routeMBaseNbhd` for small ε — trivial-class; RLCT is a germ at 0, worked.tex:141-149).
4. `[gap]` **r>0 shift match:** the regular prefactor `(-r²+r(H⁰+Hᴸ))/2` (worked.tex:406-410) added to
   `½·cCodim` — arithmetic; `aoyagiLambda` already carries it (`Lambda.lean:87`).

**Cost M.** Items 1,3,4 are S; item 2 (localization glue) is the M content. Gated on `hbox` landing first.

**Kill-condition (the real math risk).** The real-vs-complex factor: `rlctAt` is the REAL rlct of a real
loss; `codimRepCanonical(fibre)` is the COMPLEX/algebraic codim over `K`. Kill = an instance where
`⨅ optimalSet rlctAt(dlnLoss) ≠ ½·codimRepCanonical(fibre over K)` because the real critical set is larger
than the complex fibre's real points, or a real branch is missed. `[OBS]` The harness framing already
absorbs the factor (`aoyagiLambda` = real RLCT and *equals* ½·(complex cCodim) by construction, verified at
the ground-truth cases `(2,2,2)→3/2` etc., `Lambda.lean:96-107`), but the equality of ANALYTIC SETS
(`optimalSet` real ↔ `fibre` real points, via `zeroLocus_lossDLN_eq_fibre`) is the load-bearing check to run
against a non-square instance before declaring item 2 done.

---

## Target [2] — the θ-analytic seam  ·  cost split: combinatorial-binding **M**, analytic-pole **XL/greenfield**

**NOW.** `aoyagiTheta ℓ a = a(ℓ−a)+1` and its lattice-box identity `aoyagiTheta_eq_orderBox_card_succ`
(`AoyagiOrder.lean:185`) are Proved — the order-SIDE (the clean combinatorial count) is done. `rlctOrderAt`
is OPAQUE (`Rlct.lean:124`). The non-identity θ_geo ≠ θ_order is banked (6≠5 at (2,2,2,2,2), `AoyagiOrder.lean:33-36`).

**Paper.** Lemmas 4–5, the two partial-sum envelopes + the two-condition binding characterization + the
two-sided (upper-union + explicit-construction) count → `rorder = a(ℓ−a)+1` (worked.tex:727-763); the
gnote is explicit that equating this to the analytic pole multiplicity "needs meromorphic continuation,
which Mathlib lacks."

**Gap (as statements).**
- `[gap, M]` **Tree-binding** (task #69): identify `orderBox`/the envelope-band count with the built tree's
  actual binding-branch multiplicity — the Case-1(2) `J`-increment bookkeeping (worked.tex:508-510,
  744-746) over `buildTree`. `[OBS]` `AoyagiOrder`'s docstring (`:168`) already names this as the missing
  step; it is combinatorial (no analytics), sits on the SAME resolution-tree the spine built, and the
  count is already the clean object — so it is M, not L.
- `[gap, XL/greenfield]` **Analytic pole order:** bind `rlctOrderAt` (the zeta pole multiplicity) to
  `a(ℓ−a)+1`. Needs the b-function / meromorphic continuation of `∫|F|^{-z}φ` (Atiyah / Bernstein–Gelfand);
  **Mathlib has none of it.** This is the genuine wall.

**Cost.** Tree-binding M; analytic pole XL (a multi-module analytic sub-programme, likely its own expedition).

**Kill-condition.** For tree-binding: an instance where the tree's binding-branch count ≠ `a(ℓ−a)+1` (the
mint guard forbids ever routing it through `numTop`/`cTheta` — the 6≠5 witness). For the analytic leg: no
kill needed — it is a scoped Deferred with a named Mathlib absence, not a claim.

---

## Target [3] — R6, the regular peel (Lemma 2 + Theorem 3)  ·  VALUE built; OBJECT cost **M**

**NOW.** The general-L r>0 regular VALUE is **built sorry-free via the front-pivot gauge**
(`deepest_regular_core_reduces_frontPivot_front`, `deepest_gauge_construction_ofBundle`, `AxCheck:923`);
priorities.md:44 records "R6 REMOVED from the owed list — elder charge-8 retraction." Compass fork 11 still
lists R6 as OWED FIRST-CLASS (the OBJECT). This is a documented, live tension to resolve at scope-confirmation.

**Paper.** Lemma 2 block-elimination (Schur complement, unipotent Q₁,Q₂; worked.tex:340-359); Theorem 3
`P₁·(∏A)·P₂ = diag(C₁, ∏C)` with the RLCT split (worked.tex:363-424).

**Gap (as statements).** Not the value (built). The residue is R6-as-OBJECT:
- `[gap]` **Lemma 2** as a named reusable `block_elimination` (the RankNormalForm/`left/right_normal_form_of_*_vanish`
  content, #159, exists in a form — verify it is the reusable statement).
- `[gap]` **Theorem 3** as a named structural `product_reduction` (the full P₁,P₂ split), not only its
  value-consequence. This is where the **SchurCore depth-≥3 wall** lives (rr4-precedent documents
  non-generalization at depth ≥ 3, `RR4.lean:12-21`).

**`[CLAIM]` Did the engine accidentally build the peel's hard part? — Partially: the VALUE, yes; the
STRUCTURAL OBJECT, no.** The front-pivot gauge SIDESTEPS the depth-≥3 SchurCore wall by computing the shift
value without forming the full structural peel — so the wall is *avoided*, not *climbed*. If R6-as-object is
adopted, the depth-≥3 wall is still there and is the L-cost driver. `[Question]` Is R6-as-OBJECT actually
wanted, given the VALUE is banked and the localization glue (target [1] item 2) needs only the value + the
localization identity? My read: only if a downstream consumer needs Theorem 3 as a structural theorem (none
identified); otherwise it is scope, not sequencing. **Surface to operator** (compass already flags this).

**Cost.** VALUE = done. OBJECT = M if Lemma 2 reuses #159 and Theorem 3 is stated at the value's generality;
L if the full depth-≥3 structural peel is demanded.

**Kill-condition.** The SchurCore depth-≥3 wall: an L≥3 instance where the structural peel's inductive step
does not close (rr4-precedent's documented failure) — the cost-probe gate.

---

## Target [4] — R7 completeness (`realizedProfiles = Clearable-Adm`)  ·  cost **S–M** (the hard half is LANDED)

**`[CLAIM]` The engine already built R7's hard direction. The ⊇ (descent invariant / SteerInv) is landed
sorry-free; only the ⊆-Clearable strand obstruction is new work.**

**NOW.** `realizedProfiles_eq_clearableAdm` (`ClearableReify.lean:75`) is the sorried statement (`AxCheck:1373`,
+sorryAx until R7). But its proof pieces are largely on disk:
- **⊇ direction** (`a ∈ Adm ∧ Clearable ⟹ a ∈ realizedProfiles`): this is EXACTLY
  `realize_aux M a ha hc hMpos conRoot (SteerInv_conRoot M a hL)` — **already PROVEN sorry-free**
  (`O5Realization.lean:821`). `realize_aux` is general in `a` (not tStar-only); `tStar_realized` is just its
  minimizer instance. The whole 3-phase `SteerInv` machinery (`SteerPre/Anchored/Done`, `exists_steered_child`
  :517, `clearable_suffix_lt_runMinWidth` :355, `childLeaves_subset`, `leafOfState_carries`) is landed.
- **⊆ `Adm`**: `leaf_mem_Adm` (banked).
- `[gap]` **⊆ `Clearable`** (the strand obstruction, cert §2): a t̃=0 leaf divisor is Clearable, because a
  non-clearable profile is stranded above the shrunken chain (`occ_above ⊆ [·, r_S−1]`, so a level-`r_S`
  divisor is invisible to Case-1 under any pick — chooser/branch-independent). This is the one genuinely-new
  proof; it is stated cleanly in cert-o5-realization §2 and rides the banked o4 `LiveHeadDom` structure.

**Paper.** This is a paper-CORRECTING result (the 4th read-off defect): the paper's implicit
stratum-completeness "t̃=0 profile-set = all of Adm" is FALSE at interior-bottleneck widths
(witness (3,3,4,2,3), cert §2; ledger `verify-realization-gap-defect.md`). So R7 is an honest statement
ABOUT the built object, not a transcription of a paper claim.

**Cost S–M.** ⊇ = wrapper around landed `realize_aux` (S). ⊆-Clearable strand obstruction = the M content
(a clean induction on the recursion, banked o4 reused).

**Kill-condition.** K1/K3 (cert §7) already FIRED and characterized the gap; the strand obstruction is
chooser/branch-independent (verified exhaustively at (3,3,4,2,3), cert §2 B5). Kill for the Lean proof = an
interior-bottleneck instance where a level-`r_S` divisor DOES reach t̃=0 (would break ⊆-Clearable) — 0/791
in the battery.

---

## Target [5] — zero-width (b) layer-collapse + R4-small  ·  cost **S** each, independent

**Zero-width (b).** `[OBS]` The ARITHMETIC half is DONE: `lambdaCore_eq_zero_of_exists_width_zero` +
`aoyagiLambda_of_exists_width_le` (`Lambda.lean:259,328`) — at a zero reduced width the singular core drops
to the regular Morse block. What is OWED is the ANALYTIC layer-collapse (a zero-width LAYER reducing depth
`L`), and dropping the `hMpos : ∀ i, 0 < M i` hypothesis that the attainment layer needs
(`o5_realization`, `tStar_realized`, `aoyagi_learning_coefficient` all carry it; the UPPER-bound
`minAdm_le_terminalExponents`/`r1_resolution_general_le` stay width-free). `[Claim]` **Scope: real for the
fully-general theorem (a bottleneck layer `H^s = r` gives `M^s = 0`), but off the headline critical path**
— the headline may carry `hMpos`, and the arithmetic collapse already gives the value there. **Independent**
of [1]–[4]: it is a hypothesis-weakening pass on the attainment chain, touching `O5Realization` +
`Lambda`, colliding with nothing.

**R4-small (genDivExp propagation).** `[OBS]` compass fork 3 re-priced this **LARGE → SMALL** (~1 module +
~10 mechanical constructor edits; no Finset transport — the LARGE priced a transport the math does not
require). It is the divisor-sharing bookkeeping (`support(row i) = {k : divTilde k < i}`, b-recursion
worked.tex:484), executable at the discharge batch. **Independent** of [1]–[4] (its guard `bExp_spec` is an
executable invariant; no consumer reads internal-state support — region_glue blind, GeoAlphaGauge needs
only Monotone).

**Kill-conditions.** R4: `g-coupled-binding-334` / `g-delta-flatten` (a per-row-multiplicity flatten breaks
at corank≥2 — the (3,3,4) coupled witness, cert-r4-sharing). Zero-width: `M=![2,2,0]` — `tStar=(2,0)` never
realized (immediate rollover), the documented `hMpos` witness (`O5Realization.lean:858`).

---

## Ranking — value / cost

| Target | Value (to the story) | Cost | value/cost |
|---|---|---|---|
| **[1] cite discharge (native λ)** | **Highest** — kills the last opaque axiom in the destination; makes `rlct=C/2` fully Proved | **M** (post-hbox residue) | **top** |
| [4] R7 completeness | High — the full two-sided correspondence; paper-correcting; hard half landed | S–M | high |
| [3] R6-as-object | Medium — widens engine scope; VALUE already banked | M–L (depth-≥3 wall) | medium |
| [5] zero-width + R4-small | Medium — library completeness; both off critical path | S each | medium-high |
| [2] θ tree-binding | Medium — order side of (C,θ); combinatorial | M | medium |
| [2] θ analytic pole | High if reached — but greenfield | XL | low |

## The ONE central question for the next expedition

**"Discharge `cited_aoyagi_dln`: prove `rlct(lossDLN) = ½·codimRepCanonical(fibre)` natively, by
instantiating `RlctInterface.rlct := ⨅ optimalSet rlctAt` and composing the engine's landed
`aoyagi_learning_coefficient(_gen)` (rlct = aoyagiLambda) with the banked `minAdm_eq_cCodim`
(aoyagiLambda-core = ½·cCodim), through the localization glue and the real↔complex analytic-set bridge."**

Why this one: it converts the destination's single remaining Cited axiom into Proved, it stands directly on
what the engine expedition is finishing (no new deep geometry — the singular-locus lower bound is `hbox`,
landing now), and it is the honest completion of the "rising sea" — the layer under `rlct=C/2` closed so the
result stands without re-opening. R4/zero-width fold in as its library-completeness siblings; R7 is the
natural companion (the full correspondence); R6-as-object and the θ analytic pole are the two items to
explicitly SCOPE OUT (surface to operator) rather than silently carry.

**Single highest-risk assumption in that choice.** `[Question→risk]` That the localization/analytic-set
bridge (target [1] item 2 + the real↔complex kill-condition) is genuinely bounded glue and not a hidden
wall. The engine's `⨅` is over the REAL `optimalSet`; `cited_aoyagi_dln` asserts equality to the COMPLEX
`codimRepCanonical(fibre over K)`. If the real critical locus and the complex fibre's real points diverge on
some instance — or if `deepest_le_of_homogeneous_core` does not transport cleanly from the abstract core to
the concrete `dlnLoss` at the interface level — item 2 balloons from M to L. This is the FIRST thing a
next-expedition opening recon should adversarially test (a non-square, r>0 instance against
`zeroLocus_lossDLN_eq_fibre`), before committing the spine.

---

## Close — reflection (per role)

- **Most likely to ADVANCE the expedition:** the finding in §0 — that the engine is the native-λ route and
  the cite-discharge residue is M-class, not XL. It shortens the whole post-spine picture and should be
  reflected at close (and the stale `rlct-runway-target.md` memory retired: the singular-locus lower bound
  is built as the resolution, not owed as a smoothness argument).
- **Most likely to BREAK:** the real↔complex analytic-set bridge inside target [1] item 2 (the highest-risk
  assumption above) — the one place the "bounded glue" pricing could be wrong.
- **Next computation that would clarify:** exhibit `⨅ optimalSet rlctAt(dlnLoss) = ½·codimRepCanonical(fibre
  over K)` end-to-end on ONE non-trivial instance (e.g. a rank-r, non-square-width DLN), tracing the
  `optimalSet` real ↔ `fibre` real-points identification and the r>0 shift explicitly. If it composes from
  the banked decls, target [1] is confirmed M and the central question is de-risked; if the analytic-set
  step needs new content, item 2 re-prices and R6-as-object becomes more load-bearing.
