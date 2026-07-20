# Inv_val — Lean STATEMENT + maintenance signatures (loss-t15, PHASE 3b, statement-first gate)

*Seat: loss-t15. The drafted `Inv_val` statement + per-case value-maintenance lemma signatures for
team-lead's gate (option (a): DESIGN NOW, BUILD after t14's det-walk lands). Grounded in §7
(`cert-ledger-accumulation.md`) + `cert-loss-factorization.md`. TWO certs / ONE skeleton (settled;
no cert wait). Concrete where t14-independent; spec'd where coupled to t14's landed representation.*

---

## 0. The object and the acc/state threading

`Inv_val` is the VALUE instance of t14's shared induction skeleton (tree walk over
`tGeoG`/`geometricLeafPaths`, per-`stepUpdate`-case dispatch, `conRoot` base, `DivBirthInv`
threading, `geoChartMap_flat_{pivot,center,spectator}` + `flatSwapCLE_apply_flat` reads). It states,
threaded by the fold accumulator `acc` and the construction state `s : ConState L`:

    Inv_val(acc, s) :  ∀ w, prod M (acc w) = partialDiag M s w

`prod M (acc w) : Matrix (Fin (M 0)) (Fin (M (last))) ℝ`. `partialDiag M s w` is the state's
Aoyagi partial-diagonal form (§7): the `s.cleared = J` already-resolved diagonal cells carry the
`b`-chain monomials, the rest is the un-resolved residual block.

    partialDiag M s w  =  diag(b(s)(w)) · [[E_J, O],[O, D_J(s)(w)]]

- `b(s) : Fin s.numDiv → ℝ`-valued monomials of `w` — the divisibility chain (`b₁ = ∏_{t̃=0} u`
  squarefree; `bᵢ/bᵢ₋₁ = ∏_{born at level i−1} u`), read from `s.divExp`/`s.divProfile`/
  `s.divBirthCoord` (power-1, NOT `divExp` powers — §7 delta (2)).
- `E_J` = identity on the cleared J×J corner; `D_J(s)(w)` = the residual block on the un-cleared
  coords (the ratio coordinates `d'_{ij}`) — §7 delta (1). At a leaf `D_J` is fully cleared.

**t14-COUPLING (finalize on landing):** the exact Lean encoding of `partialDiag` (block split at `J`
over the rectangular `Fin (M 0) × Fin (M last)`, `E_J`, and the `D_J` residual representation) mirrors
t14's landed partial-form representation in its det walk (shape-check discipline: reuse its block
plumbing, do not invent parallel). The b-chain read reuses the leaf's TYPED `bExp`/`bChain`.

## 1. The statement (Lean target)

```
/-- The state's partial-diagonal form (helper; block encoding mirrors t14's landed det-walk form). -/
noncomputable def partialDiag (M) (s : ConState L) (w : Params M) :
    Matrix (Fin (M 0)) (Fin (M (Fin.last L))) ℝ := <block: diag(b s w) · [[E_J,O],[O, D_J s w]]>

/-- **Inv_val** (the value instance of t14's skeleton): the acc-threaded prod-diagonalization. -/
def InvVal (acc : Params M → Params M) (s : ConState L) : Prop :=
  ∀ w, prod M (acc w) = partialDiag M s w
```

## 2. Base + four per-case maintenance signatures (α-marked per §7's value-carrying table)

Threading direction/motive mirror t14 (innermost-first relative cocycle, cert §2). `α` = the incidence
Q,P Schur (`residualSchurShear`, banked this seat); the det is det-1-BLIND to it, the value is not
(§7 delta (3)) — so the value-carrying steps APPLY `α` to clear a residual column/block.

```
/-- BASE (conRoot, L=1): the raw product is the whole residual, no cleared cells. -/
theorem invVal_conRoot : InvVal id (conRoot : ConState L)          -- prod M (id w) = ∏ C^{(s)}

/-- case-1(1) RE-MERGE — value-carrying: α = id (pivot = diagonal already); b-power STAYS 1
   (squarefree; the re-merge accumulates only in the det's divExp, NOT in b). -/
theorem invVal_step_case11 (acc) (n : StepData M) (e : Edge M) (he : e.case = .case11)
    (hInv : InvVal (acc ∘ geoChartMapNorm alphaGauge ⟨n,e,pivot⟩) <child s>) : InvVal acc <parent s>

/-- case-1(2) SPLIT — value-carrying: α Schur clears ONE residual column toward D_{J+1}; a new
   b-chain entry appended (b-power 1). -/
theorem invVal_step_case12 (acc) (n) (e) (he : e.case = .case12) (hInv : InvVal … <child>) : InvVal acc <parent>

/-- case-2 BIRTH — value-carrying: α Schur clears the residual block toward [[1,O],[O,D_{J+1}]];
   new pivot b-chain entry (b-power 1). -/
theorem invVal_step_case2 (acc) (n) (e) (he : e.case = .case2) (hInv : InvVal … <child>) : InvVal acc <parent>

/-- rollover — NON-value-carrying: a chartless relabel (localSub = id); partialDiag unchanged up to
   the layer reindex, α = id. -/
theorem invVal_step_rollover (acc) (n) (e) (he : e.case = .rollover) (hInv : InvVal … <child>) : InvVal acc <parent>
```

(The `<child s>`/`<parent s>` and the exact `acc ∘ …` threading are the pieces that mirror t14's
landed step-case pattern; marked for shape-check on landing.)

## 3. The leaf discharge — `InvVal → LeafDiagFrob` (t14-INDEPENDENT; the bridge to the proven reduction)

This is the load-bearing bridge and is buildable NOW in shape (it needs only `InvVal` at a leaf +
`resRank = 0`, both this seat's). At a spine leaf `s_leaf` (fully monomialized, `resRank = 0`), `D_J`
is cleared so `partialDiag M s_leaf w = diag(b(s_leaf)(w))` (rectangular diagonal). Then:

```
/-- The bridge: at a leaf, InvVal gives prod = diag(b), which is exactly LeafDiagFrob. -/
theorem leafDiagFrob_of_invVal (l : LeafData M) (s_leaf : ConState L)
    (hInv : InvVal l.chartMap s_leaf) (hleaf : <l is the leaf of s_leaf, D_J cleared>) :
    LeafDiagFrob l
```

Proof shape (all pieces this seat / small new reads):
- `frobSq (prod (chartMap w)) = frobSq (diag (b w)) = Σⱼ (b w j)²` (a `frobSq`-of-rectangular-diagonal
  lemma — small, new).
- `b w j = (∏_k z_{divCoord k}(w)) · ρⱼ(w)` with `ρⱼ = bⱼ/b₁` a power-1 monomial (`bChain` divisibility,
  TYPED); `b₁ = ∏_k z_{divCoord k}` (terminal product = `D`, `cert-loss-factorization` (a) squarefree).
- Instantiate `LeafDiagFrob` with `m := l.numB`, `r w := ρ(w)`, `hi := ` ratio bound on the flat-cube
  `srcBox`; `∃ i, r i = 1` = the `b₁`-index ratio. Then `leafPullback_of_diagFrob` (PROVEN) closes
  `LeafPullback` end-to-end.

## 4. Wiring `leafDiagFrob_geoAtlasNorm` (the current one `sorry`)

`leafDiagFrob_geoAtlasNorm l hl := leafDiagFrob_of_invVal l s_leaf (invVal_leaf …) hleaf`, where
`invVal_leaf` is `InvVal` specialized to the leaf via the fold of `invVal_conRoot` + the four
maintenance steps down the `buildTree` path (the walk instantiation — the t14-timed piece).

## 5. (B) discharge pre-stage (comment for `ChartBridgeFaithful`)

`chartBridgeFaithful_buildTree`'s (B) sorry needs `∀ c ∈ geoAtlas, LeafPullback c`. Once the loss lane
closes: `leafPullback_geoAtlasNorm` supplies the `LeafPullback c` conjunct per atlas piece (the atlas
there is `geoAtlas = geoAtlasNorm (fun _ => id)`; the α-atlas transfer lemma `geoAtlas = geoAtlasNorm
alphaGauge`-image-equal — or (B) consumes `geoAtlasNorm alphaGauge` directly once the cover/fold
transfer lands). I will pre-stage this wiring line as a comment at the (B) slot.

## 6. What is t14-BLOCKED vs buildable now

- **NOW (t14-independent):** `LeafDiagFrob`/`leafPullback_of_diagFrob` (DONE), the leaf-discharge
  bridge shape (§3), the `frobSq`-of-diagonal lemma, the `bExp`/`bChain` → `ρ` instantiation.
- **AFTER t14's walk lands:** `partialDiag`'s exact block encoding (mirror t14), the four maintenance
  proofs + the walk instantiation `invVal_leaf` (mirror t14's step-case plumbing). No cert owed.
- **HEADS-UP (t10 `LeafData.fullDivCoord`):** Jacobian-side field; loss reads are ANALYTIC (three-ledger
  split) so statements unaffected — merge origin on landing so the module re-elaborates on the new type.

---

## ADDENDUM 2026-07-20 (loss-t15 respawn) — resid tripwire, bmon indexing, t14-aligned maintenance shapes

Respawn after a VM restart; predecessor's banked work intact. t14's fold walk is fully CLOSED
(`geoAtlas_cocycle`, `geoAtlas_fold_det`, `geoAtlas_leaf_leafJacobian`, all clean-three). The ENTRY-WISE
`InvVal` + `leafDiagFrob_of_invVal_leaf` are banked green (`GeoInvValWalk.lean`). Build is blocked on the
elder's resid A-vs-B ruling. This addendum records what the respawn analysis firmed.

### (I) RESID: the tripwire fired — pure option A is not honest; recommend A-scaling × B-recursive-ratio

The residual block after a blow-up is `u · [[1, a],[b, a·b + ρ]]` (`value_threaded_verify.py` PART C;
worked.tex ssec:blowup): a scaling exceptional value `u` (ledger-derivable, a clean monomial off
`divBirthCoord`) times a RATIO block whose `(1,1)` entry `a·b + ρ` is a genuine POLYNOMIAL, and which
deepens into the partial matrix-product of the not-yet-processed layers. So **"closed-form monomial×ratio
per cell" (A) understates the ratio part.** Honest encoding: HYBRID — `resid = (A: ledger scaling
monomial) × (B: state-level recursive ratio block)`.

- What the CLEARING-step maintenance consumes from resid: the block's scaling factorization + the pivot
  corner (`= scaling×1 → bmon`) + the pivot row/col RATIOS. The α-Schur `Lg = [[1,0],[-b,1]]`,
  `Rg = [[1,-a],[0,1]]` READ `a, b` to clear the off-diagonal to `0`. Because the clearing reads the
  row/col ratio VALUES, **option C (constrain cleared cells only) CANNOT prove the clearing step** — the
  payload must expose at least the pivot row/col of the residual.
- resid stays a function of `(s, w)` alone (Codex pitfall #2): `buildTree` is deterministic (unique path
  to each `s`), so a state-level recursive `resid` matches the fold; the "matches-the-fold" lemma is the
  content, and it is provable.
- This CHALLENGES the tick-340b "option A closed-form-per-cell approved" meanwhile-conclusion. Surfaced
  to team-lead + elder pre-collision (tick-284 lesson).

### (II) BMON indexing: level = CLEARING level t̃ (not birth layer)

`value_threaded_verify.py`'s `bchain` groups by CLEARING LEVEL: `b_i = ∏_{div : t̃(div) ≤ i} z_div`
(`b_1 = ∏` terminal, t̃=0). So the pinned prose "born at level ≤ level(i)" should read "**clearing level
≤ level(i)**" — `level(i)` from `tildeOf ∘ divProfile`, coordinate from `birthFlatCoord ∘ divBirthCoord`.
The diagonal-position ↔ distinct-clearing-level reindexing is new value-side content t14 never does (t14
is per-divisor scalar). Confirm this reading when pinning the concrete `bmon`.

### (III) BANKED this respawn (resid-independent, clean-three, pushed)

The α-atlas walk tree-plumbing (`GeoInvValWalk.lean`), the `tGeoG`/`fannedEdgesG` analogs of t14's
`GeoFoldRegroup.mem_edgesLeaves_fanned_{charted,chartless}` (hardcoded to gauge `fun _ => id`):
`mem_edgesLeaves_fannedG_charted` / `mem_edgesLeaves_fannedG_chartless`. Pure tree structure, payload-
independent, so they land regardless of the resid ruling. These are what the walk uses to decompose
`leaves (tGeoG alphaGauge acc (buildTree … s))` at each step (mirroring how `geoAtlas_cocycle` uses the
id-gauge versions). Note: the value walk needs NO differentiability lemmas (it tracks `prod` VALUES, not
`fderiv`) — a simplification vs t14's det walk.

### (IV) The four maintenance statement shapes (t14-aligned; for the binder-vs-design diff)

Parametric in `(cleared, bmon, resid)` (so ruling-robust in SHAPE; only the concrete payload + the
PROOFS wait on the ruling). Direction mirrors t14's `ledger_det_maintenance_*` (parent `InvVal` → child
`InvVal` with `acc` extended by the edge chart `B = geoChartMapNorm alphaGauge g`); the walk then recurses
via the child `ih` (as in `geoAtlas_cocycle`). Binders track t14's exactly (`inv : DivBirthInv M s`,
`htree`, `hnr`, `hocc`, `hce`, `hd`, `hp`, the cell facts `hpivcell`/`hucell` for case-1); the value delta
is the `InvVal` conclusion in place of the `ledgerMonomial` equation.

```
-- BASE (conRoot): nothing cleared; InvVal reduces to `resid conRoot w = prod M w` (resid-dependent).
invVal_conRoot : InvVal cleared bmon resid id (conRoot : ConState L)

-- case-2 (birth): child = s.stepAppendAdvance (resRows*resCols) t₀; α clears the block → [[1,O],[O,D']].
invVal_maintenance_case2
  (s) (inv : DivBirthInv M s) (g edges) (htree : buildTree M (conOracle M) s = .branch g.node edges)
  (hnr) (hocc : nodeOccMin M g.node = none) (hce : g.edge.case = .case2) (hd) (hp) (t₀) (acc)
  (hInv : InvVal cleared bmon resid acc s) :
  InvVal cleared bmon resid (acc ∘ geoChartMapNorm alphaGauge g)
    (s.stepAppendAdvance (g.node.resRows * g.node.resCols) t₀)

-- case-1(1) (re-merge): child = the bumpedExp state; α = id (pivot = diagonal); NO new cleared cell,
--   NO b-power change (squarefree — the re-merge lives only in the det's divExp, cert (a)).
invVal_maintenance_case11
  (s) (inv) (g edges) (htree) (hnr) (hce : g.edge.case = .case11) (f) (hmerge) (target) (hocc)
  (hf) (b) (hb) (hd) (hp) (hpivcell : cNodeOf M g.node hd ⟨g.pivot,hp⟩ = birthFlatCoord M s f h) (acc)
  (hInv : InvVal cleared bmon resid acc s) :
  InvVal cleared bmon resid (acc ∘ geoChartMapNorm alphaGauge g) <the case-11 bumpedExp child>

-- case-1(2) (split): child = s.stepAppendAdvance (divExp f + b) t₀; α clears one residual column;
--   new cleared cell + one appended b-chain entry (b-power 1).
invVal_maintenance_case12
  (s) (inv) (g edges) (htree) (hnr) (hce : g.edge.case = .case12) (f) (target) (hocc) (hf) (b) (hb)
  (hd) (hp) (hucell : ∃ i ≠ ⟨g.pivot,hp⟩, cNodeOf M g.node hd i = birthFlatCoord M s f h) (t₀) (acc)
  (hInv : InvVal cleared bmon resid acc s) :
  InvVal cleared bmon resid (acc ∘ geoChartMapNorm alphaGauge g) (s.stepAppendAdvance (s.divExp f + b) t₀)

-- rollover (chartless): child = s.stepRollover; B = id (localSub = id); payload carried up the reindex.
invVal_maintenance_rollover (s) (acc) (hInv : InvVal cleared bmon resid acc s) :
  InvVal cleared bmon resid acc s.stepRollover
```

The walk headline `geoAtlas_invVal_cocycle` mirrors `geoAtlas_cocycle` (WF induction on `conRel_wf`,
`conOracle` re-dispatch, the four cases via `mem_edgesLeaves_fannedG_{charted,chartless}` → maintenance →
child `ih`), threading `DivBirthInv`/`DivExpPos`, over `tGeoG alphaGauge`. Terminal: `p.chartMap = acc`,
all cleared ⟹ `leafDiagFrob_of_invVal_leaf`. Headline scope `s = conRoot`, `acc = id`.

**OPEN vs the ruling.** case-2/case-1(2) (the CLEARING steps) consume the residual scaling factorization +
pivot row/col (finding I) — their PROOFS wait on the resid encoding. case-1(1)/rollover touch only the
cleared cells + spectator reads — closest to resid-free, but case-1(1)'s "no b-power change" still needs
resid unchanged on the (unchanged) residual, so it too reads resid's transformation. The base at conRoot
is entirely resid (nothing cleared).
