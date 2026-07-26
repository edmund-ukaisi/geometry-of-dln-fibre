# Statement cards — over-vanishing per-type CONCRETE facts, canonical `(20,1,1)`

Seat: the OVER-VANISHING per-type concrete grind (feeds the (ii) generic backbone
`DLN.Aoyagi.Corank2OverVanish334`). Module: `lean/DLNFibre/DLN/Aoyagi/Corank2OverVanishCanon334.lean`
@ `b715977e5` (branch `expedition/aoyagi-r2overvanish-pertype`). All results axiom-clean
`[propext, Classical.choice, Quot.sound]` (verified by `#print axioms`; NO `sorryAx` — the Core
Tonelli sorry does NOT enter, because `canon_domination` rides the pure-algebra
`monoSumSqGerm_le_of_regSeq_entries`, not the step-6 integrability bridge).

## Setup / conventions

- **Canonical leaf** `idxCanon = (p1,p2,p3) = (20,1,1)` ∈ `Idx` (an over-vanishing leaf: no
  single-entry survivor; `p2 = p3 = 1` makes it a COINCIDING leaf, `vm` degree 2).
- **`gCanon = gFlat idxCanon`** (the `∘id`s and `Idx` projections resolved; `gFlat_idxCanon : rfl`).
- **`Ψ = psiCanon = blockShear phiCanon`**, `phiCanon` the straightening displacement placing the
  negative of each column-`c=1` reg-seq entry's quadratic/cubic correction into `{12,13,14,15}`.
- **`vmExpCanon` = `1@1 + 1@20`** (`prod_vmExpCanon : ∏ u^vmExp = u₁·u₂₀`).
- **`Scanon`** = the 8 reg-seq entry indices = `pairsCanon.image finProdFinEquiv`,
  `pairsCanon = {(0,0),(0,1),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1)}` (columns `c=0,1`; drop `c=2`).
- **`zcCanon k = zcPair (finProdFinEquiv.symm k)`**, `Zcanon = {0,2,3,4,12,13,14,15} = zc '' S`.

All 8 reg-seq entry values were `sympy`-verified END-TO-END against the Lean `gFlat` (the faithful
composite of `blockBlowupMap`/`nativeSel`/`nativePerm`/`blockShear` from the source data), max error
`1.4e-15` over 2000 random points.

---

> **Claim (1′) — the 8 reg-seq entry identities.** For the canonical leaf, each reg-seq `coreGen`
> entry of the folded chart pulls back to `vm·(single straightened coordinate)`.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.OverVanishCanon334.canon_hentry`
>   (`lean/DLNFibre/DLN/Aoyagi/Corank2OverVanishCanon334.lean` @ `b715977e5`)
> - **Gloss.** `∀ u, ∀ k ∈ Scanon, coreGen dvec eWrap k (gFlat idxCanon (psiCanon u)) =
>   (∏ d, (u d)^(vmExpCanon d)) · u (zcCanon k)`. For each of the 8 reg-seq entry indices, the
>   `k`-th flattened core-generator of the whole-conjugate leaf chart `gFlat idxCanon`, folded with
>   the straightening `Ψ = psiCanon`, equals the dominant monomial `u₁·u₂₀` times the single
>   coordinate `u_{zc k}` — exactly (globally in `u`).
> - **Proved.** The 8 identities, unconditionally, via `coreGen_eWrap_entry` (`= (A1·A0)` matrix
>   entry) + `Matrix.mul_apply`/`Fin.sum_univ_three` + a `decide`-powered `simp` unfolding the whole
>   folded composite to a polynomial + `ring`.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free, axiom-clean.

> **Claim (piece 4, per-type) — the product-germ domination.** The folded loss dominates
> `vm²·∑_{Z} z²` near every point.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.OverVanishCanon334.canon_domination`
> - **Gloss.** `∀ u, monoSumSqGerm vmExpCanon Zcanon u ≤ sumSqFam (fun i ↦ coreGen dvec eWrap i ∘
>   (gFlat idxCanon ∘ psiCanon)) u` — the product germ `(∏u^vmExp)²·∑_{j∈Z} u_j²` is `≤` the
>   pulled-back sum-of-squares loss of the folded chart.
> - **Proved.** Unconditionally, by feeding the 8 entry identities to the (ii)
>   `monoSumSqGerm_le_of_regSeq_entries` (reindex `S ≃ Z` via `hzc_inj`/`hzc_img`; drop the 4
>   non-reg-seq squares). Pure algebra — does NOT touch the Core Tonelli bridge.
> - **Assumed / Cited / Deferred.** none.
> - **Status.** sorry-free, axiom-clean.

> **Claim (2) — the straightening `Ψ`.** `Ψ = psiCanon` is a det-1 unipotent shear fixing
> `supp(vm)` and `supp(jacExp)`.
>
> - **Lean:** `jacDet_psiCanon` (`jacDet psiCanon u = 1`), `differentiable_psiCanon`,
>   `psiCanon_apply_offblock` (fixes every coord ∉ `{12,13,14,15}`), `phiCanon_keep`/`phiCanon_read`
>   (`Ψ` keeps and reads only kept coords), `hzc_inj`/`hzc_img`.
> - **Gloss.** `Ψ` is a `blockShear` whose displacement `φ` sits in `{12,13,14,15}` and reads only
>   coordinates outside that block, so it is a polynomial automorphism with `|jacDet| = 1`.
> - **Proved.** All, unconditionally.  **Status.** sorry-free, axiom-clean.

> **Claim (3) — the folded Jacobian (`hW`).** Folding `Ψ` leaves the monomial Jacobian weight
> unchanged.
>
> - **Lean:** `DLNFibre.DLN.Aoyagi.OverVanishCanon334.canon_foldedJac`
> - **Gloss.** `∀ u, |jacDet (gFlat idxCanon ∘ psiCanon) u| = jacWeight (jacExp idxCanon) u` — the
>   chain rule (`Ψ` contributes `|jacDet| = 1`) + the base `hjac_gFlat` + `jacWeight_fixOn` (`Ψ`
>   fixes every binding axis `{1,20}` of `jacExp idxCanon`).
> - **Proved.** Unconditionally.  **Status.** sorry-free, axiom-clean.

> **Claim (cubic cover) — cubic-inflation cover-transport.** The coinciding-leaf `Ψ` is
> CUBIC-unipotent, so the quadratic `image_comp_blockShear_superset` does not apply; a cubic sibling
> transports the cover.
>
> - **Lean:** `blockShear_covers_cubic` (generic atom: `‖φ x‖ ≤ C·r³ ⟹ closedBall 0 r ⊆ blockShear
>   φ '' closedBall 0 (r + C·r³)`), `phiCanon_norm_bound` (`1 ≤ r ⟹ ‖phiCanon x‖ ≤ 2·r³`),
>   `psiCanon_cubic_cover` (`1 ≤ r ⟹ closedBall 0 r ⊆ Ψ '' closedBall 0 (r + 2·r³)`),
>   `image_comp_psiCanon_cubic_superset`.
> - **Proved.** Unconditionally.  **Status.** sorry-free, axiom-clean.
> - **Caveat (for the (ii)/assembly step 6).** The cubic bound needs `1 ≤ r` (holds — `leafR ≥ 1`);
>   NON-coinciding pattern-A leaves are purely quadratic (the existing atom applies there).

---

## Generalization (derived + `sympy`-verified; NOT yet in Lean)

- My seat = the **8-entry reg-seq over-vanishing leaves**: `p2 ∈ σC2(p1)` (for `p1=20`,
  `p2 ∈ {1,5,6,7}`), 16 per `p1` × 9 = 144.
- Reg-seq keys ONLY on `p2`: **pattern A** (`p2 ∈ {1,5}`) `S={0,1,3,4,6,7,9,10}` (drop col `c=2`);
  **pattern B** (`p2 ∈ {6,7}`) `S={0,2,3,5,6,8,9,11}` (drop col `c=1`). Straighten-block is
  `{12,13,14,15}` for `p2 ∈ {1,6}`, `{16,17,18,19}` for `p2 ∈ {5,7}`.
- `vmExp = {p2,p3,20}` (degree 3) generically, collapsing to `{p2,20}` (degree 2) on the coinciding
  `p2=p3` leaves. The entry-identity STRUCTURE is `vm`-agnostic, so `(20,1,1)` is a faithful
  structural template for pattern-A-`p2=1`.
- All 16 `p1=20` leaves confirmed `shearOK` (the straightening displacement never reads its own
  block) — the blockShear straightening is valid uniformly. `σ_{p1}`-transport (pnp: EXACT 144/144)
  extends `p1=20` → all 9 dominants.
