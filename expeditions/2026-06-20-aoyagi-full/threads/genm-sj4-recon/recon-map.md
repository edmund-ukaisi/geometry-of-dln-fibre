# recon-map — #4 `DecoratedBaseHyp` z-dependent rebuild (banked-state map)

**Seat:** self-recon (READ-ONLY internal reconnaissance). **Date:** 2026-07-12. **NO Lean edits, NO build.**
**Charge:** map our OWN banked state for the z-dependent generalization of the `DecoratedBaseHyp` base leg
(route-ii native discharge of `(□) = RouteMBoxThresholdFinite`), so the next formalisation tide names banked
pieces rather than starting blind.

**Checkpoints read:** canonical `@cd11d759` (main checkout); reference `origin/wip/genm-sj4-base-fixedz`
`@7fd86617` (desc4's fixed-Z WIP, `git fetch`ed). Design docs: `stephyp-buildplan.md §6″`,
`joint-corner-cert.md`, `genm-sj5-piece2-design.md`, synthesis UPDATE-948→972.

---

## 0. The frame (what is where)

- **`FaithfulSJAt` does NOT exist on canonical `@cd11d759`.** Canonical's `adm` (RouteMSJAdm.lean:115) is the
  desc3 valuation form `genuineCarrier ∧ (a=0 ∨ b=0 ∨ admValuation)`. `FaithfulSJAt` lives ONLY on the
  reference branch (desc4's strengthen). The tide starts from the reference branch's 4 files, not canonical.
- **The base leg is #4-COMPLETE (sorry-free) against fixed-Z.** On the reference branch,
  `decoratedBaseHyp_faithful : DecoratedBaseHyp adm` (RouteMSJBaseHyp.lean, end) is sorry-free + axiom-clean.
  The "9 sorries" in the commit message is the REPO-WIDE count at that checkpoint; among the 4 named files
  only `RouteMSJCorankGram.corankGram_box_lt_top` (line 132) carries a real `sorry`, and that file is a
  SEPARATE GAP-B m-column-majorant piece — **not imported by `RouteMSJBaseHyp`, not on the #4 critical path.**
  So the #4 base-leg lemmas (RouteMSJAdm + RouteMSJBaseHyp + RouteMSJBaseFinite) are all sorry-free.
- **What is "owed" is therefore NOT sorries-to-fill but a RE-ARCHITECTURE** (Γ×R split) + one fresh
  construction (P1 tailProd) + one bedrock witness (P4). The corankLeaf analytic core is unchanged.
- **The contract (`DecoratedDescent` driver) is untouched and mechanical** on canonical — `adm`-abstract, so it
  accepts whatever `FaithfulSJAt`-based `adm` the tide lands.

---

## 1. The contract on canonical (`RouteMSJDecoratedRec.lean`, `@cd11d759`, sorry-free)

The driver is `adm`-abstract and mechanical (arity strong-induction). The tide supplies `adm`; the driver
already discharges `(□)` modulo `DecoratedDescent`.

- **`DecoratedBaseHyp adm`** (line 154) — the **width-2 leaf ONLY** (`n = 1`, i.e. `M : Fin (1+1) → ℕ`):
  `∀ (M : Fin (1+1) → ℕ) (D : SJDecoration M), adm 1 M D → DecoratedBoxThresholdFinite D`. This is #4's target.
  **Because the driver dispatches `n = 1` here and `n ≥ 2` to the step, #4 NEVER sees intermediate arity.**
- **`DecoratedStepHyp adm`** (line 144) — the `n = L+2` step, fed the DECORATED strong IH
  (`∀ M' D', adm (L+1) M' D' → DecoratedBoxThresholdFinite D'`). This is #5. It CONSUMES `adm D` at the
  current (intermediate) arity and must PRODUCE `adm D'` for the peeled reduced decoration to invoke the IH.
- **`DecoratedDescent`** (line 206) — `∃ adm, (∀ n M, adm n M (trivial M)) ∧ DecoratedStepHyp adm ∧
  DecoratedBaseHyp adm`. **`decoratedBoxThresholdFinite_of_decoratedStep`** (line 161) is the arity recursion;
  `n=0` vacuous, `n=1`→hbase, `n=k+2`→hstep. **`routeMBoxThresholdFinite_of_decoratedDescent`** (line 216)
  closes `(□)`.
- `FaithfulSJAt` d≥1 vs d=0 clauses: see §2 (reference branch).

**Load-bearing consequence:** `FaithfulSJAt` is a **general-arity loop invariant** — CARRIED at every arity,
CONSUMED at width-2 (#4), PRESERVED L−1→L (#5). A clause that holds only at width-2 breaks #5-preservation
(that is exactly the fixed-Z failure). This is the lens for the whole recon.

---

## 2. The reference checkpoint (`origin/wip/genm-sj4-base-fixedz`) — Z-independent vs fixed-Z-specific

### 2a. `RouteMSJAdm.lean` — `FaithfulSJAt` (def at line 136)

```
FaithfulSJAt D :=
  (D.d = 0 ∧ ∀ z x u, D.carrier.loss u z x = ∑ v, (x v)^2)              -- (d=0) observable free-block leaf
  ∨ (1 ≤ D.d ∧ ∃ i₀,
        (α) ∀ j ℓ, supp i₀ ℓ ≤ supp j ℓ                                  -- pSimultaneous
      ∧ (β) minAdm M / 2 ≤ monomialThreshold D.d (sharedDivisorExp supp) jac
      ∧ (δ≡0) ∀ i ℓ, supp i ℓ = sharedDivisorExp supp ℓ                  -- residualSupport ≡ 0
      ∧ (γ') ∃ a n Dt (Z : Matrix (Fin n) (Fin Dt) ℝ) c
              (eΓ : D.Z ≃ᵐ (Fin a → Fin n → ℝ)) (ρ : D.ι ≃ Fin a × Fin Dt),
              0 < c ∧ (Z*Zᵀ - c•1).PosSemidef                            -- ★ UNITS BOUND (carried, fixed Z)
            ∧ MeasurePreserving eΓ ∧ D.dom = eΓ ⁻¹' matBox a n 1
            ∧ minAdm M ≤ a*n
            ∧ ∀ z i, residual … i = rmatMul (eΓ z) Z (ρ i).1 (ρ i).2)    -- provenance, FIXED Z
```

**Z-INDEPENDENT — reusable VERBATIM in the z-dependent rebuild** (these are pure carrier-support / jac / dim
properties, hold on all of `dom`, so carriable by the UPDATE-955 criterion):
- the whole **(d=0) observable-loss disjunct** (RouteMSJAdm ~137-139);
- **(α) pSimultaneous**, **(β) monomialThreshold ≥ ½minAdm**, **(δ≡0) residualSupport≡0** clauses
  (RouteMSJAdm ~142-149); `minAdm M ≤ a*n` (dims);
- `genuineCarrier` (RouteMSJAdm:53), `admValuation`, `adm`, `bindingCut`, `admCorankA/B`, `adm_trivial`,
  `genuineCarrier_trivial`, both regression tests — all unchanged. `genuineCarrier` already pins
  `D.Z ≃ᵐ Params M`; the Γ×R split is a FURTHER factorization of `Params M = front × tail`, so it is
  COMPATIBLE (no genuineCarrier edit needed — this is the FLAG-2 "keep ν fixed" point: record the tail in the
  split, do not shrink ν).

**FIXED-Z-SPECIFIC — MUST change (this is P2):** the **(γ') provenance clause** (RouteMSJAdm ~150-159). Two
defects, both #5-fatal at intermediate arity:
1. `eΓ : D.Z ≃ᵐ (Fin a → Fin n → ℝ)` maps ALL of `D.Z` to a SINGLE free block → forgets the tail remainder;
   `genuineCarrier` pins `D.Z ≃ Params M` (all tail params), so single-block is unsatisfiable when the tail is
   nonempty (intermediate arity). [UPDATE-959 reason (2).]
2. `Z` is a FIXED matrix, but `prod(redChain) = A_front·A₂···A_L` is MULTILINEAR (≥2 varying factors) at
   intermediate arity → one fixed `Z` cannot equal the varying deeper product. [UPDATE-959 reason (1).]

### 2b. `RouteMSJBaseHyp.lean` — the base leg (the 3-way dispatch)

**All sorry-free, all Z-INDEPENDENT / reusable verbatim** except the `decoratedBaseHyp_faithful` case-(iii)
UNPACK (which reads the fixed-Z γ' and must be re-pointed at the Γ×R split):
- **`decoratedBase_corankZero`** (case i) — design-independent (vacuous threshold). Verbatim.
- **`decoratedBase_d0_of_lossEq`** (case ii) — takes `e : D.Z ≃ᵐ Params M`; unchanged. Verbatim.
- **`decoratedBase_routeA_of_leafForm`** (case iii, ~line 130) — **the corankLeaf CORE (P3), UNCHANGED.**
  Stated for ANY fixed `Z : Matrix (Fin n) (Fin Dt) ℝ` with `hZ : (Z*Zᵀ − cpos•1).PosSemidef`; Tonelli-splits
  into a `u`-monomial box (finite below `monomialThreshold`, β) × the Γ-block leaf (banked
  `corankLeaf_rpow_lt_top`). At the z-dependent base, plug `Z = 1` (Z_tail=I at width-2). **Reusable verbatim.**
- **`decLoss_commonDivisor_factor`**, **`decLoss_clean_of_uniformResidualSupport`**, `eqRec_fun_apply_eqRec` —
  Z-independent carrier algebra. Verbatim.
- **`WeightedLeafForm`** (RouteMSJBaseHyp ~248) — ★ **ALREADY the z-dependent shape, STAGED:**
  `∃ a n Dt (Γ : D.Z → Matrix (Fin a)(Fin n)) (Ztail : D.Z → Matrix (Fin n)(Fin Dt)) (ρ : D.ι → Fin a×Fin Dt),
  minAdm M ≤ a*n ∧ ∀ z i, residual … i = (Γ z * Ztail z)(ρ i).1 (ρ i).2`. This is the P2 target modulo
  (i) `ρ` must be an `≃` (the frobSq reindex uses `Equiv.sum_comp`), (ii) no units bound (see the tension in §5),
  (iii) the Γ×R measure-split shape (`Γ`,`Ztail` should factor through an `eΓ : D.Z ≃ᵐ (Fin a→Fin n→ℝ)×R`).
- **`decoratedBaseHyp_faithful`** (end) — case (iii) currently `obtain ⟨a,n,Dt,Z,c,eΓ,ρ,…⟩` from the fixed-Z
  γ'. This UNPACK line is the ONE place in the base leg that must be re-pointed (P3 wiring).

### 2c. `RouteMSJBaseFinite.lean` — `baseBoxCoV_lt_top` + `sjBase1_freeMatrix` (banked width-2 Morse).
Z-independent, reusable verbatim. `sjBase1_freeMatrix` is itself sorry-free (the `d=0` leaf both routes consume).

### 2d. `RouteMSJCorankGram.lean` — GAP-B, **NOT on the #4 critical path.** `corankGram_box_lt_top` (sorry,
line 132) is the m-column-majorant of a DIFFERENT (route-agnostic) plan; the sorry-free content
(`posSemidef_gram_sub_submatrix_cols`, `det_gram_le_of_submatrix_cols`) is reusable if ever needed, but the #4
base leg uses `corankLeaf_rpow_lt_top` (sorry-free), not this file. Ignore for #4.

---

## 3. Reusable-to-consume (banked, plug-in-ready for #4)

| Piece | File:where | Signature / role | For #4? |
|---|---|---|---|
| **`corankLeaf_rpow_lt_top`** (the LOSS part, DONE) | `RouteMSJLeafFinite` (`n_rpow_lt_top` on canonical; renamed on ref branch) | `{a n D}(h:0<a*n)(Z:Matrix (Fin n)(Fin D))(c)(hc:0<c)(hZ:(Z*Zᵀ−c•1).PosSemidef)(c')(0≤c')(c'<a*n/2)(T)(0<T) : ∫_{matBox a n T}(frobSq(rmatMul Γ Z))^{−c'} < ⊤`. Rayleigh majorant → free-Γ Morse. | **YES, verbatim** (Z=1 at base). Sorry-free, axiom-clean. |
| `decoratedBase_routeA_of_leafForm` | `RouteMSJBaseHyp` ~130 | the Tonelli split (β × corankLeaf). | **YES, verbatim** (the P3 core). |
| `baseBoxCoV_lt_top` / `sjBase1_freeMatrix` | `RouteMSJBaseFinite` | width-2 free-matrix Morse (d=0 leaf). | YES (case ii). |
| `monomialIntegrand_lintegral_unitBox_lt_top`, `monomialThreshold_eq_iInf_axisRatio`, `axisRatio_lt_exp` | `RouteMSJMonomialLower` / `MonomialThresholdIdentity` | the β `u`-monomial box factor. | YES (case iii). |
| `frobSq_mul_rpow_le` / `frobSq_mul_ge` (Rayleigh) | `RouteMSJLeafRayleigh` | `c·frobSq Γ ≤ frobSq(Γ·Z)` from `Z·Zᵀ≽c·I`. | inside corankLeaf. |
| `exists_gram_sub_smul_one_posSemidef_of_rank_eq` (+ `posDef_gram_of_rank_eq`, `exists_pos_smul_one_le_of_posDef`) | `RouteMSJUnitsBridge` | full-row-rank ⟹ `∃c>0, Z·Zᵀ≽c·I` (eigenvalue-FREE, sphere-min). | derives the units bound (at base trivially Z=1,c=1; at intermediate = #5's per-peel sector supply). |
| `corank_survival_ae` | `RouteMSJCorankSurvival` | `b ≤ Zdeep.rank ⟹ ∀ᵐ A, (A·Zdeep).rank = b` (AG-free, minor-cut null). | #5 (invariant preservation, #2b). |
| `minAdm_redChain_succ_ge`, `_ge_corankWidth`, `minAdm_binding_convexity_le` | `RouteMSJTransversality` | invariant-ii convexity / `minAdm ≤ a·n` preservation. | #5; the `minAdm≤a·n` clause is #5-preservable via these. |
| `freedSchurLoss_inner_peel_le` (+ `_bounded_le`, `_shear_lt_top`, `pivotEnergy_inverse_free`, `measure_shearbox_lt_top`, `volume_genBox_lt_top`) | `RouteMSJInnerDescent` | Route-B measure bedrock: integrate-Γ-first block bound, exponent-shift `−(c'−ab/2)`. | **#5** (the coupled corner), NOT #4. Staged for the step. |
| `minAdm_backPeel_cominimizer_ge_corankWidth`, `exists_minAdm_backPeel_cominimizer_corankWidth` | `RouteMSJBackPeel` | the QIP back-peel `minAdm = peelCharge + minAdm(redChain)` (#1). | #5. |

**LOSS part confirmed DONE:** `corankLeaf_rpow_lt_top` exists, sorry-free, signature above; it takes a fixed
`Z` and gives the leaf integral finiteness. At the z-dependent base, `Z = 1`, `c = 1`, `hZ` = `(1−1•1)=0`
PosSemidef — trivial. So the base leg's analytic engine needs **no adaptation** — only the carrier wiring does.

---

## 4. Staged-for-this-point (built expressly for the z-dependent #4)

- **`WeightedLeafForm`** (RouteMSJBaseHyp ~248) — the z-dependent provenance shape, type-checked and staged.
  The P2 target is a small refinement of it (make `ρ` an `≃`; factor `Γ`,`Ztail` through the `eΓ : D.Z ≃ᵐ
  (Fin a→Fin n→ℝ)×R` split; decide the units-bound status per §5).
- **The 4-piece plan is BANKED** (synthesis UPDATE-960 line 122 + UPDATE-967 line 100, probe-de-risked):
  - **P1 TAIL-PRODUCT INFRA** (~40-60 LoC, the one genuinely-new load-bearing piece): a fresh `tailProd`
    suffix/segment product `Z_tail = A₂···A_L : Matrix (Fin (M 1)) (Fin (M last))`, `= I` at width-2 (tail
    empty). **Piece-1 PROBE (UPDATE-967) found the banked handles do NOT reuse:** `prodAux` is a PREFIX
    product; `tailChain` (RouteMSJResolution:172) is width-≥3-only; `prodAux_split_exists` is EXISTENTIAL-only
    (not a concrete `Z_tail` the γ' can name); general-L (incl. L=0) forces `Fin`-width casing/casts. So P1 is
    a genuine fresh recursive-suffix def + width-2 base + Fin-casts (multi-tide-costly historically, hence the
    escape-valve). `prod_eq_layerMul` does NOT exist as a general lemma — only `D1RectHrankClose`'s width-2
    `prod H v = layer0·layer1`.
  - **P2 γ' REWIRE** (RouteMSJAdm): the Γ×R split (above), `Z_tail : R → Matrix` tied to `tailProd`,
    provenance `res = (Γ(z)·Z_tail(r))_ρ`, `minAdm ≤ a·n`; **the R-tie MUST FORCE `R = Unit`/`Z_tail = I` at
    width-2** (else #4 cannot derive the base from an arbitrary witness). KEEP the reusable α/β/δ≡0/d=0/
    genuineCarrier clauses (§2a).
  - **P3 #4(iii) BASE-SPEC**: width-2 → tail empty → R trivial + Z_tail=I → `decoratedBase_routeA_of_leafForm
    (Z=1)`; corankLeaf core + `decLoss_clean_of_uniformResidualSupport` + ρ-reindex + δ≡0 collapse UNCHANGED.
  - **P4 NON-VACUITY WITNESS** (bedrock): an intermediate-arity (width-3) decoration satisfying the Γ×R +
    Z_tail(r) γ' — proving the d≥1 clause is inhabited MID-recursion (the fixed-Z was vacuous there).
- **The #5 mechanism (Route B) is decorrelated-confirmed** (`joint-corner-cert.md`): integrate-Γ-first (freed
  Morse, exponent shift `½peelCharge`) + BLACK-BOX decorated IH at `c'−½peelCharge < ½minAdm(redChain)`
  (`carrierThreshold_shift`). #4's z-dependent γ' shape is what #5 preserves — so the two must be co-consistent.

---

## 5. Pitfalls that bite

1. **★ THE UNITS-BOUND CLAUSE STATUS — a live design inconsistency (see Verdict).** The fixed-Z γ' CARRIES the
   units bound `0 < c ∧ (Z·Zᵀ − c•1).PosSemidef` (RouteMSJAdm ref:156), and UPDATE-960 P2 lists "units bound
   ∀r" as a KEPT clause. But UPDATE-955 LOCKS the carried set at exactly 6 clauses with the criterion **"a
   clause may be carried IFF z-INDEPENDENT"**, and explicitly DROPS coercivity (z-dependent, fails on
   `{σ_min < ε} ⊂ dom`). A units bound `∀r, Z_tail(r)·Z_tail(r)ᵀ ≽ c·I` over the FULL `R` is FALSE at
   intermediate arity (`r=0` ⟹ `Z_tail=0`; the rank-deficient sublocus is inside `dom` by genuineCarrier). So
   carrying it re-creates the fixed-Z unsatisfiability in a subtler form. Resolution (per the z-independence
   criterion): **DROP the units bound from the carried γ'; #4 DERIVES it at base (Z_tail=I ⟹ `(1−1•1)=0`
   PosSemidef, `c=1`).** This MUST be written into the tide-spec explicitly, or P4 will be built against an
   unsatisfiable clause. (This is precisely the `genuineCarrier`-gives-SPANNING-not-δ≡0 class of conflation
   the charge warns about — support/coercivity are separate from spanning.)
2. **Opaque-width `Fin`-cast quirk** (`lean/CLAUDE.md`): matrix-apply `simp` fires in isolation but "no
   progress" at DEPENDENT non-syntactic widths (`Fin (M 1)`, `Fin (M last)`). Working pattern: prove each entry
   as a `have` at EXPLICIT `⟨_, by decide⟩`/`by omega` indices, then `exact` into the `fin_cases` goal (Fin
   proof-irrelevance unifies). **This is exactly what bit P1** (the `tailProd` + width-2-`=I` + general-L
   `Fin`-casing) — flagged multi-tide-costly, the reason desc4 invoked the escape-valve.
3. **Dependent-matrix reassociation** (`lean/CLAUDE.md`): `rw [Matrix.mul_assoc]`/`simp`/`conv` will NOT match
   `(a*b)*c` through the dependent `HMul`; use a fully-applied `mul_three_reassoc` term. Cast bookkeeping at
   the EQUIV level, never entrywise (`finCongr_refl` → `Matrix.reindex_refl_refl` via `erw`). Peel
   layer-products by prefix/suffix-length induction (`prodAux_succ`), not entrywise. **P1's `tailProd`
   recursion will hit this** — reuse the kernel, don't re-derive.
4. **Heavy-spectral-`def` isDefEq/whnf timeout** (`lean/CLAUDE.md`): not on the #4 base path (no
   eigenvector/eigenvalue term in the base leg — the units bridge is eigenvalue-FREE via sphere-min), but if
   the tide reaches for a spectral form for the units derivation, use the abstract-`Aux`-over-abstract-binding
   form + `rw` (not `unfold`), `rw`-chains (not defeq-heavy `calc`). Prefer `exists_pos_smul_one_le_of_posDef`
   (already spectral-free).
5. **`ρ` must be an `≃`, not a function.** The base's `frobSq (Γ·Z) = Σ_i res_i²` reindex uses
   `Equiv.sum_comp ρ` (RouteMSJBaseHyp `decoratedBaseHyp_faithful` case iii). `WeightedLeafForm` currently has
   `ρ : D.ι → Fin a × Fin Dt` (function) — the P2 clause must upgrade it to `≃` (the ρ-Equiv PRODUCTION
   obligation, also a #5 fidelity requirement per `stephyp-buildplan §6″`).
6. **FLAG-2 `ν`-fixed.** Keep `D.ν = Fin (M 0) × Fin (M last)` (the product index type) fixed under the split;
   record the tail in the split coordinate, do NOT shrink `ν`, else `genuineCarrier` preservation fails.

---

## 6. Dead / ruled-out routes

- **The FIXED-Z γ' shape** (reference branch, RouteMSJAdm:150-159) — #4-sound-as-a-lemma but **#5-UNPRESERVABLE**
  (decorrelated-confirmed, UPDATE-959): fixed `Z` is linear where the deeper product is multilinear; the
  single-block `eΓ` forgets the tail remainder; unsatisfiable at intermediate arity. Kept only as a REFERENCE
  starting point (the corankLeaf core + base-spec to reuse), NOT to commit to canonical.
- **Carrying the units-sector coercivity as an `adm` clause** (UPDATE-948 S1 / UPDATE-955) — z-DEPENDENT
  (fails on the rank-drop sublocus ⊂ dom), CANNOT be carried; per-peel-supplied by the sector cover (#5), not
  #4. This is the pitfall §5.1 in its ruled-out form.
- **The §6/§7 naive-corner / corank-of-Z stratification** (superseded by route-B, `stephyp-buildplan §6″`) —
  the Eckart–Young "single matrix m=1" was a category error; "charges ADD to ½Σ" was units-only. This is #5's
  concern; for #4 it only matters that the base does NOT reach for the naive corner (it uses corankLeaf).
- **`prodAux` / `tailChain` / `prodAux_split_exists` as P1 handles** — ruled out by the Piece-1 probe (prefix
  vs suffix, width-≥3-only, existential-only). P1 is a fresh build.

---

## 7. ★ VERDICT — NARROW DESIGN GAP; pin ONE item by a short pen-and-paper FIRST, then tide-ready

**Not fully tide-ready.** ~90% is pinned (the Γ×R fix is decorrelated-confirmed, the 6 reusable clauses are
locked, the corankLeaf core + base-spec are unchanged and sorry-free, the `WeightedLeafForm` staging is close,
the pitfalls are known-and-flagged). But there is a **narrow, load-bearing design gap** that a short focused
pen-and-paper should close BEFORE the fidelity-critical base tide commits — honoring the disposition
(pen-and-paper before formalising for the base, audited hardest; a green-but-subtly-wrong invariant is the
trap, and this is a SECOND-order repeat of the exact trap that already bit once):

**The gap = the units-bound clause status + the P4 non-vacuity witness (one question, two faces).** The two
banked design statements CONFLICT: UPDATE-955 (units NOT carried, drop + derive-at-base) vs UPDATE-960 P2 /
the fixed-Z reference γ' (units bound "∀r" carried). Carrying it makes the d≥1 γ' UNSATISFIABLE at intermediate
arity (rank-deficient tail sublocus) — the same fixed-Z failure. The correct resolution is clear from the
z-independence criterion (DROP; derive at base), but it must be (a) WRITTEN into the exact γ' clause set, and
(b) VALIDATED by exhibiting the P4 intermediate-arity witness against the DROPPED form — because if a tide
builds P4 against the units-∀r form it will fail, and if it silently keeps units-∀r it lands another
unpreservable invariant. **This is a ~1-page pen-and-paper** (finalize the exact carried clauses; hand-derive
one width-3 witness), not a full design pass — the mechanism is already decorrelated-confirmed.

**Reasoning it is narrow, not a wall:** the analytic engine (corankLeaf, base-spec) is done and unchanged; the
fix (Γ×R) is confirmed; only the CARRIED-clause boundary (which is fidelity-critical) needs pinning + one
witness. If the pen-and-paper confirms "drop units, derive at base, width-3 witness exists" (which the
evidence strongly indicates), the tide is a bounded 4-piece build with known pitfalls.

**Escape hatch:** if the operator prefers to proceed straight to the tide, the tide-spec MUST hard-code
"units bound DROPPED from carried γ', derived at base (Z_tail=I,c=1); P4 witness built against the
units-dropped form" and STOP-flag at the first sign the width-3 γ' is unsatisfiable.

---

## 8. Proposed tide-spec skeleton (build order, named banked pieces per piece)

**Start from `origin/wip/genm-sj4-base-fixedz` (desc4's worktree = least rebuild).** Pieces green-gate in
order; checkpoint-between if degrading.

- **P0 (pen-and-paper, PRE-tide):** finalize the exact carried γ' clause set — resolve units-bound status
  (recommend DROP, derive at base) + exhibit one width-3 intermediate-arity non-vacuity witness on paper.
  Output: a 1-page cert the tide's P2/P4 target off.

- **P1 — `tailProd` infra (fresh, ~40-60 LoC).** New: recursive suffix/segment product `tailProd M A :
  Matrix (Fin (M 1)) (Fin (M last))`, `= 1` at width-2. Reuse the dependent-matrix reassociation kernel
  (`mul_three_reassoc`, `prodAux_succ`-style induction, equiv-level casts). Fin-casts via the `have`+`exact`
  at explicit `⟨_,by decide⟩` pattern (pitfall §5.2/5.3). Green-gate standalone.

- **P2 — γ' rewire (`RouteMSJAdm.FaithfulSJAt`).** Replace the fixed-Z γ' (lines 150-159) with the Γ×R form:
  `eΓ : D.Z ≃ᵐ (Fin a→Fin n→ℝ) × R`, `Z_tail : R → Matrix (Fin n)(Fin Dt)` tied to `tailProd`, `ρ : D.ι ≃
  Fin a × Fin Dt`, `minAdm M ≤ a·n`, provenance `res = rmatMul (Γ z) (Z_tail r) (ρ i)`; R-tie forces
  `R=Unit`/`Z_tail=1` at width-2; **units bound DROPPED** (per P0). KEEP α/β/δ≡0/d=0/genuineCarrier verbatim
  (§2a). Base off `WeightedLeafForm`. Re-prove `genuineCarrier_trivial`, `adm_trivial` (ride d=0, unchanged).

- **P3 — #4(iii) base-spec wiring (`RouteMSJBaseHyp`).** Re-point `decoratedBaseHyp_faithful` case (iii)'s
  `obtain` at the Γ×R γ'; at width-2 specialize `R=Unit`, `Z_tail=1`, `c=1`, `hZ:(1−1•1)=0 PosSemidef`; feed
  `decoratedBase_routeA_of_leafForm (Z:=1)` (VERBATIM) + `decLoss_clean_of_uniformResidualSupport` (δ≡0) +
  `Equiv.sum_comp ρ`. Consumes `corankLeaf_rpow_lt_top` (DONE). Cases (i)/(ii) verbatim.

- **P4 — non-vacuity witness (bedrock).** Commit an in-file `example`/`theorem`: a concrete width-3 decoration
  (e.g. off the rank-1 `(3,3,2,2)→(2,2,2)` regression already in RouteMSJAdm) satisfying the Γ×R + Z_tail(r)
  d≥1 γ' at intermediate arity. Guards against silent vacuity (the fixed-Z trap). Build against the
  units-dropped form (P0/P2).

- **Wire + AxCheck:** import `RouteMSJBaseHyp` into the aggregator; `decoratedBaseHyp_faithful : DecoratedBaseHyp
  adm` green + axiom-clean `[propext, Classical.choice, Quot.sound]`. Hand `adm`/`htriv`/`hbase` to
  `DecoratedDescent` (the driver is done); #5 (DecoratedStepHyp) is the remaining leg.

**Consistency check for the tide:** the z-dependent γ' shape P2 lands MUST be the shape #5's Route B preserves
(same Γ×R split, same `res=(Γ·Z_tail)_ρ`, units per-peel-supplied not carried). Co-audit against
`joint-corner-cert.md` + `stephyp-buildplan §6″` (the ρ-Equiv production + uniform-transversality are #5's,
but the CARRIED γ' is shared).
