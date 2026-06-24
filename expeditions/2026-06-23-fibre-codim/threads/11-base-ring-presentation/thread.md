# thread 11 — localized base ring presentation (G2-2, formalisation / tide)

**Type:** formalisation (tide) · `OPENED → SPECIFY/DESIGN → CHECKPOINT(no-skip) → PROVE → AUDIT`.
The next rung of the determinantal-presentation build. G2-1 landed the matrix-level Schur relation
(`Core.DeterminantalChart`); this rung lifts the **base** to an explicit *coordinate-ring* presentation
on the pivot chart — the prerequisite for the Schur `AlgEquiv` (G2-3, the wall).

## Read first — the controller's ring-level architecture
`expeditions/2026-06-23-fibre-codim/synthesis.md` § "RING-LEVEL ARCHITECTURE for G2-2..G2-4" — the full
height-composition the chain rests on (catenary `codim_Rep(fibre)=C+codim_{Σ̄^r}(fibre)`; height-additivity
`height P = height(m_E)+0 = δ` on the descended comorphism `R_base→R_total`, going-down only on the chart).
**Part of your job at the checkpoint is to Codex-vet that whole composition** before we commit the chain.

## Goal (a new `Core` module — e.g. `DeterminantalChartRing.lean`)
Present the **localized base coordinate ring** explicitly. The base is `Mat^{rk≤r} ⊆ Mat (Fin p)(Fin q) k`,
coordinate ring `R_base = MvPolynomial (Fin p × Fin q) k ⧸ vanishingIdeal(Mat^{rk≤r})`. On the pivot chart
(localize at `det Δ`, the top-left r×r minor), G2-1's Schur relation `B22 = B21·Δ⁻¹·B12` forces the
bottom-right block, so:

> `R_base` localized at `det Δ`  ≅  `k[Δ entries, B12, B21][ (det Δ)⁻¹ ]`  (free Schur coordinates).

Deliverables (priority order; checkpoint before grinding the hardest):
1. **The determinantal ideal fact:** `vanishingIdeal(Mat^{rk≤r}) = ` the ideal of `(r+1)`-minors (prime;
   the radical/vanishing ideal over alg-closed `k`). **Probe Mathlib first** — `Matrix.det`/minor ideals,
   `RingTheory.MvPolynomial`/determinantal-variety content; this may be partly present or may need building.
2. **The localized presentation:** `R_base,loc[det Δ⁻¹] ≅ₐ` the explicit Schur polynomial localization.
3. **Base facts for G2-4:** `R_base` is a domain (irreducible determinantal variety), `dim R_base = δ`
   (tie to the thermometer `DeterminantalStratumDim`), and `height(m_E) = δ` for `E` a closed point.

## SPECIFY/DESIGN-first — no-skip checkpoint
1. SPECIFY: pin the localized-presentation statement + the determinantal-ideal handle; probe the Mathlib
   determinantal-ideal + `Localization.Away` + `MvPolynomial`-quotient API with `example` blocks.
   **Fire a decorrelated `local-codex-consult`** (authenticated, xhigh) on BOTH (a) the localized base
   presentation and (b) the full ring-level composition in the synthesis architecture (sanity-check it
   before the chain commits); save under `threads/11-base-ring-presentation/codex/`.
2. **CHECKPOINT — report to `main`**: the determinantal-ideal reachability, the localized-presentation
   plan, the Codex verdict on the full composition, and a GO/NO-GO. If the determinantal ideal or the
   localized presentation needs machinery absent at v4.29 (this is a real risk — determinantal ideals are
   deep), STOP and report precisely. A wall here is important signal (it may mean the whole chart route
   needs a different presentation strategy). Do NOT grind / do NOT sorry / do NOT weaken.
3. PROVE → AUDIT.

## Hard rules (lean/CLAUDE.md)
Build via `scripts/lb` (NEVER bare `lake build`/`lake exe cache get`). Zero sorry/axiom/native_decide/#exit.
`↦`; `decide +kernel`; one-line docstrings; name=content. **Core only — never import `DLNFibre.DLN`.** Do
NOT edit the aggregator — report the import line. Confirm Mathlib lemmas exist before building on them.
Don't touch other worktrees or any stash. In-repo memory only.

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` on headlines = `[propext,
Classical.choice, Quot.sound]`. Witness: the `(2,2,2), r=1` base chart.

## Scope
**Just G2-2** (the localized base ring presentation + the base facts for G2-4 + the composition Codex-vet).
G2-3 (total + Schur AlgEquiv + flatness), G2-4, G2-5, G3/G4 are later. Report to `main`: theorem names +
signatures; green/sorries/axioms; module path + aggregator line; the determinantal-ideal Mathlib status;
the decorrelated-Codex read (incl. the composition sanity-check); v4.29 friction. Commit when green.

---

## PROGRESS LOG (formaliser)

### Sub-rung 1 — bordered Schur minor foundation. **LANDED** (commit `eec3f774`, aggregated `9e7ce92c`).
`DLNFibre.Core.DeterminantalChartRing`:
- `det_fromBlocks_scalar_eq` — `det[[Δ,u],[v,d]] = d·detΔ − v·adjΔ·u` over any CommRing (universal-coefficient route).
- `schur_expr_eq_zero_of_rank_le` — the Schur expression is an (r+1)-minor, vanishes on `Mat^{rk≤r}`.
Sorry-free, axiom-clean. Statement card written. The generator-free handle replacing determinantal-ideal theory.

### Sub-rung 2 step (a) — lift to the base ideal. **LANDED** (commit `ccaab34d`, pushed).
- `eval_det_submatrix_multPoly` — `eval(canonicalCoord A)` of a minor of the generic product `multPoly d` = the minor of `mult d A`.
- `det_submatrix_multPoly_mem_sigmaIdeal` — that `(r+1)`-minor ∈ `sigmaIdeal d r`. General in N. Uses the engine's `eval_multPoly` bridge (sidesteps the `mult = A 0` dependent-Fin wall). Sorry-free, axiom-clean.

### Sub-rung 2 steps (b)–(e) — the localized presentation proper. **SPECIFY done, GRIND not started (checkpoint).**
Validated (SPECIFY probes, all type-check):
- `detPivotPoly` (top-left r×r minor of `multPoly (dStratum q p)`), `Localization.Away`, the `IsLocalization.Away` instance, the localized base ideal `Iad = sigmaIdeal.map (algebraMap)`.
- **`height Iad = C` is the EASY half**: `IsLocalization.height_map_of_disjoint` + engine `height sigmaIdeal = C` (Brick A) + `sigmaIdeal` prime (`isPrime_vanishingIdeal_productRankLocusLE_stratum`). Needs `detΔ ∉ sigmaIdeal` (a witness: a rank-≤r matrix with invertible top-left block, e.g. the realizer `diag(I_r,0)`).
- **The `J` side (`Iad = J` + `AlgEquiv` + `height J = C`) is the bulk**: the genuinely-large construction. `height J = C` follows from the explicit presentation `Ad/J ≅ free Schur localization` (Codex's reindex dodge); the `AlgEquiv` (direction-B comorphism + explicit inverse) is the load-bearing build.

Banked two hole-free seams; checkpointing before opening the large `AlgEquiv` construction. The composition stays on the height-additivity architecture (engine has `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`).

### Sub-rung 2 step (b₀) — `height Iad = C`. **LANDED** (commit `a6bd7c25`, pushed).
The localized base ideal has the same height as the base ideal (= C), via localization-height
transport at the pivot minor + the realizer witness `diag(I_r,0)`:
- `detPivotPoly`, `chartWitness` (+ `mult_chartWitness`, `rank_chartWitness_le`, `chartWitness_mem`),
  `mult_chartWitness_pivot_submatrix`, `detPivot_chartWitness`, `detPivotPoly_notMem_sigmaIdeal`,
  `height_map_sigmaIdeal_away` (= height sigmaIdeal), `height_map_sigmaIdeal_away_eq_cCodim` (= cCodim = C).
- Generalised `eval_det_submatrix_multPoly` to any minor index type `ι`.
All sorry-free, axiom-clean. The EASY half of `Iad = J`; feeds the G2-4 height-additivity chain.
Friction resolved: the `mult = A 0` dependent-`Fin` wall (the `Fin.last 1` vs `Fin.succ 0` codomain
mismatch) — solved by stating the witness helper about `mult ... submatrix` directly (not `A 0`).

### NEXT — step (b)-(e): the graph-ideal elimination. **NOT started.**
Per controller Q2: `J` = graph ideal of `B22 = Schur/detΔ`; eliminate B22 ⟹ `Ad/J ≅ k[Δ,B12,B21]_detΔ`,
`height J = #(B22 vars) = C` falls out. Expose facts `{Iad = J, A_loc regular dim δ}`, not a bundled
`AlgEquiv`. (i) ψ + `J ⊆ Iad` (≈done from step a); (ii) elimination iso; (iii) `Iad = J` by height
comparison (uses landed `height Iad = C` + (ii)'s `height J = C`). The genuine remaining bulk.

### Step (ii) the elimination — DE-RISKED, concrete route (Codex elimination consult, saved).
Q3 squeeze (Krull `height ≤ #gens` to collapse `Iad=J` without the iso) **FAILS** — Krull only gives
the upper bound `height J ≤ C`, and `J ⊆ Iad` gives the same direction; no lower bound, no squeeze.
So the full iso is genuinely needed for `height J = C`. The Codex-validated lowest-friction route:
1. **`ker_aeval_eq_graphIdeal`** (reusable, new): `ker (aeval c : MvPolynomial ι R →ₐ R) = span (range
   fun i ↦ X i − C (c i))`, `[Finite ι]`. By `Finite.induction_empty_option` + `optionEquivLeft` +
   `Polynomial.ker_evalRingHom`. The easy `⊇` is done (probe); the `⊆` is the induction (the meat).
   ⟹ `J` prime (`RingHom.ker_isPrime`, needs `IsDomain Sd`) + `MvPolynomial B22 Sd / J ≅ₐ Sd`
   (`quotientKerAlgEquivOfSurjective`, surjective onto constants).
2. **Block relabeling** (NOT per-index aeval — the `dStratum`-Fin `omega` tax is real): `Equiv.uniqueSigma`
   (drop `Σ_:Fin 1`), `finCongr`+`finSumFinEquiv.symm`, `Equiv.prodCongr`/`sumProdDistrib`/`prodSumDistrib`/
   `sumAssoc`/`sumComm`, then `renameEquiv` + `sumAlgEquiv` (orientation: make the sum `B22 ⊕ SchurVar`).
3. `height J = #B22 = (p−r)(q−r) = C` from the iso (poly bridge / `MvPolynomial.ringKrullDim`).
4. `Iad = J` by `le_antisymm hJI` + `by_contra` + `Ideal.height_strict_mono_of_is_prime` (uses landed
   `height Iad = C` + step-3 `height J = C`).
5. Regularity `A_loc/Iad ≅ Sd` ⟹ regular dim δ: `IsRegularLocalRing` (no global API) via
   `Localization.AtPrime` + `IsLocalization.AtPrime.ringKrullDim_eq_height` + `MvPolynomial.ringKrullDim`.
Mathlib lemmas all confirmed present. `ker_aeval_eq_graphIdeal`'s `⊆`-induction is the genuine bulk.

---

## CLOSEOUT (thread 11) — 2026-06-24

**Status: CLOSED.** The base-codimension content of G2-2 is landed (sorry-free, axiom-clean,
aggregated, pushed). The localized graph-ideal elimination is split off to a **fresh tide** (handoff
below) — it is ≈ all three banked seams combined and the most reindex-heavy, so it deserves clean
context.

### Landed (all in `lean/DLNFibre/Core/DeterminantalChartRing.lean`, on `origin/expedition/fibre-codimension`)
| Seam | Headline theorem(s) | Commit |
|---|---|---|
| Bordered Schur minor | `det_fromBlocks_scalar_eq` (`BorderedId`; + `borderedId_of_det_ne_zero`, `borderedId_map`, `borderedId_of_map`); `schur_expr_eq_zero_of_rank_le` | `9e7ce92c` (aggregated) |
| `(r+1)`-minor lift | `eval_det_submatrix_multPoly`, `det_submatrix_multPoly_mem_sigmaIdeal` | `ccaab34d` |
| `height Iad = C` | `detPivotPoly`, `chartWitness` (+`mult_chartWitness`, `rank_chartWitness_le`, `chartWitness_mem`, `mult_chartWitness_pivot_submatrix`, `detPivot_chartWitness`), `detPivotPoly_notMem_sigmaIdeal`, `height_map_sigmaIdeal_away`, `height_map_sigmaIdeal_away_eq_cCodim` | `a6bd7c25` |
| Elimination de-risk + Codex consult (docs) | — | `91ac8eaf` (HEAD) |

Statement card: `threads/11-base-ring-presentation/statement-card.md` (sub-rung 1; status sorry-free,
awaiting reviewer fidelity read). Codex artefacts: `codex/g2-2-{,encoding-,elimination-}{prompt,answer}.md`.

---

## HANDOFF → fresh elimination tide (G2-2 step ii): `Iad = J` + `A_loc/Iad ≅ Sd` (regular, dim δ)

**Goal.** Expose, on the pivot chart, the facts `{Iad = J, A_loc/Iad regular of dim δ}` for the
localized determinantal base — feeding the G2-3 total presentation / G2-4 height-additivity chain.
Build on `DeterminantalChartRing` (Core only; never import `DLNFibre.DLN`). `δ = r(p+q−r)`, `C = (p−r)(q−r)`.

**Objects (landed, ready to use).**
- `A_eng := MvPolynomial (RepCoord (dStratum q p)) k` (`RepCoord (dStratum q p) = Σ _ : Fin 1, Fin p × Fin q`).
- `detPivotPoly q p r hp hq : A_eng` — the pivot minor `detΔ` (top-left r×r det of `multPoly`).
- `A_loc := Localization.Away (detPivotPoly …)`; `Iad := (sigmaIdeal (dStratum q p) r).map (algebraMap A_eng A_loc)`.
- **`height Iad = C`** is LANDED: `height_map_sigmaIdeal_away_eq_cCodim` (= `cCodim`, which is `C`).
- `det_submatrix_multPoly_mem_sigmaIdeal` — every `(r+1)`-minor of `multPoly` ∈ `sigmaIdeal` (the `J ⊆ Iad` seed).
- `sigmaIdeal (dStratum q p) r` and `Iad` are PRIME (`isPrime_vanishingIdeal_productRankLocusLE_stratum`, `[IsAlgClosed k]`; for `Iad`, localize a prime not meeting the monoid).

**Step 1 — the reusable graph-ideal kernel lemma `ker_aeval_eq_graphIdeal` (the genuinely-new core).**
`ker (aeval c : MvPolynomial ι R →ₐ[R] R) = Ideal.span (Set.range fun i ↦ X i − C (c i))`, `[Finite ι]`.
- Easy `⊇` is DONE (probe): `Ideal.span_le` + `simp [RingHom.mem_ker]`.
- `⊆` is the induction: `Finite.induction_empty_option`. **Universe caveat:** the base case uses
  `PEmpty : Type (u+1)`; state the predicate carefully (`P : ∀ (α) [Fintype α], Prop`, with `c` quantified
  inside) and watch universes. `Option` step: `MvPolynomial.optionEquivLeft` turns `MvPolynomial (Option α)`
  into `Polynomial (MvPolynomial α)`; peel the `none` variable via `Polynomial.ker_evalRingHom`
  (`= span {X − C x}`, in `RingTheory/Polynomial/Ideal.lean`) and the `some` variables via the IH.
  Confirmed API: `MvPolynomial.isEmptyAlgEquiv`, `optionEquivLeft`/`_X_some`/`_X_none`/`_C`,
  `Polynomial.ker_evalRingHom`, `Finite.induction_empty_option`. ~60-100 LoC; the long pole.
- Best as its own small module `Core/MvPolynomialGraphIdeal.lean` (reusable, pure MvPolynomial, no DLN/RepCoord).
- Consequences: `J` prime via `RingHom.ker_isPrime (aeval …)` (needs `IsDomain` of the base — for `Sd`
  use `IsLocalization.isDomain_of_le_nonZeroDivisors` + `powers_le_nonZeroDivisors_of_noZeroDivisors`
  + `detΔS ≠ 0` which is `det_mvPolynomialX`-style nonzero); and the quotient iso
  `MvPolynomial B22block Sd / J ≅ₐ Sd` via `quotientKerAlgEquivOfSurjective` (surjective onto constants:
  `fun y ↦ ⟨C y, by simp⟩`) + `Ideal.quotientEquivAlgOfEq (ker_aeval_eq_graphIdeal …).symm`.

**Step 2 — block relabeling (use this, NOT a per-index `aeval psiGen`).** The per-index classifier pays
the `dStratum q p (Fin.castSucc 0) = q` / `omega` tax repeatedly (it is `rfl` but does not flow into
`omega`). Instead relabel once. The decomposition equiv ASSEMBLES (verified in SPECIFY):
- `Fin p ≃ Fin r ⊕ Fin (p−r)` := `(finCongr (by omega : p = r + (p−r))).trans finSumFinEquiv.symm`;
  same for `Fin q`.
- `Fin p × Fin q ≃ ((Fin r×Fin r)⊕(Fin r×Fin(q−r)))⊕((Fin(p−r)×Fin r)⊕(Fin(p−r)×Fin(q−r)))`
  := `Equiv.sumProdDistrib _ _ _ |>.trans (Equiv.sumCongr (Equiv.prodSumDistrib …) (Equiv.prodSumDistrib …))`
  (precompose `Equiv.prodCongr` of the two `Fin` splits).
- Drop the `Σ _ : Fin 1` with `Equiv.uniqueSigma`; reassociate/commute (`Equiv.sumAssoc`/`sumComm`) so the
  final sum is **`B22block ⊕ SchurVar`** (orientation trap: `MvPolynomial.sumAlgEquiv R S₁ S₂` gives
  `MvPolynomial (S₁ ⊕ S₂) R ≃ₐ MvPolynomial S₁ (MvPolynomial S₂ R)` with `S₁` the OUTER block — so
  `S₁ = B22block` to put B22 outermost for elimination).
- `MvPolynomial.renameEquiv` (relabel `RepCoord` ≃ `B22block ⊕ SchurVar`) then `MvPolynomial.sumAlgEquiv`
  ⟹ `A_eng ≃ₐ MvPolynomial B22block (MvPolynomial SchurVar k)`. Localize at `detΔ` ⟹ work over `Sd`.
- `SchurVar := (Fin r×Fin r)⊕(Fin r×Fin(q−r))⊕(Fin(p−r)×Fin r)` (the free Δ,B12,B21 coords);
  `Sd := Localization.Away (detΔS)` where `ΔS i j := X (Sum.inl (i,j))`. The forced B22 value is
  `forcedB22 a b := algebraMap _ Sd ((B21S * (ΔS).adjugate * B12S) a b) * IsLocalization.Away.invSelf detΔS`
  — use `Matrix.adjugate` (NOT `Matrix.inv`); confirmed to typecheck.

**Step 3 — `height J = C`.** From `MvPolynomial B22block Sd / J ≅ Sd` + the poly/localization dimension
bridge: `height J = (#A_eng vars) − δ = pq − δ = C`. Use `MvPolynomial.ringKrullDim_of_isNoetherianRing`
(reindex `SchurVar ≃ Fin δ`) + the localization-height tools. (The landed `varietyDim_…_stratum` gives
`dim base = δ` already, if useful as a cross-check.)

**Step 4 — `Iad = J`.** `J ⊆ Iad` from `det_submatrix_multPoly_mem_sigmaIdeal` (the Schur entries are
localized `(r+1)`-minors), transported through the relabel/localization equivs. Then:
`le_antisymm hJI` + `by_contra hnot` ⟹ `J < Iad` ⟹ `Ideal.height_strict_mono_of_is_prime` gives
`height J < height Iad`, but both `= C` (landed `height Iad = C` + step 3) — contradiction.

**Step 5 — regularity / dim δ.** `A_loc/Iad ≅ₐ Sd` (from step 4 + the quotient iso) ⟹ regular of dim δ.
Mathlib has `IsRegularLocalRing` but no robust global `IsRegularRing`; expose locally: for each maximal
`m` of `A_loc/Iad`, `Localization.AtPrime m` is regular of dim δ. API: `IsLocalization.AtPrime.ringKrullDim_eq_height`,
`IsLocalization.height_map_of_disjoint`, `IsLocalization.isMaximal_iff_isMaximal_disjoint`,
`MvPolynomial.ringKrullDim_of_isNoetherianRing` (reindex `SchurVar ≃ Fin δ`). [If G2-3/G2-4 only need
the smooth/free presentation rather than literal regularity, exposing `A_loc/Iad ≅ Sd` may suffice —
confirm with the controller against the G2-3 spec.]

**Witness throughout:** the `(2,2,2), r = 1` base chart (`q=p=2, r=1`: `δ=3`, `C=1`).
**Codex consults to read:** `codex/g2-2-encoding-answer.md` (direction-B, explicit-inverse) and
`codex/g2-2-elimination-answer.md` (the route above, incl. the Q3-squeeze refutation). All Mathlib
lemma names in this handoff were grep-confirmed present at the v4.29 pin.
