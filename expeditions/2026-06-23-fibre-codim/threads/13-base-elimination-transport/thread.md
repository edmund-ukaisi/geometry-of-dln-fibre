# thread 13 — base elimination transport (G2-2 completion, formalisation / tide)

**Type:** formalisation (tide) · the final rung of G2-2 (the localized base presentation). Threads 11+12
banked all the reusable engines; this tide does the reindex + localization transport that assembles them
into the downstream interface. Fully de-risked (no wall; route + Mathlib API confirmed). Fresh tide for
clean context — it's reindex-heavy (~150–200 LoC).

## Read first
- **`threads/12-base-elimination/thread.md`** — the predecessor's PROGRESS LOG + de-risked transport route
  (commit `da4138f2`): the exact reindex chain, `forcedB22`, the localization-transport plan.
- **`threads/11-base-ring-presentation/thread.md`** — the base-codim landed objects + handoff.
- Saved Codex consults: `threads/12-base-elimination/codex/heightJ-*`, `threads/11/codex/*` (encoding).
- **Landed engines you build on (all green, axiom-clean):**
  - `Core/MvPolynomialKerAeval.lean`: `ker_aeval_eq_graphIdeal` (arbitrary ι), `graphIdeal`,
    `graphIdealQuotientEquiv` (`MvPolynomial ι R ⧸ graphIdeal c ≃ₐ[R] R`), `graphIdeal_isPrime [IsDomain R]`.
  - `Core/GraphIdealHeight.lean`: `height_graphIdeal_eq (c : σ → MvPolynomial τ k) : (graphIdeal c).height = Nat.card σ`.
  - `Core/DeterminantalChartRing.lean`: `det_submatrix_multPoly_mem_sigmaIdeal` (the `J ⊆ Iad` seed),
    `detPivotPoly`, `height_map_sigmaIdeal_away_eq_cCodim` (**landed `height Iad = C`**).
  - `Core/DeterminantalBaseElimination.lean` (thread 12 — **the starting handle**): `repCoordReindex`
    (`RepCoord (dStratum q p) ≃ B22block ⊕ SchurVar`, `card_B22block=C`, `card_SchurVar=δ`),
    `blockAlgEquiv` (`A_eng ≃ₐ MvPolynomial B22block (MvPolynomial SchurVar k)`), and the linchpin
    `blockAlgEquiv_detPivot` (`detΔ ↦ C detSchurS` — so localizing `A_eng` at `detΔ` corresponds to
    localizing the `SchurVar` coefficient ring at `detSchurS`). The reindex/detΔ bridge is DONE; this
    tide does the final localization transport + `Iad=J` + the equiv on top of it.
  - `Core/DeterminantalStratumDim.lean`: base domain + `dim = δ`.
- `lean/CLAUDE.md`.

## Goal — expose the minimal downstream interface
For the localized base ring `A_loc = Localization.Away detΔ` of the determinantal base (`dStratum q p`):
1. **`A_loc/Iad ≅ₐ[k] Sd`** (Sd = the free Schur localization `k[Δ,B12,B21]_detΔ`) — the
   downstream-composable object G2-3 consumes.
2. Reuse the **landed `height Iad = C`**.
3. `A_loc` is a domain of dim δ / regular — DERIVE from the equiv (Sd is a poly localization); do not
   materialize a separate regularity object.

**The literal `J` stays INTERNAL** (don't expose it). Prove `Iad = J` (or directly the equiv) as a
private lemma.

## ⚠ CORRECTNESS GUARD (controller, non-negotiable)
`A_loc/Iad ≅ Sd` genuinely requires the HARD direction `Iad ⊆ J` — equivalently the inclusion
`Sd → A_loc/Iad` is **injective** (`Iad ∩ Sd = 0`: no nonzero poly in the Δ,B12,B21 coords vanishes on
the base). The easy `J ⊆ Iad` (the `det_submatrix_multPoly_mem_sigmaIdeal` seed) gives only
**surjectivity**. This hard direction must be **honestly proven**, NOT assumed — shipping the equiv with
it skipped is a silent hole. Two routes (pick the lower-friction PROOF; the content is non-negotiable):
- **(a) height route:** transport `height_graphIdeal_eq` to `height J = C` (the reindex + localization
  transport), then `Iad = J` by `Ideal.height_strict_mono_of_is_prime` (`J ⊆ Iad` + `height J = C` +
  landed `height Iad = C` + both prime ⟹ equal) ⟹ the equiv.
- **(b) injectivity route:** prove `Iad ∩ Sd = 0` directly (algebraic independence of the δ base coords ⟸
  `dim base = δ`, landed).
**If neither route to the hard direction lands cleanly, CHECKPOINT — do not grind/assume it.**

## The transport (the reindex-heavy bulk, per the predecessor's de-risked route)
- `RepCoord (dStratum q p) ≃ B22block ⊕ SchurVar` (renameEquiv + sumAlgEquiv; **orientation trap**: B22block
  outermost; `multPoly (dStratum q p) r c = X ⟨0,(r,c)⟩` so entries ARE coord vars; `detΔ` in the SchurVar block).
- `forcedB22` via `adjugate` (not `inv`). The localized transport via `MvPolynomial.isLocalization` +
  `IsLocalization.height_map_of_disjoint` + the translation automorphism (`X_b ↦ X_b + C(forcedB22 b)`).
- Do NOT use per-index `aeval` (the `dStratum`-Fin `omega` tax) — use `renameEquiv`+`sumAlgEquiv`.

## Do NOT re-explore (dead ends)
Q3 Krull-squeeze (only gives `height J ≤ C`); determinantal-ideal generators (absent at v4.29).

## Process / rules
SPECIFY-first; bank seams; checkpoint if the hard direction or the localization transport walls. Build via
`scripts/lb` from the **worktree** lean dir (`cd /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean`
EXPLICITLY for every call — the default cwd is the MAIN checkout, a different live branch; never `git add -A`).
NEVER bare `lake build`/`cache get`. Zero sorry/axiom/native_decide. `↦`; `decide +kernel`; name=content.
**Core only — never import `DLNFibre.DLN`.** Don't edit the aggregator — report the import line(s).

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` = `[propext, Classical.choice,
Quot.sound]`. Witness: `(2,2,2), r=1` (#B22block = C = 1, #SchurVar = δ = 3). Report to `main`: names +
signatures; green/sorries/axioms; module path(s) + aggregator line(s); v4.29 friction.

## Scope
**G2-2 completion** (the equiv + interface). Then G2-3 (the TOTAL presentation + flatness — the genuine
wall) is the next rung. This closes rung 2 of ~6.

---

## HANDOFF FROM THREAD 12 (2026-06-24) — the landed state + the precise residual

Thread 12 landed FAR more than the original brief assumed: the entire reindex + detΔ-localization
bridge AND the height-transport infra AND `height J = C` AND all four coordinate-image lemmas. On
`origin/expedition/fibre-codimension` HEAD `8ecc821c`, all sorry-free, axiom-clean, aggregated.
**Start from the bordered-minor identity `(*)` — do NOT rebuild any of the below.**

### Complete landed engine set (the fresh tide builds ON these)
- `Core/MvPolynomialKerAeval.lean`: `ker_aeval_eq_graphIdeal` (arbitrary ι), `graphIdeal`,
  `graphIdealQuotientEquiv` (`MvPolynomial ι R ⧸ graphIdeal c ≃ₐ[R] R`), `graphIdeal_isPrime`.
- `Core/GraphIdealHeight.lean`: `height_graphIdeal_eq`, `height_coordIdeal_eq`,
  `height_coordIdeal_localization_eq`, `translateAux` (the translation auto, an `AlgEquiv`),
  `height_graphIdeal_localization_eq` (`(graphIdeal c).height = #σ` for `c : σ → Localization.Away f`).
- `Core/DeterminantalBaseElimination.lean`: `B22block`/`SchurVar` (+`card_*` = C/δ); `finSplit`
  (+`_castLE`/`_natAdd`); `repCoordReindex` + the FOUR coordinate-image lemmas
  `repCoordReindex_{pivot,b22,b12,b21}`; `mult_stratum_eq`/`multPoly_stratum_apply`
  (`multPoly (dStratum q p) a b = X ⟨0,(a,b)⟩`); `detSchurS` (+`_ne_zero`); `renameEquiv_detPivot`;
  `blockAlgEquiv` (`A_eng ≃ₐ MvPolynomial B22block (MvPolynomial SchurVar k)`) + `blockAlgEquiv_detPivot`
  (`detΔ ↦ C detSchurS`); `forcedNum` (`B21·adjΔ·B12`, adjugate); `forcedB22` (= `forcedNum/detSchurS`
  via `IsLocalization.mk'`); **`height_graphIdeal_forcedB22_eq`** (`height (graphIdeal forcedB22) =
  (p−r)(q−r) = C`).
- `Core/DeterminantalChartRing.lean` (predecessor): `det_fromBlocks_scalar_eq` (the bordered Schur
  minor identity over any CommRing), `det_submatrix_multPoly_mem_sigmaIdeal` (`(r+1)`-minor ∈
  sigmaIdeal), `height_map_sigmaIdeal_away_eq_cCodim` (**`height Iad = C`**).

### The localized AlgEquiv `Ψ` (SPECIFY-confirmed; typechecks)
`Ψ : Localization.Away detΔ ≃ₐ[k] Localization.Away (C detSchurS)` :=
`IsLocalization.algEquivOfAlgEquiv _ _ (blockAlgEquiv q p r hp hq) hmap` where
`hmap : Submonoid.map blockAlgEquiv.toAlgHom (powers detΔ) = powers (C detSchurS)` is
`Submonoid.map_powers` + `blockAlgEquiv_detPivot` (`congr 1; exact blockAlgEquiv_detPivot …`).
`MvPolynomial.isLocalization` identifies `Localization.Away (C detSchurS)` with `MvPolynomial B22block Sd`.

### The residual — (1) DONE; (2) the careful step; (3) mechanical
**(1) `height J = C`** — DONE (`height_graphIdeal_forcedB22_eq`).

**(2) `J ⊆ Ψ(Iad)` — the friction-heavy, CONTENT-CARRYING step (the correctness-guard seed; be
careful).** Forward route (`Ideal.mem_map_of_mem`). The spine is the **bordered-minor identity** `(*)`:
`blockAlgEquiv (minorPoly_ab) = C detSchurS · X_{ab} − C (forcedNum_{ab})`, where `minorPoly_ab` =
the bordered `(r+1)`-minor of `multPoly` at (pivot rows ∪ {row `cast (natAdd r a)`}, pivot cols ∪
{col `cast (natAdd r b)`}). Prove `(*)` via `AlgHom.map_det` + `det_fromBlocks_scalar_eq` (LANDED) +
the four `repCoordReindex_*` coordinate lemmas (the entries map to coord/SchurVar vars); the
`Fin r ⊕ Unit ≃ Fin (r+1)` reindex via `det_submatrix_equiv_self` + `submatrix_submatrix` (the exact
pattern is in `schur_expr_eq_zero_of_rank_le`). `minorPoly_ab ∈ sigmaIdeal` is LANDED
`det_submatrix_multPoly_mem_sigmaIdeal` ⟹ its `A_loc`-image ∈ `Iad` ⟹ `Ψ` of it ∈ `Ψ(Iad)`.
**Unit-divide:** `C detSchurS` is a unit in `MvPolynomial B22block Sd`
(`IsLocalization.Away.algebraMap_isUnit` + `RingHom.isUnit_map C`); `forcedNum = detSchurS · forcedB22`
by `IsLocalization.mk'_spec'`; so `(*) = C detSchurS · (X_{ab} − C(forcedB22 ab))`, and
`Ideal.unit_mul_mem_iff_mem` ⟹ `X_{ab} − C(forcedB22 ab) ∈ Ψ(Iad)` ⟹ `J ⊆ Ψ(Iad)`.
Codex consult with the full recipe: `../12-base-elimination/codex/inclusion-answer.md`.

**(3) `Iad = J` + the equiv — mechanical.** `K := Iad.map (Ψ : … →+* …)`; `height K = height Iad = C`
(`height_map_algEquiv Ψ Iad`); `K` prime (`Ideal.map_isPrime_of_equiv Ψ`). Squeeze: `le_antisymm`
(J ⊆ K from (2)) + `Ideal.height_strict_mono_of_is_prime` (rules out `J ⊊ K`: `height J = C =
height K`) ⟹ `K = J`. Equiv: `Ideal.quotientEquivAlg Iad J Ψ hKJ.symm : A_loc ⧸ Iad ≃ₐ[k] T ⧸ J`,
then `(graphIdealQuotientEquiv forcedB22).restrictScalars k : T ⧸ J ≃ₐ[k] Sd`; compose.
{domain, dim δ} derive from the equiv. Codex Q4 chain in `inclusion-answer.md`.

**Interface (controller, settled):** expose ONLY `A_loc/Iad ≅ₐ[k] Sd` + reuse landed `height Iad = C`;
`J` internal. **Guard:** the `Iad ⊆ J` hard direction is earned by (2)+(3)'s squeeze (load-bearing,
not assumed — `height J = C` is the discharge).

**Note for the operator:** two tracked scratch files `Core/{FlatTrivialProductProbe,ChartFlatnessProbe}.lean`
exist (NOT thread 12's — likely a G2-3 flatness probe); worth pruning if abandoned.
