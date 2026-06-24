# thread 12 — base ring elimination (G2-2 completion, formalisation / tide)

**Type:** formalisation (tide) · `OPENED → (land ker_aeval) → (elimination) → AUDIT`. Completes G2-2:
the localized base coordinate ring presentation. Thread 11 banked the base-**codimension** content
(3 seams: bordered-minor identity, the `(r+1)`-minor lift, `height Iad = C`); this tide builds the
localized graph-ideal **elimination** → `Iad = J` + `A_loc regular of dim δ`. Fully de-risked by
thread 11 (no wall; the route + all Mathlib API confirmed). Fresh tide for clean context — the
elimination is large + reindex-heavy.

## Read first
- **`expeditions/2026-06-23-fibre-codim/threads/11-base-ring-presentation/thread.md`** — the parent
  thread; its PROGRESS LOG has the validated decomposition plan + the banked seams.
- **The saved Codex consults** `threads/11-base-ring-presentation/codex/g2-2-elimination-{prompt,answer}.md`
  + `g2-2-encoding-{prompt,answer}.md` — the validated elimination architecture.
- `Core/DeterminantalChartRing.lean` (thread 11's module: `det_fromBlocks_scalar_eq`,
  `det_submatrix_multPoly_mem_sigmaIdeal`, `detPivotPoly`, `height_map_sigmaIdeal_away_eq_cCodim`).
- `Core/DeterminantalStratumDim.lean` (`isPrime_…`/`varietyDim_…=δ` — `A_loc` domain + dim δ engine-landed).
- `lean/CLAUDE.md` (zero sorry/axiom/native_decide; `decide +kernel`; `↦`; name=content; bedrock).

## Deliverable 1 (FIRST, self-contained, reusable) — `ker_aeval_eq_graphIdeal`
New module `Core/MvPolynomialKerAeval.lean`. The general missing-from-Mathlib fact:

> `ker (aeval c : MvPolynomial ι R →ₐ[R] R) = Ideal.span (Set.range fun i ↦ X i − C (c i))`  (`[Finite ι]`).

- `⊇` is easy (each `X i − C (c i) ∈ ker`; probe-confirmed in thread 11).
- `⊆` is the induction: `Finite.induction_empty_option` + `optionEquivLeft` + `Polynomial.ker_evalRingHom`.
  **Thread 11 hit universe friction at the base case** (`PEmpty : Type (u+1)` vs `Type u`) + the
  intricate `Option`-step kernel transport — it's a genuine ~60–100 LoC build. **Likely fix:** dodge the
  universe-crossing by working through `Fin n` + an `Equiv` (`Fintype.equivFin`), or `ULift`, or handle
  the empty case via `MvPolynomial.isEmptyRingEquiv`. This is the genuine bulk; land it as a clean
  standalone seam first.

## Deliverable 2 — the localized base presentation → `Iad = J` + `A_loc regular dim δ`
(In `DeterminantalChartRing` or a new presentation module.) Using Deliverable 1:
1. **Block reindex** `RepCoord (dStratum q p) ≃ B22block ⊕ rest`: `finCongr` + `finSumFinEquiv` give
   `Fin p ≃ Fin r ⊕ Fin (p−r)`; `Equiv.sumProdDistrib`/`prodSumDistrib` give the 4-way block split;
   `MvPolynomial.renameEquiv` + `sumAlgEquiv` isolate the B22 variables. (Use `renameEquiv`+`sumAlgEquiv`,
   NOT per-index `aeval` — the `dStratum`-Fin `omega` tax is real, per thread 11 + Codex.)
2. **The elimination** `Ad/J ≅ k[Δ,B12,B21]_detΔ` (free Schur localization): `J` = graph ideal of
   `B22 = (Schur expr)/detΔ`; via Deliverable 1, `J` is the kernel of the `aeval` sending each B22
   variable to its forced value, so `Ad/J ≅` (the rest) — eliminating the B22 vars.
3. `height J = C` from the iso (poly bridge: `height J = #vars − dim(Ad/J) = #(B22 vars) = (p−r)(q−r) = C`);
   `J` prime (kernel of a map to a domain).
4. **`Iad = J`** by height comparison: `J ⊆ Iad` (≈ from thread 11's `det_submatrix_multPoly_mem_sigmaIdeal`,
   mapped to the localization) + `height J = C` + `height Iad = C` (LANDED, thread 11) + both prime ⟹ equal
   (`Ideal.height_strict_mono_of_is_prime` rules out `J ⊊ Iad`).
5. **`A_loc regular of dim δ`** (`A_loc = Ad/Iad = Ad/J ≅` free Schur localization, regular).

**Expose the FACTS `{Iad = J, A_loc regular of dim δ}`** (the minimal downstream interface for G2-3/G2-4) —
a fully-bundled `AlgEquiv` term is optional if exposing the facts directly is lower friction.

## Do NOT re-explore (dead ends, thread 11 + Codex)
- The **Q3 Krull-squeeze** (collapse `Iad = J` without the iso) FAILS: `Ideal.height_le_spanFinrank`
  gives only `height J ≤ C`, the same direction as `J ⊆ Iad` — no lower bound. The elimination iso is
  genuinely needed for `height J = C`.
- Determinantal-ideal generating-set theory is absent at v4.29 — the generator-free Schur-graph route
  (thread 11) is the way; do not attempt determinantal generators.

## Process / rules
SPECIFY-first; bank hole-free seams (land Deliverable 1 standalone first); checkpoint to `main` if the
elimination iso or the localization bookkeeping walls. Build via `scripts/lb` (NEVER bare `lake
build`/`cache get`). Zero sorry/axiom/native_decide. `↦`; `decide +kernel`; name=content. **Core only —
never import `DLNFibre.DLN`.** Don't edit the aggregator — report the import line(s). Don't touch other
worktrees/stash. In-repo memory only.

## AUDIT gate
`scripts/lb` whole-library green; `scripts/sorries` 0; `#print axioms` on headlines = `[propext,
Classical.choice, Quot.sound]`. Witness: `(2,2,2), r=1`. Report to `main`: names + signatures;
green/sorries/axioms; module path(s) + aggregator line(s); v4.29 friction for the gotchas log.

## Scope
**G2-2 completion** (Deliverables 1 + 2). G2-3 (the TOTAL presentation + flatness — the genuine wall),
G2-4, G2-5, G3/G4 are later tides.

---

## PROGRESS LOG (tide G2-2b)

### Deliverable 1 — `ker_aeval_eq_graphIdeal`. **LANDED** (commit `e4b85042`).
`Core/MvPolynomialKerAeval.lean`. `RingHom.ker (aeval c).toRingHom = graphIdeal c` for an
**arbitrary** index type `ι` (NO `Finite`/`Fintype`). Dodged the predecessor's universe friction:
instead of `Finite.induction_empty_option`+`optionEquivLeft`, used the **translation identity**
`p − C (aeval c p) ∈ graphIdeal c` proved by `MvPolynomial.induction_on` (mul_X step:
`p·Xᵢ − C(v·cᵢ) = p·(Xᵢ − C cᵢ) + (p − C v)·C cᵢ`). Exposed: `graphIdeal`, `graphIdealQuotientEquiv`
(`MvPolynomial ι R ⧸ graphIdeal c ≃ₐ[R] R`, the elimination), `graphIdeal_isPrime [IsDomain R]`,
`aeval_surjective`. Sorry-free, axiom-clean.

### `height_graphIdeal_eq` (the `height J ≥ C` engine). **LANDED** (commit `096291ba`).
`Core/GraphIdealHeight.lean`. `(graphIdeal c).height = Nat.card σ` for `c : σ → MvPolynomial τ k`
(`k` field, `σ τ` finite): the block graph ideal eliminating the `σ`-block of
`MvPolynomial σ (MvPolynomial τ k)` has height `#σ`. Via the LANDED field catenary
`height_add_ringKrullDim_quotient_eq_card` on `MvPolynomial (σ ⊕ τ) k` (sumAlgEquiv) + quotient dim
`#τ` (Deliverable 1) ⟹ `height = (#σ+#τ) − #τ = #σ`. Avoids the localization-preserves-dimension
subtlety. Sorry-free, axiom-clean. Codex consult saved: `codex/heightJ-{prompt,answer}.md` (picked
this coordinate-ideal/catenary route over routes A/B).

### NEXT — the localized transport (the reindex-heavy bulk). **IN PROGRESS / awaiting interface decision.**
To reach `height J = C` for `J ⊆ A_loc = Localization.Away detΔ`: (a) the `RepCoord (dStratum q p)
≃ B22block ⊕ SchurVar` reindex (renameEquiv + sumAlgEquiv; `multPoly (dStratum q p) r c = X ⟨0,(r,c)⟩`
so the entries ARE the coordinate vars — `detΔ` lives in the SchurVar block); (b) localization
transport of `height_graphIdeal_eq` from the field ring to the `Sd`-based ring. Then `Iad = J` by
`height_strict_mono_of_is_prime` (cheap: landed `height Iad = C` + `height J = C`) + regularity.
Interface question to controller (re-asked): expose literal `J ⊆ A_loc`, or just `A_loc/Iad ≅ Sd`
(regular dim δ)? The latter halves the transport bookkeeping.

**Route DE-RISKED (probes typecheck, no wall — just sizable):**
- The reindex components assemble: `Fin p ≃ Fin r ⊕ Fin (p−r)` via `(finCongr ..).trans
  finSumFinEquiv.symm`; same for `q`.
- `multPoly (dStratum q p) r c = X ⟨0,(r,c)⟩` (the `mult = A 0` reduction at `N=1`), so the generic
  product entries ARE the `RepCoord` coordinate vars — `detΔ` lives purely in the `Δ ⊆ SchurVar`
  block, and the reindex is a pure relabelling.
- **Translation automorphism** `translateAux c := aeval (fun b ↦ X b + C (c b))` is an
  `AlgEquiv` (inverse = `translateAux (−c)`; `comp = id` both ways by `MvPolynomial.algHom_ext`), and
  `(span {X b}).map (translateAux (−c)) = graphIdeal c` (by `Ideal.map_span` + the `aeval_X` rewrite).
  ⟹ `height (graphIdeal c) = height (coordinate ideal)` by `height_map_algEquiv`. CONFIRMED to
  typecheck. This is the bridge from `height_graphIdeal_eq` (graph ideal) to the coordinate ideal,
  whose localization-transport (`MvPolynomial.isLocalization` + `IsLocalization.height_map_of_disjoint`)
  carries the height to the `Sd`-based ring.
The remaining build is mechanical (the chained reindex/localization transports) — held pending the
interface decision rather than ground speculatively at the wrong target.

### D2 reindex + detΔ-localization infrastructure. **LANDED** (36817e5f, 8784c8af, cce4016e, c0cd6e2f).
`Core/DeterminantalBaseElimination.lean` (new module, all sorry-free, axiom-clean):
- `B22block` (#=C), `SchurVar` (#=δ); `card_B22block`, `card_SchurVar`.
- `finSplit`/`finSplit_castLE`, `blockRearrange`, `repCoordReindex : RepCoord (dStratum q p) ≃
  B22block ⊕ SchurVar`; `repCoordReindex_pivot` (pivot coord ↦ Δ-block; `change` to the defeq
  forward-computation form dodges the `uniqueSigma` `.rec` / Fin-1 friction).
- `mult_stratum_eq` (N=1 product = lone factor A 0, any CommRing), `multPoly_stratum_apply`
  (`multPoly (dStratum q p) a b = X ⟨0,(a,b)⟩`).
- `detSchurS` (det of the Δ-coordinate matrix in `MvPolynomial SchurVar k`); `renameEquiv_detPivot`
  (`detΔ ↦ rename Sum.inr detSchurS`); `blockAlgEquiv : A_eng ≃ₐ MvPolynomial B22block
  (MvPolynomial SchurVar k)`; `blockAlgEquiv_detPivot` (`detΔ ↦ C detSchurS`).

### Height-transport infrastructure. **LANDED** (8ad18d88, 7a250485) — the heaviest infra done.
- `height_coordIdeal_localization_eq` (GraphIdealHeight.lean): coord-ideal height = `#σ` over
  `Sd = Localization.Away f` (`f ≠ 0`). The localized transport (Codex-vetted, `localtransport`
  consult): `MvPolynomial σ Sd` = localization of `MvPolynomial σ (MvPolynomial τ k)` at `powers (C f)`
  (`MvPolynomial.isLocalization`), coord ideal = `map` of the un-localized, `C f ∉` coord prime
  (`f ≠ 0`) ⟹ `height_map_of_disjoint` + `height_coordIdeal_eq`.
- `detSchurS_ne_zero` (DeterminantalBaseElimination.lean): `Sd` is a domain / valid localization.
- The localized AlgEquiv `A_loc ≃ₐ Localization.Away (C detSchurS)` via
  `IsLocalization.algEquivOfAlgEquiv (blockAlgEquiv) (Submonoid.map_powers + blockAlgEquiv_detPivot)`
  — SPECIFY-probe-confirmed (typechecks).

### REMAINING — the final identification (~50-70 LoC; (1)/(3) clean, (2) the involved step).
Define `forcedB22 : B22block → Sd` (Schur value `B21·adjΔ·B12 / detΔ`) and `J = graphIdeal forcedB22`
in `MvPolynomial B22block Sd`. Then:
1. **`height J = C`** — `translateAux forcedB22` (probe-confirmed AlgEquiv) maps `J` to the coord
   ideal ⟹ `height J = height_coordIdeal_localization_eq detSchurS detSchurS_ne_zero = #B22block = C`.
   CLEAN given the infra.
2. **`J ⊆ Ψ(Iad)`** (the one involved step) — trace the Schur minor relation
   (`detΔ·B22 − B21 adjΔ B12 ∈ sigmaIdeal`, the LANDED `det_submatrix_multPoly_mem_sigmaIdeal`)
   through the localized `Ψ`, or pull `J`'s generators back through `Ψ⁻¹` into `Iad`. Carries the
   actual Schur content — be careful (the correctness guard's hard-direction seed).
3. **`Iad = J`** by `Ideal.height_strict_mono_of_is_prime` (`Ψ`-transported `height Iad = C` +
   `height J = C`, both prime) — honestly proves `Iad ⊆ J`. Then `A_loc/Iad ≅ Sd` via
   `graphIdealQuotientEquiv`. Expose ONLY the equiv (J internal); {domain, dim δ} derive from it.

---

## CLOSEOUT (thread 12) — 2026-06-24. **CLOSED.**

**Status:** the COMPLETE engine + height-transport infrastructure for the determinantal base
elimination is landed (sorry-free, axiom-clean, aggregated by controller at `07096546`, pushed —
HEAD `b8bb0c30` on `origin/expedition/fibre-codimension`). Working tree clean. Only the final
`forcedB22`/`Iad = J`/`A_loc/Iad ≅ Sd` identification remains; split to a fresh tide.

### Landed (3 modules)
| Module | Headlines | Reviewer |
|---|---|---|
| `Core/MvPolynomialKerAeval.lean` | `ker_aeval_eq_graphIdeal` (arbitrary ι), `graphIdeal`, `graphIdealQuotientEquiv`, `graphIdeal_isPrime`, `aeval_surjective` | FIDELITY PASS |
| `Core/GraphIdealHeight.lean` | `height_graphIdeal_eq`, `ringKrullDim_quotient_graphIdeal_eq`, `height_coordIdeal_eq`, **`height_coordIdeal_localization_eq`** (the localized transport) | seam 2 PASS; localized-transport fresh |
| `Core/DeterminantalBaseElimination.lean` | `B22block`/`SchurVar` (+`card_*`), `finSplit`(+`_castLE`), `blockRearrange`, `repCoordReindex`(+`_pivot`), `mult_stratum_eq`, `multPoly_stratum_apply`, `detSchurS`(+`_ne_zero`), `renameEquiv_detPivot`, **`blockAlgEquiv`**(+`_detPivot`) | fresh — needs fidelity read |

Codex consults: `codex/heightJ-{prompt,answer}.md`, `codex/localtransport-{prompt,answer}.md`. Statement card: `statement-card.md`.

## HANDOFF → fresh tide (G2-2c: the final identification only — NOT the reindex, that's DONE)

**Do NOT rebuild the reindex / blockAlgEquiv / height infra — it is all LANDED above.** Start from
the landed objects. The remaining work is ONLY steps (1)/(2)/(3) of the "REMAINING" section above:

**Setup (landed, ready):** `A_loc := Localization.Away (detPivotPoly q p r hp hq)`;
`Sd := Localization.Away (detSchurS q p r)` (`detSchurS_ne_zero` ⟹ `Sd` a domain);
`blockAlgEquiv_detPivot : blockAlgEquiv detΔ = C detSchurS` gives the localized
`Ψ : A_loc ≃ₐ[k] Localization.Away (C detSchurS)` via `IsLocalization.algEquivOfAlgEquiv blockAlgEquiv
(Submonoid.map_powers ▸ blockAlgEquiv_detPivot)` (SPECIFY-confirmed). `MvPolynomial.isLocalization`
identifies `Localization.Away (C detSchurS)` with `MvPolynomial B22block Sd`.

**(1) `height J = C` — LANDED (commit 3a736f4f).** `forcedNum`, `forcedB22` (= `forcedNum/detSchurS`
via `IsLocalization.mk'`; **adjugate not inv**; denominator-correct, NOT a localized numerator graph
ideal), and `height_graphIdeal_forcedB22_eq : (graphIdeal (forcedB22 q p r Sd)).height = (p−r)(q−r)`.
Built on the LANDED reusable `height_graphIdeal_localization_eq` (`GraphIdealHeight.lean`:
`translateAux` translation auto + `height_coordIdeal_localization_eq` + `detSchurS_ne_zero`). DONE.

**(2) `J ⊆ Ψ(Iad)`** (the one involved step — carries the Schur content, the correctness-guard seed):
the generator `X_{ab} − C(forcedB22 ab)` pulls back through `Ψ⁻¹` to (the localization of) the Schur
expression `detΔ⁻¹·(detΔ·B22 − (B21 adjΔ B12))_{ab}`, which is in `Iad` because `detΔ·B22 − B21 adjΔ
B12` is the bordered `(r+1)`-minor — LANDED `det_submatrix_multPoly_mem_sigmaIdeal` (the
`(r+1)`-minor ∈ `sigmaIdeal`), and `Iad = sigmaIdeal.map`. (Or push forward; pull-back through `Ψ⁻¹`
is likely lower friction.)

**(3) `Iad = J` + the equiv** — `height_strict_mono_of_is_prime` (`Ψ`-transported `height Iad = C`
[from LANDED `height_map_sigmaIdeal_away_eq_cCodim` + AlgEquiv height transport] + step-1
`height J = C`, both prime, `J ⊆ Ψ(Iad)`) ⟹ `Ψ(Iad) = J` ⟹ `Iad = Ψ⁻¹ J`. Then
`A_loc/Iad ≅ (MvPolynomial B22block Sd)/J ≅ Sd` via `graphIdealQuotientEquiv`.

**INTERFACE (controller, settled):** expose ONLY `A_loc/Iad ≅ₐ[k] Sd` + reuse landed `height Iad = C`.
`J` stays INTERNAL. {domain, dim δ} derive from the equiv (`Sd` = a poly localization). **GUARD
(non-negotiable):** the equiv needs the HARD direction `Iad ⊆ J` (= injectivity `Iad ∩ Sd = 0`);
step (2)+(3) prove it HONESTLY (not assumed — the squeeze is load-bearing: if `J ⊊ Iad`, `height J`
would be `< C` and the proof fails). Do NOT ship the equiv with it skipped.
