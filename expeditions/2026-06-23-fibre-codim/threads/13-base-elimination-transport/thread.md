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
