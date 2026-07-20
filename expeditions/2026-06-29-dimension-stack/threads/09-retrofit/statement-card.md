# Statement card — RF (thread 09, retrofit + final cleanup)

The final rung of `dimension-stack`: the foundation-first interface cleanup after the 7-module
dimension stack (R1–R4, E1–E2) landed. **No new theorems**; this is a name=content + style retrofit.

## Build / sorry / axiom status

- `./scripts/lb DLNFibre` — **green, 3819 jobs** (full aggregator). Job count unchanged by the
  retrofit (no dependency-graph change: comment-only aggregator edit + prose/docstring + an
  instance-implicit-hyp drop on two off-path off-the-graph-leaf theorems).
- `scripts/sorries` — **0 sorry / 0 #exit / 0 native_decide / 0 axiom**.
- **DLN-payoff axioms UNCHANGED** (`#print axioms`, both before and after every edit):
  - `DLNFibre.Core.codimRepCanonical_fibre_eq_cCodim_add_shift` → `[propext, Classical.choice, Quot.sound]`
  - `DLNFibre.DLN.rlct_lossDLN_eq_half_cCodim_add_shift` → `[propext, Classical.choice, Quot.sound]`
  - No `sorryAx`, no new axiom. The retrofit changed no proof's meaning.

## Task 1 — drop dead-weight `[IsAlgClosed]` on the `codimRep_*` consumers

**Already done in R4** (`2a610f8f`), not a residual. The three consumers in
`lean/DLNFibre/Core/NullstellensatzCodim.lean` —
`codimRep_add_varietyDim_eq_card`, `codimRep_eq_card_sub_varietyDim`,
`codimRepCanonical_eq_card_sub_varietyDim` — carry **only `[Field k]`** (file-level
`variable {k : Type u} [Field k]`); the bridge lemmas they delegate to
(`height_vanishingIdeal_{add,eq}_…` in `Core.Dimension.Codimension`) need `[Field k] [Finite σ]`,
and `[Finite (RepCoord d)]` auto-discharges from the global instance at `OrbitCodim.lean:99`.

- Weakest sufficient hypothesis confirmed for all three: **`[Field k]`** (the R0 `_NOALG` finding,
  now permanent — the `_NOALG` probe variants are gone, reverted as planned).
- **None genuinely needs closure.** Pre-R4 they carried `[IsAlgClosed k]` (verified at `8b240bee`);
  the move to the field-general bridge shed it.
- **No ripple to callers.** Transitive consumers (`DeterminantalStratumDim.lean:237`,
  `VoigtDischarge.lean:67`, `FibreDimFibrationProbe.lean:60`) keep their own `[IsAlgClosed]`/`[CharZero]`
  where genuinely needed — those come from the *primality / variety-dim* content they feed in
  (`isPrime_vanishingIdeal_productRankLocusLE_stratum` needs closure for orbit-closure
  irreducibility), not from the field-general bridge. Honest, unchanged.

## Task 2 — `DeepChartRing.lean:138` stale prose

Fixed. The prose attributed `vanishingIdeal_isRadical` to "over `[IsAlgClosed k]`". Corrected to:
"a field-general no-nilpotents fact — every vanishing ideal is radical over any field, not the strong
Nullstellensatz". `sigmaIdeal` is literally `MvPolynomial.vanishingIdeal (…)`
(`SigmaComponents.lean:130`), so its radicality is `vanishingIdeal_isRadical`, which is field-general
(no-nilpotents over a field — `Codimension.lean:73`), independent of closure.

## Task 3 — zero `longLine`

| file(s) | longLine before | after |
|---|---|---|
| `lean/DLNFibre.lean` | **105** (codepoint: 105) | **0** |
| `lean/DLNFibre/Core/Dimension/*.lean` (7 files) | **0** (already clean) | **0** |

- The seven `Dimension/` modules were already clean (R1–E2 built them upstream-grade); confirmed by
  both the linter (no warning in the build) and a codepoint check.
- `DLNFibre.lean` (the aggregator) was reflowed: every over-100-codepoint comment block re-wrapped to
  ≤100 codepoints, **imports untouched** (178 imports, byte-identical and in order — `diff` clean) and
  comment **content preserved word-for-word** (zero symmetric difference in the comment word-multiset
  vs `HEAD`). Pure rewrap; the single-writer aggregator's import structure is unchanged.
- **Counting caveat (lesson):** `awk length` counts UTF-8 *bytes*; the Lean `longLine` linter (and
  Python `len(str)`) count *codepoints* (`String.length`). The aggregator's comments are dense with
  wide chars (`δ Σ̄ ⁻¹ ᵢ ≃ₐ ⧸ →ₐ ∏ ∑`), so the two disagree. Reflow against codepoint width, not byte
  width. The final 0/0 is codepoint-confirmed AND linter-confirmed (no `DLNFibre.lean:` warning in the
  full build).
- Out-of-scope files still carry longLine warnings (≈763 across the library); the brief scoped task 3
  strictly to `DLNFibre.lean` + the seven `Dimension/` modules.

## Task 4 — final name=content sweep

Swept the retrofitted consumers + the `Dimension/` modules for stale `[IsAlgClosed]` / `CharZero` /
Nullstellensatz docstring drift.

- **Dimension modules:** all `[IsAlgClosed]` mentions are correct name=content — they document the
  *absence* of closure ("no `[IsAlgClosed]`", "is **not** needed", "exclusively an entry-2 concern").
  No drift.
- **Retrofit consumers:** the `[IsAlgClosed]`/`[CharZero]` on `varietyDim_productRankLocusLE_stratum`,
  `isPrime_vanishingIdeal_productRankLocusLE_stratum`, and the `FibreDimFibrationProbe` examples are
  genuine (primality / determinantal-variety irreducibility / char-0 `cCodim` matching), correctly
  attributed in their docstrings. No drift.
- **Surprise / extra win (surfaced by the sweep, in-scope generalisation done):** `DeepChartRing.lean`'s
  `IadDeep_isRadical` and `isReduced_Sred` carried `[IsAlgClosed k]` as **dead-weight** theorem
  hypotheses — the same spurious-closure pattern R0 found on the `codimRep_*` lemmas. Their proof
  bodies use only `vanishingIdeal_isRadical` (field-general) + `IsLocalization.map_radical` +
  `Ideal.isRadical_iff_quotient_reduced`, none of which touch closure. Both have **zero external
  consumers** (used only within `DeepChartRing`; `isReduced_Sred` has none at all), so dropping the
  hyp is self-contained — **no ripple** (L2-checked). Tightened both to `[Field k]` (file-level),
  fixed their docstrings + the module's top docstring (line 25, which still said `Sred` reduced "over
  `[IsAlgClosed k]`"). This is the same free generalisation win as the codimRep retrofit. The genuine
  closure on `DeepChartRing`'s `schurToSred` / `sredSchurAlgebra` / `sredSchur_isScalarTower` (they use
  `basePresentationEquiv`, which needs closure + char-0) is left intact — correctly attributed at
  line 325. (NB `DeepChartRing` is itself an off-critical-path superseded R2-3b-route module; the win
  is real but the module is not load-bearing.)

## Files changed

- `lean/DLNFibre.lean` — aggregator comment reflow to ≤100 codepoints (imports + content unchanged).
- `lean/DLNFibre/Core/DeepChartRing.lean` — task-2 prose fix at the `Sred`-reducedness note; plus the
  task-4 win: `[IsAlgClosed]` dropped from `IadDeep_isRadical` + `isReduced_Sred` (now `[Field k]`),
  three docstrings corrected to match (lines ~25, ~144, ~157).

## Holes / blockers

None. All four tasks closed; gate green.
