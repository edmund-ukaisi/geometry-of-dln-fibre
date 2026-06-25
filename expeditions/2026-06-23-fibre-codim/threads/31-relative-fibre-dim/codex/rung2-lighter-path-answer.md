   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efacd-3505-7fb3-8af2-49e577913154
--------
user
# Codex consult — is there a varietyDim-ONLY path lighter than building the full product iso `e`?

Lean 4 + Mathlib v4.29. CRITICAL scope finding: the chart `AlgEquiv` route (c)'s rung 2 needs is
ESSENTIALLY the product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg` that a PRIOR tide (R2-3b-4)
attempted and **never finished** (it remains a hypothesis in the repo, never a committed `def`). The
prior wall was Lean-mechanical: descending the gauge `gaugeEquiv` through the localization (at `ΔP`)
AND the quotient (by the cut ideal), then proving the coordinates SPLIT as `SchurLoc ⊗ FibreAlg`.

I only need a `varietyDim` (Krull-dim) statement: `varietyDim(chart) = δ + varietyDim F`. I have
LANDED:
- `varietyDim_eq_of_coordRingAlgEquiv` — transports `varietyDim` across a coordinate-ring `AlgEquiv`.
- `ringKrullDim_quotient_radical` — radical-insensitivity (so I work with reduced/`vanishingIdeal`).
- `gaugeEquiv` (universal coordinate-change `AlgEquiv` on the UNquotiented polynomial ring, over any
  `CommRing`), the sweep `Σ^r = H·F`, `multComap`, `Sred`, `SchurLoc`, `schurToSred`.
- `SchurLoc = Localization.Away detSchurS` of a polynomial ring; Mathlib has `MvPolynomial.krullDim
  _of_isNoetherianRing` (`dim R[X_1..X_n] = dim R + n`).

## The question

Building the full `e` (an `AlgEquiv` with both directions + round-trips through a
localized-quotient ring) is heavy and previously stalled. For a DIMENSION-only conclusion, is there a
LIGHTER path that avoids constructing the full `AlgEquiv`? Candidates:

1. **Inequality squeeze instead of iso.** `varietyDim(chart) ≤ δ + dim F` AND `≥ δ + dim F`
   separately, each via a one-directional regular map (a surjection/closed-immersion of coordinate
   rings) rather than a full iso. A surjection `A ↠ B` gives `dim B ≤ dim A`; an injection of
   f.g. domains gives `dim A ≤ dim B`. Could the two inequalities be gotten from the two `AlgHom`
   directions WITHOUT proving they're mutually inverse (the round-trips were the heavy part)? Does the
   reducible case break the domain-injection direction?

2. **The unquotiented gauge + ideal-image bookkeeping.** `gaugeEquiv` is a clean `AlgEquiv` on the
   UNquotiented `MvPolynomial (RepCoord d) k`. It carries `vanishingIdeal(chart)` to
   `vanishingIdeal(gauged chart)`. If the gauged chart's vanishing ideal VISIBLY splits as
   `(SchurLoc-coords ideal) + (fibre-coords ideal)` — i.e. the gauged coordinates separate into δ
   free base directions ⊗ the fibre — can I read `varietyDim` off the split WITHOUT a tensor `AlgEquiv`,
   e.g. via `MvPolynomial` variable-partition + `krullDim` of the polynomial extension? The gauge is
   an iso on the unquotiented ring (no localization/quotient descent needed THERE) — does staying
   unquotiented and only quotienting at the end dodge the descent that walled `e`?

3. **`δ`-free-directions directly.** Maybe avoid `SchurLoc ⊗ FibreAlg` entirely: show the chart
   coordinate ring is `≅ FibreAlg-coords localized-polynomial-extended by δ Schur variables`, so
   `dim = dim F + δ` directly via `MvPolynomial.krullDim_of_isNoetherianRing` + localization. This is
   the polynomial-extension route stated as a coordinate-ring iso to `(FibreAlg)[X_1..X_δ]_loc` rather
   than a tensor — is that iso EASIER to build than the symmetric tensor `e` (it's the same content,
   but maybe a cleaner Lean target)?

4. **Is the descent genuinely unavoidable?** The prior `e` needed gauge-descent through
   `Localization.Away ΔP ⧸ IadDeep`. For the dimension statement, can I work on the UNquotiented +
   UNlocalized ring as long as possible, applying the gauge `AlgEquiv` there, and only take
   `vanishingIdeal`/`ringKrullDim` at the end — so the localization/quotient interchange that walled
   `e` never arises?

Tell me: (a) which path is lightest for a DIMENSION-only conclusion, (b) whether any path genuinely
avoids the localized-quotient gauge-descent that stalled `e`, (c) an honest module estimate for the
lightest path, and (d) if NO path is materially lighter than the full `e` (i.e. rung 2 just IS
building `e`, which stalled), say so — that is a scope escalation, and the fallback is citing `hSweep`.
Be adversarial: I suspect the dimension-only framing should be lighter than the full reduced-iso, but
I need to know if the gauge-descent is the irreducible core either way.

codex
I’ll inspect the local Lean/exposition structure around the landed lemmas and the stalled product-iso attempt, then I’ll give a scope judgment grounded in what the repo actually has rather than guessing from the names.
exec
/bin/bash -lc 'pwd && rg -n "varietyDim_eq_of_coordRingAlgEquiv|ringKrullDim_quotient_radical|gaugeEquiv|Sred|SchurLoc|schurToSred|hSweep|IadDeep|Delta|ΔP|varietyDim" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-lighter-path-prompt.md:1:# Codex consult — is there a varietyDim-ONLY path lighter than building the full product iso `e`?
./rung2-lighter-path-prompt.md:4:ESSENTIALLY the product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg` that a PRIOR tide (R2-3b-4)
./rung2-lighter-path-prompt.md:6:prior wall was Lean-mechanical: descending the gauge `gaugeEquiv` through the localization (at `ΔP`)
./rung2-lighter-path-prompt.md:7:AND the quotient (by the cut ideal), then proving the coordinates SPLIT as `SchurLoc ⊗ FibreAlg`.
./rung2-lighter-path-prompt.md:9:I only need a `varietyDim` (Krull-dim) statement: `varietyDim(chart) = δ + varietyDim F`. I have
./rung2-lighter-path-prompt.md:11:- `varietyDim_eq_of_coordRingAlgEquiv` — transports `varietyDim` across a coordinate-ring `AlgEquiv`.
./rung2-lighter-path-prompt.md:12:- `ringKrullDim_quotient_radical` — radical-insensitivity (so I work with reduced/`vanishingIdeal`).
./rung2-lighter-path-prompt.md:13:- `gaugeEquiv` (universal coordinate-change `AlgEquiv` on the UNquotiented polynomial ring, over any
./rung2-lighter-path-prompt.md:14:  `CommRing`), the sweep `Σ^r = H·F`, `multComap`, `Sred`, `SchurLoc`, `schurToSred`.
./rung2-lighter-path-prompt.md:15:- `SchurLoc = Localization.Away detSchurS` of a polynomial ring; Mathlib has `MvPolynomial.krullDim
./rung2-lighter-path-prompt.md:24:1. **Inequality squeeze instead of iso.** `varietyDim(chart) ≤ δ + dim F` AND `≥ δ + dim F`
./rung2-lighter-path-prompt.md:31:2. **The unquotiented gauge + ideal-image bookkeeping.** `gaugeEquiv` is a clean `AlgEquiv` on the
./rung2-lighter-path-prompt.md:34:   `(SchurLoc-coords ideal) + (fibre-coords ideal)` — i.e. the gauged coordinates separate into δ
./rung2-lighter-path-prompt.md:35:   free base directions ⊗ the fibre — can I read `varietyDim` off the split WITHOUT a tensor `AlgEquiv`,
./rung2-lighter-path-prompt.md:40:3. **`δ`-free-directions directly.** Maybe avoid `SchurLoc ⊗ FibreAlg` entirely: show the chart
./rung2-lighter-path-prompt.md:48:   `Localization.Away ΔP ⧸ IadDeep`. For the dimension statement, can I work on the UNquotiented +
./rung2-lighter-path-prompt.md:56:building `e`, which stalled), say so — that is a scope escalation, and the fallback is citing `hSweep`.
./route-choice-prompt.md:7:## The exact target (`hSweep`)
./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-prompt.md:65:   reducedness), say so plainly — that triggers a fallback to citing `hSweep`.
./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-lighter-path-answer.md:16:# Codex consult — is there a varietyDim-ONLY path lighter than building the full product iso `e`?
./rung2-lighter-path-answer.md:19:ESSENTIALLY the product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg` that a PRIOR tide (R2-3b-4)
./rung2-lighter-path-answer.md:21:prior wall was Lean-mechanical: descending the gauge `gaugeEquiv` through the localization (at `ΔP`)
./rung2-lighter-path-answer.md:22:AND the quotient (by the cut ideal), then proving the coordinates SPLIT as `SchurLoc ⊗ FibreAlg`.
./rung2-lighter-path-answer.md:24:I only need a `varietyDim` (Krull-dim) statement: `varietyDim(chart) = δ + varietyDim F`. I have
./rung2-lighter-path-answer.md:26:- `varietyDim_eq_of_coordRingAlgEquiv` — transports `varietyDim` across a coordinate-ring `AlgEquiv`.
./rung2-lighter-path-answer.md:27:- `ringKrullDim_quotient_radical` — radical-insensitivity (so I work with reduced/`vanishingIdeal`).
./rung2-lighter-path-answer.md:28:- `gaugeEquiv` (universal coordinate-change `AlgEquiv` on the UNquotiented polynomial ring, over any
./rung2-lighter-path-answer.md:29:  `CommRing`), the sweep `Σ^r = H·F`, `multComap`, `Sred`, `SchurLoc`, `schurToSred`.
./rung2-lighter-path-answer.md:30:- `SchurLoc = Localization.Away detSchurS` of a polynomial ring; Mathlib has `MvPolynomial.krullDim
./rung2-lighter-path-answer.md:39:1. **Inequality squeeze instead of iso.** `varietyDim(chart) ≤ δ + dim F` AND `≥ δ + dim F`
./rung2-lighter-path-answer.md:46:2. **The unquotiented gauge + ideal-image bookkeeping.** `gaugeEquiv` is a clean `AlgEquiv` on the
./rung2-lighter-path-answer.md:49:   `(SchurLoc-coords ideal) + (fibre-coords ideal)` — i.e. the gauged coordinates separate into δ
./rung2-lighter-path-answer.md:50:   free base directions ⊗ the fibre — can I read `varietyDim` off the split WITHOUT a tensor `AlgEquiv`,
./rung2-lighter-path-answer.md:55:3. **`δ`-free-directions directly.** Maybe avoid `SchurLoc ⊗ FibreAlg` entirely: show the chart
./rung2-lighter-path-answer.md:63:   `Localization.Away ΔP ⧸ IadDeep`. For the dimension statement, can I work on the UNquotiented +
./rung2-lighter-path-answer.md:71:building `e`, which stalled), say so — that is a scope escalation, and the fallback is citing `hSweep`.
./rung2-regular-section-prompt.md:3:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-prompt.md:4:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-prompt.md:5:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-prompt.md:13:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-prompt.md:18:- `U_P ⊆ Mat^{=r}` = pivot chart where the top-left `r×r` minor `ΔP` is invertible (a principal open
./rung2-regular-section-prompt.md:19:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-prompt.md:20:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-prompt.md:22:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-prompt.md:26:1. **On the pivot chart `D(ΔP)`, is there a REGULAR (polynomial-in-entries-after-inverting-ΔP)
./rung2-regular-section-prompt.md:29:   the inverse of that block and its Schur complement — all REGULAR after inverting `ΔP`. So I expect
./rung2-regular-section-prompt.md:37:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-prompt.md:40:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-prompt.md:42:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-prompt.md:44:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-prompt.md:46:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-prompt.md:50:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-prompt.md:58:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-prompt.md:59:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./route-choice-answer.md:22:## The exact target (`hSweep`)
./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./route-choice-answer.md:185:## The exact target (`hSweep`)
./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./route-choice-answer.md:674:./DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./route-choice-answer.md:679:./DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:681:./DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:686:./DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./route-choice-answer.md:687:./DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./route-choice-answer.md:689:./DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:691:./DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./route-choice-answer.md:692:./DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:693:./DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./route-choice-answer.md:694:./DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./route-choice-answer.md:695:./DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:697:./DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./route-choice-answer.md:698:./DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./route-choice-answer.md:700:./DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:702:./DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./route-choice-answer.md:703:./DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./route-choice-answer.md:704:./DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./route-choice-answer.md:705:./DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:707:./DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:708:./DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./route-choice-answer.md:712:./DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./route-choice-answer.md:714:./DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:717:./DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./route-choice-answer.md:821:./DLNFibre/Core/OrbitDifferentialRank.lean:659:/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
./route-choice-answer.md:822:./DLNFibre/Core/OrbitDifferentialRank.lean:660:Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
./route-choice-answer.md:823:./DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./route-choice-answer.md:824:./DLNFibre/Core/OrbitDifferentialRank.lean:666:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:825:./DLNFibre/Core/OrbitDifferentialRank.lean:668:  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
./route-choice-answer.md:846:./DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./route-choice-answer.md:847:./DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./route-choice-answer.md:852:./DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./route-choice-answer.md:854:./DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:855:./DLNFibre/Core/RadicalCatenary.lean:181:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
./route-choice-answer.md:862:./DLNFibre/Core/RadicalCatenary.lean:197:  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
./route-choice-answer.md:863:./DLNFibre/Core/RadicalCatenary.lean:203:The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
./route-choice-answer.md:864:./DLNFibre/Core/RadicalCatenary.lean:208:      + varietyDim (canonicalCoord dWitness ''
./route-choice-answer.md:865:./DLNFibre/Core/RadicalCatenary.lean:211:  codimRepCanonical_add_varietyDim_eq_card_of_nonempty
./route-choice-answer.md:884:./DLNFibre/Core/OrbitImageDim.lean:10:(`varietyDim_eq_ringKrullDim_range_orbitPullback`), discharges the AG-half of `hVoigt`:
./route-choice-answer.md:885:./DLNFibre/Core/OrbitImageDim.lean:15:- **A0** (landed): `varietyDim Z_M = (ringKrullDim (orbitPullback M).range).unbotD 0`.
./route-choice-answer.md:886:./DLNFibre/Core/OrbitImageDim.lean:77:the A4.3 identity is needed (the chain is `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`);
./route-choice-answer.md:887:./DLNFibre/Core/OrbitImageDim.lean:90:/-- **A4.4 chained with A0: `varietyDim Z_M ≤ finrank (range δ⁰)`.** Combining the landed A0 link
./route-choice-answer.md:888:./DLNFibre/Core/OrbitImageDim.lean:91:(`varietyDim_eq_ringKrullDim_range_orbitPullback`, needs `[Infinite k]`) with the submersion bound,
./route-choice-answer.md:889:./DLNFibre/Core/OrbitImageDim.lean:95:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ
./route-choice-answer.md:890:./DLNFibre/Core/OrbitImageDim.lean:101:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:891:./DLNFibre/Core/OrbitImageDim.lean:103:  rw [varietyDim_eq_ringKrullDim_range_orbitPullback M]
./route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:944:./DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./route-choice-answer.md:946:./DLNFibre/Core/FibreDimFibrationProbe.lean:59:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:947:./DLNFibre/Core/FibreDimFibrationProbe.lean:60:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./route-choice-answer.md:952:./DLNFibre/Core/FibreDimFibrationProbe.lean:96:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./route-choice-answer.md:954:./DLNFibre/Core/FibreDimFibrationProbe.lean:100:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./route-choice-answer.md:955:./DLNFibre/Core/FibreDimFibrationProbe.lean:102:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./route-choice-answer.md:1050:./DLNFibre/Core/VoigtDischarge.lean:8:The capstone of the AG half. The A4 submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`
./route-choice-answer.md:1051:./DLNFibre/Core/VoigtDischarge.lean:9:(`varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`, char 0) and the A6.1 reverse
./route-choice-answer.md:1052:./DLNFibre/Core/VoigtDischarge.lean:10:inequality `finrank (range δ⁰) ≤ varietyDim Z_M` (`finrank_range_deformationδ_le_varietyDim`) squeeze
./route-choice-answer.md:1053:./DLNFibre/Core/VoigtDischarge.lean:11:to **equality** `varietyDim Z_M = finrank (range δ⁰)` (the orbit closure is smooth of the expected
./route-choice-answer.md:1054:./DLNFibre/Core/VoigtDischarge.lean:33:/-! ## The squeeze — `varietyDim Z_M = finrank (range δ⁰)` -/
./route-choice-answer.md:1055:./DLNFibre/Core/VoigtDischarge.lean:38:theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
./route-choice-answer.md:1056:./DLNFibre/Core/VoigtDischarge.lean:40:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:1057:./DLNFibre/Core/VoigtDischarge.lean:43:  refine le_antisymm ?_ (finrank_range_deformationδ_le_varietyDim M)
./route-choice-answer.md:1058:./DLNFibre/Core/VoigtDischarge.lean:44:  exact varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional M
./route-choice-answer.md:1059:./DLNFibre/Core/VoigtDischarge.lean:64:    have hadd := codimRep_add_varietyDim_eq_card (canonicalCoord d) (orbitRankLocus M)
./route-choice-answer.md:1061:./DLNFibre/Core/VoigtDischarge.lean:66:    rwa [varietyDim_orbitRankLocus_eq_finrank_range_deformationδ M, ← hr] at hadd
./route-choice-answer.md:1063:./DLNFibre/Core/OrbitTangentCotangent.lean:14:# `DLNFibre.Core.OrbitTangentCotangent` — A6.1: the reverse inequality `finrank(range δ⁰) ≤ varietyDim Z_M`
./route-choice-answer.md:1064:./DLNFibre/Core/OrbitTangentCotangent.lean:19:`varietyDim Z_M = finrank (range δ⁰)`, the geometric heart of Voigt's lemma.
./route-choice-answer.md:1067:./DLNFibre/Core/OrbitTangentCotangent.lean:564:/-! ## R6 — chain `finrank (m_M.Cotangent)` to `varietyDim Z_M` -/
./route-choice-answer.md:1068:./DLNFibre/Core/OrbitTangentCotangent.lean:566:/-- `ringKrullDim (orbitRing M)` is a finite natural number `n`, equal to `varietyDim Z_M`:
./route-choice-answer.md:1069:./DLNFibre/Core/OrbitTangentCotangent.lean:571:      ∧ varietyDim (canonicalCoord d '' orbitRankLocus M) = (n : ℕ∞) := by
./route-choice-answer.md:1070:./DLNFibre/Core/OrbitTangentCotangent.lean:579:  -- `varietyDim Z_M = (ringKrullDim (orbitRing M)).unbotD 0` (L6.4 + `varietyDim` def)
./route-choice-answer.md:1071:./DLNFibre/Core/OrbitTangentCotangent.lean:580:  have hvar : varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:1072:./DLNFibre/Core/OrbitTangentCotangent.lean:582:    rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M]; rfl
./route-choice-answer.md:1073:./DLNFibre/Core/OrbitTangentCotangent.lean:598:/-- **R6 — `finrank k (m_M.Cotangent) = varietyDim Z_M`.** The cotangent finrank equals the variety
./route-choice-answer.md:1074:./DLNFibre/Core/OrbitTangentCotangent.lean:601:GAP3 (`ringKrullDim (AtPrime m_M) = ringKrullDim (orbitRing M)`), and `varietyDim Z_M =
./route-choice-answer.md:1075:./DLNFibre/Core/OrbitTangentCotangent.lean:603:theorem finrank_cotangent_eq_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./route-choice-answer.md:1076:./DLNFibre/Core/OrbitTangentCotangent.lean:605:      = varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./route-choice-answer.md:1078:./DLNFibre/Core/OrbitTangentCotangent.lean:635:/-! ## The A6.1 headline — `finrank (range δ⁰) ≤ varietyDim Z_M` -/
./route-choice-answer.md:1079:./DLNFibre/Core/OrbitTangentCotangent.lean:637:/-- **A6.1 (the reverse inequality).** `finrank k (range δ⁰) ≤ varietyDim Z_M`: the orbit tangent
./route-choice-answer.md:1080:./DLNFibre/Core/OrbitTangentCotangent.lean:641:theorem finrank_range_deformationδ_le_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./route-choice-answer.md:1081:./DLNFibre/Core/OrbitTangentCotangent.lean:643:      ≤ varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./route-choice-answer.md:1082:./DLNFibre/Core/OrbitTangentCotangent.lean:644:  rw [← finrank_cotangent_eq_varietyDim M]
./route-choice-answer.md:1083:./DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./route-choice-answer.md:1084:./DLNFibre/Core/RouteCAssembly.lean:18:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./route-choice-answer.md:1085:./DLNFibre/Core/RouteCAssembly.lean:20:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:1087:./DLNFibre/Core/RouteCAssembly.lean:52:          + varietyDim (canonicalCoord d '' fibre d B))
./route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./route-choice-answer.md:1090:./DLNFibre/Core/RouteCAssembly.lean:56:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./route-choice-answer.md:1096:./DLNFibre/Core/RouteCAssembly.lean:69:        + varietyDim (canonicalCoord d '' fibre d B) := by
./route-choice-answer.md:1097:./DLNFibre/Core/RouteCAssembly.lean:72:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./route-choice-answer.md:1098:./DLNFibre/Core/RouteCAssembly.lean:79:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./route-choice-answer.md:1099:./DLNFibre/Core/RouteCAssembly.lean:80:      = varietyDim (canonicalCoord d '' fibre d B)
./route-choice-answer.md:1100:./DLNFibre/Core/RouteCAssembly.lean:82:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./route-choice-answer.md:1101:./DLNFibre/Core/RouteCAssembly.lean:83:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./route-choice-answer.md:1102:./DLNFibre/Core/RouteCAssembly.lean:88:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./route-choice-answer.md:1103:./DLNFibre/Core/RouteCAssembly.lean:89:      _ = varietyDim (canonicalCoord d '' fibre d B)
./route-choice-answer.md:1104:./DLNFibre/Core/RouteCAssembly.lean:100:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:1107:./DLNFibre/Core/RouteCAssembly.lean:109:          + varietyDim (canonicalCoord d '' fibre d B))
./route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./route-choice-answer.md:1110:./DLNFibre/Core/RouteCAssembly.lean:115:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./route-choice-answer.md:1111:./DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./route-choice-answer.md:1172:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./route-choice-answer.md:1191:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./route-choice-answer.md:1192:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:1195:  rw [varietyDim, ← hI] at hvd
./route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:1321:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./route-choice-answer.md:1325:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:1326:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./route-choice-answer.md:1362:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./route-choice-answer.md:1366:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./route-choice-answer.md:1368:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./route-choice-answer.md:7471:/bin/bash -lc 'rg -n "hSweep|relative|fibre dimension|generic fibre|generic fiber|tower|trdeg|Noether normalization|NoetherNormalization|route|bundle|locally trivial|fibration|FlatTrivial|ChartFlatness|SmoothLocalRelativeDimension|Relative" DLNFibre/Core -S' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./route-choice-answer.md:7513:DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./route-choice-answer.md:7525:DLNFibre/Core/OrbitImageDim.lean:77:the A4.3 identity is needed (the chain is `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`);
./route-choice-answer.md:7552:DLNFibre/Core/DeepChartRing.lean:325:/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower
./route-choice-answer.md:7553:DLNFibre/Core/DeepChartRing.lean:328:structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
./route-choice-answer.md:7554:DLNFibre/Core/DeepChartRing.lean:339:tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
./route-choice-answer.md:7705:DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./route-choice-answer.md:7707:DLNFibre/Core/RouteCAssembly.lean:44:identity `hSweep`, the Cited closure bridge `hClosure`, and the two reducible-locus catenary
./route-choice-answer.md:7708:DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:7709:DLNFibre/Core/RouteCAssembly.lean:70:    rw [← hClosure, hSweep]
./route-choice-answer.md:7710:DLNFibre/Core/RouteCAssembly.lean:98:homogeneous-sweep dimension identity `hSweep` and the Cited closure bridge `hClosure` as named
./route-choice-answer.md:7711:DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:7712:DLNFibre/Core/RouteCAssembly.lean:114:  codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep d r h B hB hSweep hClosure
./route-choice-answer.md:7961:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./route-choice-answer.md:8286:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./route-choice-answer.md:8287:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./route-choice-answer.md:8289:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./route-choice-answer.md:8313:identity `hSweep`, the Cited closure bridge `hClosure`, and the two reducible-locus catenary
./route-choice-answer.md:8319:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:8321:          + varietyDim (canonicalCoord d '' fibre d B))
./route-choice-answer.md:8322:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:8323:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./route-choice-answer.md:8325:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./route-choice-answer.md:8327:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./route-choice-answer.md:8336:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./route-choice-answer.md:8338:        + varietyDim (canonicalCoord d '' fibre d B) := by
./route-choice-answer.md:8339:    rw [← hClosure, hSweep]
./route-choice-answer.md:8341:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./route-choice-answer.md:8348:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./route-choice-answer.md:8349:      = varietyDim (canonicalCoord d '' fibre d B)
./route-choice-answer.md:8351:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./route-choice-answer.md:8352:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./route-choice-answer.md:8357:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./route-choice-answer.md:8358:      _ = varietyDim (canonicalCoord d '' fibre d B)
./route-choice-answer.md:8367:homogeneous-sweep dimension identity `hSweep` and the Cited closure bridge `hClosure` as named
./route-choice-answer.md:8369:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./route-choice-answer.md:8376:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:8378:          + varietyDim (canonicalCoord d '' fibre d B))
./route-choice-answer.md:8379:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./route-choice-answer.md:8380:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./route-choice-answer.md:8383:  codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep d r h B hB hSweep hClosure
./route-choice-answer.md:8384:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./route-choice-answer.md:8385:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./route-choice-answer.md:8835:`Σ^r` and `F` are not domains in the examples you care about. Your `varietyDim` is `ringKrullDim` of a possibly reducible coordinate ring, hence a **max over components**, while `trdeg_add_eq` is a domain/no-zero-divisors function-field theorem.
./route-choice-answer.md:8843:It does not identify `relative_trdeg` with `varietyDim F_B` at your chosen closed rank-`r` point. The missing input is the no-jump/local-triviality statement:
./route-choice-answer.md:8868:bridge from flat ring maps to set-level varietyDim/fibre ideals
./route-choice-answer.md:8873:The set-level `varietyDim` bridge is not free. `multComap` gives the ring map shape, but exact-rank geometry wants localized quotient rings/pivot charts, not just the global closure ring where lower-rank fibres jump.
./route-choice-answer.md:8899:6. finite-cover/localization gluing for set-level varietyDim
./route-choice-answer.md:8922:`Σ^r` and `F` are not domains in the examples you care about. Your `varietyDim` is `ringKrullDim` of a possibly reducible coordinate ring, hence a **max over components**, while `trdeg_add_eq` is a domain/no-zero-divisors function-field theorem.
./route-choice-answer.md:8930:It does not identify `relative_trdeg` with `varietyDim F_B` at your chosen closed rank-`r` point. The missing input is the no-jump/local-triviality statement:
./route-choice-answer.md:8955:bridge from flat ring maps to set-level varietyDim/fibre ideals
./route-choice-answer.md:8960:The set-level `varietyDim` bridge is not free. `multComap` gives the ring map shape, but exact-rank geometry wants localized quotient rings/pivot charts, not just the global closure ring where lower-rank fibres jump.
./route-choice-answer.md:8986:6. finite-cover/localization gluing for set-level varietyDim
./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:80:   reducedness), say so plainly — that triggers a fallback to citing `hSweep`.
./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:93:/bin/bash -lc "rg -n \"varietyDim|ringKrullDim|radical|IsJacobson|KrullDim|tensor|TensorProduct\" . -g '*.lean' -g '*.md' | head -300" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:95:./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:96:./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:97:./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:98:./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:101:./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:103:./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:104:./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:105:./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:106:./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:108:./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:110:./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:112:./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:114:./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:117:./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:118:./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:122:./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:124:./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:126:./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:127:./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:128:./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:130:./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:132:./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:134:./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:136:./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:139:./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:140:./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:144:./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:146:./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:148:./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:149:./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:150:./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:151:./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:152:./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:155:./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:157:./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:158:./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:161:./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:162:./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:163:./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:164:./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:167:./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:169:./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:170:./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:173:./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./noncirc-setlevel-answer.md:174:./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./noncirc-setlevel-answer.md:175:./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./noncirc-setlevel-answer.md:176:./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./noncirc-setlevel-answer.md:177:./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./noncirc-setlevel-answer.md:178:./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./noncirc-setlevel-answer.md:179:./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./noncirc-setlevel-answer.md:180:./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./noncirc-setlevel-answer.md:181:./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:182:./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./noncirc-setlevel-answer.md:183:./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./noncirc-setlevel-answer.md:184:./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:185:./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:186:./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./noncirc-setlevel-answer.md:187:./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./noncirc-setlevel-answer.md:188:./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./noncirc-setlevel-answer.md:189:./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./noncirc-setlevel-answer.md:190:./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./noncirc-setlevel-answer.md:191:./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./noncirc-setlevel-answer.md:192:./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./noncirc-setlevel-answer.md:193:./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:194:./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./noncirc-setlevel-answer.md:195:./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./noncirc-setlevel-answer.md:196:./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./noncirc-setlevel-answer.md:197:./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./noncirc-setlevel-answer.md:198:./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./noncirc-setlevel-answer.md:200:./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./noncirc-setlevel-answer.md:201:./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:203:./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./noncirc-setlevel-answer.md:204:./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./noncirc-setlevel-answer.md:205:./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:206:./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./noncirc-setlevel-answer.md:208:./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./noncirc-setlevel-answer.md:214:./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./noncirc-setlevel-answer.md:215:./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./noncirc-setlevel-answer.md:223:./route-choice-answer.md:674:./DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./noncirc-setlevel-answer.md:225:./route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./noncirc-setlevel-answer.md:226:./route-choice-answer.md:679:./DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:227:./route-choice-answer.md:681:./DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:231:./route-choice-answer.md:686:./DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./noncirc-setlevel-answer.md:232:./route-choice-answer.md:687:./DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./noncirc-setlevel-answer.md:233:./route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./noncirc-setlevel-answer.md:234:./route-choice-answer.md:689:./DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:235:./route-choice-answer.md:691:./DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./noncirc-setlevel-answer.md:236:./route-choice-answer.md:692:./DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:237:./route-choice-answer.md:693:./DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./noncirc-setlevel-answer.md:238:./route-choice-answer.md:694:./DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./noncirc-setlevel-answer.md:239:./route-choice-answer.md:695:./DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:240:./route-choice-answer.md:697:./DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./noncirc-setlevel-answer.md:241:./route-choice-answer.md:698:./DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:242:./route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./noncirc-setlevel-answer.md:243:./route-choice-answer.md:700:./DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:244:./route-choice-answer.md:702:./DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./noncirc-setlevel-answer.md:245:./route-choice-answer.md:703:./DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./noncirc-setlevel-answer.md:246:./route-choice-answer.md:704:./DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./noncirc-setlevel-answer.md:247:./route-choice-answer.md:705:./DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:248:./route-choice-answer.md:707:./DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./noncirc-setlevel-answer.md:249:./route-choice-answer.md:708:./DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./noncirc-setlevel-answer.md:250:./route-choice-answer.md:712:./DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./noncirc-setlevel-answer.md:251:./route-choice-answer.md:714:./DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:252:./route-choice-answer.md:717:./DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./noncirc-setlevel-answer.md:260:./route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./noncirc-setlevel-answer.md:261:./route-choice-answer.md:821:./DLNFibre/Core/OrbitDifferentialRank.lean:659:/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
./noncirc-setlevel-answer.md:262:./route-choice-answer.md:822:./DLNFibre/Core/OrbitDifferentialRank.lean:660:Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
./noncirc-setlevel-answer.md:263:./route-choice-answer.md:823:./DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./noncirc-setlevel-answer.md:264:./route-choice-answer.md:824:./DLNFibre/Core/OrbitDifferentialRank.lean:666:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:265:./route-choice-answer.md:825:./DLNFibre/Core/OrbitDifferentialRank.lean:668:  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
./noncirc-setlevel-answer.md:266:./route-choice-answer.md:846:./DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./noncirc-setlevel-answer.md:267:./route-choice-answer.md:847:./DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./noncirc-setlevel-answer.md:268:./route-choice-answer.md:852:./DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./noncirc-setlevel-answer.md:269:./route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./noncirc-setlevel-answer.md:270:./route-choice-answer.md:854:./DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:271:./route-choice-answer.md:855:./DLNFibre/Core/RadicalCatenary.lean:181:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
./noncirc-setlevel-answer.md:272:./route-choice-answer.md:862:./DLNFibre/Core/RadicalCatenary.lean:197:  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
./noncirc-setlevel-answer.md:273:./route-choice-answer.md:863:./DLNFibre/Core/RadicalCatenary.lean:203:The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
./noncirc-setlevel-answer.md:274:./route-choice-answer.md:864:./DLNFibre/Core/RadicalCatenary.lean:208:      + varietyDim (canonicalCoord dWitness ''
./noncirc-setlevel-answer.md:275:./route-choice-answer.md:865:./DLNFibre/Core/RadicalCatenary.lean:211:  codimRepCanonical_add_varietyDim_eq_card_of_nonempty
./noncirc-setlevel-answer.md:276:./route-choice-answer.md:884:./DLNFibre/Core/OrbitImageDim.lean:10:(`varietyDim_eq_ringKrullDim_range_orbitPullback`), discharges the AG-half of `hVoigt`:
./noncirc-setlevel-answer.md:277:./route-choice-answer.md:885:./DLNFibre/Core/OrbitImageDim.lean:15:- **A0** (landed): `varietyDim Z_M = (ringKrullDim (orbitPullback M).range).unbotD 0`.
./noncirc-setlevel-answer.md:278:./route-choice-answer.md:886:./DLNFibre/Core/OrbitImageDim.lean:77:the A4.3 identity is needed (the chain is `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`);
./noncirc-setlevel-answer.md:279:./route-choice-answer.md:887:./DLNFibre/Core/OrbitImageDim.lean:90:/-- **A4.4 chained with A0: `varietyDim Z_M ≤ finrank (range δ⁰)`.** Combining the landed A0 link
./noncirc-setlevel-answer.md:280:./route-choice-answer.md:888:./DLNFibre/Core/OrbitImageDim.lean:91:(`varietyDim_eq_ringKrullDim_range_orbitPullback`, needs `[Infinite k]`) with the submersion bound,
./noncirc-setlevel-answer.md:281:./route-choice-answer.md:889:./DLNFibre/Core/OrbitImageDim.lean:95:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ
./noncirc-setlevel-answer.md:282:./route-choice-answer.md:890:./DLNFibre/Core/OrbitImageDim.lean:101:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:283:./route-choice-answer.md:891:./DLNFibre/Core/OrbitImageDim.lean:103:  rw [varietyDim_eq_ringKrullDim_range_orbitPullback M]
./noncirc-setlevel-answer.md:291:./route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./noncirc-setlevel-answer.md:292:./route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:293:./route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:294:./route-choice-answer.md:944:./DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./noncirc-setlevel-answer.md:295:./route-choice-answer.md:946:./DLNFibre/Core/FibreDimFibrationProbe.lean:59:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./noncirc-setlevel-answer.md:296:./route-choice-answer.md:947:./DLNFibre/Core/FibreDimFibrationProbe.lean:60:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./noncirc-setlevel-answer.md:297:./route-choice-answer.md:952:./DLNFibre/Core/FibreDimFibrationProbe.lean:96:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./noncirc-setlevel-answer.md:299:./route-choice-answer.md:954:./DLNFibre/Core/FibreDimFibrationProbe.lean:100:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./noncirc-setlevel-answer.md:300:./route-choice-answer.md:955:./DLNFibre/Core/FibreDimFibrationProbe.lean:102:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./noncirc-setlevel-answer.md:301:./route-choice-answer.md:1050:./DLNFibre/Core/VoigtDischarge.lean:8:The capstone of the AG half. The A4 submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`
./noncirc-setlevel-answer.md:302:./route-choice-answer.md:1051:./DLNFibre/Core/VoigtDischarge.lean:9:(`varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`, char 0) and the A6.1 reverse
./noncirc-setlevel-answer.md:303:./route-choice-answer.md:1052:./DLNFibre/Core/VoigtDischarge.lean:10:inequality `finrank (range δ⁰) ≤ varietyDim Z_M` (`finrank_range_deformationδ_le_varietyDim`) squeeze
./noncirc-setlevel-answer.md:304:./route-choice-answer.md:1053:./DLNFibre/Core/VoigtDischarge.lean:11:to **equality** `varietyDim Z_M = finrank (range δ⁰)` (the orbit closure is smooth of the expected
./noncirc-setlevel-answer.md:305:./route-choice-answer.md:1054:./DLNFibre/Core/VoigtDischarge.lean:33:/-! ## The squeeze — `varietyDim Z_M = finrank (range δ⁰)` -/
./noncirc-setlevel-answer.md:306:./route-choice-answer.md:1055:./DLNFibre/Core/VoigtDischarge.lean:38:theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
./noncirc-setlevel-answer.md:307:./route-choice-answer.md:1056:./DLNFibre/Core/VoigtDischarge.lean:40:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:308:./route-choice-answer.md:1057:./DLNFibre/Core/VoigtDischarge.lean:43:  refine le_antisymm ?_ (finrank_range_deformationδ_le_varietyDim M)
./noncirc-setlevel-answer.md:309:./route-choice-answer.md:1058:./DLNFibre/Core/VoigtDischarge.lean:44:  exact varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional M
./noncirc-setlevel-answer.md:310:./route-choice-answer.md:1059:./DLNFibre/Core/VoigtDischarge.lean:64:    have hadd := codimRep_add_varietyDim_eq_card (canonicalCoord d) (orbitRankLocus M)
./noncirc-setlevel-answer.md:311:./route-choice-answer.md:1061:./DLNFibre/Core/VoigtDischarge.lean:66:    rwa [varietyDim_orbitRankLocus_eq_finrank_range_deformationδ M, ← hr] at hadd
./noncirc-setlevel-answer.md:312:./route-choice-answer.md:1063:./DLNFibre/Core/OrbitTangentCotangent.lean:14:# `DLNFibre.Core.OrbitTangentCotangent` — A6.1: the reverse inequality `finrank(range δ⁰) ≤ varietyDim Z_M`
./noncirc-setlevel-answer.md:313:./route-choice-answer.md:1064:./DLNFibre/Core/OrbitTangentCotangent.lean:19:`varietyDim Z_M = finrank (range δ⁰)`, the geometric heart of Voigt's lemma.
./noncirc-setlevel-answer.md:315:./route-choice-answer.md:1067:./DLNFibre/Core/OrbitTangentCotangent.lean:564:/-! ## R6 — chain `finrank (m_M.Cotangent)` to `varietyDim Z_M` -/
./noncirc-setlevel-answer.md:316:./route-choice-answer.md:1068:./DLNFibre/Core/OrbitTangentCotangent.lean:566:/-- `ringKrullDim (orbitRing M)` is a finite natural number `n`, equal to `varietyDim Z_M`:
./noncirc-setlevel-answer.md:317:./route-choice-answer.md:1069:./DLNFibre/Core/OrbitTangentCotangent.lean:571:      ∧ varietyDim (canonicalCoord d '' orbitRankLocus M) = (n : ℕ∞) := by
./noncirc-setlevel-answer.md:318:./route-choice-answer.md:1070:./DLNFibre/Core/OrbitTangentCotangent.lean:579:  -- `varietyDim Z_M = (ringKrullDim (orbitRing M)).unbotD 0` (L6.4 + `varietyDim` def)
./noncirc-setlevel-answer.md:319:./route-choice-answer.md:1071:./DLNFibre/Core/OrbitTangentCotangent.lean:580:  have hvar : varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:320:./route-choice-answer.md:1072:./DLNFibre/Core/OrbitTangentCotangent.lean:582:    rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M]; rfl
./noncirc-setlevel-answer.md:321:./route-choice-answer.md:1073:./DLNFibre/Core/OrbitTangentCotangent.lean:598:/-- **R6 — `finrank k (m_M.Cotangent) = varietyDim Z_M`.** The cotangent finrank equals the variety
./noncirc-setlevel-answer.md:322:./route-choice-answer.md:1074:./DLNFibre/Core/OrbitTangentCotangent.lean:601:GAP3 (`ringKrullDim (AtPrime m_M) = ringKrullDim (orbitRing M)`), and `varietyDim Z_M =
./noncirc-setlevel-answer.md:323:./route-choice-answer.md:1075:./DLNFibre/Core/OrbitTangentCotangent.lean:603:theorem finrank_cotangent_eq_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./noncirc-setlevel-answer.md:324:./route-choice-answer.md:1076:./DLNFibre/Core/OrbitTangentCotangent.lean:605:      = varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./noncirc-setlevel-answer.md:325:./route-choice-answer.md:1078:./DLNFibre/Core/OrbitTangentCotangent.lean:635:/-! ## The A6.1 headline — `finrank (range δ⁰) ≤ varietyDim Z_M` -/
./noncirc-setlevel-answer.md:326:./route-choice-answer.md:1079:./DLNFibre/Core/OrbitTangentCotangent.lean:637:/-- **A6.1 (the reverse inequality).** `finrank k (range δ⁰) ≤ varietyDim Z_M`: the orbit tangent
./noncirc-setlevel-answer.md:327:./route-choice-answer.md:1080:./DLNFibre/Core/OrbitTangentCotangent.lean:641:theorem finrank_range_deformationδ_le_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./noncirc-setlevel-answer.md:328:./route-choice-answer.md:1081:./DLNFibre/Core/OrbitTangentCotangent.lean:643:      ≤ varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./noncirc-setlevel-answer.md:329:./route-choice-answer.md:1082:./DLNFibre/Core/OrbitTangentCotangent.lean:644:  rw [← finrank_cotangent_eq_varietyDim M]
./noncirc-setlevel-answer.md:330:./route-choice-answer.md:1083:./DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./noncirc-setlevel-answer.md:331:./route-choice-answer.md:1084:./DLNFibre/Core/RouteCAssembly.lean:18:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./noncirc-setlevel-answer.md:332:./route-choice-answer.md:1085:./DLNFibre/Core/RouteCAssembly.lean:20:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./noncirc-setlevel-answer.md:333:./route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:334:./route-choice-answer.md:1087:./DLNFibre/Core/RouteCAssembly.lean:52:          + varietyDim (canonicalCoord d '' fibre d B))
./noncirc-setlevel-answer.md:335:./route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:336:./route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./noncirc-setlevel-answer.md:337:./route-choice-answer.md:1090:./DLNFibre/Core/RouteCAssembly.lean:56:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./noncirc-setlevel-answer.md:338:./route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./noncirc-setlevel-answer.md:339:./route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./noncirc-setlevel-answer.md:340:./route-choice-answer.md:1096:./DLNFibre/Core/RouteCAssembly.lean:69:        + varietyDim (canonicalCoord d '' fibre d B) := by
./noncirc-setlevel-answer.md:341:./route-choice-answer.md:1097:./DLNFibre/Core/RouteCAssembly.lean:72:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./noncirc-setlevel-answer.md:342:./route-choice-answer.md:1098:./DLNFibre/Core/RouteCAssembly.lean:79:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./noncirc-setlevel-answer.md:343:./route-choice-answer.md:1099:./DLNFibre/Core/RouteCAssembly.lean:80:      = varietyDim (canonicalCoord d '' fibre d B)
./noncirc-setlevel-answer.md:344:./route-choice-answer.md:1100:./DLNFibre/Core/RouteCAssembly.lean:82:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./noncirc-setlevel-answer.md:345:./route-choice-answer.md:1101:./DLNFibre/Core/RouteCAssembly.lean:83:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./noncirc-setlevel-answer.md:346:./route-choice-answer.md:1102:./DLNFibre/Core/RouteCAssembly.lean:88:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./noncirc-setlevel-answer.md:347:./route-choice-answer.md:1103:./DLNFibre/Core/RouteCAssembly.lean:89:      _ = varietyDim (canonicalCoord d '' fibre d B)
./noncirc-setlevel-answer.md:348:./route-choice-answer.md:1104:./DLNFibre/Core/RouteCAssembly.lean:100:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./noncirc-setlevel-answer.md:349:./route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:350:./route-choice-answer.md:1107:./DLNFibre/Core/RouteCAssembly.lean:109:          + varietyDim (canonicalCoord d '' fibre d B))
./noncirc-setlevel-answer.md:351:./route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:352:./route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./noncirc-setlevel-answer.md:353:./route-choice-answer.md:1110:./DLNFibre/Core/RouteCAssembly.lean:115:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./noncirc-setlevel-answer.md:354:./route-choice-answer.md:1111:./DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./noncirc-setlevel-answer.md:356:./route-choice-answer.md:1172:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./noncirc-setlevel-answer.md:359:./route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:363:./route-choice-answer.md:1191:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./noncirc-setlevel-answer.md:364:./route-choice-answer.md:1192:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./noncirc-setlevel-answer.md:365:./route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:366:./route-choice-answer.md:1195:  rw [varietyDim, ← hI] at hvd
./noncirc-setlevel-answer.md:383:./route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./noncirc-setlevel-answer.md:384:./route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:385:./route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:386:./route-choice-answer.md:1321:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./noncirc-setlevel-answer.md:387:./route-choice-answer.md:1325:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./noncirc-setlevel-answer.md:388:./route-choice-answer.md:1326:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./noncirc-setlevel-answer.md:445:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:446:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:464:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:466:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:477:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:484:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:489:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:491:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:499:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:503:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:506:   reducedness), say so plainly — that triggers a fallback to citing `hSweep`.
./noncirc-setlevel-answer.md:508:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:519:/bin/bash -lc "rg -n \"varietyDim|ringKrullDim|radical|IsJacobson|KrullDim|tensor|TensorProduct\" . -g '*.lean' -g '*.md' | head -300" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:521:./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:522:./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:523:./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:524:./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:527:./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:529:./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:530:./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:531:./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:532:./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:534:./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:536:./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:538:./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:540:./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:543:./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:544:./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:548:./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:550:./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:552:./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:553:./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-answer.md:554:./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-answer.md:556:./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-answer.md:558:./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-answer.md:560:./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-answer.md:562:./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-answer.md:565:./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-answer.md:566:./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-answer.md:570:./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-answer.md:572:./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-answer.md:574:./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./noncirc-setlevel-answer.md:575:./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:576:./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:577:./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:578:./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:581:./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:583:./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:584:./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:587:./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./noncirc-setlevel-answer.md:588:./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./noncirc-setlevel-answer.md:589:./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./noncirc-setlevel-answer.md:590:./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./noncirc-setlevel-answer.md:593:./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./noncirc-setlevel-answer.md:595:./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./noncirc-setlevel-answer.md:596:./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-answer.md:599:./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./noncirc-setlevel-answer.md:600:./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./noncirc-setlevel-answer.md:601:./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./noncirc-setlevel-answer.md:602:./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./noncirc-setlevel-answer.md:603:./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./noncirc-setlevel-answer.md:604:./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./noncirc-setlevel-answer.md:605:./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./noncirc-setlevel-answer.md:606:./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./noncirc-setlevel-answer.md:607:./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:608:./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./noncirc-setlevel-answer.md:609:./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./noncirc-setlevel-answer.md:610:./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:611:./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./noncirc-setlevel-answer.md:612:./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./noncirc-setlevel-answer.md:613:./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./noncirc-setlevel-answer.md:614:./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./noncirc-setlevel-answer.md:615:./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./noncirc-setlevel-answer.md:616:./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./noncirc-setlevel-answer.md:617:./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./noncirc-setlevel-answer.md:618:./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./noncirc-setlevel-answer.md:619:./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:620:./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./noncirc-setlevel-answer.md:621:./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./noncirc-setlevel-answer.md:622:./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./noncirc-setlevel-answer.md:623:./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./noncirc-setlevel-answer.md:624:./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./noncirc-setlevel-answer.md:626:./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./noncirc-setlevel-answer.md:627:./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:629:./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./noncirc-setlevel-answer.md:630:./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./noncirc-setlevel-answer.md:631:./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:632:./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./noncirc-setlevel-answer.md:634:./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./noncirc-setlevel-answer.md:640:./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./noncirc-setlevel-answer.md:641:./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./noncirc-setlevel-answer.md:695:route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./noncirc-setlevel-answer.md:710:route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./noncirc-setlevel-answer.md:711:route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./noncirc-setlevel-answer.md:712:route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./noncirc-setlevel-answer.md:732:route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./noncirc-setlevel-answer.md:733:route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:737:route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./noncirc-setlevel-answer.md:738:route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./noncirc-setlevel-answer.md:755:route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:761:route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:768:route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./noncirc-setlevel-answer.md:782:route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./noncirc-setlevel-answer.md:784:route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./noncirc-setlevel-answer.md:787:route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./noncirc-setlevel-answer.md:788:route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./noncirc-setlevel-answer.md:834:route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./noncirc-setlevel-answer.md:846:route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./noncirc-setlevel-answer.md:870:route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./noncirc-setlevel-answer.md:871:route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:872:route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:895:route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:896:route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:897:route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./noncirc-setlevel-answer.md:899:route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./noncirc-setlevel-answer.md:902:route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./noncirc-setlevel-answer.md:904:route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:905:route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./noncirc-setlevel-answer.md:906:route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./noncirc-setlevel-answer.md:921:route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./noncirc-setlevel-answer.md:928:route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:946:route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./noncirc-setlevel-answer.md:947:route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./noncirc-setlevel-answer.md:948:route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./noncirc-setlevel-answer.md:1090:/bin/bash -lc 'rg -n "ringKrullDim.*TensorProduct|TensorProduct.*ringKrullDim|varietyDim.*prod|zeroLocus.*prod|vanishingIdeal.*union|iSup|iInf|sup.*vanishing|trdeg.*TensorProduct|TensorProduct.*trdeg" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:2011:So for question 1, the answer is yes mathematically and easy in Lean, but there is no obvious prepackaged lemma named exactly `ringKrullDim_quotient_radical` in v4.29. It is a two-rewrite lemma from `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`.
./noncirc-setlevel-answer.md:2447:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:131:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
./noncirc-setlevel-answer.md:2448:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:132:It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
./noncirc-setlevel-answer.md:2452:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:138:/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
./noncirc-setlevel-answer.md:2455:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:147:  rw [← Ideal.radical_eq_iff, IadDeep,
./noncirc-setlevel-answer.md:2456:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:148:    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
./noncirc-setlevel-answer.md:2458:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:152:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
./noncirc-setlevel-answer.md:2468:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:417:`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
./noncirc-setlevel-answer.md:2481:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:106:⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
./noncirc-setlevel-answer.md:2488:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:133:    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]
./noncirc-setlevel-answer.md:2639:lemma test_ringKrullDim_quotient_radical (I : Ideal R) :
./noncirc-setlevel-answer.md:2643:lemma test_ringKrullDim_quotient_radical' (I : Ideal R) :
./noncirc-setlevel-answer.md:2645:  rw [test_ringKrullDim_quotient_radical]
./noncirc-setlevel-answer.md:2656:lemma test_ringKrullDim_quotient_radical (I : Ideal R) :
./noncirc-setlevel-answer.md:2660:lemma test_ringKrullDim_quotient_radical' (I : Ideal R) :
./noncirc-setlevel-answer.md:2662:  rw [test_ringKrullDim_quotient_radical]
./noncirc-setlevel-answer.md:2712:/bin/bash -lc 'rg -n "def vanishingIdeal|theorem vanishingIdeal|lemma vanishingIdeal|zeroLocus_eq|vanishingIdeal.*iUnion|vanishingIdeal.*union|radical|varietyDim" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./noncirc-setlevel-answer.md:2729:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./noncirc-setlevel-answer.md:2730:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./noncirc-setlevel-answer.md:2742:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./noncirc-setlevel-answer.md:2743:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./noncirc-setlevel-answer.md:2744:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:2745:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:2746:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./noncirc-setlevel-answer.md:2747:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./noncirc-setlevel-answer.md:2748:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./noncirc-setlevel-answer.md:2749:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:2750:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./noncirc-setlevel-answer.md:2751:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:2752:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./noncirc-setlevel-answer.md:2753:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./noncirc-setlevel-answer.md:2754:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:2755:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./noncirc-setlevel-answer.md:2756:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:2757:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./noncirc-setlevel-answer.md:2758:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:2759:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./noncirc-setlevel-answer.md:2760:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./noncirc-setlevel-answer.md:2761:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./noncirc-setlevel-answer.md:2762:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./noncirc-setlevel-answer.md:2763:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./noncirc-setlevel-answer.md:2764:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./noncirc-setlevel-answer.md:2766:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./noncirc-setlevel-answer.md:2767:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:2768:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./noncirc-setlevel-answer.md:2792:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./noncirc-setlevel-answer.md:2797:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./noncirc-setlevel-answer.md:2800:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:2802:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./noncirc-setlevel-answer.md:2810:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./noncirc-setlevel-answer.md:2815:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./noncirc-setlevel-answer.md:2816:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./noncirc-setlevel-answer.md:2818:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./noncirc-setlevel-answer.md:2820:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./noncirc-setlevel-answer.md:2821:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./noncirc-setlevel-answer.md:2822:  have hne : varietyDim Z ≠ ⊤ := by
./noncirc-setlevel-answer.md:2882:One more adversarial point: the project’s `varietyDim` itself says it is the dimension of the Zariski closure unless the set is closed. That is fine for radical-insensitivity, but for chart opens and exact-rank strata you must explicitly account for “open chart has same closure dimension” or use the cited `hClosure` bridge.
./noncirc-setlevel-answer.md:3214:**Verdict: YES.** The set-level/`varietyDim` route dodges the R2-3b-4 circularity. The old circularity was specific to building a scheme/ring iso through the *generator* ideal and needing `sigmaIdeal ≤ ker`. If you work with sets and `vanishingIdeal`, the coordinate rings are already reduced-by-definition, and the required ideal containment for pullbacks is the tautological one: “a polynomial vanishing on the target pulls back to one vanishing on the source.”
./noncirc-setlevel-answer.md:3216:1. **Radical-insensitivity:** yes. I do not see a prepackaged v4.29 lemma named exactly `ringKrullDim_quotient_radical`, but it is a two-line lemma from Mathlib:
./noncirc-setlevel-answer.md:3220:lemma ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
./noncirc-setlevel-answer.md:3224:The relevant upstream pieces are `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`. So `varietyDim` genuinely only sees the radical/closed-set structure.
./noncirc-setlevel-answer.md:3231:None of that needs `sigmaIdeal ≤ ker`. The warning is different: a bare set bijection does not preserve `varietyDim`; you need the map and inverse to be regular on the pivot chart, typically via localization/principal-open coordinates. That is new chart algebra, but not the old reducedness circularity.
./noncirc-setlevel-answer.md:3237:But I do not see this as an existing Mathlib v4.29 theorem for `varietyDim`, nor a general
./noncirc-setlevel-answer.md:3242:`dim (⋃ᵢ Zᵢ) = maxᵢ dim Zᵢ` for finite nonempty covers, radical-insensitively. Mathlib has the Spec-level zero-locus/vanishing-ideal union facts, e.g. `PrimeSpectrum.vanishingIdeal_union`, `PrimeSpectrum.vanishingIdeal_iUnion`, `PrimeSpectrum.zeroLocus_inf`, but I do not see a ready `varietyDim_finite_iUnion` theorem. Also note your `varietyDim` sends the empty set to `0` via `unbotD 0`, so state product/union lemmas with the relevant nonemptiness assumptions.
./noncirc-setlevel-answer.md:3249:  `varietyDim(chart) = varietyDim U_P + varietyDim F = δ + varietyDim F`.
./noncirc-setlevel-answer.md:3251:- Glue: finite pivot cover gives global dimension by finite-union max; use the closure/open-chart bridge carefully because `varietyDim` is closure dimension for arbitrary sets.
./noncirc-setlevel-answer.md:3253:So the de-risk claim is correct: radical-insensitivity of `varietyDim` removes the need to prove `fibreGenIdeal = radical fibreGenIdeal` or `sigmaIdeal ≤ ker` for the generator-level scheme iso. The remaining risk is library/build cost for product dimension and finite-glue lemmas, not circularity.
./noncirc-setlevel-answer.md:3256:**Verdict: YES.** The set-level/`varietyDim` route dodges the R2-3b-4 circularity. The old circularity was specific to building a scheme/ring iso through the *generator* ideal and needing `sigmaIdeal ≤ ker`. If you work with sets and `vanishingIdeal`, the coordinate rings are already reduced-by-definition, and the required ideal containment for pullbacks is the tautological one: “a polynomial vanishing on the target pulls back to one vanishing on the source.”
./noncirc-setlevel-answer.md:3258:1. **Radical-insensitivity:** yes. I do not see a prepackaged v4.29 lemma named exactly `ringKrullDim_quotient_radical`, but it is a two-line lemma from Mathlib:
./noncirc-setlevel-answer.md:3262:lemma ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
./noncirc-setlevel-answer.md:3266:The relevant upstream pieces are `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`. So `varietyDim` genuinely only sees the radical/closed-set structure.
./noncirc-setlevel-answer.md:3273:None of that needs `sigmaIdeal ≤ ker`. The warning is different: a bare set bijection does not preserve `varietyDim`; you need the map and inverse to be regular on the pivot chart, typically via localization/principal-open coordinates. That is new chart algebra, but not the old reducedness circularity.
./noncirc-setlevel-answer.md:3279:But I do not see this as an existing Mathlib v4.29 theorem for `varietyDim`, nor a general
./noncirc-setlevel-answer.md:3284:`dim (⋃ᵢ Zᵢ) = maxᵢ dim Zᵢ` for finite nonempty covers, radical-insensitively. Mathlib has the Spec-level zero-locus/vanishing-ideal union facts, e.g. `PrimeSpectrum.vanishingIdeal_union`, `PrimeSpectrum.vanishingIdeal_iUnion`, `PrimeSpectrum.zeroLocus_inf`, but I do not see a ready `varietyDim_finite_iUnion` theorem. Also note your `varietyDim` sends the empty set to `0` via `unbotD 0`, so state product/union lemmas with the relevant nonemptiness assumptions.
./noncirc-setlevel-answer.md:3291:  `varietyDim(chart) = varietyDim U_P + varietyDim F = δ + varietyDim F`.
./noncirc-setlevel-answer.md:3293:- Glue: finite pivot cover gives global dimension by finite-union max; use the closure/open-chart bridge carefully because `varietyDim` is closure dimension for arbitrary sets.
./noncirc-setlevel-answer.md:3295:So the de-risk claim is correct: radical-insensitivity of `varietyDim` removes the need to prove `fibreGenIdeal = radical fibreGenIdeal` or `sigmaIdeal ≤ ker` for the generator-level scheme iso. The remaining risk is library/build cost for product dimension and finite-glue lemmas, not circularity.
./rung2-regular-section-answer.md:18:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-answer.md:19:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-answer.md:20:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:28:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-answer.md:33:- `U_P ⊆ Mat^{=r}` = pivot chart where the top-left `r×r` minor `ΔP` is invertible (a principal open
./rung2-regular-section-answer.md:34:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-answer.md:35:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-answer.md:37:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-answer.md:41:1. **On the pivot chart `D(ΔP)`, is there a REGULAR (polynomial-in-entries-after-inverting-ΔP)
./rung2-regular-section-answer.md:44:   the inverse of that block and its Schur complement — all REGULAR after inverting `ΔP`. So I expect
./rung2-regular-section-answer.md:52:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-answer.md:55:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-answer.md:57:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-answer.md:59:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-answer.md:61:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-answer.md:65:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-answer.md:73:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-answer.md:74:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:78:I’ll inspect the local Lean/exposition scaffolding around `varietyDim`, pivot charts, and the landed rank/base-change lemmas so the advice matches the actual API rather than an abstract algebraic-geometry answer.
./rung2-regular-section-answer.md:80:/bin/bash -lc 'pwd && rg -n "def varietyDim|varietyDim|vanishingIdeal|ringKrullDim|exists_baseChange_of_rank_eq|DeepChartRing|ΔPdeep|mult_smul|baseChange|rank_eq" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-answer.md:96:./rung2-regular-section-prompt.md:3:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-answer.md:97:./rung2-regular-section-prompt.md:4:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-answer.md:98:./rung2-regular-section-prompt.md:5:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:100:./rung2-regular-section-prompt.md:13:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-answer.md:101:./rung2-regular-section-prompt.md:19:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-answer.md:102:./rung2-regular-section-prompt.md:20:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-answer.md:104:./rung2-regular-section-prompt.md:22:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-answer.md:105:./rung2-regular-section-prompt.md:37:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-answer.md:106:./rung2-regular-section-prompt.md:40:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-answer.md:108:./rung2-regular-section-prompt.md:42:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-answer.md:110:./rung2-regular-section-prompt.md:44:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-answer.md:111:./rung2-regular-section-prompt.md:46:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-answer.md:113:./rung2-regular-section-prompt.md:50:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-answer.md:114:./rung2-regular-section-prompt.md:58:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-answer.md:115:./rung2-regular-section-prompt.md:59:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:116:./rung2-regular-section-answer.md:18:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-answer.md:117:./rung2-regular-section-answer.md:19:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-answer.md:118:./rung2-regular-section-answer.md:20:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:120:./rung2-regular-section-answer.md:28:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-answer.md:121:./rung2-regular-section-answer.md:34:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-answer.md:122:./rung2-regular-section-answer.md:35:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-answer.md:124:./rung2-regular-section-answer.md:37:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-answer.md:125:./rung2-regular-section-answer.md:52:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-answer.md:126:./rung2-regular-section-answer.md:55:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-answer.md:128:./rung2-regular-section-answer.md:57:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-answer.md:130:./rung2-regular-section-answer.md:59:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-answer.md:131:./rung2-regular-section-answer.md:61:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-answer.md:133:./rung2-regular-section-answer.md:65:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-answer.md:134:./rung2-regular-section-answer.md:73:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-answer.md:135:./rung2-regular-section-answer.md:74:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:136:./rung2-regular-section-answer.md:78:I’ll inspect the local Lean/exposition scaffolding around `varietyDim`, pivot charts, and the landed rank/base-change lemmas so the advice matches the actual API rather than an abstract algebraic-geometry answer.
./rung2-regular-section-answer.md:137:./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./rung2-regular-section-answer.md:138:./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./rung2-regular-section-answer.md:139:./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./rung2-regular-section-answer.md:141:./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./rung2-regular-section-answer.md:142:./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./rung2-regular-section-answer.md:144:./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./rung2-regular-section-answer.md:145:./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./rung2-regular-section-answer.md:146:./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./rung2-regular-section-answer.md:148:./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./rung2-regular-section-answer.md:150:./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./rung2-regular-section-answer.md:151:./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-regular-section-answer.md:152:./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:153:./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:154:./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:155:./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:158:./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:160:./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:161:./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:162:./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:163:./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:164:./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:165:./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:168:./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:170:./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:171:./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:174:./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:175:./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:176:./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:177:./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:180:./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:182:./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:183:./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:186:./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./rung2-regular-section-answer.md:187:./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./rung2-regular-section-answer.md:189:./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./rung2-regular-section-answer.md:190:./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./rung2-regular-section-answer.md:191:./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./rung2-regular-section-answer.md:194:./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./rung2-regular-section-answer.md:195:./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./rung2-regular-section-answer.md:198:./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./rung2-regular-section-answer.md:199:./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:200:./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./rung2-regular-section-answer.md:202:./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./rung2-regular-section-answer.md:203:./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:204:./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:205:./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./rung2-regular-section-answer.md:206:./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./rung2-regular-section-answer.md:207:./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./rung2-regular-section-answer.md:208:./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./rung2-regular-section-answer.md:220:./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./rung2-regular-section-answer.md:226:./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./rung2-regular-section-answer.md:227:./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./rung2-regular-section-answer.md:228:./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:229:./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./rung2-regular-section-answer.md:231:./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./rung2-regular-section-answer.md:232:./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./rung2-regular-section-answer.md:233:./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./rung2-regular-section-answer.md:234:./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./rung2-regular-section-answer.md:261:./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./rung2-regular-section-answer.md:262:./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./rung2-regular-section-answer.md:267:./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./rung2-regular-section-answer.md:268:./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./rung2-regular-section-answer.md:269:./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:270:./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./rung2-regular-section-answer.md:283:./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./rung2-regular-section-answer.md:309:./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./rung2-regular-section-answer.md:310:./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./rung2-regular-section-answer.md:334:./route-choice-answer.md:674:./DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./rung2-regular-section-answer.md:337:./route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./rung2-regular-section-answer.md:339:./route-choice-answer.md:679:./DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:341:./route-choice-answer.md:681:./DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:346:./route-choice-answer.md:686:./DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:347:./route-choice-answer.md:687:./DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./rung2-regular-section-answer.md:348:./route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./rung2-regular-section-answer.md:349:./route-choice-answer.md:689:./DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:351:./route-choice-answer.md:691:./DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./rung2-regular-section-answer.md:352:./route-choice-answer.md:692:./DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./rung2-regular-section-answer.md:353:./route-choice-answer.md:693:./DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./rung2-regular-section-answer.md:354:./route-choice-answer.md:694:./DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./rung2-regular-section-answer.md:355:./route-choice-answer.md:695:./DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:357:./route-choice-answer.md:697:./DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./rung2-regular-section-answer.md:358:./route-choice-answer.md:698:./DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./rung2-regular-section-answer.md:359:./route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./rung2-regular-section-answer.md:360:./route-choice-answer.md:700:./DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:362:./route-choice-answer.md:702:./DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./rung2-regular-section-answer.md:363:./route-choice-answer.md:703:./DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./rung2-regular-section-answer.md:364:./route-choice-answer.md:704:./DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./rung2-regular-section-answer.md:365:./route-choice-answer.md:705:./DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:367:./route-choice-answer.md:707:./DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:368:./route-choice-answer.md:708:./DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./rung2-regular-section-answer.md:372:./route-choice-answer.md:712:./DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./rung2-regular-section-answer.md:374:./route-choice-answer.md:714:./DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:377:./route-choice-answer.md:717:./DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./rung2-regular-section-answer.md:429:./route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./rung2-regular-section-answer.md:430:./route-choice-answer.md:821:./DLNFibre/Core/OrbitDifferentialRank.lean:659:/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
./rung2-regular-section-answer.md:431:./route-choice-answer.md:822:./DLNFibre/Core/OrbitDifferentialRank.lean:660:Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
./rung2-regular-section-answer.md:432:./route-choice-answer.md:823:./DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./rung2-regular-section-answer.md:433:./route-choice-answer.md:824:./DLNFibre/Core/OrbitDifferentialRank.lean:666:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:434:./route-choice-answer.md:825:./DLNFibre/Core/OrbitDifferentialRank.lean:668:  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
./rung2-regular-section-answer.md:438:./route-choice-answer.md:846:./DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./rung2-regular-section-answer.md:439:./route-choice-answer.md:847:./DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./rung2-regular-section-answer.md:444:./route-choice-answer.md:852:./DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./rung2-regular-section-answer.md:445:./route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./rung2-regular-section-answer.md:446:./route-choice-answer.md:854:./DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:447:./route-choice-answer.md:855:./DLNFibre/Core/RadicalCatenary.lean:181:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
./rung2-regular-section-answer.md:454:./route-choice-answer.md:862:./DLNFibre/Core/RadicalCatenary.lean:197:  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:455:./route-choice-answer.md:863:./DLNFibre/Core/RadicalCatenary.lean:203:The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
./rung2-regular-section-answer.md:456:./route-choice-answer.md:864:./DLNFibre/Core/RadicalCatenary.lean:208:      + varietyDim (canonicalCoord dWitness ''
./rung2-regular-section-answer.md:457:./route-choice-answer.md:865:./DLNFibre/Core/RadicalCatenary.lean:211:  codimRepCanonical_add_varietyDim_eq_card_of_nonempty
./rung2-regular-section-answer.md:458:./route-choice-answer.md:884:./DLNFibre/Core/OrbitImageDim.lean:10:(`varietyDim_eq_ringKrullDim_range_orbitPullback`), discharges the AG-half of `hVoigt`:
./rung2-regular-section-answer.md:459:./route-choice-answer.md:885:./DLNFibre/Core/OrbitImageDim.lean:15:- **A0** (landed): `varietyDim Z_M = (ringKrullDim (orbitPullback M).range).unbotD 0`.
./rung2-regular-section-answer.md:460:./route-choice-answer.md:886:./DLNFibre/Core/OrbitImageDim.lean:77:the A4.3 identity is needed (the chain is `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`);
./rung2-regular-section-answer.md:461:./route-choice-answer.md:887:./DLNFibre/Core/OrbitImageDim.lean:90:/-- **A4.4 chained with A0: `varietyDim Z_M ≤ finrank (range δ⁰)`.** Combining the landed A0 link
./rung2-regular-section-answer.md:462:./route-choice-answer.md:888:./DLNFibre/Core/OrbitImageDim.lean:91:(`varietyDim_eq_ringKrullDim_range_orbitPullback`, needs `[Infinite k]`) with the submersion bound,
./rung2-regular-section-answer.md:463:./route-choice-answer.md:889:./DLNFibre/Core/OrbitImageDim.lean:95:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ
./rung2-regular-section-answer.md:464:./route-choice-answer.md:890:./DLNFibre/Core/OrbitImageDim.lean:101:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:465:./route-choice-answer.md:891:./DLNFibre/Core/OrbitImageDim.lean:103:  rw [varietyDim_eq_ringKrullDim_range_orbitPullback M]
./rung2-regular-section-answer.md:507:./route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./rung2-regular-section-answer.md:508:./route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:509:./route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:510:./route-choice-answer.md:944:./DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./rung2-regular-section-answer.md:512:./route-choice-answer.md:946:./DLNFibre/Core/FibreDimFibrationProbe.lean:59:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:513:./route-choice-answer.md:947:./DLNFibre/Core/FibreDimFibrationProbe.lean:60:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./rung2-regular-section-answer.md:516:./route-choice-answer.md:952:./DLNFibre/Core/FibreDimFibrationProbe.lean:96:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./rung2-regular-section-answer.md:518:./route-choice-answer.md:954:./DLNFibre/Core/FibreDimFibrationProbe.lean:100:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./rung2-regular-section-answer.md:519:./route-choice-answer.md:955:./DLNFibre/Core/FibreDimFibrationProbe.lean:102:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./rung2-regular-section-answer.md:596:./route-choice-answer.md:1050:./DLNFibre/Core/VoigtDischarge.lean:8:The capstone of the AG half. The A4 submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`
./rung2-regular-section-answer.md:597:./route-choice-answer.md:1051:./DLNFibre/Core/VoigtDischarge.lean:9:(`varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`, char 0) and the A6.1 reverse
./rung2-regular-section-answer.md:598:./route-choice-answer.md:1052:./DLNFibre/Core/VoigtDischarge.lean:10:inequality `finrank (range δ⁰) ≤ varietyDim Z_M` (`finrank_range_deformationδ_le_varietyDim`) squeeze
./rung2-regular-section-answer.md:599:./route-choice-answer.md:1053:./DLNFibre/Core/VoigtDischarge.lean:11:to **equality** `varietyDim Z_M = finrank (range δ⁰)` (the orbit closure is smooth of the expected
./rung2-regular-section-answer.md:600:./route-choice-answer.md:1054:./DLNFibre/Core/VoigtDischarge.lean:33:/-! ## The squeeze — `varietyDim Z_M = finrank (range δ⁰)` -/
./rung2-regular-section-answer.md:601:./route-choice-answer.md:1055:./DLNFibre/Core/VoigtDischarge.lean:38:theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
./rung2-regular-section-answer.md:602:./route-choice-answer.md:1056:./DLNFibre/Core/VoigtDischarge.lean:40:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:603:./route-choice-answer.md:1057:./DLNFibre/Core/VoigtDischarge.lean:43:  refine le_antisymm ?_ (finrank_range_deformationδ_le_varietyDim M)
./rung2-regular-section-answer.md:604:./route-choice-answer.md:1058:./DLNFibre/Core/VoigtDischarge.lean:44:  exact varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional M
./rung2-regular-section-answer.md:605:./route-choice-answer.md:1059:./DLNFibre/Core/VoigtDischarge.lean:64:    have hadd := codimRep_add_varietyDim_eq_card (canonicalCoord d) (orbitRankLocus M)
./rung2-regular-section-answer.md:607:./route-choice-answer.md:1061:./DLNFibre/Core/VoigtDischarge.lean:66:    rwa [varietyDim_orbitRankLocus_eq_finrank_range_deformationδ M, ← hr] at hadd
./rung2-regular-section-answer.md:609:./route-choice-answer.md:1063:./DLNFibre/Core/OrbitTangentCotangent.lean:14:# `DLNFibre.Core.OrbitTangentCotangent` — A6.1: the reverse inequality `finrank(range δ⁰) ≤ varietyDim Z_M`
./rung2-regular-section-answer.md:610:./route-choice-answer.md:1064:./DLNFibre/Core/OrbitTangentCotangent.lean:19:`varietyDim Z_M = finrank (range δ⁰)`, the geometric heart of Voigt's lemma.
./rung2-regular-section-answer.md:613:./route-choice-answer.md:1067:./DLNFibre/Core/OrbitTangentCotangent.lean:564:/-! ## R6 — chain `finrank (m_M.Cotangent)` to `varietyDim Z_M` -/
./rung2-regular-section-answer.md:614:./route-choice-answer.md:1068:./DLNFibre/Core/OrbitTangentCotangent.lean:566:/-- `ringKrullDim (orbitRing M)` is a finite natural number `n`, equal to `varietyDim Z_M`:
./rung2-regular-section-answer.md:615:./route-choice-answer.md:1069:./DLNFibre/Core/OrbitTangentCotangent.lean:571:      ∧ varietyDim (canonicalCoord d '' orbitRankLocus M) = (n : ℕ∞) := by
./rung2-regular-section-answer.md:616:./route-choice-answer.md:1070:./DLNFibre/Core/OrbitTangentCotangent.lean:579:  -- `varietyDim Z_M = (ringKrullDim (orbitRing M)).unbotD 0` (L6.4 + `varietyDim` def)
./rung2-regular-section-answer.md:617:./route-choice-answer.md:1071:./DLNFibre/Core/OrbitTangentCotangent.lean:580:  have hvar : varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:618:./route-choice-answer.md:1072:./DLNFibre/Core/OrbitTangentCotangent.lean:582:    rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M]; rfl
./rung2-regular-section-answer.md:619:./route-choice-answer.md:1073:./DLNFibre/Core/OrbitTangentCotangent.lean:598:/-- **R6 — `finrank k (m_M.Cotangent) = varietyDim Z_M`.** The cotangent finrank equals the variety
./rung2-regular-section-answer.md:620:./route-choice-answer.md:1074:./DLNFibre/Core/OrbitTangentCotangent.lean:601:GAP3 (`ringKrullDim (AtPrime m_M) = ringKrullDim (orbitRing M)`), and `varietyDim Z_M =
./rung2-regular-section-answer.md:621:./route-choice-answer.md:1075:./DLNFibre/Core/OrbitTangentCotangent.lean:603:theorem finrank_cotangent_eq_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./rung2-regular-section-answer.md:622:./route-choice-answer.md:1076:./DLNFibre/Core/OrbitTangentCotangent.lean:605:      = varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./rung2-regular-section-answer.md:624:./route-choice-answer.md:1078:./DLNFibre/Core/OrbitTangentCotangent.lean:635:/-! ## The A6.1 headline — `finrank (range δ⁰) ≤ varietyDim Z_M` -/
./rung2-regular-section-answer.md:625:./route-choice-answer.md:1079:./DLNFibre/Core/OrbitTangentCotangent.lean:637:/-- **A6.1 (the reverse inequality).** `finrank k (range δ⁰) ≤ varietyDim Z_M`: the orbit tangent
./rung2-regular-section-answer.md:626:./route-choice-answer.md:1080:./DLNFibre/Core/OrbitTangentCotangent.lean:641:theorem finrank_range_deformationδ_le_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./rung2-regular-section-answer.md:627:./route-choice-answer.md:1081:./DLNFibre/Core/OrbitTangentCotangent.lean:643:      ≤ varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./rung2-regular-section-answer.md:628:./route-choice-answer.md:1082:./DLNFibre/Core/OrbitTangentCotangent.lean:644:  rw [← finrank_cotangent_eq_varietyDim M]
./rung2-regular-section-answer.md:629:./route-choice-answer.md:1083:./DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./rung2-regular-section-answer.md:630:./route-choice-answer.md:1084:./DLNFibre/Core/RouteCAssembly.lean:18:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./rung2-regular-section-answer.md:631:./route-choice-answer.md:1085:./DLNFibre/Core/RouteCAssembly.lean:20:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./rung2-regular-section-answer.md:632:./route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:633:./route-choice-answer.md:1087:./DLNFibre/Core/RouteCAssembly.lean:52:          + varietyDim (canonicalCoord d '' fibre d B))
./rung2-regular-section-answer.md:634:./route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:635:./route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./rung2-regular-section-answer.md:636:./route-choice-answer.md:1090:./DLNFibre/Core/RouteCAssembly.lean:56:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./rung2-regular-section-answer.md:637:./route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:638:./route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:639:./route-choice-answer.md:1096:./DLNFibre/Core/RouteCAssembly.lean:69:        + varietyDim (canonicalCoord d '' fibre d B) := by
./rung2-regular-section-answer.md:640:./route-choice-answer.md:1097:./DLNFibre/Core/RouteCAssembly.lean:72:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./rung2-regular-section-answer.md:641:./route-choice-answer.md:1098:./DLNFibre/Core/RouteCAssembly.lean:79:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./rung2-regular-section-answer.md:642:./route-choice-answer.md:1099:./DLNFibre/Core/RouteCAssembly.lean:80:      = varietyDim (canonicalCoord d '' fibre d B)
./rung2-regular-section-answer.md:643:./route-choice-answer.md:1100:./DLNFibre/Core/RouteCAssembly.lean:82:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./rung2-regular-section-answer.md:644:./route-choice-answer.md:1101:./DLNFibre/Core/RouteCAssembly.lean:83:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./rung2-regular-section-answer.md:645:./route-choice-answer.md:1102:./DLNFibre/Core/RouteCAssembly.lean:88:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./rung2-regular-section-answer.md:646:./route-choice-answer.md:1103:./DLNFibre/Core/RouteCAssembly.lean:89:      _ = varietyDim (canonicalCoord d '' fibre d B)
./rung2-regular-section-answer.md:647:./route-choice-answer.md:1104:./DLNFibre/Core/RouteCAssembly.lean:100:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./rung2-regular-section-answer.md:648:./route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:649:./route-choice-answer.md:1107:./DLNFibre/Core/RouteCAssembly.lean:109:          + varietyDim (canonicalCoord d '' fibre d B))
./rung2-regular-section-answer.md:650:./route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:651:./route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./rung2-regular-section-answer.md:652:./route-choice-answer.md:1110:./DLNFibre/Core/RouteCAssembly.lean:115:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./rung2-regular-section-answer.md:653:./route-choice-answer.md:1111:./DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./rung2-regular-section-answer.md:662:./route-choice-answer.md:1172:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./rung2-regular-section-answer.md:665:./route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./rung2-regular-section-answer.md:672:./route-choice-answer.md:1191:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./rung2-regular-section-answer.md:673:./route-choice-answer.md:1192:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./rung2-regular-section-answer.md:674:./route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:675:./route-choice-answer.md:1195:  rw [varietyDim, ← hI] at hvd
./rung2-regular-section-answer.md:698:./route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./rung2-regular-section-answer.md:699:./route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:700:./route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:701:./route-choice-answer.md:1321:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./rung2-regular-section-answer.md:703:./route-choice-answer.md:1325:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:704:./route-choice-answer.md:1326:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./rung2-regular-section-answer.md:714:./route-choice-answer.md:1362:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./rung2-regular-section-answer.md:716:./route-choice-answer.md:1366:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./rung2-regular-section-answer.md:717:./route-choice-answer.md:1368:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./rung2-regular-section-answer.md:758:./route-choice-answer.md:7513:DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./rung2-regular-section-answer.md:761:./route-choice-answer.md:7525:DLNFibre/Core/OrbitImageDim.lean:77:the A4.3 identity is needed (the chain is `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`);
./rung2-regular-section-answer.md:763:./route-choice-answer.md:7552:DLNFibre/Core/DeepChartRing.lean:325:/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower
./rung2-regular-section-answer.md:764:./route-choice-answer.md:7553:DLNFibre/Core/DeepChartRing.lean:328:structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
./rung2-regular-section-answer.md:765:./route-choice-answer.md:7554:DLNFibre/Core/DeepChartRing.lean:339:tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
./rung2-regular-section-answer.md:779:./route-choice-answer.md:7705:DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./rung2-regular-section-answer.md:780:./route-choice-answer.md:7708:DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:781:./route-choice-answer.md:7711:DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:790:./route-choice-answer.md:7961:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./rung2-regular-section-answer.md:801:./route-choice-answer.md:8286:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./rung2-regular-section-answer.md:802:./route-choice-answer.md:8287:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./rung2-regular-section-answer.md:803:./route-choice-answer.md:8289:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./rung2-regular-section-answer.md:804:./route-choice-answer.md:8319:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:805:./route-choice-answer.md:8321:          + varietyDim (canonicalCoord d '' fibre d B))
./rung2-regular-section-answer.md:806:./route-choice-answer.md:8322:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:807:./route-choice-answer.md:8323:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./rung2-regular-section-answer.md:808:./route-choice-answer.md:8325:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./rung2-regular-section-answer.md:809:./route-choice-answer.md:8327:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:810:./route-choice-answer.md:8336:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:811:./route-choice-answer.md:8338:        + varietyDim (canonicalCoord d '' fibre d B) := by
./rung2-regular-section-answer.md:812:./route-choice-answer.md:8341:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./rung2-regular-section-answer.md:813:./route-choice-answer.md:8348:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./rung2-regular-section-answer.md:814:./route-choice-answer.md:8349:      = varietyDim (canonicalCoord d '' fibre d B)
./rung2-regular-section-answer.md:815:./route-choice-answer.md:8351:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./rung2-regular-section-answer.md:816:./route-choice-answer.md:8352:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./rung2-regular-section-answer.md:817:./route-choice-answer.md:8357:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./rung2-regular-section-answer.md:818:./route-choice-answer.md:8358:      _ = varietyDim (canonicalCoord d '' fibre d B)
./rung2-regular-section-answer.md:819:./route-choice-answer.md:8369:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./rung2-regular-section-answer.md:820:./route-choice-answer.md:8376:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:821:./route-choice-answer.md:8378:          + varietyDim (canonicalCoord d '' fibre d B))
./rung2-regular-section-answer.md:822:./route-choice-answer.md:8379:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:823:./route-choice-answer.md:8380:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./rung2-regular-section-answer.md:824:./route-choice-answer.md:8384:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./rung2-regular-section-answer.md:825:./route-choice-answer.md:8385:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./rung2-regular-section-answer.md:880:./route-choice-answer.md:8835:`Σ^r` and `F` are not domains in the examples you care about. Your `varietyDim` is `ringKrullDim` of a possibly reducible coordinate ring, hence a **max over components**, while `trdeg_add_eq` is a domain/no-zero-divisors function-field theorem.
./rung2-regular-section-answer.md:881:./route-choice-answer.md:8843:It does not identify `relative_trdeg` with `varietyDim F_B` at your chosen closed rank-`r` point. The missing input is the no-jump/local-triviality statement:
./rung2-regular-section-answer.md:882:./route-choice-answer.md:8868:bridge from flat ring maps to set-level varietyDim/fibre ideals
./rung2-regular-section-answer.md:883:./route-choice-answer.md:8873:The set-level `varietyDim` bridge is not free. `multComap` gives the ring map shape, but exact-rank geometry wants localized quotient rings/pivot charts, not just the global closure ring where lower-rank fibres jump.
./rung2-regular-section-answer.md:884:./route-choice-answer.md:8899:6. finite-cover/localization gluing for set-level varietyDim
./rung2-regular-section-answer.md:885:./route-choice-answer.md:8922:`Σ^r` and `F` are not domains in the examples you care about. Your `varietyDim` is `ringKrullDim` of a possibly reducible coordinate ring, hence a **max over components**, while `trdeg_add_eq` is a domain/no-zero-divisors function-field theorem.
./rung2-regular-section-answer.md:886:./route-choice-answer.md:8930:It does not identify `relative_trdeg` with `varietyDim F_B` at your chosen closed rank-`r` point. The missing input is the no-jump/local-triviality statement:
./rung2-regular-section-answer.md:887:./route-choice-answer.md:8955:bridge from flat ring maps to set-level varietyDim/fibre ideals
./rung2-regular-section-answer.md:888:./route-choice-answer.md:8960:The set-level `varietyDim` bridge is not free. `multComap` gives the ring map shape, but exact-rank geometry wants localized quotient rings/pivot charts, not just the global closure ring where lower-rank fibres jump.
./rung2-regular-section-answer.md:889:./route-choice-answer.md:8986:6. finite-cover/localization gluing for set-level varietyDim
./rung2-regular-section-answer.md:890:./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./rung2-regular-section-answer.md:891:./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./rung2-regular-section-answer.md:892:./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./rung2-regular-section-answer.md:894:./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./rung2-regular-section-answer.md:895:./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./rung2-regular-section-answer.md:897:./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./rung2-regular-section-answer.md:898:./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./rung2-regular-section-answer.md:899:./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./rung2-regular-section-answer.md:901:./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./rung2-regular-section-answer.md:903:./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./rung2-regular-section-answer.md:904:./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-regular-section-answer.md:905:./noncirc-setlevel-answer.md:93:/bin/bash -lc "rg -n \"varietyDim|ringKrullDim|radical|IsJacobson|KrullDim|tensor|TensorProduct\" . -g '*.lean' -g '*.md' | head -300" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-answer.md:906:./noncirc-setlevel-answer.md:95:./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:907:./noncirc-setlevel-answer.md:96:./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:908:./noncirc-setlevel-answer.md:97:./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:909:./noncirc-setlevel-answer.md:98:./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:912:./noncirc-setlevel-answer.md:101:./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:914:./noncirc-setlevel-answer.md:103:./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:915:./noncirc-setlevel-answer.md:104:./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:916:./noncirc-setlevel-answer.md:105:./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./rung2-regular-section-answer.md:917:./noncirc-setlevel-answer.md:106:./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./rung2-regular-section-answer.md:918:./noncirc-setlevel-answer.md:108:./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./rung2-regular-section-answer.md:920:./noncirc-setlevel-answer.md:110:./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./rung2-regular-section-answer.md:921:./noncirc-setlevel-answer.md:112:./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./rung2-regular-section-answer.md:923:./noncirc-setlevel-answer.md:114:./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./rung2-regular-section-answer.md:924:./noncirc-setlevel-answer.md:117:./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./rung2-regular-section-answer.md:925:./noncirc-setlevel-answer.md:118:./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./rung2-regular-section-answer.md:927:./noncirc-setlevel-answer.md:122:./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./rung2-regular-section-answer.md:929:./noncirc-setlevel-answer.md:124:./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./rung2-regular-section-answer.md:930:./noncirc-setlevel-answer.md:126:./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-regular-section-answer.md:931:./noncirc-setlevel-answer.md:127:./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./rung2-regular-section-answer.md:932:./noncirc-setlevel-answer.md:128:./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./rung2-regular-section-answer.md:933:./noncirc-setlevel-answer.md:130:./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./rung2-regular-section-answer.md:935:./noncirc-setlevel-answer.md:132:./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./rung2-regular-section-answer.md:936:./noncirc-setlevel-answer.md:134:./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./rung2-regular-section-answer.md:938:./noncirc-setlevel-answer.md:136:./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./rung2-regular-section-answer.md:939:./noncirc-setlevel-answer.md:139:./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./rung2-regular-section-answer.md:940:./noncirc-setlevel-answer.md:140:./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./rung2-regular-section-answer.md:942:./noncirc-setlevel-answer.md:144:./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./rung2-regular-section-answer.md:944:./noncirc-setlevel-answer.md:146:./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./rung2-regular-section-answer.md:945:./noncirc-setlevel-answer.md:148:./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-regular-section-answer.md:946:./noncirc-setlevel-answer.md:149:./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:947:./noncirc-setlevel-answer.md:150:./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:948:./noncirc-setlevel-answer.md:151:./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:949:./noncirc-setlevel-answer.md:152:./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:952:./noncirc-setlevel-answer.md:155:./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:954:./noncirc-setlevel-answer.md:157:./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:955:./noncirc-setlevel-answer.md:158:./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:958:./noncirc-setlevel-answer.md:161:./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:959:./noncirc-setlevel-answer.md:162:./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:960:./noncirc-setlevel-answer.md:163:./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:961:./noncirc-setlevel-answer.md:164:./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:964:./noncirc-setlevel-answer.md:167:./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:966:./noncirc-setlevel-answer.md:169:./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:967:./noncirc-setlevel-answer.md:170:./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:970:./noncirc-setlevel-answer.md:173:./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./rung2-regular-section-answer.md:971:./noncirc-setlevel-answer.md:174:./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./rung2-regular-section-answer.md:972:./noncirc-setlevel-answer.md:175:./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./rung2-regular-section-answer.md:973:./noncirc-setlevel-answer.md:176:./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./rung2-regular-section-answer.md:974:./noncirc-setlevel-answer.md:177:./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./rung2-regular-section-answer.md:975:./noncirc-setlevel-answer.md:178:./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./rung2-regular-section-answer.md:976:./noncirc-setlevel-answer.md:179:./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./rung2-regular-section-answer.md:977:./noncirc-setlevel-answer.md:180:./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./rung2-regular-section-answer.md:978:./noncirc-setlevel-answer.md:181:./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:979:./noncirc-setlevel-answer.md:182:./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./rung2-regular-section-answer.md:980:./noncirc-setlevel-answer.md:183:./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./rung2-regular-section-answer.md:981:./noncirc-setlevel-answer.md:184:./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:982:./noncirc-setlevel-answer.md:185:./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:983:./noncirc-setlevel-answer.md:186:./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./rung2-regular-section-answer.md:984:./noncirc-setlevel-answer.md:187:./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./rung2-regular-section-answer.md:985:./noncirc-setlevel-answer.md:188:./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./rung2-regular-section-answer.md:986:./noncirc-setlevel-answer.md:189:./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./rung2-regular-section-answer.md:987:./noncirc-setlevel-answer.md:190:./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./rung2-regular-section-answer.md:988:./noncirc-setlevel-answer.md:191:./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./rung2-regular-section-answer.md:989:./noncirc-setlevel-answer.md:192:./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./rung2-regular-section-answer.md:990:./noncirc-setlevel-answer.md:193:./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:991:./noncirc-setlevel-answer.md:194:./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./rung2-regular-section-answer.md:992:./noncirc-setlevel-answer.md:195:./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./rung2-regular-section-answer.md:993:./noncirc-setlevel-answer.md:196:./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./rung2-regular-section-answer.md:994:./noncirc-setlevel-answer.md:197:./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./rung2-regular-section-answer.md:995:./noncirc-setlevel-answer.md:198:./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./rung2-regular-section-answer.md:997:./noncirc-setlevel-answer.md:200:./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./rung2-regular-section-answer.md:998:./noncirc-setlevel-answer.md:201:./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./rung2-regular-section-answer.md:1000:./noncirc-setlevel-answer.md:203:./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./rung2-regular-section-answer.md:1001:./noncirc-setlevel-answer.md:204:./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./rung2-regular-section-answer.md:1002:./noncirc-setlevel-answer.md:205:./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:1003:./noncirc-setlevel-answer.md:206:./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./rung2-regular-section-answer.md:1005:./noncirc-setlevel-answer.md:208:./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./rung2-regular-section-answer.md:1011:./noncirc-setlevel-answer.md:214:./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./rung2-regular-section-answer.md:1012:./noncirc-setlevel-answer.md:215:./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./rung2-regular-section-answer.md:1020:./noncirc-setlevel-answer.md:223:./route-choice-answer.md:674:./DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./rung2-regular-section-answer.md:1022:./noncirc-setlevel-answer.md:225:./route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./rung2-regular-section-answer.md:1023:./noncirc-setlevel-answer.md:226:./route-choice-answer.md:679:./DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:1024:./noncirc-setlevel-answer.md:227:./route-choice-answer.md:681:./DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:1028:./noncirc-setlevel-answer.md:231:./route-choice-answer.md:686:./DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:1029:./noncirc-setlevel-answer.md:232:./route-choice-answer.md:687:./DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./rung2-regular-section-answer.md:1030:./noncirc-setlevel-answer.md:233:./route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./rung2-regular-section-answer.md:1031:./noncirc-setlevel-answer.md:234:./route-choice-answer.md:689:./DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:1032:./noncirc-setlevel-answer.md:235:./route-choice-answer.md:691:./DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./rung2-regular-section-answer.md:1033:./noncirc-setlevel-answer.md:236:./route-choice-answer.md:692:./DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./rung2-regular-section-answer.md:1034:./noncirc-setlevel-answer.md:237:./route-choice-answer.md:693:./DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./rung2-regular-section-answer.md:1035:./noncirc-setlevel-answer.md:238:./route-choice-answer.md:694:./DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./rung2-regular-section-answer.md:1036:./noncirc-setlevel-answer.md:239:./route-choice-answer.md:695:./DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:1037:./noncirc-setlevel-answer.md:240:./route-choice-answer.md:697:./DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./rung2-regular-section-answer.md:1038:./noncirc-setlevel-answer.md:241:./route-choice-answer.md:698:./DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./rung2-regular-section-answer.md:1039:./noncirc-setlevel-answer.md:242:./route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./rung2-regular-section-answer.md:1040:./noncirc-setlevel-answer.md:243:./route-choice-answer.md:700:./DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:1041:./noncirc-setlevel-answer.md:244:./route-choice-answer.md:702:./DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./rung2-regular-section-answer.md:1042:./noncirc-setlevel-answer.md:245:./route-choice-answer.md:703:./DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./rung2-regular-section-answer.md:1043:./noncirc-setlevel-answer.md:246:./route-choice-answer.md:704:./DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./rung2-regular-section-answer.md:1044:./noncirc-setlevel-answer.md:247:./route-choice-answer.md:705:./DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:1045:./noncirc-setlevel-answer.md:248:./route-choice-answer.md:707:./DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:1046:./noncirc-setlevel-answer.md:249:./route-choice-answer.md:708:./DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./rung2-regular-section-answer.md:1047:./noncirc-setlevel-answer.md:250:./route-choice-answer.md:712:./DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./rung2-regular-section-answer.md:1048:./noncirc-setlevel-answer.md:251:./route-choice-answer.md:714:./DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:1049:./noncirc-setlevel-answer.md:252:./route-choice-answer.md:717:./DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./rung2-regular-section-answer.md:1057:./noncirc-setlevel-answer.md:260:./route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./rung2-regular-section-answer.md:1058:./noncirc-setlevel-answer.md:261:./route-choice-answer.md:821:./DLNFibre/Core/OrbitDifferentialRank.lean:659:/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
./rung2-regular-section-answer.md:1059:./noncirc-setlevel-answer.md:262:./route-choice-answer.md:822:./DLNFibre/Core/OrbitDifferentialRank.lean:660:Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
./rung2-regular-section-answer.md:1060:./noncirc-setlevel-answer.md:263:./route-choice-answer.md:823:./DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./rung2-regular-section-answer.md:1061:./noncirc-setlevel-answer.md:264:./route-choice-answer.md:824:./DLNFibre/Core/OrbitDifferentialRank.lean:666:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:1062:./noncirc-setlevel-answer.md:265:./route-choice-answer.md:825:./DLNFibre/Core/OrbitDifferentialRank.lean:668:  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
./rung2-regular-section-answer.md:1063:./noncirc-setlevel-answer.md:266:./route-choice-answer.md:846:./DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./rung2-regular-section-answer.md:1064:./noncirc-setlevel-answer.md:267:./route-choice-answer.md:847:./DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./rung2-regular-section-answer.md:1065:./noncirc-setlevel-answer.md:268:./route-choice-answer.md:852:./DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./rung2-regular-section-answer.md:1066:./noncirc-setlevel-answer.md:269:./route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./rung2-regular-section-answer.md:1067:./noncirc-setlevel-answer.md:270:./route-choice-answer.md:854:./DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:1068:./noncirc-setlevel-answer.md:271:./route-choice-answer.md:855:./DLNFibre/Core/RadicalCatenary.lean:181:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
./rung2-regular-section-answer.md:1069:./noncirc-setlevel-answer.md:272:./route-choice-answer.md:862:./DLNFibre/Core/RadicalCatenary.lean:197:  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:1070:./noncirc-setlevel-answer.md:273:./route-choice-answer.md:863:./DLNFibre/Core/RadicalCatenary.lean:203:The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
./rung2-regular-section-answer.md:1071:./noncirc-setlevel-answer.md:274:./route-choice-answer.md:864:./DLNFibre/Core/RadicalCatenary.lean:208:      + varietyDim (canonicalCoord dWitness ''
./rung2-regular-section-answer.md:1072:./noncirc-setlevel-answer.md:275:./route-choice-answer.md:865:./DLNFibre/Core/RadicalCatenary.lean:211:  codimRepCanonical_add_varietyDim_eq_card_of_nonempty
./rung2-regular-section-answer.md:1073:./noncirc-setlevel-answer.md:276:./route-choice-answer.md:884:./DLNFibre/Core/OrbitImageDim.lean:10:(`varietyDim_eq_ringKrullDim_range_orbitPullback`), discharges the AG-half of `hVoigt`:
./rung2-regular-section-answer.md:1074:./noncirc-setlevel-answer.md:277:./route-choice-answer.md:885:./DLNFibre/Core/OrbitImageDim.lean:15:- **A0** (landed): `varietyDim Z_M = (ringKrullDim (orbitPullback M).range).unbotD 0`.
./rung2-regular-section-answer.md:1075:./noncirc-setlevel-answer.md:278:./route-choice-answer.md:886:./DLNFibre/Core/OrbitImageDim.lean:77:the A4.3 identity is needed (the chain is `varietyDim = trdeg ≤ genericDifferentialRank ≤ finrank δ⁰`);
./rung2-regular-section-answer.md:1076:./noncirc-setlevel-answer.md:279:./route-choice-answer.md:887:./DLNFibre/Core/OrbitImageDim.lean:90:/-- **A4.4 chained with A0: `varietyDim Z_M ≤ finrank (range δ⁰)`.** Combining the landed A0 link
./rung2-regular-section-answer.md:1077:./noncirc-setlevel-answer.md:280:./route-choice-answer.md:888:./DLNFibre/Core/OrbitImageDim.lean:91:(`varietyDim_eq_ringKrullDim_range_orbitPullback`, needs `[Infinite k]`) with the submersion bound,
./rung2-regular-section-answer.md:1078:./noncirc-setlevel-answer.md:281:./route-choice-answer.md:889:./DLNFibre/Core/OrbitImageDim.lean:95:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ
./rung2-regular-section-answer.md:1079:./noncirc-setlevel-answer.md:282:./route-choice-answer.md:890:./DLNFibre/Core/OrbitImageDim.lean:101:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:1080:./noncirc-setlevel-answer.md:283:./route-choice-answer.md:891:./DLNFibre/Core/OrbitImageDim.lean:103:  rw [varietyDim_eq_ringKrullDim_range_orbitPullback M]
./rung2-regular-section-answer.md:1088:./noncirc-setlevel-answer.md:291:./route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./rung2-regular-section-answer.md:1089:./noncirc-setlevel-answer.md:292:./route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:1090:./noncirc-setlevel-answer.md:293:./route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:1091:./noncirc-setlevel-answer.md:294:./route-choice-answer.md:944:./DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./rung2-regular-section-answer.md:1092:./noncirc-setlevel-answer.md:295:./route-choice-answer.md:946:./DLNFibre/Core/FibreDimFibrationProbe.lean:59:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:1093:./noncirc-setlevel-answer.md:296:./route-choice-answer.md:947:./DLNFibre/Core/FibreDimFibrationProbe.lean:60:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./rung2-regular-section-answer.md:1094:./noncirc-setlevel-answer.md:297:./route-choice-answer.md:952:./DLNFibre/Core/FibreDimFibrationProbe.lean:96:MvPolynomial (RepCoord stratum) k ⧸ vanishingIdeal(…)`. From the thermometer (varietyDim = δ) which
./rung2-regular-section-answer.md:1096:./noncirc-setlevel-answer.md:299:./route-choice-answer.md:954:./DLNFibre/Core/FibreDimFibrationProbe.lean:100:/-- `varietyDim` unfolds to the `unbotD 0` of the quotient `ringKrullDim`. -/
./rung2-regular-section-answer.md:1097:./noncirc-setlevel-answer.md:300:./route-choice-answer.md:955:./DLNFibre/Core/FibreDimFibrationProbe.lean:102:    varietyDim Z = (ringKrullDim (MvPolynomial (RepCoord (dStratum 2 2)) k ⧸
./rung2-regular-section-answer.md:1098:./noncirc-setlevel-answer.md:301:./route-choice-answer.md:1050:./DLNFibre/Core/VoigtDischarge.lean:8:The capstone of the AG half. The A4 submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`
./rung2-regular-section-answer.md:1099:./noncirc-setlevel-answer.md:302:./route-choice-answer.md:1051:./DLNFibre/Core/VoigtDischarge.lean:9:(`varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`, char 0) and the A6.1 reverse
./rung2-regular-section-answer.md:1100:./noncirc-setlevel-answer.md:303:./route-choice-answer.md:1052:./DLNFibre/Core/VoigtDischarge.lean:10:inequality `finrank (range δ⁰) ≤ varietyDim Z_M` (`finrank_range_deformationδ_le_varietyDim`) squeeze
./rung2-regular-section-answer.md:1101:./noncirc-setlevel-answer.md:304:./route-choice-answer.md:1053:./DLNFibre/Core/VoigtDischarge.lean:11:to **equality** `varietyDim Z_M = finrank (range δ⁰)` (the orbit closure is smooth of the expected
./rung2-regular-section-answer.md:1102:./noncirc-setlevel-answer.md:305:./route-choice-answer.md:1054:./DLNFibre/Core/VoigtDischarge.lean:33:/-! ## The squeeze — `varietyDim Z_M = finrank (range δ⁰)` -/
./rung2-regular-section-answer.md:1103:./noncirc-setlevel-answer.md:306:./route-choice-answer.md:1055:./DLNFibre/Core/VoigtDischarge.lean:38:theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
./rung2-regular-section-answer.md:1104:./noncirc-setlevel-answer.md:307:./route-choice-answer.md:1056:./DLNFibre/Core/VoigtDischarge.lean:40:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:1105:./noncirc-setlevel-answer.md:308:./route-choice-answer.md:1057:./DLNFibre/Core/VoigtDischarge.lean:43:  refine le_antisymm ?_ (finrank_range_deformationδ_le_varietyDim M)
./rung2-regular-section-answer.md:1106:./noncirc-setlevel-answer.md:309:./route-choice-answer.md:1058:./DLNFibre/Core/VoigtDischarge.lean:44:  exact varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional M
./rung2-regular-section-answer.md:1107:./noncirc-setlevel-answer.md:310:./route-choice-answer.md:1059:./DLNFibre/Core/VoigtDischarge.lean:64:    have hadd := codimRep_add_varietyDim_eq_card (canonicalCoord d) (orbitRankLocus M)
./rung2-regular-section-answer.md:1108:./noncirc-setlevel-answer.md:311:./route-choice-answer.md:1061:./DLNFibre/Core/VoigtDischarge.lean:66:    rwa [varietyDim_orbitRankLocus_eq_finrank_range_deformationδ M, ← hr] at hadd
./rung2-regular-section-answer.md:1109:./noncirc-setlevel-answer.md:312:./route-choice-answer.md:1063:./DLNFibre/Core/OrbitTangentCotangent.lean:14:# `DLNFibre.Core.OrbitTangentCotangent` — A6.1: the reverse inequality `finrank(range δ⁰) ≤ varietyDim Z_M`
./rung2-regular-section-answer.md:1110:./noncirc-setlevel-answer.md:313:./route-choice-answer.md:1064:./DLNFibre/Core/OrbitTangentCotangent.lean:19:`varietyDim Z_M = finrank (range δ⁰)`, the geometric heart of Voigt's lemma.
./rung2-regular-section-answer.md:1112:./noncirc-setlevel-answer.md:315:./route-choice-answer.md:1067:./DLNFibre/Core/OrbitTangentCotangent.lean:564:/-! ## R6 — chain `finrank (m_M.Cotangent)` to `varietyDim Z_M` -/
./rung2-regular-section-answer.md:1113:./noncirc-setlevel-answer.md:316:./route-choice-answer.md:1068:./DLNFibre/Core/OrbitTangentCotangent.lean:566:/-- `ringKrullDim (orbitRing M)` is a finite natural number `n`, equal to `varietyDim Z_M`:
./rung2-regular-section-answer.md:1114:./noncirc-setlevel-answer.md:317:./route-choice-answer.md:1069:./DLNFibre/Core/OrbitTangentCotangent.lean:571:      ∧ varietyDim (canonicalCoord d '' orbitRankLocus M) = (n : ℕ∞) := by
./rung2-regular-section-answer.md:1115:./noncirc-setlevel-answer.md:318:./route-choice-answer.md:1070:./DLNFibre/Core/OrbitTangentCotangent.lean:579:  -- `varietyDim Z_M = (ringKrullDim (orbitRing M)).unbotD 0` (L6.4 + `varietyDim` def)
./rung2-regular-section-answer.md:1116:./noncirc-setlevel-answer.md:319:./route-choice-answer.md:1071:./DLNFibre/Core/OrbitTangentCotangent.lean:580:  have hvar : varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:1117:./noncirc-setlevel-answer.md:320:./route-choice-answer.md:1072:./DLNFibre/Core/OrbitTangentCotangent.lean:582:    rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M]; rfl
./rung2-regular-section-answer.md:1118:./noncirc-setlevel-answer.md:321:./route-choice-answer.md:1073:./DLNFibre/Core/OrbitTangentCotangent.lean:598:/-- **R6 — `finrank k (m_M.Cotangent) = varietyDim Z_M`.** The cotangent finrank equals the variety
./rung2-regular-section-answer.md:1119:./noncirc-setlevel-answer.md:322:./route-choice-answer.md:1074:./DLNFibre/Core/OrbitTangentCotangent.lean:601:GAP3 (`ringKrullDim (AtPrime m_M) = ringKrullDim (orbitRing M)`), and `varietyDim Z_M =
./rung2-regular-section-answer.md:1120:./noncirc-setlevel-answer.md:323:./route-choice-answer.md:1075:./DLNFibre/Core/OrbitTangentCotangent.lean:603:theorem finrank_cotangent_eq_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./rung2-regular-section-answer.md:1121:./noncirc-setlevel-answer.md:324:./route-choice-answer.md:1076:./DLNFibre/Core/OrbitTangentCotangent.lean:605:      = varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./rung2-regular-section-answer.md:1122:./noncirc-setlevel-answer.md:325:./route-choice-answer.md:1078:./DLNFibre/Core/OrbitTangentCotangent.lean:635:/-! ## The A6.1 headline — `finrank (range δ⁰) ≤ varietyDim Z_M` -/
./rung2-regular-section-answer.md:1123:./noncirc-setlevel-answer.md:326:./route-choice-answer.md:1079:./DLNFibre/Core/OrbitTangentCotangent.lean:637:/-- **A6.1 (the reverse inequality).** `finrank k (range δ⁰) ≤ varietyDim Z_M`: the orbit tangent
./rung2-regular-section-answer.md:1124:./noncirc-setlevel-answer.md:327:./route-choice-answer.md:1080:./DLNFibre/Core/OrbitTangentCotangent.lean:641:theorem finrank_range_deformationδ_le_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./rung2-regular-section-answer.md:1125:./noncirc-setlevel-answer.md:328:./route-choice-answer.md:1081:./DLNFibre/Core/OrbitTangentCotangent.lean:643:      ≤ varietyDim (canonicalCoord d '' orbitRankLocus M) := by
./rung2-regular-section-answer.md:1126:./noncirc-setlevel-answer.md:329:./route-choice-answer.md:1082:./DLNFibre/Core/OrbitTangentCotangent.lean:644:  rw [← finrank_cotangent_eq_varietyDim M]
./rung2-regular-section-answer.md:1127:./noncirc-setlevel-answer.md:330:./route-choice-answer.md:1083:./DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./rung2-regular-section-answer.md:1128:./noncirc-setlevel-answer.md:331:./route-choice-answer.md:1084:./DLNFibre/Core/RouteCAssembly.lean:18:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./rung2-regular-section-answer.md:1129:./noncirc-setlevel-answer.md:332:./route-choice-answer.md:1085:./DLNFibre/Core/RouteCAssembly.lean:20:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./rung2-regular-section-answer.md:1130:./noncirc-setlevel-answer.md:333:./route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:1131:./noncirc-setlevel-answer.md:334:./route-choice-answer.md:1087:./DLNFibre/Core/RouteCAssembly.lean:52:          + varietyDim (canonicalCoord d '' fibre d B))
./rung2-regular-section-answer.md:1132:./noncirc-setlevel-answer.md:335:./route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:1133:./noncirc-setlevel-answer.md:336:./route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./rung2-regular-section-answer.md:1134:./noncirc-setlevel-answer.md:337:./route-choice-answer.md:1090:./DLNFibre/Core/RouteCAssembly.lean:56:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./rung2-regular-section-answer.md:1135:./noncirc-setlevel-answer.md:338:./route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:1136:./noncirc-setlevel-answer.md:339:./route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:1137:./noncirc-setlevel-answer.md:340:./route-choice-answer.md:1096:./DLNFibre/Core/RouteCAssembly.lean:69:        + varietyDim (canonicalCoord d '' fibre d B) := by
./rung2-regular-section-answer.md:1138:./noncirc-setlevel-answer.md:341:./route-choice-answer.md:1097:./DLNFibre/Core/RouteCAssembly.lean:72:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./rung2-regular-section-answer.md:1139:./noncirc-setlevel-answer.md:342:./route-choice-answer.md:1098:./DLNFibre/Core/RouteCAssembly.lean:79:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./rung2-regular-section-answer.md:1140:./noncirc-setlevel-answer.md:343:./route-choice-answer.md:1099:./DLNFibre/Core/RouteCAssembly.lean:80:      = varietyDim (canonicalCoord d '' fibre d B)
./rung2-regular-section-answer.md:1141:./noncirc-setlevel-answer.md:344:./route-choice-answer.md:1100:./DLNFibre/Core/RouteCAssembly.lean:82:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./rung2-regular-section-answer.md:1142:./noncirc-setlevel-answer.md:345:./route-choice-answer.md:1101:./DLNFibre/Core/RouteCAssembly.lean:83:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./rung2-regular-section-answer.md:1143:./noncirc-setlevel-answer.md:346:./route-choice-answer.md:1102:./DLNFibre/Core/RouteCAssembly.lean:88:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./rung2-regular-section-answer.md:1144:./noncirc-setlevel-answer.md:347:./route-choice-answer.md:1103:./DLNFibre/Core/RouteCAssembly.lean:89:      _ = varietyDim (canonicalCoord d '' fibre d B)
./rung2-regular-section-answer.md:1145:./noncirc-setlevel-answer.md:348:./route-choice-answer.md:1104:./DLNFibre/Core/RouteCAssembly.lean:100:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./rung2-regular-section-answer.md:1146:./noncirc-setlevel-answer.md:349:./route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:1147:./noncirc-setlevel-answer.md:350:./route-choice-answer.md:1107:./DLNFibre/Core/RouteCAssembly.lean:109:          + varietyDim (canonicalCoord d '' fibre d B))
./rung2-regular-section-answer.md:1148:./noncirc-setlevel-answer.md:351:./route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:1149:./noncirc-setlevel-answer.md:352:./route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./rung2-regular-section-answer.md:1150:./noncirc-setlevel-answer.md:353:./route-choice-answer.md:1110:./DLNFibre/Core/RouteCAssembly.lean:115:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./rung2-regular-section-answer.md:1151:./noncirc-setlevel-answer.md:354:./route-choice-answer.md:1111:./DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./rung2-regular-section-answer.md:1153:./noncirc-setlevel-answer.md:356:./route-choice-answer.md:1172:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./rung2-regular-section-answer.md:1156:./noncirc-setlevel-answer.md:359:./route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./rung2-regular-section-answer.md:1160:./noncirc-setlevel-answer.md:363:./route-choice-answer.md:1191:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./rung2-regular-section-answer.md:1161:./noncirc-setlevel-answer.md:364:./route-choice-answer.md:1192:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./rung2-regular-section-answer.md:1162:./noncirc-setlevel-answer.md:365:./route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:1163:./noncirc-setlevel-answer.md:366:./route-choice-answer.md:1195:  rw [varietyDim, ← hI] at hvd
./rung2-regular-section-answer.md:1180:./noncirc-setlevel-answer.md:383:./route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./rung2-regular-section-answer.md:1181:./noncirc-setlevel-answer.md:384:./route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:1182:./noncirc-setlevel-answer.md:385:./route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:1183:./noncirc-setlevel-answer.md:386:./route-choice-answer.md:1321:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./rung2-regular-section-answer.md:1184:./noncirc-setlevel-answer.md:387:./route-choice-answer.md:1325:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:1185:./noncirc-setlevel-answer.md:388:./route-choice-answer.md:1326:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./rung2-regular-section-answer.md:1192:./noncirc-setlevel-answer.md:445:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./rung2-regular-section-answer.md:1193:./noncirc-setlevel-answer.md:446:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./rung2-regular-section-answer.md:1194:./noncirc-setlevel-answer.md:464:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./rung2-regular-section-answer.md:1196:./noncirc-setlevel-answer.md:466:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./rung2-regular-section-answer.md:1197:./noncirc-setlevel-answer.md:477:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./rung2-regular-section-answer.md:1199:./noncirc-setlevel-answer.md:484:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./rung2-regular-section-answer.md:1200:./noncirc-setlevel-answer.md:489:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./rung2-regular-section-answer.md:1201:./noncirc-setlevel-answer.md:491:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./rung2-regular-section-answer.md:1203:./noncirc-setlevel-answer.md:499:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./rung2-regular-section-answer.md:1205:./noncirc-setlevel-answer.md:503:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./rung2-regular-section-answer.md:1206:./noncirc-setlevel-answer.md:508:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-regular-section-answer.md:1207:./noncirc-setlevel-answer.md:519:/bin/bash -lc "rg -n \"varietyDim|ringKrullDim|radical|IsJacobson|KrullDim|tensor|TensorProduct\" . -g '*.lean' -g '*.md' | head -300" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-answer.md:1208:./noncirc-setlevel-answer.md:521:./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:1209:./noncirc-setlevel-answer.md:522:./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:1210:./noncirc-setlevel-answer.md:523:./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:1211:./noncirc-setlevel-answer.md:524:./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:1214:./noncirc-setlevel-answer.md:527:./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:1216:./noncirc-setlevel-answer.md:529:./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:1217:./noncirc-setlevel-answer.md:530:./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:1218:./noncirc-setlevel-answer.md:531:./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./rung2-regular-section-answer.md:1219:./noncirc-setlevel-answer.md:532:./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./rung2-regular-section-answer.md:1220:./noncirc-setlevel-answer.md:534:./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./rung2-regular-section-answer.md:1222:./noncirc-setlevel-answer.md:536:./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./rung2-regular-section-answer.md:1223:./noncirc-setlevel-answer.md:538:./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./rung2-regular-section-answer.md:1225:./noncirc-setlevel-answer.md:540:./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./rung2-regular-section-answer.md:1226:./noncirc-setlevel-answer.md:543:./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./rung2-regular-section-answer.md:1227:./noncirc-setlevel-answer.md:544:./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./rung2-regular-section-answer.md:1229:./noncirc-setlevel-answer.md:548:./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./rung2-regular-section-answer.md:1231:./noncirc-setlevel-answer.md:550:./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./rung2-regular-section-answer.md:1232:./noncirc-setlevel-answer.md:552:./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-regular-section-answer.md:1233:./noncirc-setlevel-answer.md:553:./noncirc-setlevel-answer.md:19:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./rung2-regular-section-answer.md:1234:./noncirc-setlevel-answer.md:554:./noncirc-setlevel-answer.md:20:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./rung2-regular-section-answer.md:1235:./noncirc-setlevel-answer.md:556:./noncirc-setlevel-answer.md:38:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./rung2-regular-section-answer.md:1237:./noncirc-setlevel-answer.md:558:./noncirc-setlevel-answer.md:40:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./rung2-regular-section-answer.md:1238:./noncirc-setlevel-answer.md:560:./noncirc-setlevel-answer.md:51:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./rung2-regular-section-answer.md:1240:./noncirc-setlevel-answer.md:562:./noncirc-setlevel-answer.md:58:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./rung2-regular-section-answer.md:1241:./noncirc-setlevel-answer.md:565:./noncirc-setlevel-answer.md:63:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./rung2-regular-section-answer.md:1242:./noncirc-setlevel-answer.md:566:./noncirc-setlevel-answer.md:65:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./rung2-regular-section-answer.md:1244:./noncirc-setlevel-answer.md:570:./noncirc-setlevel-answer.md:73:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./rung2-regular-section-answer.md:1246:./noncirc-setlevel-answer.md:572:./noncirc-setlevel-answer.md:77:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./rung2-regular-section-answer.md:1247:./noncirc-setlevel-answer.md:574:./noncirc-setlevel-answer.md:82:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-regular-section-answer.md:1248:./noncirc-setlevel-answer.md:575:./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:1249:./noncirc-setlevel-answer.md:576:./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:1250:./noncirc-setlevel-answer.md:577:./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:1251:./noncirc-setlevel-answer.md:578:./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:1254:./noncirc-setlevel-answer.md:581:./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:1256:./noncirc-setlevel-answer.md:583:./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:1257:./noncirc-setlevel-answer.md:584:./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:1260:./noncirc-setlevel-answer.md:587:./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:1261:./noncirc-setlevel-answer.md:588:./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:1262:./noncirc-setlevel-answer.md:589:./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:1263:./noncirc-setlevel-answer.md:590:./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:1266:./noncirc-setlevel-answer.md:593:./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:1268:./noncirc-setlevel-answer.md:595:./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:1269:./noncirc-setlevel-answer.md:596:./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:1272:./noncirc-setlevel-answer.md:599:./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./rung2-regular-section-answer.md:1273:./noncirc-setlevel-answer.md:600:./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./rung2-regular-section-answer.md:1274:./noncirc-setlevel-answer.md:601:./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./rung2-regular-section-answer.md:1275:./noncirc-setlevel-answer.md:602:./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./rung2-regular-section-answer.md:1276:./noncirc-setlevel-answer.md:603:./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./rung2-regular-section-answer.md:1277:./noncirc-setlevel-answer.md:604:./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./rung2-regular-section-answer.md:1278:./noncirc-setlevel-answer.md:605:./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./rung2-regular-section-answer.md:1279:./noncirc-setlevel-answer.md:606:./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./rung2-regular-section-answer.md:1280:./noncirc-setlevel-answer.md:607:./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:1281:./noncirc-setlevel-answer.md:608:./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./rung2-regular-section-answer.md:1282:./noncirc-setlevel-answer.md:609:./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./rung2-regular-section-answer.md:1283:./noncirc-setlevel-answer.md:610:./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:1284:./noncirc-setlevel-answer.md:611:./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:1285:./noncirc-setlevel-answer.md:612:./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./rung2-regular-section-answer.md:1286:./noncirc-setlevel-answer.md:613:./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./rung2-regular-section-answer.md:1287:./noncirc-setlevel-answer.md:614:./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./rung2-regular-section-answer.md:1288:./noncirc-setlevel-answer.md:615:./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./rung2-regular-section-answer.md:1289:./noncirc-setlevel-answer.md:616:./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./rung2-regular-section-answer.md:1290:./noncirc-setlevel-answer.md:617:./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./rung2-regular-section-answer.md:1291:./noncirc-setlevel-answer.md:618:./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./rung2-regular-section-answer.md:1292:./noncirc-setlevel-answer.md:619:./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:1293:./noncirc-setlevel-answer.md:620:./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./rung2-regular-section-answer.md:1294:./noncirc-setlevel-answer.md:621:./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./rung2-regular-section-answer.md:1295:./noncirc-setlevel-answer.md:622:./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./rung2-regular-section-answer.md:1296:./noncirc-setlevel-answer.md:623:./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./rung2-regular-section-answer.md:1297:./noncirc-setlevel-answer.md:624:./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./rung2-regular-section-answer.md:1299:./noncirc-setlevel-answer.md:626:./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./rung2-regular-section-answer.md:1300:./noncirc-setlevel-answer.md:627:./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./rung2-regular-section-answer.md:1302:./noncirc-setlevel-answer.md:629:./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./rung2-regular-section-answer.md:1303:./noncirc-setlevel-answer.md:630:./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./rung2-regular-section-answer.md:1304:./noncirc-setlevel-answer.md:631:./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:1305:./noncirc-setlevel-answer.md:632:./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./rung2-regular-section-answer.md:1307:./noncirc-setlevel-answer.md:634:./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./rung2-regular-section-answer.md:1313:./noncirc-setlevel-answer.md:640:./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./rung2-regular-section-answer.md:1314:./noncirc-setlevel-answer.md:641:./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./rung2-regular-section-answer.md:1327:./noncirc-setlevel-answer.md:695:route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./rung2-regular-section-answer.md:1328:./noncirc-setlevel-answer.md:710:route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./rung2-regular-section-answer.md:1329:./noncirc-setlevel-answer.md:711:route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./rung2-regular-section-answer.md:1330:./noncirc-setlevel-answer.md:712:route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./rung2-regular-section-answer.md:1333:./noncirc-setlevel-answer.md:732:route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./rung2-regular-section-answer.md:1334:./noncirc-setlevel-answer.md:733:route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:1336:./noncirc-setlevel-answer.md:737:route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./rung2-regular-section-answer.md:1337:./noncirc-setlevel-answer.md:738:route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./rung2-regular-section-answer.md:1340:./noncirc-setlevel-answer.md:755:route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./rung2-regular-section-answer.md:1343:./noncirc-setlevel-answer.md:761:route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:1347:./noncirc-setlevel-answer.md:768:route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./rung2-regular-section-answer.md:1350:./noncirc-setlevel-answer.md:782:route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./rung2-regular-section-answer.md:1352:./noncirc-setlevel-answer.md:784:route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./rung2-regular-section-answer.md:1355:./noncirc-setlevel-answer.md:787:route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./rung2-regular-section-answer.md:1356:./noncirc-setlevel-answer.md:788:route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./rung2-regular-section-answer.md:1358:./noncirc-setlevel-answer.md:834:route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./rung2-regular-section-answer.md:1360:./noncirc-setlevel-answer.md:846:route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./rung2-regular-section-answer.md:1361:./noncirc-setlevel-answer.md:870:route-choice-answer.md:939:./DLNFibre/Core/FibreDimFibrationProbe.lean:37:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./rung2-regular-section-answer.md:1362:./noncirc-setlevel-answer.md:871:route-choice-answer.md:940:./DLNFibre/Core/FibreDimFibrationProbe.lean:39:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:1363:./noncirc-setlevel-answer.md:872:route-choice-answer.md:941:./DLNFibre/Core/FibreDimFibrationProbe.lean:41:  varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:1367:./noncirc-setlevel-answer.md:895:route-choice-answer.md:1086:./DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:1368:./noncirc-setlevel-answer.md:896:route-choice-answer.md:1088:./DLNFibre/Core/RouteCAssembly.lean:53:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:1369:./noncirc-setlevel-answer.md:897:route-choice-answer.md:1089:./DLNFibre/Core/RouteCAssembly.lean:54:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./rung2-regular-section-answer.md:1370:./noncirc-setlevel-answer.md:899:route-choice-answer.md:1092:./DLNFibre/Core/RouteCAssembly.lean:58:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:1371:./noncirc-setlevel-answer.md:902:route-choice-answer.md:1095:./DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:1372:./noncirc-setlevel-answer.md:904:route-choice-answer.md:1106:./DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:1373:./noncirc-setlevel-answer.md:905:route-choice-answer.md:1108:./DLNFibre/Core/RouteCAssembly.lean:110:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:1374:./noncirc-setlevel-answer.md:906:route-choice-answer.md:1109:./DLNFibre/Core/RouteCAssembly.lean:111:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./rung2-regular-section-answer.md:1377:./noncirc-setlevel-answer.md:921:route-choice-answer.md:1178:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./rung2-regular-section-answer.md:1380:./noncirc-setlevel-answer.md:928:route-choice-answer.md:1194:    varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:1390:./noncirc-setlevel-answer.md:946:route-choice-answer.md:1303:/-- LANDED: the determinantal-stratum dimension `varietyDim (Mat^{≤r}) = r(n+m−r) = δ`. -/
./rung2-regular-section-answer.md:1391:./noncirc-setlevel-answer.md:947:route-choice-answer.md:1305:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:1392:./noncirc-setlevel-answer.md:948:route-choice-answer.md:1307:  varietyDim_productRankLocusLE_stratum n m r hn hm
./rung2-regular-section-answer.md:1404:./noncirc-setlevel-answer.md:1090:/bin/bash -lc 'rg -n "ringKrullDim.*TensorProduct|TensorProduct.*ringKrullDim|varietyDim.*prod|zeroLocus.*prod|vanishingIdeal.*union|iSup|iInf|sup.*vanishing|trdeg.*TensorProduct|TensorProduct.*trdeg" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-answer.md:1560:./noncirc-setlevel-answer.md:2011:So for question 1, the answer is yes mathematically and easy in Lean, but there is no obvious prepackaged lemma named exactly `ringKrullDim_quotient_radical` in v4.29. It is a two-rewrite lemma from `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`.
./rung2-regular-section-answer.md:1581:./noncirc-setlevel-answer.md:2447:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:131:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
./rung2-regular-section-answer.md:1582:./noncirc-setlevel-answer.md:2448:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:132:It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
./rung2-regular-section-answer.md:1586:./noncirc-setlevel-answer.md:2452:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:138:/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
./rung2-regular-section-answer.md:1589:./noncirc-setlevel-answer.md:2455:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:147:  rw [← Ideal.radical_eq_iff, IadDeep,
./rung2-regular-section-answer.md:1590:./noncirc-setlevel-answer.md:2456:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:148:    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
./rung2-regular-section-answer.md:1592:./noncirc-setlevel-answer.md:2458:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:152:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
./rung2-regular-section-answer.md:1602:./noncirc-setlevel-answer.md:2468:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:417:`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
./rung2-regular-section-answer.md:1628:./noncirc-setlevel-answer.md:2639:lemma test_ringKrullDim_quotient_radical (I : Ideal R) :
./rung2-regular-section-answer.md:1631:./noncirc-setlevel-answer.md:2643:lemma test_ringKrullDim_quotient_radical' (I : Ideal R) :
./rung2-regular-section-answer.md:1633:./noncirc-setlevel-answer.md:2645:  rw [test_ringKrullDim_quotient_radical]
./rung2-regular-section-answer.md:1634:./noncirc-setlevel-answer.md:2656:lemma test_ringKrullDim_quotient_radical (I : Ideal R) :
./rung2-regular-section-answer.md:1637:./noncirc-setlevel-answer.md:2660:lemma test_ringKrullDim_quotient_radical' (I : Ideal R) :
./rung2-regular-section-answer.md:1639:./noncirc-setlevel-answer.md:2662:  rw [test_ringKrullDim_quotient_radical]
./rung2-regular-section-answer.md:1645:./noncirc-setlevel-answer.md:2712:/bin/bash -lc 'rg -n "def vanishingIdeal|theorem vanishingIdeal|lemma vanishingIdeal|zeroLocus_eq|vanishingIdeal.*iUnion|vanishingIdeal.*union|radical|varietyDim" /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory/Nullstellensatz.lean -S | head -300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-answer.md:1659:./noncirc-setlevel-answer.md:2729:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./rung2-regular-section-answer.md:1660:./noncirc-setlevel-answer.md:2730:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./rung2-regular-section-answer.md:1669:./noncirc-setlevel-answer.md:2742:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./rung2-regular-section-answer.md:1670:./noncirc-setlevel-answer.md:2743:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./rung2-regular-section-answer.md:1671:./noncirc-setlevel-answer.md:2744:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:1672:./noncirc-setlevel-answer.md:2745:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:1673:./noncirc-setlevel-answer.md:2746:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:1674:./noncirc-setlevel-answer.md:2747:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./rung2-regular-section-answer.md:1675:./noncirc-setlevel-answer.md:2748:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./rung2-regular-section-answer.md:1676:./noncirc-setlevel-answer.md:2749:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:1677:./noncirc-setlevel-answer.md:2750:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./rung2-regular-section-answer.md:1678:./noncirc-setlevel-answer.md:2751:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./rung2-regular-section-answer.md:1679:./noncirc-setlevel-answer.md:2752:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./rung2-regular-section-answer.md:1680:./noncirc-setlevel-answer.md:2753:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./rung2-regular-section-answer.md:1681:./noncirc-setlevel-answer.md:2754:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:1682:./noncirc-setlevel-answer.md:2755:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./rung2-regular-section-answer.md:1683:./noncirc-setlevel-answer.md:2756:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./rung2-regular-section-answer.md:1684:./noncirc-setlevel-answer.md:2757:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./rung2-regular-section-answer.md:1685:./noncirc-setlevel-answer.md:2758:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:1686:./noncirc-setlevel-answer.md:2759:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./rung2-regular-section-answer.md:1687:./noncirc-setlevel-answer.md:2760:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./rung2-regular-section-answer.md:1688:./noncirc-setlevel-answer.md:2761:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./rung2-regular-section-answer.md:1689:./noncirc-setlevel-answer.md:2762:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:1690:./noncirc-setlevel-answer.md:2763:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:1691:./noncirc-setlevel-answer.md:2764:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./rung2-regular-section-answer.md:1693:./noncirc-setlevel-answer.md:2766:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./rung2-regular-section-answer.md:1694:./noncirc-setlevel-answer.md:2767:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:1695:./noncirc-setlevel-answer.md:2768:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./rung2-regular-section-answer.md:1702:./noncirc-setlevel-answer.md:2792:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./rung2-regular-section-answer.md:1705:./noncirc-setlevel-answer.md:2797:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./rung2-regular-section-answer.md:1707:./noncirc-setlevel-answer.md:2800:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:1709:./noncirc-setlevel-answer.md:2802:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:1714:./noncirc-setlevel-answer.md:2810:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:1715:./noncirc-setlevel-answer.md:2815:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./rung2-regular-section-answer.md:1716:./noncirc-setlevel-answer.md:2816:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./rung2-regular-section-answer.md:1717:./noncirc-setlevel-answer.md:2818:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:1719:./noncirc-setlevel-answer.md:2820:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./rung2-regular-section-answer.md:1720:./noncirc-setlevel-answer.md:2821:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./rung2-regular-section-answer.md:1721:./noncirc-setlevel-answer.md:2822:  have hne : varietyDim Z ≠ ⊤ := by
./rung2-regular-section-answer.md:1742:./noncirc-setlevel-answer.md:2882:One more adversarial point: the project’s `varietyDim` itself says it is the dimension of the Zariski closure unless the set is closed. That is fine for radical-insensitivity, but for chart opens and exact-rank strata you must explicitly account for “open chart has same closure dimension” or use the cited `hClosure` bridge.
./rung2-regular-section-answer.md:1749:./noncirc-setlevel-answer.md:3214:**Verdict: YES.** The set-level/`varietyDim` route dodges the R2-3b-4 circularity. The old circularity was specific to building a scheme/ring iso through the *generator* ideal and needing `sigmaIdeal ≤ ker`. If you work with sets and `vanishingIdeal`, the coordinate rings are already reduced-by-definition, and the required ideal containment for pullbacks is the tautological one: “a polynomial vanishing on the target pulls back to one vanishing on the source.”
./rung2-regular-section-answer.md:1750:./noncirc-setlevel-answer.md:3216:1. **Radical-insensitivity:** yes. I do not see a prepackaged v4.29 lemma named exactly `ringKrullDim_quotient_radical`, but it is a two-line lemma from Mathlib:
./rung2-regular-section-answer.md:1751:./noncirc-setlevel-answer.md:3220:lemma ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
./rung2-regular-section-answer.md:1754:./noncirc-setlevel-answer.md:3224:The relevant upstream pieces are `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`. So `varietyDim` genuinely only sees the radical/closed-set structure.
./rung2-regular-section-answer.md:1755:./noncirc-setlevel-answer.md:3231:None of that needs `sigmaIdeal ≤ ker`. The warning is different: a bare set bijection does not preserve `varietyDim`; you need the map and inverse to be regular on the pivot chart, typically via localization/principal-open coordinates. That is new chart algebra, but not the old reducedness circularity.
./rung2-regular-section-answer.md:1756:./noncirc-setlevel-answer.md:3237:But I do not see this as an existing Mathlib v4.29 theorem for `varietyDim`, nor a general
./rung2-regular-section-answer.md:1758:./noncirc-setlevel-answer.md:3242:`dim (⋃ᵢ Zᵢ) = maxᵢ dim Zᵢ` for finite nonempty covers, radical-insensitively. Mathlib has the Spec-level zero-locus/vanishing-ideal union facts, e.g. `PrimeSpectrum.vanishingIdeal_union`, `PrimeSpectrum.vanishingIdeal_iUnion`, `PrimeSpectrum.zeroLocus_inf`, but I do not see a ready `varietyDim_finite_iUnion` theorem. Also note your `varietyDim` sends the empty set to `0` via `unbotD 0`, so state product/union lemmas with the relevant nonemptiness assumptions.
./rung2-regular-section-answer.md:1759:./noncirc-setlevel-answer.md:3249:  `varietyDim(chart) = varietyDim U_P + varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:1760:./noncirc-setlevel-answer.md:3251:- Glue: finite pivot cover gives global dimension by finite-union max; use the closure/open-chart bridge carefully because `varietyDim` is closure dimension for arbitrary sets.
./rung2-regular-section-answer.md:1761:./noncirc-setlevel-answer.md:3253:So the de-risk claim is correct: radical-insensitivity of `varietyDim` removes the need to prove `fibreGenIdeal = radical fibreGenIdeal` or `sigmaIdeal ≤ ker` for the generator-level scheme iso. The remaining risk is library/build cost for product dimension and finite-glue lemmas, not circularity.
./rung2-regular-section-answer.md:1762:./noncirc-setlevel-answer.md:3256:**Verdict: YES.** The set-level/`varietyDim` route dodges the R2-3b-4 circularity. The old circularity was specific to building a scheme/ring iso through the *generator* ideal and needing `sigmaIdeal ≤ ker`. If you work with sets and `vanishingIdeal`, the coordinate rings are already reduced-by-definition, and the required ideal containment for pullbacks is the tautological one: “a polynomial vanishing on the target pulls back to one vanishing on the source.”
./rung2-regular-section-answer.md:1763:./noncirc-setlevel-answer.md:3258:1. **Radical-insensitivity:** yes. I do not see a prepackaged v4.29 lemma named exactly `ringKrullDim_quotient_radical`, but it is a two-line lemma from Mathlib:
./rung2-regular-section-answer.md:1764:./noncirc-setlevel-answer.md:3262:lemma ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
./rung2-regular-section-answer.md:1767:./noncirc-setlevel-answer.md:3266:The relevant upstream pieces are `ringKrullDim_quotient` and `PrimeSpectrum.zeroLocus_radical`. So `varietyDim` genuinely only sees the radical/closed-set structure.
./rung2-regular-section-answer.md:1768:./noncirc-setlevel-answer.md:3273:None of that needs `sigmaIdeal ≤ ker`. The warning is different: a bare set bijection does not preserve `varietyDim`; you need the map and inverse to be regular on the pivot chart, typically via localization/principal-open coordinates. That is new chart algebra, but not the old reducedness circularity.
./rung2-regular-section-answer.md:1769:./noncirc-setlevel-answer.md:3279:But I do not see this as an existing Mathlib v4.29 theorem for `varietyDim`, nor a general
./rung2-regular-section-answer.md:1771:./noncirc-setlevel-answer.md:3284:`dim (⋃ᵢ Zᵢ) = maxᵢ dim Zᵢ` for finite nonempty covers, radical-insensitively. Mathlib has the Spec-level zero-locus/vanishing-ideal union facts, e.g. `PrimeSpectrum.vanishingIdeal_union`, `PrimeSpectrum.vanishingIdeal_iUnion`, `PrimeSpectrum.zeroLocus_inf`, but I do not see a ready `varietyDim_finite_iUnion` theorem. Also note your `varietyDim` sends the empty set to `0` via `unbotD 0`, so state product/union lemmas with the relevant nonemptiness assumptions.
./rung2-regular-section-answer.md:1772:./noncirc-setlevel-answer.md:3291:  `varietyDim(chart) = varietyDim U_P + varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:1773:./noncirc-setlevel-answer.md:3293:- Glue: finite pivot cover gives global dimension by finite-union max; use the closure/open-chart bridge carefully because `varietyDim` is closure dimension for arbitrary sets.
./rung2-regular-section-answer.md:1774:./noncirc-setlevel-answer.md:3295:So the de-risk claim is correct: radical-insensitivity of `varietyDim` removes the need to prove `fibreGenIdeal = radical fibreGenIdeal` or `sigmaIdeal ≤ ker` for the generator-level scheme iso. The remaining risk is library/build cost for product dimension and finite-glue lemmas, not circularity.
./rung2-regular-section-answer.md:1945:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-answer.md:1946:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-answer.md:1947:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:1955:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-answer.md:1960:- `U_P ⊆ Mat^{=r}` = pivot chart where the top-left `r×r` minor `ΔP` is invertible (a principal open
./rung2-regular-section-answer.md:1961:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-answer.md:1962:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-answer.md:1964:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-answer.md:1968:1. **On the pivot chart `D(ΔP)`, is there a REGULAR (polynomial-in-entries-after-inverting-ΔP)
./rung2-regular-section-answer.md:1971:   the inverse of that block and its Schur complement — all REGULAR after inverting `ΔP`. So I expect
./rung2-regular-section-answer.md:1979:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-answer.md:1982:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-answer.md:1984:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-answer.md:1986:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-answer.md:1988:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-answer.md:1992:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-answer.md:2000:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-answer.md:2001:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:2005:I’ll inspect the local Lean/exposition scaffolding around `varietyDim`, pivot charts, and the landed rank/base-change lemmas so the advice matches the actual API rather than an abstract algebraic-geometry answer.
./rung2-regular-section-answer.md:2007:/bin/bash -lc 'pwd && rg -n "def varietyDim|varietyDim|vanishingIdeal|ringKrullDim|exists_baseChange_of_rank_eq|DeepChartRing|ΔPdeep|mult_smul|baseChange|rank_eq" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-answer.md:2023:./rung2-regular-section-prompt.md:3:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-answer.md:2024:./rung2-regular-section-prompt.md:4:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-answer.md:2025:./rung2-regular-section-prompt.md:5:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:2027:./rung2-regular-section-prompt.md:13:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-answer.md:2028:./rung2-regular-section-prompt.md:19:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-answer.md:2029:./rung2-regular-section-prompt.md:20:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-answer.md:2031:./rung2-regular-section-prompt.md:22:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-answer.md:2032:./rung2-regular-section-prompt.md:37:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-answer.md:2033:./rung2-regular-section-prompt.md:40:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-answer.md:2035:./rung2-regular-section-prompt.md:42:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-answer.md:2037:./rung2-regular-section-prompt.md:44:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-answer.md:2038:./rung2-regular-section-prompt.md:46:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-answer.md:2040:./rung2-regular-section-prompt.md:50:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-answer.md:2041:./rung2-regular-section-prompt.md:58:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-answer.md:2042:./rung2-regular-section-prompt.md:59:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:2043:./rung2-regular-section-answer.md:18:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-answer.md:2044:./rung2-regular-section-answer.md:19:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-answer.md:2045:./rung2-regular-section-answer.md:20:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-answer.md:2047:./rung2-regular-section-answer.md:28:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-answer.md:2048:./rung2-regular-section-answer.md:34:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-answer.md:2049:./rung2-regular-section-answer.md:35:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-answer.md:2051:./rung2-regular-section-answer.md:37:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-answer.md:2052:./rung2-regular-section-answer.md:52:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-answer.md:2053:./rung2-regular-section-answer.md:55:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-answer.md:2055:./rung2-regular-section-answer.md:57:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-answer.md:2057:./rung2-regular-section-answer.md:59:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-answer.md:2058:./rung2-regular-section-answer.md:61:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-answer.md:2060:./rung2-regular-section-answer.md:65:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-answer.md:2061:./rung2-regular-section-answer.md:73:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-answer.md:2062:./rung2-regular-section-answer.md:74:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./rung2-regular-section-answer.md:2063:./rung2-regular-section-answer.md:78:I’ll inspect the local Lean/exposition scaffolding around `varietyDim`, pivot charts, and the landed rank/base-change lemmas so the advice matches the actual API rather than an abstract algebraic-geometry answer.
./rung2-regular-section-answer.md:2064:./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./rung2-regular-section-answer.md:2065:./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./rung2-regular-section-answer.md:2066:./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./rung2-regular-section-answer.md:2068:./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./rung2-regular-section-answer.md:2069:./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./rung2-regular-section-answer.md:2071:./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./rung2-regular-section-answer.md:2072:./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./rung2-regular-section-answer.md:2073:./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./rung2-regular-section-answer.md:2075:./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./rung2-regular-section-answer.md:2077:./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./rung2-regular-section-answer.md:2078:./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-regular-section-answer.md:2079:./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:2080:./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:2081:./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:2082:./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:2085:./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:2087:./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:2088:./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:2089:./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:2090:./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:2091:./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:2092:./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:2095:./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:2097:./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:2098:./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:2101:./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./rung2-regular-section-answer.md:2102:./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./rung2-regular-section-answer.md:2103:./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./rung2-regular-section-answer.md:2104:./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./rung2-regular-section-answer.md:2107:./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./rung2-regular-section-answer.md:2109:./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./rung2-regular-section-answer.md:2110:./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./rung2-regular-section-answer.md:2113:./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./rung2-regular-section-answer.md:2114:./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./rung2-regular-section-answer.md:2116:./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./rung2-regular-section-answer.md:2117:./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./rung2-regular-section-answer.md:2118:./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./rung2-regular-section-answer.md:2121:./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./rung2-regular-section-answer.md:2122:./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./rung2-regular-section-answer.md:2125:./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./rung2-regular-section-answer.md:2126:./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:2127:./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./rung2-regular-section-answer.md:2129:./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./rung2-regular-section-answer.md:2130:./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:2131:./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./rung2-regular-section-answer.md:2132:./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./rung2-regular-section-answer.md:2133:./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./rung2-regular-section-answer.md:2134:./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./rung2-regular-section-answer.md:2135:./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./rung2-regular-section-answer.md:2147:./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./rung2-regular-section-answer.md:2153:./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./rung2-regular-section-answer.md:2154:./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./rung2-regular-section-answer.md:2155:./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./rung2-regular-section-answer.md:2156:./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./rung2-regular-section-answer.md:2158:./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./rung2-regular-section-answer.md:2159:./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./rung2-regular-section-answer.md:2160:./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./rung2-regular-section-answer.md:2161:./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./rung2-regular-section-answer.md:2170:/bin/bash -lc "rg -n \"def varietyDim|theorem .*varietyDim|ringKrullDim_quotient|radical|vanishingIdeal_isRadical|DeepChartRing|ΔPdeep|pivot|Localization\\.Away|exists_baseChange_of_rank_eq|baseChange|mult_smul|def mult|rank_eq|ProductRank\" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/*.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-answer.md:2175:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:128:-- Deep chart ring (R2-3b-1+2, the residual G2-3 wall foundation): `Sred = Localization.Away(ΔPdeep) ⧸
./rung2-regular-section-answer.md:2177:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:135:-- (= landed `BaseChange.baseChange`) on the generic tuple, `gaugeEquiv d P`, over arbitrary CommRing R,
./rung2-regular-section-answer.md:2195:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./rung2-regular-section-answer.md:2196:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:5:# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
./rung2-regular-section-answer.md:2197:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:13:on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
./rung2-regular-section-answer.md:2198:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:19:1. `ΔPdeep d r hp hq` — the deep pivot minor: the determinant of the top-left `r×r` submatrix of the
./rung2-regular-section-answer.md:2199:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:22:   `Localization.Away (ΔPdeep …)` (the deep analog of `Iad`).
./rung2-regular-section-answer.md:2200:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:23:3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
./rung2-regular-section-answer.md:2201:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:33:   pivot minor `detPivotPoly` to the deep `ΔPdeep` (det commutes with `aeval`, `AlgHom.map_det`),
./rung2-regular-section-answer.md:2202:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:41:7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
./rung2-regular-section-answer.md:2203:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:42:   Localization.Away (ΔPdeep …)` (`IsLocalization.Away.mapₐ`), lifted to the quotients
./rung2-regular-section-answer.md:2205:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:104:/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
./rung2-regular-section-answer.md:2207:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:107:noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:2208:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:114:pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
./rung2-regular-section-answer.md:2209:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:117:    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
./rung2-regular-section-answer.md:2210:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:119:    (Localization.Away (ΔPdeep (k := k) d r hp hq)))
./rung2-regular-section-answer.md:2211:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:121:/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
./rung2-regular-section-answer.md:2213:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:126:  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq
./rung2-regular-section-answer.md:2214:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:132:It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
./rung2-regular-section-answer.md:2218:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:138:/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
./rung2-regular-section-answer.md:2223:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:147:  rw [← Ideal.radical_eq_iff, IadDeep,
./rung2-regular-section-answer.md:2224:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:148:    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
./rung2-regular-section-answer.md:2226:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:152:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
./rung2-regular-section-answer.md:2228:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:163:`deepBaseComap` carries the `N = 1` pivot minor `detPivotPoly` to the deep `ΔPdeep` (making the
./rung2-regular-section-answer.md:2230:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:168:`detPivotPoly (d 0) (d last) r` to the deep pivot minor `ΔPdeep d r`. The determinant commutes with
./rung2-regular-section-answer.md:2232:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:176:      = ΔPdeep (k := k) d r hp hq := by
./rung2-regular-section-answer.md:2233:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:177:  rw [detPivotPoly, ΔPdeep, AlgHom.map_det]
./rung2-regular-section-answer.md:2234:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:248:The localized base map `Localization.Away detPivotPoly →ₐ[k] Localization.Away (ΔPdeep …)`
./rung2-regular-section-answer.md:2237:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:254:Localization.Away (ΔPdeep …)`, `IsLocalization.Away.mapₐ` of the deep base comorphism
./rung2-regular-section-answer.md:2238:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:256:codomain localization instance at `deepBaseComap d (detPivotPoly …)` is `ΔPdeep`'s (the transport
./rung2-regular-section-answer.md:2240:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:261:      Localization.Away (ΔPdeep (k := k) d r hp hq) := by
./rung2-regular-section-answer.md:2242:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:264:      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
./rung2-regular-section-answer.md:2246:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:277:      = algebraMap (MvPolynomial (RepCoord d) k) (Localization.Away (ΔPdeep (k := k) d r hp hq))
./rung2-regular-section-answer.md:2248:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:281:      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
./rung2-regular-section-answer.md:2255:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:408:`deepBaseComap (detPivotPoly …) = ΔPdeep …`. -/
./rung2-regular-section-answer.md:2256:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:412:      = ΔPdeep (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
./rung2-regular-section-answer.md:2339:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./rung2-regular-section-answer.md:2526:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VoigtDischarge.lean:38:theorem varietyDim_orbitRankLocus_eq_finrank_range_deformationδ
./rung2-regular-section-answer.md:2583:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:603:theorem finrank_cotangent_eq_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./rung2-regular-section-answer.md:2585:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:641:theorem finrank_range_deformationδ_le_varietyDim [IsAlgClosed k] (M : Tuple (k := k) d) :
./rung2-regular-section-answer.md:2599:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:2604:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./rung2-regular-section-answer.md:2605:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./rung2-regular-section-answer.md:2606:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:2607:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./rung2-regular-section-answer.md:2666:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:106:⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
./rung2-regular-section-answer.md:2673:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:133:    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]
./rung2-regular-section-answer.md:2694:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./rung2-regular-section-answer.md:2695:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:2697:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:2698:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:2699:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:2700:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:2733:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:8:# `DLNFibre.Core.VarietyDimRadical` — `varietyDim`/`ringKrullDim` is radical-insensitive
./rung2-regular-section-answer.md:2734:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:12:inclusion `sigmaIdeal ≤ ker`, available only as `≤ radical`. The **dimension** identity `hSweep`
./rung2-regular-section-answer.md:2737:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:19:- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
./rung2-regular-section-answer.md:2740:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:30:theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
./rung2-regular-section-answer.md:2747:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:40:  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]
./rung2-regular-section-answer.md:2755:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:95:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ
./rung2-regular-section-answer.md:2845:The key repo fact so far: `varietyDim` is still the set-level ambient-polynomial definition in `NullstellensatzCodim`, and `VarietyDimRadical` has only radical-insensitivity, not a general “regular isomorphism preserves dimension” layer. That makes the transport choice the main Lean cost, not the existence of the section.
./rung2-regular-section-answer.md:2868:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./rung2-regular-section-answer.md:2873:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./rung2-regular-section-answer.md:2876:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:2878:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:2886:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:2891:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./rung2-regular-section-answer.md:2892:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./rung2-regular-section-answer.md:2894:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:2896:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./rung2-regular-section-answer.md:2897:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./rung2-regular-section-answer.md:2898:  have hne : varietyDim Z ≠ ⊤ := by
./rung2-regular-section-answer.md:2911:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./rung2-regular-section-answer.md:2912:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:2915:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./rung2-regular-section-answer.md:2916:  height_vanishingIdeal_add_varietyDim_eq_card hp
./rung2-regular-section-answer.md:2919:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./rung2-regular-section-answer.md:2921:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:2924:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./rung2-regular-section-answer.md:2925:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./rung2-regular-section-answer.md:2928:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./rung2-regular-section-answer.md:2930:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:2934:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:2935:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./rung2-regular-section-answer.md:2954:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./rung2-regular-section-answer.md:2959:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:2967:# `DLNFibre.Core.VarietyDimRadical` — `varietyDim`/`ringKrullDim` is radical-insensitive
./rung2-regular-section-answer.md:2971:inclusion `sigmaIdeal ≤ ker`, available only as `≤ radical`. The **dimension** identity `hSweep`
./rung2-regular-section-answer.md:2972:(`varietyDim Σ^r = δ + varietyDim F`) never touches that question, because `varietyDim` reads only
./rung2-regular-section-answer.md:2978:- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
./rung2-regular-section-answer.md:2989:theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
./rung2-regular-section-answer.md:2994:fibre-dimension build consumes (it reads `varietyDim` off `vanishingIdeal`, while a chart
./rung2-regular-section-answer.md:2999:  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]
./rung2-regular-section-answer.md:3495:# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
./rung2-regular-section-answer.md:3502:vector `d : Fin (N + 1) → ℕ`, the deep localized chart ring `Sred` of the rank-`≤ r` product locus
./rung2-regular-section-answer.md:3503:on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
./rung2-regular-section-answer.md:3504:`SchurLoc`-algebra structure (the `R = SchurLoc`-algebra structure that R2-3a's `e` needs).
./rung2-regular-section-answer.md:3509:1. `ΔPdeep d r hp hq` — the deep pivot minor: the determinant of the top-left `r×r` submatrix of the
./rung2-regular-section-answer.md:3511:2. `IadDeep d r hp hq` — the localized base ideal `(sigmaIdeal d r).map (algebraMap …)` pushed into
./rung2-regular-section-answer.md:3512:   `Localization.Away (ΔPdeep …)` (the deep analog of `Iad`).
./rung2-regular-section-answer.md:3513:3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
./rung2-regular-section-answer.md:3514:   its `CommRing` / `Algebra k` instances inherited, and `isReduced_Sred` : `IsReduced (Sred …)`
./rung2-regular-section-answer.md:3515:   (over `[IsAlgClosed k]`, justifying the name — this is R2-3a's `hSred`, now discharged).
./rung2-regular-section-answer.md:3521:**R2-3b-2 — the localized base→total map + the `SchurLoc`-algebra structure.**
./rung2-regular-section-answer.md:3523:   pivot minor `detPivotPoly` to the deep `ΔPdeep` (det commutes with `aeval`, `AlgHom.map_det`),
./rung2-regular-section-answer.md:3531:7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
./rung2-regular-section-answer.md:3532:   Localization.Away (ΔPdeep …)` (`IsLocalization.Away.mapₐ`), lifted to the quotients
./rung2-regular-section-answer.md:3534:   `SchurLoc q p r →ₐ[k] Sred d r hp hq`. The resulting `SchurLoc`-algebra structure on `Sred`
./rung2-regular-section-answer.md:3535:   (`RingHom.toAlgebra`) + the `IsScalarTower k (SchurLoc …) (Sred …)` instance.
./rung2-regular-section-answer.md:3537:**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
./rung2-regular-section-answer.md:3541:discharged here: `isReduced_Sred`, so R2-3b-4 needs only `e` itself.) The R2-3b-3
./rung2-regular-section-answer.md:3592:/-! ## R2-3b-1 — the deep chart ring `Sred` -/
./rung2-regular-section-answer.md:3594:/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
./rung2-regular-section-answer.md:3597:noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:3603:/-- **The deep localized base ideal** `IadDeep d r`: the determinantal base ideal `sigmaIdeal d r`
./rung2-regular-section-answer.md:3604:pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
./rung2-regular-section-answer.md:3605:noncomputable def IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:3607:    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
./rung2-regular-section-answer.md:3609:    (Localization.Away (ΔPdeep (k := k) d r hp hq)))
./rung2-regular-section-answer.md:3611:/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
./rung2-regular-section-answer.md:3614:noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:3616:  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq
./rung2-regular-section-answer.md:3618:/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)
./rung2-regular-section-answer.md:3620:The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
./rung2-regular-section-answer.md:3621:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
./rung2-regular-section-answer.md:3622:It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
./rung2-regular-section-answer.md:3628:/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
./rung2-regular-section-answer.md:3632:theorem IadDeep_isRadical [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:3634:    (IadDeep (k := k) d r hp hq).IsRadical := by
./rung2-regular-section-answer.md:3637:  rw [← Ideal.radical_eq_iff, IadDeep,
./rung2-regular-section-answer.md:3638:    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
./rung2-regular-section-answer.md:3641:/-- **`Sred` is reduced** (`[IsAlgClosed k]`), justifying the name.
./rung2-regular-section-answer.md:3642:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
./rung2-regular-section-answer.md:3644:(`Ideal.isRadical_iff_quotient_reduced`). This is exactly R2-3a's `hSred : IsReduced S` for
./rung2-regular-section-answer.md:3645:`S = Sred` — so R2-3b-4 needs to build only `e` itself, not also `IsReduced S`. -/
./rung2-regular-section-answer.md:3646:theorem isReduced_Sred [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:3648:    IsReduced (Sred (k := k) d r hp hq) :=
./rung2-regular-section-answer.md:3649:  (Ideal.isRadical_iff_quotient_reduced _).mp (IadDeep_isRadical d r hp hq)
./rung2-regular-section-answer.md:3653:`deepBaseComap` carries the `N = 1` pivot minor `detPivotPoly` to the deep `ΔPdeep` (making the
./rung2-regular-section-answer.md:3658:`detPivotPoly (d 0) (d last) r` to the deep pivot minor `ΔPdeep d r`. The determinant commutes with
./rung2-regular-section-answer.md:3666:      = ΔPdeep (k := k) d r hp hq := by
./rung2-regular-section-answer.md:3667:  rw [detPivotPoly, ΔPdeep, AlgHom.map_det]
./rung2-regular-section-answer.md:3736:/-! ## R2-3b-2 — the localized base map and the `SchurLoc`-algebra structure on `Sred`
./rung2-regular-section-answer.md:3738:The localized base map `Localization.Away detPivotPoly →ₐ[k] Localization.Away (ΔPdeep …)`
./rung2-regular-section-answer.md:3744:Localization.Away (ΔPdeep …)`, `IsLocalization.Away.mapₐ` of the deep base comorphism
./rung2-regular-section-answer.md:3746:codomain localization instance at `deepBaseComap d (detPivotPoly …)` is `ΔPdeep`'s (the transport
./rung2-regular-section-answer.md:3751:      Localization.Away (ΔPdeep (k := k) d r hp hq) := by
./rung2-regular-section-answer.md:3754:      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
./rung2-regular-section-answer.md:3767:      = algebraMap (MvPolynomial (RepCoord d) k) (Localization.Away (ΔPdeep (k := k) d r hp hq))
./rung2-regular-section-answer.md:3771:      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
./rung2-regular-section-answer.md:3777:/-- The base ideal `Iad` is carried into `IadDeep` by `baseLocMap`
./rung2-regular-section-answer.md:3778:(`Iad ≤ IadDeep.comap baseLocMap`), the hypothesis the quotient lift needs. `Iad`/`IadDeep` are the
./rung2-regular-section-answer.md:3782:theorem Iad_le_comap_IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:3785:      ≤ (IadDeep (k := k) d r hp hq).comap (baseLocMap (k := k) d r hp hq) := by
./rung2-regular-section-answer.md:3788:  rw [Ideal.mem_comap, Ideal.mem_comap, baseLocMap_algebraMap, IadDeep]
./rung2-regular-section-answer.md:3795:Sred d r`: the quotient lift of `baseLocMap` (`Ideal.quotientMapₐ`, the ideal hypothesis from
./rung2-regular-section-answer.md:3796:`Iad_le_comap_IadDeep`). -/
./rung2-regular-section-answer.md:3801:      →ₐ[k] Sred (k := k) d r hp hq :=
./rung2-regular-section-answer.md:3802:  Ideal.quotientMapₐ (IadDeep (k := k) d r hp hq) (baseLocMap (k := k) d r hp hq)
./rung2-regular-section-answer.md:3803:    (Iad_le_comap_IadDeep d r hp hq)
./rung2-regular-section-answer.md:3805:/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
./rung2-regular-section-answer.md:3807:algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
./rung2-regular-section-answer.md:3809:noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:3811:    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
./rung2-regular-section-answer.md:3815:/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower
./rung2-regular-section-answer.md:3817:The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
./rung2-regular-section-answer.md:3818:structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
./rung2-regular-section-answer.md:3819:`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/
./rung2-regular-section-answer.md:3821:/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
./rung2-regular-section-answer.md:3822:(`RingHom.toAlgebra`). The `R = SchurLoc q p r`-algebra structure R2-3a's product iso `e` needs. -/
./rung2-regular-section-answer.md:3825:    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
./rung2-regular-section-answer.md:3826:  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra
./rung2-regular-section-answer.md:3828:/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
./rung2-regular-section-answer.md:3829:tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
./rung2-regular-section-answer.md:3833:    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
./rung2-regular-section-answer.md:3837:  -- `algebraMap (SchurLoc …) Sred = schurToSred.toRingHom` (by `toAlgebra`); `schurToSred` is a
./rung2-regular-section-answer.md:3838:  -- `k`-algebra map, so it commutes with `algebraMap k (SchurLoc …)` (`AlgHom.commutes`).
./rung2-regular-section-answer.md:3839:  change algebraMap k (Sred (k := k) d r hp hq) x
./rung2-regular-section-answer.md:3840:      = (schurToSred (k := k) d r hp hq).toRingHom (algebraMap k _ x)
./rung2-regular-section-answer.md:3841:  exact (AlgHom.commutes (schurToSred (k := k) d r hp hq) x).symm
./rung2-regular-section-answer.md:3898:`deepBaseComap (detPivotPoly …) = ΔPdeep …`. -/
./rung2-regular-section-answer.md:3902:      = ΔPdeep (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
./rung2-regular-section-answer.md:3907:`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
./rung2-regular-section-answer.md:3913:      →ₐ[AlgebraicClosure ℚ] Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
./rung2-regular-section-answer.md:3916:/-- `Sred` is reduced at the `N = 1` anchor `dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — the
./rung2-regular-section-answer.md:3917:name is honest there, and R2-3a's `hSred` is discharged. -/
./rung2-regular-section-answer.md:3919:    IsReduced (Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h) :=
./rung2-regular-section-answer.md:3920:  isReduced_Sred (dStratum 2 2) 1 h h
./rung2-regular-section-answer.md:3975:abbrev SchurLoc (q p r : ℕ) : Type u :=
./rung2-regular-section-answer.md:3982:      ≃ₐ[k] MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r) := by
./rung2-regular-section-answer.md:3985:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
./rung2-regular-section-answer.md:3991:    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) x
./rung2-regular-section-answer.md:3992:        = C (algebraMap k (SchurLoc (k := k) q p r) x) := by
./rung2-regular-section-answer.md:3993:      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:3994:        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
./rung2-regular-section-answer.md:4000:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
./rung2-regular-section-answer.md:4004:        (S := SchurLoc (k := k) q p r))
./rung2-regular-section-answer.md:4011:    (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
./rung2-regular-section-answer.md:4171:          (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
./rung2-regular-section-answer.md:4174:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
./rung2-regular-section-answer.md:4180:    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) y
./rung2-regular-section-answer.md:4181:        = C (algebraMap k (SchurLoc (k := k) q p r) y) := by
./rung2-regular-section-answer.md:4182:      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:4183:        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
./rung2-regular-section-answer.md:4187:      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
./rung2-regular-section-answer.md:4190:        (M := Submonoid.powers (detSchurS (k := k) q p r)) (S := SchurLoc (k := k) q p r))
./rung2-regular-section-answer.md:4208:    C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:4210:        * (X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b')))
./rung2-regular-section-answer.md:4222:    IsLocalization.mk'_spec' (SchurLoc (k := k) q p r) ((forcedNum (k := k) q p r) a' b')
./rung2-regular-section-answer.md:4229:    graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))
./rung2-regular-section-answer.md:4234:  show X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b'))
./rung2-regular-section-answer.md:4237:  have hunit : IsUnit (C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:4238:      (detSchurS (k := k) q p r)) : MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) :=
./rung2-regular-section-answer.md:4240:      (C : SchurLoc (k := k) q p r →+* _)
./rung2-regular-section-answer.md:4258:      = graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) := by
./rung2-regular-section-answer.md:4259:  set Q := MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:4262:  set J : Ideal Q := graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) with hJ
./rung2-regular-section-answer.md:4275:  haveI : IsDomain (SchurLoc (k := k) q p r) :=
./rung2-regular-section-answer.md:4276:    IsLocalization.isDomain_of_le_nonZeroDivisors (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:4287:    height_graphIdeal_forcedB22_eq q p r (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:4305:      ≃ₐ[k] SchurLoc (k := k) q p r := by
./rung2-regular-section-answer.md:4307:      ≃ₐ[k] (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:4308:        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))) :=
./rung2-regular-section-answer.md:4310:      (graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
./rung2-regular-section-answer.md:4313:  have e₂ : (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:4314:        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
./rung2-regular-section-answer.md:4315:      ≃ₐ[k] SchurLoc (k := k) q p r :=
./rung2-regular-section-answer.md:4316:    (graphIdealQuotientEquiv (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))).restrictScalars k
./rung2-regular-section-answer.md:4337:      ≃ₐ[k] SchurLoc (k := k) 2 2 1 :=
./rung2-regular-section-answer.md:4343:There is already a ring-level pivot chart presentation for the base (`A_loc/Iad ≃ SchurLoc`) and the deep chart ring (`Sred`). That suggests the lowest-friction Lean path is likely not to introduce a general category of regular maps, but to express the trivialization directly as an `AlgEquiv` between localized quotient coordinate rings.
./rung2-regular-section-answer.md:4359:**inherited** from the reduced ambient rank-locus chart `Sred` via the **faithfully-flat product
./rung2-regular-section-answer.md:4449:ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
./rung2-regular-section-answer.md:4452:⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
./rung2-regular-section-answer.md:4457:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
./rung2-regular-section-answer.md:4459:  letI := hSred
./rung2-regular-section-answer.md:4476:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
./rung2-regular-section-answer.md:4479:    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]
./rung2-regular-section-answer.md:4510:/bin/bash -lc 'rg -n "FibreAlg|fibreGenIdeal|BundleShift|Sred|tensor|TensorProduct|height.*ringKrullDim|codim.*varietyDim|Route|fibration|relative" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-answer.md:4512:/bin/bash -lc 'rg -n "Regular|IsRegular|regular|AlgEquiv.*quotient|varietyDim.*AlgEquiv|varietyDim.*equiv|ringKrullDim.*AlgEquiv|ringKrullDim.*RingEquiv|product.*varietyDim|finite.*union.*varietyDim|iUnion.*varietyDim|Product|Prod" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/RingTheory /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib/AlgebraicGeometry | head -n 300' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-regular-section-answer.md:4518:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:128:-- Deep chart ring (R2-3b-1+2, the residual G2-3 wall foundation): `Sred = Localization.Away(ΔPdeep) ⧸
./rung2-regular-section-answer.md:4519:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:130:-- bridges, and the localized base→total map `schurToSred : SchurLoc → Sred` giving Sred its
./rung2-regular-section-answer.md:4520:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:131:-- SchurLoc-algebra structure (R2-3a's R = SchurLoc, S = Sred). The crux containments (det transport,
./rung2-regular-section-answer.md:4524:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./rung2-regular-section-answer.md:4539:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:4540:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./rung2-regular-section-answer.md:4541:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:4542:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./rung2-regular-section-answer.md:4543:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./rung2-regular-section-answer.md:4544:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:4545:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:4546:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./rung2-regular-section-answer.md:4570:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:5:# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
./rung2-regular-section-answer.md:4571:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:12:vector `d : Fin (N + 1) → ℕ`, the deep localized chart ring `Sred` of the rank-`≤ r` product locus
./rung2-regular-section-answer.md:4572:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:13:on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
./rung2-regular-section-answer.md:4573:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:23:3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
./rung2-regular-section-answer.md:4574:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:24:   its `CommRing` / `Algebra k` instances inherited, and `isReduced_Sred` : `IsReduced (Sred …)`
./rung2-regular-section-answer.md:4575:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:25:   (over `[IsAlgClosed k]`, justifying the name — this is R2-3a's `hSred`, now discharged).
./rung2-regular-section-answer.md:4577:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:41:7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
./rung2-regular-section-answer.md:4578:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:44:   `SchurLoc q p r →ₐ[k] Sred d r hp hq`. The resulting `SchurLoc`-algebra structure on `Sred`
./rung2-regular-section-answer.md:4579:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:45:   (`RingHom.toAlgebra`) + the `IsScalarTower k (SchurLoc …) (Sred …)` instance.
./rung2-regular-section-answer.md:4580:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:47:**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
./rung2-regular-section-answer.md:4582:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:51:discharged here: `isReduced_Sred`, so R2-3b-4 needs only `e` itself.) The R2-3b-3
./rung2-regular-section-answer.md:4583:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:102:/-! ## R2-3b-1 — the deep chart ring `Sred` -/
./rung2-regular-section-answer.md:4584:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:121:/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
./rung2-regular-section-answer.md:4585:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:124:noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:4586:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:128:/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)
./rung2-regular-section-answer.md:4587:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:130:The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
./rung2-regular-section-answer.md:4588:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:131:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
./rung2-regular-section-answer.md:4589:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:151:/-- **`Sred` is reduced** (`[IsAlgClosed k]`), justifying the name.
./rung2-regular-section-answer.md:4590:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:152:`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
./rung2-regular-section-answer.md:4591:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:154:(`Ideal.isRadical_iff_quotient_reduced`). This is exactly R2-3a's `hSred : IsReduced S` for
./rung2-regular-section-answer.md:4592:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:155:`S = Sred` — so R2-3b-4 needs to build only `e` itself, not also `IsReduced S`. -/
./rung2-regular-section-answer.md:4593:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:156:theorem isReduced_Sred [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:4594:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:158:    IsReduced (Sred (k := k) d r hp hq) :=
./rung2-regular-section-answer.md:4596:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:246:/-! ## R2-3b-2 — the localized base map and the `SchurLoc`-algebra structure on `Sred`
./rung2-regular-section-answer.md:4597:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:305:Sred d r`: the quotient lift of `baseLocMap` (`Ideal.quotientMapₐ`, the ideal hypothesis from
./rung2-regular-section-answer.md:4598:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:311:      →ₐ[k] Sred (k := k) d r hp hq :=
./rung2-regular-section-answer.md:4599:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:315:/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
./rung2-regular-section-answer.md:4600:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:317:algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
./rung2-regular-section-answer.md:4601:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:319:noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:4602:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:321:    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
./rung2-regular-section-answer.md:4603:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:325:/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower
./rung2-regular-section-answer.md:4604:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:327:The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
./rung2-regular-section-answer.md:4605:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:328:structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
./rung2-regular-section-answer.md:4606:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:329:`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/
./rung2-regular-section-answer.md:4607:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:331:/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
./rung2-regular-section-answer.md:4608:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:335:    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
./rung2-regular-section-answer.md:4609:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:336:  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra
./rung2-regular-section-answer.md:4610:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:338:/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
./rung2-regular-section-answer.md:4611:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:339:tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
./rung2-regular-section-answer.md:4612:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:343:    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
./rung2-regular-section-answer.md:4613:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:347:  -- `algebraMap (SchurLoc …) Sred = schurToSred.toRingHom` (by `toAlgebra`); `schurToSred` is a
./rung2-regular-section-answer.md:4614:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:349:  change algebraMap k (Sred (k := k) d r hp hq) x
./rung2-regular-section-answer.md:4615:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:350:      = (schurToSred (k := k) d r hp hq).toRingHom (algebraMap k _ x)
./rung2-regular-section-answer.md:4616:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:351:  exact (AlgHom.commutes (schurToSred (k := k) d r hp hq) x).symm
./rung2-regular-section-answer.md:4617:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:417:`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
./rung2-regular-section-answer.md:4618:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:423:      →ₐ[AlgebraicClosure ℚ] Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
./rung2-regular-section-answer.md:4619:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:426:/-- `Sred` is reduced at the `N = 1` anchor `dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — the
./rung2-regular-section-answer.md:4620:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:427:name is honest there, and R2-3a's `hSred` is discharged. -/
./rung2-regular-section-answer.md:4621:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:429:    IsReduced (Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h) :=
./rung2-regular-section-answer.md:4622:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:430:  isReduced_Sred (dStratum 2 2) 1 h h
./rung2-regular-section-answer.md:4633:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:55:/-- LANDED: the catenary closer (PRIMALITY-gated) — `codim Z = card − varietyDim Z`. -/
./rung2-regular-section-answer.md:4634:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:59:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./rung2-regular-section-answer.md:4635:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:60:  codimRepCanonical_eq_card_sub_varietyDim Z hp
./rung2-regular-section-answer.md:4661:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./rung2-regular-section-answer.md:4673:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./rung2-regular-section-answer.md:4674:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./rung2-regular-section-answer.md:4675:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./rung2-regular-section-answer.md:4676:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:4677:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:181:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
./rung2-regular-section-answer.md:4679:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:197:  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:4680:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:203:The reducible-locus catenary at `codimRepCanonical`/`varietyDim` fires on the whole space `univ`
./rung2-regular-section-answer.md:4681:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:211:  codimRepCanonical_add_varietyDim_eq_card_of_nonempty
./rung2-regular-section-answer.md:4719:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:13:**inherited** from the reduced ambient rank-locus chart `Sred` via the **faithfully-flat product
./rung2-regular-section-answer.md:4741:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:103:ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
./rung2-regular-section-answer.md:4744:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:106:⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
./rung2-regular-section-answer.md:4746:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:111:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
./rung2-regular-section-answer.md:4748:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:113:  letI := hSred
./rung2-regular-section-answer.md:4756:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:130:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
./rung2-regular-section-answer.md:4758:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:133:    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]
./rung2-regular-section-answer.md:4765:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./rung2-regular-section-answer.md:4766:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./rung2-regular-section-answer.md:4818:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VoigtDischarge.lean:64:    have hadd := codimRep_add_varietyDim_eq_card (canonicalCoord d) (orbitRankLocus M)
./rung2-regular-section-answer.md:4820:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:20:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./rung2-regular-section-answer.md:4822:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:83:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./rung2-regular-section-answer.md:4824:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:100:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./rung2-regular-section-answer.md:4825:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:115:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./rung2-regular-section-answer.md:4826:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./rung2-regular-section-answer.md:4936:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./rung2-regular-section-answer.md:5147:A useful distinction is emerging: the repository already has route-b machinery phrased exactly as `Sred ≃ₐ[k] SchurLoc ⊗ FibreAlg`, which is the ring form of the pivot trivialization. The route-c set-level goal can reuse that shape if you add dimension transport lemmas for coordinate rings, but a pointwise `σ : U → H` alone will not plug into existing APIs.
./rung2-regular-section-answer.md:5167:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
./rung2-regular-section-answer.md:5168:`varietyDim Σ^r = varietyDim Σ̄^r` (`hClosure`, Lehalleur–Rimányi 4.4/4.5) are carried as **explicit
./rung2-regular-section-answer.md:5170:relations `codimRepCanonical Z + varietyDim Z = card` are carried as named hypotheses
./rung2-regular-section-answer.md:5194:identity `hSweep`, the Cited closure bridge `hClosure`, and the two reducible-locus catenary
./rung2-regular-section-answer.md:5200:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:5202:          + varietyDim (canonicalCoord d '' fibre d B))
./rung2-regular-section-answer.md:5203:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:5204:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./rung2-regular-section-answer.md:5206:        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./rung2-regular-section-answer.md:5208:        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:5217:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:5219:        + varietyDim (canonicalCoord d '' fibre d B) := by
./rung2-regular-section-answer.md:5220:    rw [← hClosure, hSweep]
./rung2-regular-section-answer.md:5222:  have hdimF_ne : varietyDim (canonicalCoord d '' fibre d B) ≠ ⊤ := by
./rung2-regular-section-answer.md:5229:  have key : varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./rung2-regular-section-answer.md:5230:      = varietyDim (canonicalCoord d '' fibre d B)
./rung2-regular-section-answer.md:5232:    calc varietyDim (canonicalCoord d '' fibre d B) + codimRepCanonical (fibre d B)
./rung2-regular-section-answer.md:5233:        = codimRepCanonical (fibre d B) + varietyDim (canonicalCoord d '' fibre d B) := by
./rung2-regular-section-answer.md:5238:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./rung2-regular-section-answer.md:5239:      _ = varietyDim (canonicalCoord d '' fibre d B)
./rung2-regular-section-answer.md:5248:homogeneous-sweep dimension identity `hSweep` and the Cited closure bridge `hClosure` as named
./rung2-regular-section-answer.md:5250:`codimRepCanonical_add_varietyDim_eq_card_of_nonempty` (`Core.RadicalCatenary`), given that the
./rung2-regular-section-answer.md:5257:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:5259:          + varietyDim (canonicalCoord d '' fibre d B))
./rung2-regular-section-answer.md:5260:    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:5261:        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)) :
./rung2-regular-section-answer.md:5264:  codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep d r h B hB hSweep hClosure
./rung2-regular-section-answer.md:5265:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hFne)
./rung2-regular-section-answer.md:5266:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./rung2-regular-section-answer.md:5295:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./rung2-regular-section-answer.md:5425:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./rung2-regular-section-answer.md:5441:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./rung2-regular-section-answer.md:5444:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./rung2-regular-section-answer.md:5447:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}
./rung2-regular-section-answer.md:5449:    codimRepCanonical Z + varietyDim (canonicalCoord d '' Z)
./rung2-regular-section-answer.md:5465:  rw [codimRepCanonical, codimRep, varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:5568:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:67:  have hdimSigma : varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:5571:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:88:              + varietyDim (canonicalCoord d '' fibre d B)) := hCatSigma.symm
./rung2-regular-section-answer.md:5573:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:116:    (codimRepCanonical_add_varietyDim_eq_card_of_nonempty hSigmaNe)
./rung2-regular-section-answer.md:5594:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:219:noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
./rung2-regular-section-answer.md:5595:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:234:@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
./rung2-regular-section-answer.md:5596:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:242:theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
./rung2-regular-section-answer.md:5598:/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:266:    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
./rung2-regular-section-answer.md:5697:One correction to the target shape: the chart you get from `D(Δ)` is naturally a chart of the exact-rank stratum inside the closed rank-`≤ r` locus. Since `varietyDim` is closure dimension, you must keep track of whether the localized ring is for `Σ^{≤r} ∩ D(Δ)` or for `Σ^r ∩ D(Δ)`; on `D(Δ)` these have the same points because rank `≤ r` plus the nonzero `r`-minor implies rank exactly `r`.
./rung2-regular-section-answer.md:5716:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./rung2-regular-section-answer.md:6054:2. `gaugeEquiv d P` — the coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R`, assembled by
./rung2-regular-section-answer.md:6250:noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
./rung2-regular-section-answer.md:6264:/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
./rung2-regular-section-answer.md:6265:@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
./rung2-regular-section-answer.md:6267:    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl
./rung2-regular-section-answer.md:6269:/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
./rung2-regular-section-answer.md:6273:theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
./rung2-regular-section-answer.md:6275:    gaugeEquiv d P (multPoly d r c)
./rung2-regular-section-answer.md:6279:  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]
./rung2-regular-section-answer.md:6297:    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
./rung2-regular-section-answer.md:6298:  rw [gaugeEquiv_apply]
./rung2-regular-section-answer.md:6317:  gaugeEquiv dConst witnessGauge
./rung2-regular-section-answer.md:6319:/-- The mult-transport fires at the concrete non-identity gauge `witnessGauge`: `gaugeEquiv` carries
./rung2-regular-section-answer.md:6323:    gaugeEquiv (R := ℤ) dConst witnessGauge (multPoly dConst r c)
./rung2-regular-section-answer.md:6325:  gaugeEquiv_apply dConst witnessGauge (multPoly dConst r c)
./rung2-regular-section-answer.md:6339:   139	noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./rung2-regular-section-answer.md:6344:   144	the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./rung2-regular-section-answer.md:6347:   147	theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./rung2-regular-section-answer.md:6349:   149	    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./rung2-regular-section-answer.md:6357:   157	  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./rung2-regular-section-answer.md:6367:    30	theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
./rung2-regular-section-answer.md:6372:    35	fibre-dimension build consumes (it reads `varietyDim` off `vanishingIdeal`, while a chart
./rung2-regular-section-answer.md:6377:    40	  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]
./rung2-regular-section-answer.md:6380:   104	/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
./rung2-regular-section-answer.md:6383:   107	noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:6389:   113	/-- **The deep localized base ideal** `IadDeep d r`: the determinantal base ideal `sigmaIdeal d r`
./rung2-regular-section-answer.md:6390:   114	pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
./rung2-regular-section-answer.md:6391:   115	noncomputable def IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:6393:   117	    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
./rung2-regular-section-answer.md:6395:   119	    (Localization.Away (ΔPdeep (k := k) d r hp hq)))
./rung2-regular-section-answer.md:6397:   121	/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
./rung2-regular-section-answer.md:6400:   124	noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:6402:   126	  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq
./rung2-regular-section-answer.md:6404:   128	/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)
./rung2-regular-section-answer.md:6406:   130	The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
./rung2-regular-section-answer.md:6407:   315	/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
./rung2-regular-section-answer.md:6409:   317	algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
./rung2-regular-section-answer.md:6411:   319	noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
./rung2-regular-section-answer.md:6413:   321	    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
./rung2-regular-section-answer.md:6417:   325	/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower
./rung2-regular-section-answer.md:6419:   327	The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
./rung2-regular-section-answer.md:6420:   328	structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
./rung2-regular-section-answer.md:6421:   329	`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/
./rung2-regular-section-answer.md:6423:   331	/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
./rung2-regular-section-answer.md:6424:   332	(`RingHom.toAlgebra`). The `R = SchurLoc q p r`-algebra structure R2-3a's product iso `e` needs. -/
./rung2-regular-section-answer.md:6427:   335	    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
./rung2-regular-section-answer.md:6428:   336	  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra
./rung2-regular-section-answer.md:6430:   338	/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
./rung2-regular-section-answer.md:6431:   339	tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
./rung2-regular-section-answer.md:6435:   343	    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
./rung2-regular-section-answer.md:6567:   381	      ≃ₐ[k] SchurLoc (k := k) q p r := by
./rung2-regular-section-answer.md:6569:   383	      ≃ₐ[k] (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
./rung2-regular-section-answer.md:6570:   384	        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))) :=
./rung2-regular-section-answer.md:6572:   386	      (graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
./rung2-regular-section-answer.md:6592:   103	ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
./rung2-regular-section-answer.md:6595:   106	⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
./rung2-regular-section-answer.md:6600:   111	    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
./rung2-regular-section-answer.md:6602:   113	  letI := hSred
./rung2-regular-section-answer.md:6611:    44	identity `hSweep`, the Cited closure bridge `hClosure`, and the two reducible-locus catenary
./rung2-regular-section-answer.md:6617:    50	    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:6619:    52	          + varietyDim (canonicalCoord d '' fibre d B))
./rung2-regular-section-answer.md:6620:    53	    (hClosure : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
./rung2-regular-section-answer.md:6621:    54	        = varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r))
./rung2-regular-section-answer.md:6623:    56	        + varietyDim (canonicalCoord d '' fibre d B) = (Nat.card (RepCoord d) : ℕ∞))
./rung2-regular-section-answer.md:6625:    58	        + varietyDim (canonicalCoord d '' productRankLocusLE (k := k) d r)
./rung2-regular-section-answer.md:6630:   219	noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
./rung2-regular-section-answer.md:6644:   233	/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
./rung2-regular-section-answer.md:6645:   234	@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
./rung2-regular-section-answer.md:6647:   236	    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl
./rung2-regular-section-answer.md:6649:   238	/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
./rung2-regular-section-answer.md:6653:   242	theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
./rung2-regular-section-answer.md:6655:   244	    gaugeEquiv d P (multPoly d r c)
./rung2-regular-section-answer.md:6659:   248	  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]
./rung2-regular-section-answer.md:6768:- `ΔPdeep` and `Sred = Localization.Away ΔPdeep ⧸ IadDeep` for the deep chart: [DeepChartRing.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:104).
./rung2-regular-section-answer.md:6769:- `basePresentationEquiv : A_loc/Iad ≃ₐ[k] SchurLoc`, so the base chart is already the Schur/free chart: [DeterminantalBasePresentation.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:378).
./rung2-regular-section-answer.md:6770:- `schurToSred` makes `Sred` a `SchurLoc`-algebra: [DeepChartRing.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:319).
./rung2-regular-section-answer.md:6771:- `gaugeEquiv` is already the universal coordinate-change `AlgEquiv` for a `BaseChangeGroup` over any `CommRing`: [EndpointNormalization.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:219).
./rung2-regular-section-answer.md:6773:So define the section as a `BaseChangeGroup (k := SchurLoc …) d` whose endpoint units are the two block units above and whose interior units are `1`. Then instantiate `gaugeEquiv` with that universal gauge. This is the slicker route: it proves regularity by construction, as an algebra map over the localization.
./rung2-regular-section-answer.md:6790:The `varietyDim` transport is the real Lean friction. `varietyDim` is set-level, defined as
./rung2-regular-section-answer.md:6804:lemma varietyDim_eq_of_coordRingEquiv
./rung2-regular-section-answer.md:6806:    varietyDim Z = varietyDim W := by
./rung2-regular-section-answer.md:6807:  unfold varietyDim coordRing
./rung2-regular-section-answer.md:6816:ringKrullDim (SchurLoc q p r ⊗[k] FibreAlg d E)
./rung2-regular-section-answer.md:6822:So: build the explicit universal section/gauge; transport by coordinate-ring `AlgEquiv`; keep the set-level `varietyDim` bridge small and specific.
./rung2-regular-section-answer.md:6856:- `ΔPdeep` and `Sred = Localization.Away ΔPdeep ⧸ IadDeep` for the deep chart: [DeepChartRing.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:104).
./rung2-regular-section-answer.md:6857:- `basePresentationEquiv : A_loc/Iad ≃ₐ[k] SchurLoc`, so the base chart is already the Schur/free chart: [DeterminantalBasePresentation.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:378).
./rung2-regular-section-answer.md:6858:- `schurToSred` makes `Sred` a `SchurLoc`-algebra: [DeepChartRing.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:319).
./rung2-regular-section-answer.md:6859:- `gaugeEquiv` is already the universal coordinate-change `AlgEquiv` for a `BaseChangeGroup` over any `CommRing`: [EndpointNormalization.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:219).
./rung2-regular-section-answer.md:6861:So define the section as a `BaseChangeGroup (k := SchurLoc …) d` whose endpoint units are the two block units above and whose interior units are `1`. Then instantiate `gaugeEquiv` with that universal gauge. This is the slicker route: it proves regularity by construction, as an algebra map over the localization.
./rung2-regular-section-answer.md:6878:The `varietyDim` transport is the real Lean friction. `varietyDim` is set-level, defined as
./rung2-regular-section-answer.md:6892:lemma varietyDim_eq_of_coordRingEquiv
./rung2-regular-section-answer.md:6894:    varietyDim Z = varietyDim W := by
./rung2-regular-section-answer.md:6895:  unfold varietyDim coordRing
./rung2-regular-section-answer.md:6904:ringKrullDim (SchurLoc q p r ⊗[k] FibreAlg d E)
./rung2-regular-section-answer.md:6910:So: build the explicit universal section/gauge; transport by coordinate-ring `AlgEquiv`; keep the set-level `varietyDim` bridge small and specific.

exec
/bin/bash -lc 'ls -la && find .. -maxdepth 2 -name CLAUDE.md -o -name README.md -o -name AGENTS.md' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
total 2688
drwxrwxr-x 2 ubuntu ubuntu    4096 Jun 24 18:03 .
drwxrwxr-x 3 ubuntu ubuntu    4096 Jun 24 17:51 ..
-rw-rw-r-- 1 ubuntu ubuntu  432309 Jun 24 17:45 noncirc-setlevel-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    5060 Jun 24 17:42 noncirc-setlevel-prompt.md
-rw-rw-r-- 1 ubuntu ubuntu 1066445 Jun 24 17:35 route-choice-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    6557 Jun 24 17:32 route-choice-prompt.md
-rw-rw-r-- 1 ubuntu ubuntu  368500 Jun 24 18:03 rung2-lighter-path-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    4390 Jun 24 18:03 rung2-lighter-path-prompt.md
-rw-rw-r-- 1 ubuntu ubuntu  838635 Jun 24 17:56 rung2-regular-section-answer.md
-rw-rw-r-- 1 ubuntu ubuntu    4417 Jun 24 17:54 rung2-regular-section-prompt.md

exec
/bin/bash -lc "rg -n \"def .*SchurLoc|abbrev .*SchurLoc|def .*Sred|abbrev .*Sred|def .*gaugeEquiv|theorem .*gaugeEquiv|lemma .*gaugeEquiv|schurToSred|hSweep|e :|AlgEquiv.*SchurLoc|tensor|TensorProduct|krullDim|ringKrullDim\" -S --glob '*.lean' ." in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 exited 1 in 144ms:
codex
The thread directory already contains prior prompt/answer artifacts, and the code itself appears to be outside this narrow `codex` folder. I’m going to read the prior answer plus the Lean files it cited so I can separate “already decided” from “actually supported by landed declarations.”
exec
/bin/bash -lc "sed -n '1,240p' rung2-lighter-path-answer.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
Reading prompt from stdin...
OpenAI Codex v0.142.0
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: high
reasoning summaries: none
session id: 019efacd-3505-7fb3-8af2-49e577913154
--------
user
# Codex consult — is there a varietyDim-ONLY path lighter than building the full product iso `e`?

Lean 4 + Mathlib v4.29. CRITICAL scope finding: the chart `AlgEquiv` route (c)'s rung 2 needs is
ESSENTIALLY the product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg` that a PRIOR tide (R2-3b-4)
attempted and **never finished** (it remains a hypothesis in the repo, never a committed `def`). The
prior wall was Lean-mechanical: descending the gauge `gaugeEquiv` through the localization (at `ΔP`)
AND the quotient (by the cut ideal), then proving the coordinates SPLIT as `SchurLoc ⊗ FibreAlg`.

I only need a `varietyDim` (Krull-dim) statement: `varietyDim(chart) = δ + varietyDim F`. I have
LANDED:
- `varietyDim_eq_of_coordRingAlgEquiv` — transports `varietyDim` across a coordinate-ring `AlgEquiv`.
- `ringKrullDim_quotient_radical` — radical-insensitivity (so I work with reduced/`vanishingIdeal`).
- `gaugeEquiv` (universal coordinate-change `AlgEquiv` on the UNquotiented polynomial ring, over any
  `CommRing`), the sweep `Σ^r = H·F`, `multComap`, `Sred`, `SchurLoc`, `schurToSred`.
- `SchurLoc = Localization.Away detSchurS` of a polynomial ring; Mathlib has `MvPolynomial.krullDim
  _of_isNoetherianRing` (`dim R[X_1..X_n] = dim R + n`).

## The question

Building the full `e` (an `AlgEquiv` with both directions + round-trips through a
localized-quotient ring) is heavy and previously stalled. For a DIMENSION-only conclusion, is there a
LIGHTER path that avoids constructing the full `AlgEquiv`? Candidates:

1. **Inequality squeeze instead of iso.** `varietyDim(chart) ≤ δ + dim F` AND `≥ δ + dim F`
   separately, each via a one-directional regular map (a surjection/closed-immersion of coordinate
   rings) rather than a full iso. A surjection `A ↠ B` gives `dim B ≤ dim A`; an injection of
   f.g. domains gives `dim A ≤ dim B`. Could the two inequalities be gotten from the two `AlgHom`
   directions WITHOUT proving they're mutually inverse (the round-trips were the heavy part)? Does the
   reducible case break the domain-injection direction?

2. **The unquotiented gauge + ideal-image bookkeeping.** `gaugeEquiv` is a clean `AlgEquiv` on the
   UNquotiented `MvPolynomial (RepCoord d) k`. It carries `vanishingIdeal(chart)` to
   `vanishingIdeal(gauged chart)`. If the gauged chart's vanishing ideal VISIBLY splits as
   `(SchurLoc-coords ideal) + (fibre-coords ideal)` — i.e. the gauged coordinates separate into δ
   free base directions ⊗ the fibre — can I read `varietyDim` off the split WITHOUT a tensor `AlgEquiv`,
   e.g. via `MvPolynomial` variable-partition + `krullDim` of the polynomial extension? The gauge is
   an iso on the unquotiented ring (no localization/quotient descent needed THERE) — does staying
   unquotiented and only quotienting at the end dodge the descent that walled `e`?

3. **`δ`-free-directions directly.** Maybe avoid `SchurLoc ⊗ FibreAlg` entirely: show the chart
   coordinate ring is `≅ FibreAlg-coords localized-polynomial-extended by δ Schur variables`, so
   `dim = dim F + δ` directly via `MvPolynomial.krullDim_of_isNoetherianRing` + localization. This is
   the polynomial-extension route stated as a coordinate-ring iso to `(FibreAlg)[X_1..X_δ]_loc` rather
   than a tensor — is that iso EASIER to build than the symmetric tensor `e` (it's the same content,
   but maybe a cleaner Lean target)?

4. **Is the descent genuinely unavoidable?** The prior `e` needed gauge-descent through
   `Localization.Away ΔP ⧸ IadDeep`. For the dimension statement, can I work on the UNquotiented +
   UNlocalized ring as long as possible, applying the gauge `AlgEquiv` there, and only take
   `vanishingIdeal`/`ringKrullDim` at the end — so the localization/quotient interchange that walled
   `e` never arises?

Tell me: (a) which path is lightest for a DIMENSION-only conclusion, (b) whether any path genuinely
avoids the localized-quotient gauge-descent that stalled `e`, (c) an honest module estimate for the
lightest path, and (d) if NO path is materially lighter than the full `e` (i.e. rung 2 just IS
building `e`, which stalled), say so — that is a scope escalation, and the fallback is citing `hSweep`.
Be adversarial: I suspect the dimension-only framing should be lighter than the full reduced-iso, but
I need to know if the gauge-descent is the irreducible core either way.

codex
I’ll inspect the local Lean/exposition structure around the landed lemmas and the stalled product-iso attempt, then I’ll give a scope judgment grounded in what the repo actually has rather than guessing from the names.
exec
/bin/bash -lc 'pwd && rg -n "varietyDim_eq_of_coordRingAlgEquiv|ringKrullDim_quotient_radical|gaugeEquiv|Sred|SchurLoc|schurToSred|hSweep|IadDeep|Delta|ΔP|varietyDim" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
./rung2-lighter-path-prompt.md:1:# Codex consult — is there a varietyDim-ONLY path lighter than building the full product iso `e`?
./rung2-lighter-path-prompt.md:4:ESSENTIALLY the product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg` that a PRIOR tide (R2-3b-4)
./rung2-lighter-path-prompt.md:6:prior wall was Lean-mechanical: descending the gauge `gaugeEquiv` through the localization (at `ΔP`)
./rung2-lighter-path-prompt.md:7:AND the quotient (by the cut ideal), then proving the coordinates SPLIT as `SchurLoc ⊗ FibreAlg`.
./rung2-lighter-path-prompt.md:9:I only need a `varietyDim` (Krull-dim) statement: `varietyDim(chart) = δ + varietyDim F`. I have
./rung2-lighter-path-prompt.md:11:- `varietyDim_eq_of_coordRingAlgEquiv` — transports `varietyDim` across a coordinate-ring `AlgEquiv`.
./rung2-lighter-path-prompt.md:12:- `ringKrullDim_quotient_radical` — radical-insensitivity (so I work with reduced/`vanishingIdeal`).
./rung2-lighter-path-prompt.md:13:- `gaugeEquiv` (universal coordinate-change `AlgEquiv` on the UNquotiented polynomial ring, over any
./rung2-lighter-path-prompt.md:14:  `CommRing`), the sweep `Σ^r = H·F`, `multComap`, `Sred`, `SchurLoc`, `schurToSred`.
./rung2-lighter-path-prompt.md:15:- `SchurLoc = Localization.Away detSchurS` of a polynomial ring; Mathlib has `MvPolynomial.krullDim
./rung2-lighter-path-prompt.md:24:1. **Inequality squeeze instead of iso.** `varietyDim(chart) ≤ δ + dim F` AND `≥ δ + dim F`
./rung2-lighter-path-prompt.md:31:2. **The unquotiented gauge + ideal-image bookkeeping.** `gaugeEquiv` is a clean `AlgEquiv` on the
./rung2-lighter-path-prompt.md:34:   `(SchurLoc-coords ideal) + (fibre-coords ideal)` — i.e. the gauged coordinates separate into δ
./rung2-lighter-path-prompt.md:35:   free base directions ⊗ the fibre — can I read `varietyDim` off the split WITHOUT a tensor `AlgEquiv`,
./rung2-lighter-path-prompt.md:40:3. **`δ`-free-directions directly.** Maybe avoid `SchurLoc ⊗ FibreAlg` entirely: show the chart
./rung2-lighter-path-prompt.md:48:   `Localization.Away ΔP ⧸ IadDeep`. For the dimension statement, can I work on the UNquotiented +
./rung2-lighter-path-prompt.md:56:building `e`, which stalled), say so — that is a scope escalation, and the fallback is citing `hSweep`.
./route-choice-prompt.md:7:## The exact target (`hSweep`)
./route-choice-prompt.md:10:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-prompt.md:13:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-prompt.md:18:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-prompt.md:28:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-prompt.md:52:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-prompt.md:73:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-prompt.md:75:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./noncirc-setlevel-prompt.md:4:`hSweep : varietyDim Σ^r = δ + varietyDim F`. Rung 1 = a single-chart trivialization. The DECISIVE
./noncirc-setlevel-prompt.md:5:de-risk: is the SET-LEVEL / `varietyDim` version non-circular, given a PRIOR attempt (R2-3b-4) at a
./noncirc-setlevel-prompt.md:23:For `hSweep` I do NOT need reducedness. `varietyDim Z := (ringKrullDim (R ⧸ vanishingIdeal Z)).unbotD 0`
./noncirc-setlevel-prompt.md:25:`ringKrullDim (R⧸I) = ringKrullDim (R⧸√I)`. So `varietyDim` reads only the REDUCED/variety structure;
./noncirc-setlevel-prompt.md:36:1. **Is `varietyDim` genuinely radical-insensitive in Mathlib v4.29** — i.e. is `ringKrullDim (R⧸I) =
./noncirc-setlevel-prompt.md:43:   chart's normalizing gauge. This is a bijection of SETS / a `varietyDim`-preserving map. Does
./noncirc-setlevel-prompt.md:48:   `varietyDim(U×F) = varietyDim U + varietyDim F` secretly needs flatness/reducedness.
./noncirc-setlevel-prompt.md:50:3. **The product-dimension step `varietyDim(U × F) = varietyDim U + varietyDim F`.** For a product of
./noncirc-setlevel-prompt.md:58:4. **The glue over the finite pivot cover.** `varietyDim(⋃_i Z_i) = max_i varietyDim(Z_i)` for a
./noncirc-setlevel-prompt.md:62:5. **Net verdict:** does the SET-LEVEL/`varietyDim` route (c) dodge the R2-3b-4 circularity? If YES,
./noncirc-setlevel-prompt.md:65:   reducedness), say so plainly — that triggers a fallback to citing `hSweep`.
./noncirc-setlevel-prompt.md:67:The key thing I need from you: a clean YES/NO on whether radical-insensitivity of `varietyDim` lets
./rung2-lighter-path-answer.md:16:# Codex consult — is there a varietyDim-ONLY path lighter than building the full product iso `e`?
./rung2-lighter-path-answer.md:19:ESSENTIALLY the product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg` that a PRIOR tide (R2-3b-4)
./rung2-lighter-path-answer.md:21:prior wall was Lean-mechanical: descending the gauge `gaugeEquiv` through the localization (at `ΔP`)
./rung2-lighter-path-answer.md:22:AND the quotient (by the cut ideal), then proving the coordinates SPLIT as `SchurLoc ⊗ FibreAlg`.
./rung2-lighter-path-answer.md:24:I only need a `varietyDim` (Krull-dim) statement: `varietyDim(chart) = δ + varietyDim F`. I have
./rung2-lighter-path-answer.md:26:- `varietyDim_eq_of_coordRingAlgEquiv` — transports `varietyDim` across a coordinate-ring `AlgEquiv`.
./rung2-lighter-path-answer.md:27:- `ringKrullDim_quotient_radical` — radical-insensitivity (so I work with reduced/`vanishingIdeal`).
./rung2-lighter-path-answer.md:28:- `gaugeEquiv` (universal coordinate-change `AlgEquiv` on the UNquotiented polynomial ring, over any
./rung2-lighter-path-answer.md:29:  `CommRing`), the sweep `Σ^r = H·F`, `multComap`, `Sred`, `SchurLoc`, `schurToSred`.
./rung2-lighter-path-answer.md:30:- `SchurLoc = Localization.Away detSchurS` of a polynomial ring; Mathlib has `MvPolynomial.krullDim
./rung2-lighter-path-answer.md:39:1. **Inequality squeeze instead of iso.** `varietyDim(chart) ≤ δ + dim F` AND `≥ δ + dim F`
./rung2-lighter-path-answer.md:46:2. **The unquotiented gauge + ideal-image bookkeeping.** `gaugeEquiv` is a clean `AlgEquiv` on the
./rung2-lighter-path-answer.md:49:   `(SchurLoc-coords ideal) + (fibre-coords ideal)` — i.e. the gauged coordinates separate into δ
./rung2-lighter-path-answer.md:50:   free base directions ⊗ the fibre — can I read `varietyDim` off the split WITHOUT a tensor `AlgEquiv`,
./rung2-lighter-path-answer.md:55:3. **`δ`-free-directions directly.** Maybe avoid `SchurLoc ⊗ FibreAlg` entirely: show the chart
./rung2-lighter-path-answer.md:63:   `Localization.Away ΔP ⧸ IadDeep`. For the dimension statement, can I work on the UNquotiented +
./rung2-lighter-path-answer.md:71:building `e`, which stalled), say so — that is a scope escalation, and the fallback is citing `hSweep`.
./rung2-regular-section-prompt.md:3:Route (c), rung 2. Goal: a `varietyDim`-preserving (REGULAR, not bare-set) trivialization of one
./rung2-regular-section-prompt.md:4:pivot chart, `mult⁻¹(U_P) ∩ Σ^r ≅_reg U_P × F`, so that `varietyDim(chart) = varietyDim U_P +
./rung2-regular-section-prompt.md:5:varietyDim F = δ + varietyDim F`.
./rung2-regular-section-prompt.md:13:`varietyDim`. So the question is whether I can upgrade the existential to a regular section on a
./rung2-regular-section-prompt.md:18:- `U_P ⊆ Mat^{=r}` = pivot chart where the top-left `r×r` minor `ΔP` is invertible (a principal open
./rung2-regular-section-prompt.md:19:  `D(ΔP)`; `Localization.Away ΔP`). The engine has the deep pivot minor `ΔPdeep` and
./rung2-regular-section-prompt.md:20:  `Localization.Away (ΔPdeep)` already (`DeepChartRing`).
./rung2-regular-section-prompt.md:22:- `varietyDim` is set-level (`ringKrullDim` of `vanishingIdeal`), radical-insensitive (just landed).
./rung2-regular-section-prompt.md:26:1. **On the pivot chart `D(ΔP)`, is there a REGULAR (polynomial-in-entries-after-inverting-ΔP)
./rung2-regular-section-prompt.md:29:   the inverse of that block and its Schur complement — all REGULAR after inverting `ΔP`. So I expect
./rung2-regular-section-prompt.md:37:   a genuine regular iso, hence `varietyDim`-preserving. Any subtlety (e.g. does `σ(mult A)⁻¹ • A ∈ F`
./rung2-regular-section-prompt.md:40:3. **Is "regular iso ⟹ equal `varietyDim`" cheap in Lean v4.29?** `varietyDim` is
./rung2-regular-section-prompt.md:42:   coordinate rings, and `ringKrullDim_eq_of_ringEquiv` transports. But the engine's `varietyDim` is
./rung2-regular-section-prompt.md:44:   ring — transporting `varietyDim` across a regular iso between subsets of DIFFERENT ambient spaces
./rung2-regular-section-prompt.md:46:   ring iso, not just the set iso. Is the cleanest path to (a) define `varietyDim` intrinsically via
./rung2-regular-section-prompt.md:50:4. **Could I AVOID the regular section entirely?** E.g. is there a cleaner route to `varietyDim Σ^r =
./rung2-regular-section-prompt.md:58:the cleanest `varietyDim`-transport shape, and whether the chart route or the action-map route is
./rung2-regular-section-prompt.md:59:cheaper. Be concrete about the Lean friction in transporting set-level `varietyDim` across a regular
./route-choice-answer.md:22:## The exact target (`hSweep`)
./route-choice-answer.md:25:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-answer.md:28:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-answer.md:33:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-answer.md:43:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-answer.md:67:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-answer.md:88:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-answer.md:90:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./route-choice-answer.md:185:## The exact target (`hSweep`)
./route-choice-answer.md:188:varietyDim (Σ^r)  =  δ  +  varietyDim F
./route-choice-answer.md:191:- `varietyDim Z := (ringKrullDim (MvPolynomial (RepCoord d) k ⧸ vanishingIdeal Z)).unbotD 0` — the
./route-choice-answer.md:196:- `δ = r·(d_N + d_0 − r)` = `varietyDim(Mat^{=r})`, the determinantal stratum dim (LANDED).
./route-choice-answer.md:206:3. **`varietyDim = trdeg` for an f.g. domain coordinate ring:** the engine computes `varietyDim Z =
./route-choice-answer.md:230:show `varietyDim Σ^r = trdeg_k O(Σ^r)`, `varietyDim F = trdeg_k O(F)`, `δ = trdeg_k O(Mat^{=r})`, and
./route-choice-answer.md:251:   SET-LEVEL `varietyDim` (Krull dim of a coordinate ring of a subSET of affine space), NOT scheme/
./route-choice-answer.md:253:   bridging set-level `varietyDim` to the comorphism `multComap`'s going-down add a whole layer?
./route-choice-answer.md:325:/bin/bash -lc 'rg -n "Noether.*Norm|Noetherian.*Norm|normalization|GenericFreeness|generic freeness|height_eq_under|FlatQuasiFinite|HasGoingDown|trdeg_add_eq|rankLocus|productRankLocus|varietyDim|vanishingIdeal" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean
./route-choice-answer.md:450:./DLNFibre.lean:160:-- `codimRepCanonical Z + varietyDim Z = card` for nonempty Z. Discharges the catenary hyps of RouteCAssembly.
./route-choice-answer.md:466:./DLNFibre/Core/OrbitPullbackDim.lean:6:# `DLNFibre.Core.OrbitPullbackDim` — route-c setup: `varietyDim(Z_M) = ringKrullDim((μ_M^*).range)`
./route-choice-answer.md:467:./DLNFibre/Core/OrbitPullbackDim.lean:16:1. **Ideal identification.** `varietyDim Z_M = ringKrullDim (MvPolynomial (RepCoord d) k ⧸
./route-choice-answer.md:468:./DLNFibre/Core/OrbitPullbackDim.lean:17:   ker μ_M^*)`, immediate from the `varietyDim` definition, the Abeasis–Del Fra ideal equality L6.4
./route-choice-answer.md:471:./DLNFibre/Core/OrbitPullbackDim.lean:25:The headline `varietyDim_eq_ringKrullDim_range_orbitPullback` hands A4 a finitely-generated domain
./route-choice-answer.md:472:./DLNFibre/Core/OrbitPullbackDim.lean:48:`MvPolynomial (RepCoord d) k ⧸ ker μ_M^*`. `varietyDim` definition, then L6.4
./route-choice-answer.md:475:./DLNFibre/Core/OrbitPullbackDim.lean:52:theorem varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker [Infinite k]
./route-choice-answer.md:476:./DLNFibre/Core/OrbitPullbackDim.lean:54:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:477:./DLNFibre/Core/OrbitPullbackDim.lean:57:  rw [varietyDim, vanishingIdeal_orbitRankLocus_eq_orbitSet M, ← range_orbitMap,
./route-choice-answer.md:479:./DLNFibre/Core/OrbitPullbackDim.lean:70:transcendence degree. Combines `varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker` with the
./route-choice-answer.md:480:./DLNFibre/Core/OrbitPullbackDim.lean:74:theorem varietyDim_eq_ringKrullDim_range_orbitPullback [Infinite k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:481:./DLNFibre/Core/OrbitPullbackDim.lean:76:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:482:./DLNFibre/Core/OrbitPullbackDim.lean:78:  rw [varietyDim_orbitRankLocus_eq_ringKrullDim_quotient_ker M,
./route-choice-answer.md:483:./DLNFibre/Core/OrbitPullbackDim.lean:89:/-- The headline at the concrete `(2,2,2)/ℚ` tuple: `varietyDim (canonicalCoord '' orbitRankLocus
./route-choice-answer.md:484:./DLNFibre/Core/OrbitPullbackDim.lean:93:    varietyDim (canonicalCoord dWitness '' orbitRankLocus tupleWitnessQ)
./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./route-choice-answer.md:674:./DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./route-choice-answer.md:679:./DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:681:./DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:686:./DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./route-choice-answer.md:687:./DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./route-choice-answer.md:689:./DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:691:./DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./route-choice-answer.md:692:./DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:693:./DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./route-choice-answer.md:694:./DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./route-choice-answer.md:695:./DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:697:./DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./route-choice-answer.md:698:./DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./route-choice-answer.md:700:./DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:702:./DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./route-choice-answer.md:703:./DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./route-choice-answer.md:704:./DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./route-choice-answer.md:705:./DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:707:./DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:708:./DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./route-choice-answer.md:712:./DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./route-choice-answer.md:714:./DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:717:./DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./route-choice-answer.md:821:./DLNFibre/Core/OrbitDifferentialRank.lean:659:/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
./route-choice-answer.md:822:./DLNFibre/Core/OrbitDifferentialRank.lean:660:Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
./route-choice-answer.md:823:./DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./route-choice-answer.md:824:./DLNFibre/Core/OrbitDifferentialRank.lean:666:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:825:./DLNFibre/Core/OrbitDifferentialRank.lean:668:  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
./route-choice-answer.md:846:./DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./route-choice-answer.md:847:./DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./route-choice-answer.md:852:./DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./route-choice-answer.md:854:./DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}

exec
/bin/bash -lc "find /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim -maxdepth 3 \\( -name CLAUDE.md -o -name README.md -o -name AGENTS.md \\) -print" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/theory/README.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/CLAUDE.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/AGENTS.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/docs/policies/README.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/.agent-team/README.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/CLAUDE.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/README.md

exec
/bin/bash -lc 'find /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim -maxdepth 3 -type d -name DLNFibre -print -o -name lakefile.lean -print' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited analytic bound.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md).

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;
- the payoff: the real log-canonical threshold of the square-Frobenius loss is $C/2$ — DLNs are "mildly
  singular". The geometric codimension is the new content; the `rlct ≤ ½·codim` direction is **Cited**
  (Aoyagi / Watanabe).

The reusable **engine** (everything before "the payoff") is network-free and lives in `DLNFibre.Core`; the
DLN/RLCT **application** lives in `DLNFibre.DLN`. See [`ROADMAP.md`](ROADMAP.md) for the formalisation ladder.

## Pointers

- [`README.md`](README.md) — orientation, how to launch an expedition, Lean build.
- [`ROADMAP.md`](ROADMAP.md) — the result-map + the Core/DLN formalisation-target ladder.
- [`docs/policies/`](docs/policies/) — expedition, claims, review, precision, bedrock, codex-consultation, statement-cards, writing-style (+ the reader-facing exposition trio).
- [`docs/expositions/`](docs/expositions/) — the curated reader-facing digest (starts with `paper-digest/high-level-overview.md`).
- [`.claude/skills/`](.claude/skills/) — lean-formalisation, local-codex-consult.
- [`lean/CLAUDE.md`](lean/CLAUDE.md) — Lean build + Mathlib conventions; the Core/DLN split.
- [`theory/`](theory/) — markdown theory workspace.
- [`TEMPLATE.md`](TEMPLATE.md) — how to instantiate this harness for a new paper.

exec
/bin/bash -lc "find /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean -maxdepth 2 -type f -name '*.lean' | sort | sed -n '1,200p'" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
2026-06-24T18:03:51.586006Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019efacd-3505-7fb3-8af2-49e577913154`" }
 exited 1:
2026-06-24T18:03:51.587295Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc "find /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean -maxdepth 2 -type f -name '*.lean' | sort | sed -n '1,200p'"`: CreateProcess { message: "Rejected(\"rejected by user\")" }
exec
/bin/bash -lc 'tail -n 220 rung2-lighter-path-answer.md' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
./route-choice-answer.md:485:./DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
./route-choice-answer.md:506:./DLNFibre/Core/DeterminantalStratumDim.lean:29:4. **The catenary bridge** (LANDED `codimRep_add_varietyDim_eq_card`): `codim + dim = card = m·n`,
./route-choice-answer.md:520:./DLNFibre/Core/DeterminantalStratumDim.lean:224:> `varietyDim (Mat^{rk ≤ r}_{m × n}) = r · (n + m − r)`.
./route-choice-answer.md:521:./DLNFibre/Core/DeterminantalStratumDim.lean:229:theorem varietyDim_productRankLocusLE_stratum [IsAlgClosed k] [CharZero k] (n m r : ℕ)
./route-choice-answer.md:522:./DLNFibre/Core/DeterminantalStratumDim.lean:231:    varietyDim (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)
./route-choice-answer.md:524:./DLNFibre/Core/DeterminantalStratumDim.lean:237:  have hbridge := codimRep_add_varietyDim_eq_card (canonicalCoord (dStratum n m)) Z
./route-choice-answer.md:527:./DLNFibre/Core/DeterminantalStratumDim.lean:249:  -- `hbridge : (n−r)(m−r) + varietyDim Z = m·n`
./route-choice-answer.md:528:./DLNFibre/Core/DeterminantalStratumDim.lean:258:  have heq : (((n - r) * (m - r) : ℕ) : ℕ∞) + varietyDim (canonicalCoord (dStratum n m) '' Z)
./route-choice-answer.md:529:./DLNFibre/Core/DeterminantalStratumDim.lean:268:    varietyDim (canonicalCoord (dStratum 2 2) '' productRankLocusLE (k := k) (dStratum 2 2) 1)
./route-choice-answer.md:530:./DLNFibre/Core/DeterminantalStratumDim.lean:270:  have h := varietyDim_productRankLocusLE_stratum (k := k) 2 2 1 (by norm_num) (by norm_num)
./route-choice-answer.md:577:./DLNFibre/Core/FibreDimFibration.lean:45:`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
./route-choice-answer.md:578:./DLNFibre/Core/FibreDimFibration.lean:51:The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
./route-choice-answer.md:585:./DLNFibre/Core/FibreDimFibration.lean:64:  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
./route-choice-answer.md:586:./DLNFibre/Core/FibreDimFibration.lean:65:  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
./route-choice-answer.md:588:./DLNFibre/Core/FibreDimFibration.lean:67:    varietyDim_productRankLocusLE_stratum n m r hn hm
./route-choice-answer.md:589:./DLNFibre/Core/FibreDimFibration.lean:68:  rw [varietyDim, ← hI] at hvd
./route-choice-answer.md:605:./DLNFibre/Core/EndBaseChangeSweep.lean:16:consequence** `varietyDim (productRankLocus d r) = δ + varietyDim (fibre d E)` is the *one genuinely
./route-choice-answer.md:649:./DLNFibre/Core/NullstellensatzCodim.lean:31:   irreducible"), `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ` (`ℕ∞`, additive — `ℕ∞`
./route-choice-answer.md:650:./DLNFibre/Core/NullstellensatzCodim.lean:37:`axiom`. `varietyDim Z = ringKrullDim (R ⧸ vanishingIdeal Z)` is the Krull dimension of the
./route-choice-answer.md:674:./DLNFibre/Core/NullstellensatzCodim.lean:139:noncomputable def varietyDim (Z : Set (σ → k)) : ℕ∞ :=
./route-choice-answer.md:677:./DLNFibre/Core/NullstellensatzCodim.lean:144:the ambient dimension `Nat.card σ`: `height (vanishingIdeal Z) + varietyDim Z = Nat.card σ`. The
./route-choice-answer.md:679:./DLNFibre/Core/NullstellensatzCodim.lean:147:theorem height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:681:./DLNFibre/Core/NullstellensatzCodim.lean:149:    (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:686:./DLNFibre/Core/NullstellensatzCodim.lean:157:  rw [varietyDim, ← hm, WithBot.unbotD_coe]
./route-choice-answer.md:687:./DLNFibre/Core/NullstellensatzCodim.lean:162:`height (vanishingIdeal Z) = Nat.card σ − varietyDim Z` for an irreducible variety `Z` (`ℕ∞`
./route-choice-answer.md:688:./DLNFibre/Core/NullstellensatzCodim.lean:163:subtraction; lossless here since `varietyDim Z ≤ Nat.card σ`). The geometric codimension is the
./route-choice-answer.md:689:./DLNFibre/Core/NullstellensatzCodim.lean:165:theorem height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z : Set (σ → k)}
./route-choice-answer.md:691:./DLNFibre/Core/NullstellensatzCodim.lean:167:    (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z := by
./route-choice-answer.md:692:./DLNFibre/Core/NullstellensatzCodim.lean:168:  have hadd := height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:693:./DLNFibre/Core/NullstellensatzCodim.lean:169:  have hne : varietyDim Z ≠ ⊤ := by
./route-choice-answer.md:694:./DLNFibre/Core/NullstellensatzCodim.lean:182:`height_vanishingIdeal_add_varietyDim_eq_card` at `σ := RepCoord d`, `Z := coord '' Z`. -/
./route-choice-answer.md:695:./DLNFibre/Core/NullstellensatzCodim.lean:183:theorem codimRep_add_varietyDim_eq_card [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:697:./DLNFibre/Core/NullstellensatzCodim.lean:186:    codimRep coord Z + varietyDim (coord '' Z) = (Nat.card (RepCoord d) : ℕ∞) :=
./route-choice-answer.md:698:./DLNFibre/Core/NullstellensatzCodim.lean:187:  height_vanishingIdeal_add_varietyDim_eq_card hp
./route-choice-answer.md:699:./DLNFibre/Core/NullstellensatzCodim.lean:190:varietyDim (coord '' Z)` for an irreducible variety `coord '' Z`: geometric codimension `=` ambient
./route-choice-answer.md:700:./DLNFibre/Core/NullstellensatzCodim.lean:192:theorem codimRep_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:702:./DLNFibre/Core/NullstellensatzCodim.lean:195:    codimRep coord Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (coord '' Z) :=
./route-choice-answer.md:703:./DLNFibre/Core/NullstellensatzCodim.lean:196:  height_vanishingIdeal_eq_card_sub_varietyDim hp
./route-choice-answer.md:704:./DLNFibre/Core/NullstellensatzCodim.lean:199:`canonicalCoord d`, `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim (canonicalCoord d ''
./route-choice-answer.md:705:./DLNFibre/Core/NullstellensatzCodim.lean:201:theorem codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d : Fin (N + 1) → ℕ}
./route-choice-answer.md:707:./DLNFibre/Core/NullstellensatzCodim.lean:205:    codimRepCanonical Z = (Nat.card (RepCoord d) : ℕ∞) - varietyDim (canonicalCoord d '' Z) :=
./route-choice-answer.md:708:./DLNFibre/Core/NullstellensatzCodim.lean:206:  codimRep_eq_card_sub_varietyDim (canonicalCoord d) Z hp
./route-choice-answer.md:712:./DLNFibre/Core/NullstellensatzCodim.lean:225:alg-closed, `σ` finite), the vanishing ideal is `⊥` (prime), `varietyDim = Nat.card σ`, the bridge
./route-choice-answer.md:714:./DLNFibre/Core/NullstellensatzCodim.lean:230:      + varietyDim (Set.univ : Set (σ → k)) = (Nat.card σ : ℕ∞) := by
./route-choice-answer.md:717:./DLNFibre/Core/NullstellensatzCodim.lean:233:  exact height_vanishingIdeal_add_varietyDim_eq_card this
./route-choice-answer.md:820:./DLNFibre/Core/OrbitDifferentialRank.lean:35:Krull-dimension bound) and `varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional`
./route-choice-answer.md:821:./DLNFibre/Core/OrbitDifferentialRank.lean:659:/-- **The AG-half submersion bound `varietyDim Z_M ≤ finrank (range δ⁰)`, UNCONDITIONAL (char 0).**
./route-choice-answer.md:822:./DLNFibre/Core/OrbitDifferentialRank.lean:660:Chaining the unconditional A4.4 with the landed A0 link `varietyDim_eq_ringKrullDim_range_orbitPullback`
./route-choice-answer.md:823:./DLNFibre/Core/OrbitDifferentialRank.lean:664:theorem varietyDim_orbitRankLocus_le_finrank_range_deformationδ_unconditional
./route-choice-answer.md:824:./DLNFibre/Core/OrbitDifferentialRank.lean:666:    varietyDim (canonicalCoord d '' orbitRankLocus M)
./route-choice-answer.md:825:./DLNFibre/Core/OrbitDifferentialRank.lean:668:  varietyDim_orbitRankLocus_le_finrank_range_deformationδ M
./route-choice-answer.md:846:./DLNFibre/Core/RadicalCatenary.lean:27:The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
./route-choice-answer.md:847:./DLNFibre/Core/RadicalCatenary.lean:157:/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/
./route-choice-answer.md:852:./DLNFibre/Core/RadicalCatenary.lean:173:/-- **The reducible-locus catenary at `codimRepCanonical`/`varietyDim` (additive, `ℕ∞`).** For a
./route-choice-answer.md:853:./DLNFibre/Core/RadicalCatenary.lean:176:equal the ambient dimension: `codimRepCanonical Z + varietyDim (canonicalCoord d '' Z) = card`. No
./route-choice-answer.md:854:./DLNFibre/Core/RadicalCatenary.lean:179:theorem codimRepCanonical_add_varietyDim_eq_card_of_nonempty {d : Fin (N + 1) → ℕ}

exec
/bin/bash -lc "find /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim -maxdepth 3 \\( -name CLAUDE.md -o -name README.md -o -name AGENTS.md \\) -print" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/theory/README.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/CLAUDE.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/AGENTS.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/docs/policies/README.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/.agent-team/README.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/CLAUDE.md
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/README.md

exec
/bin/bash -lc 'find /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim -maxdepth 3 -type d -name DLNFibre -print -o -name lakefile.lean -print' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
# geometry-of-dln-fibre

AI-assisted math-research + Lean-formalisation harness for **digesting and formalising** the paper
*"Geometry of the fibers of the multiplication map of deep linear neural networks"* (Simon Pepin
Lehalleur & Richárd Rimányi, 2024; `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/`).
Orientation is in [`README.md`](README.md); this file is the disposition and the working discipline.
The process harness (disposition + policies + roles + skills + the markdown→Lean pipeline) is ported
from the `ai-research-assistant` harness and is **domain-agnostic** — see [`TEMPLATE.md`](TEMPLATE.md)
to instantiate it for another paper.

## Disposition

The work here is research. Not coding, not ticking off a support ticket, not shipping a product. 
The stance: 
- careful, conscientious, objective as a scientist.
- meticulous in calculation as Euler, bold as Grothendieck. 
- methodical as Sherlock Holmes. Observe before theorising. Distinguish data from interpretation. 
- update like a Bayesian; do not collapse to the mode. 


- **Resist the move-fast-and-ship-it instinct.** Stackable, solid progress is the goal; the trap is
  *visible* progress raced ahead of it — a clean doc or confident headline that travels far while leaving
  holes behind. When you reach for a confident headline, that is the moment to look for the confound. Each
  layer should be solid and hole-free before the next stands on it.
- **Fill the layer — completion is your strength.** *The sea rises inexorably, but not in spikes*
  ([`docs/policies/bedrock.md`](docs/policies/bedrock.md)): within a boundary already staked, close the holes
  — the generality a statement promised, the cases it already claims, fidelity to the definition and the
  underlying spirit it invokes — rather than defer them. Such hardening is high-value, and it is where your
  **comparative advantage** lies: your bottleneck is scoping, taste, and direction, not the patient completion
  of well-scoped work — so do not treat that completion capacity, which is *abundant*, as if it were *scarce*.
  **Just do it!** Don't file it as a "chore" (an *unprobed* difficulty claim, not a defer). Surface to move the
  *boundary* — but an **earned** taste-judgment that a gap is the *right* extension is itself direction:
  **Just Do It** if within reach, else **roadmap** it; only a *bare, unargued* extension waits for the operator.
- **Name results for what they are.** A result's name and statement denote exactly what is proven — no more;
  reaching for an impressive name (or "done") is the visible-progress instinct in disguise. Separate Proved /
  Assumed / Cited / Deferred. See [`docs/policies/precision.md`](docs/policies/precision.md). (Here the
  recurring trap: a `rlct_…`-named result that in fact proves only a *codimension* — the `rlct = ½·codim`
  reading needs the cited analytic bound.)
- **Build to bedrock.** A sorry-free build defeats *technical* slop; it never defeats *conceptual* slop —
  "technically correct but subtly wrong, not The Way." **Bedrock is the rock the rising sea rises over**: build
  the theory so the next result can stand on it without re-opening it. Where short feedback loops fail, **beauty
  is the instrument** — a vacuous, mis-scoped, or overclaiming result is *ugly*, and the ugliness is
  information. The **controller holds this taste and judges against it**; a green build is necessary, never
  sufficient. See [`docs/policies/bedrock.md`](docs/policies/bedrock.md).
- **Caveats live next to claims, not in footnotes.** An assumed hypothesis or a cited interface goes in the
  same paragraph as any claim that depends on it.
- **Write to figure out the truth, not to persuade.** Concise and fact-based.
- **Elementary, precisely.** Build explanations up from precise but simple well-chunked objects, established locally in the
  document. "Elementary" does not mean imprecise or dumbed-down or toy analogies: every step stays
  mathematically precise. Introduce the objects you use before you use them; prefer a chain of small exact
  statements over one dense one. Resist over-naming things to do chunking. Reach for an analogy only when it is exact and load-bearing. See
  [`docs/policies/writing-style.md`](docs/policies/writing-style.md).

## Writing and communication discipline (object-level focus)
In writing or in communication, focus on object-level. Resist meta-level pull. 
Remove authorial self-reassurance: `honestly`, `fundamentally`, `this is the whole point`, `this is loadbearing`, `of course`, `simply`, `just`, and selling phrasing.
The full list and the review function that enforces it are in [`docs/policies/review.md`](docs/policies/review.md).

## How research runs here

- **Expeditions** ([`docs/policies/expedition.md`](docs/policies/expedition.md)) are the unit: a central
  question, a controller delegating to thread teammates (explore / formalisation / infra), reviewers, and a
  synthesis at close. Run on the Agent Teams substrate (`CLAUDE_CODE_EXPERIMENTAL_AGENT_TEAMS=1`); launch with
  cwd = this repo root.
- **Pipeline: markdown → Lean.** Theory develops in markdown (`theory/`, expedition notes). A stable claim is
  formalised in Lean (`lean/`, library `DLNFibre`). The reader-facing digest/expositions live in
  `docs/expositions/`.
  - *Scholium* is a **viewer** (renders these markdown docs with KaTeX + callouts), not an editor; write to its
    conventions in [`docs/policies/scholium-writing-format.md`](docs/policies/scholium-writing-format.md). The
    recurring trap: display math `$$…$$` needs a **blank line before and after**, fences on their own lines
    (indented inside `!!!`/`???` callouts) — packed against text it falls through to markdown and the `_`
    subscripts render as emphasis. A second trap: **fenced code does not render inside a callout** — use an
    indented code block (8-space indent) there; top-level fenced code is fine.
- **Claims** carry kill-conditions; new claims are stress-tested, established/cited results verified against
  source ([`docs/policies/claims.md`](docs/policies/claims.md)).
- **Codex** is the independent second model for strategy and review
  ([`docs/policies/codex-consultation.md`](docs/policies/codex-consultation.md)).

## Team structure

Roles are documented under [`.agent-team/roles/`](.agent-team/roles/):
- `controller` — this lead session: meta-planning, delegation, integration.
- `scout` — explore / reconnaissance threads: map the terrain (Mathlib, the paper, possibility spaces), compute / derive / claims.
- `pen-and-paper` — a specialised `scout`: design-space math adjudicating a truth-value (`witness` / `obstruction` seats), exact algebra, decorrelated Codex; hands a certificate to the formaliser. No Lean.
- `formaliser` — formalisation (tide) threads.
- `reviewer` — controller-spawned independent audit (soundness / fidelity).
- `hardener` — independent principles / taste reviewer (precision, bedrock).

If dispatched into a role, read its role file and agent definition first.

## Branch discipline

- **One remote: `origin = git@github.com:edmund-ukaisi/geometry-of-dln-fibre.git`.** All work lives here.
- **`dev` is the integration branch.** Feature and expedition branches branch off `dev` and PR back into
  `dev`. `master` is the **release** branch — promoted from `dev` deliberately by the operator, never pushed
  to directly.
- Use a **feature branch** for any non-trivial unit of work; you can push here; don't commit to `dev` or `master` directly. One
  expedition runs on one branch (`expedition/<slug>`); PR at close behind signal-and-wait.
- **Pushing feature/expedition branches to `origin` is pre-authorized** (operator standing instruction,
  2026-06-12) — push freely to bank and share work. **Opening/merging PRs and the `dev → master` promotion
  remain operator-gated** (signal-and-wait); the operator performs those. Always confirm the push target is
  `origin`, never a non-`origin` remote.

## Memory

Persistent context lives **in-repo**: this file, the policies in `docs/policies/`, the expedition docs
(`synthesis.md` / statement cards / `thread.md`), `ROADMAP.md`, and `lean/CLAUDE.md`. Save conventions and
decisions there.

**Do NOT write to global Claude memory (`~/.claude/**/memory/`).** It pollutes other workspaces and is
invisible to collaborators reading the repo. This binds the controller **and every teammate** — the harness
may prompt you to save a memory there; do not. If a teammate writes one, the controller deletes it and
re-homes the content in-repo. (Agent-Teams *runtime* state under `~/.claude/teams/` and `~/.claude/tasks/` is
fine — that's the substrate, not persistent context.)

## The destination, plainly

We want, in honest Lean, the paper's results about the **fibres of matrix multiplication** for deep linear
networks:

- the space $\operatorname{Rep}_{\underline d}$ of composable matrix tuples, the multiplication map
  $\operatorname{mult}$, the zero-product / rank-$r$ loci, and the fibres $\operatorname{mult}^{-1}(B)$;
- via the **type-A quiver** translation (orbits ↔ Kostant partitions ↔ rank patterns, Gabriel, orbit-closure
  order, the `Ext` codimension): the codimension $C$ and the number $\theta$ of top-dimensional components,
  in the paper's three forms (Poincaré series, a quadratic integer program, an explicit formula), and the
  surprising **permutation invariance** of $(C,\theta)$;
- the payoff: the real log-canonical threshold of the square-Frobenius loss is $C/2$ — DLNs are "mildly
  singular". The geometric codimension is the new content; the `rlct ≤ ½·codim` direction is **Cited**
  (Aoyagi / Watanabe).

The reusable **engine** (everything before "the payoff") is network-free and lives in `DLNFibre.Core`; the
DLN/RLCT **application** lives in `DLNFibre.DLN`. See [`ROADMAP.md`](ROADMAP.md) for the formalisation ladder.

## Pointers

- [`README.md`](README.md) — orientation, how to launch an expedition, Lean build.
- [`ROADMAP.md`](ROADMAP.md) — the result-map + the Core/DLN formalisation-target ladder.
- [`docs/policies/`](docs/policies/) — expedition, claims, review, precision, bedrock, codex-consultation, statement-cards, writing-style (+ the reader-facing exposition trio).
- [`docs/expositions/`](docs/expositions/) — the curated reader-facing digest (starts with `paper-digest/high-level-overview.md`).
- [`.claude/skills/`](.claude/skills/) — lean-formalisation, local-codex-consult.
- [`lean/CLAUDE.md`](lean/CLAUDE.md) — Lean build + Mathlib conventions; the Core/DLN split.
- [`theory/`](theory/) — markdown theory workspace.
- [`TEMPLATE.md`](TEMPLATE.md) — how to instantiate this harness for a new paper.


codex
The prior answer file is a raw transcript, not a clean source of truth. I’m switching to the Lean declarations themselves: the key check is whether dimension-only can use existing quotient/radical lemmas without recreating the quotient-localized product map.
exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/CLAUDE.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
# Lean conventions (DLNFibre)

## Build
- **Multi-worktree / multi-session: build via `scripts/lb`, NOT bare `lake build`.** `lb` symlinks this
  worktree's `.lake/packages` to the shared rev-keyed mathlib store (mmap-shared, no per-worktree clone)
  and throttles total Lean workers across all sessions via a global semaphore. Full rationale + box
  sizing: [`../docs/policies/lean-build-workflow.md`](../docs/policies/lean-build-workflow.md). **Do NOT
  `lake exe cache get` in a worktree** — it re-clones ~7 GB and defeats the sharing; the shared store is
  built once by `scripts/lake-store-setup <mathlib-rev>` (detached; exceeds the 10-min cap).
- Fresh shells: `source ~/.elan/env` before any `lake` command.
- Build from this `lean/` directory: `scripts/lb DLNFibre.<Module>`, or `scripts/lb` for the whole
  library. (Bare `lake build`/`lake env lean` still work for one-off elaboration, but bypass the shared
  store + the global concurrency cap — fine for a single `#eval`, not for parallel builds.)
- Toolchain: Lean `v4.29.0` (`lean-toolchain`), Mathlib `v4.29.0` (`lakefile.toml`). Matches the `ai-research-assistant` harness one level up, so its v4.29 Mathlib idioms transfer.

## Library shape — engine vs application
- **`DLNFibre.Core.*`** is the network-free **engine** (quiver orbits, Kostant partitions / rank patterns, `Ext` codimension, `(C, θ)`). It **must never import `DLNFibre.DLN`**. The dependency arrows point `DLN → Core → Mathlib`.
- **`DLNFibre.DLN.*`** is the **application** (multiplication-map fibres, the square-Frobenius loss, the RLCT payoff); it depends on `Core`.
- State each result at the specificity its claim needs; lift a piece into shared `Core` API on its **second** use, not in anticipation of one. Good API (characterizations over predicates, weakest hypotheses, name = content) is the `bedrock`/`precision` discipline, not a folder layout.

## Aggregator
- `DLNFibre.lean` is single-writer. Add new module imports at the end; do not reorder existing imports.
- New modules live at `DLNFibre/<Core|DLN>/<Topic>/<File>.lean`; one substantive theorem family per file.

## Sorry gate
- Zero `sorry` / `axiom` / `native_decide` / `#exit` in committed files. Audit with `scripts/sorries` from `lean/` before every commit.
- A `sorry` with a correct statement is a building block; a `sorry` with a wrong statement misleads. Fix wrong statements first.

## Bedrock (the bar above the sorry gate)
A green, sorry-free build is the **floor**: it defeats *technical* slop, never *conceptual* slop —
"technically correct but subtly wrong, not The Way." Build each result as **bedrock**: something the next
theorem stands on without re-opening it. Where there's nothing to check against, **beauty is the guide** — a
vacuous, mis-scoped, or overclaiming theorem is *ugly*. In practice that recurrently means (not exhaustively):
name = content; non-vacuous, with the witness *shown* in-file; the weakest hypotheses that suffice, in usable
form; characterized (an `iff`) over asserted; every *cited*/*assumed* step named (never an `…rlct…`-style
theorem that secretly claims an unproved analytic interface — here the `rlct = ½·codim` reading rests on a
cited bound). The controller judges against this taste and holds precedence — full statement:
[`../docs/policies/bedrock.md`](../docs/policies/bedrock.md).

## Style
- `↦` not `=>` for lambda arrows.
- `decide +kernel`, not `native_decide`. Avoid `@[implemented_by]`, `@[extern]`, `unsafePerformIO`.
- One-line docstrings.
- Name a lemma for what it proves: a kernel/ideal *membership* fact is `…_mem_ker`, not `…_gen` (which reads as an ideal-generation claim).
- Confirm a Mathlib lemma exists before building a proof around it: `scripts/lean-search "..."`, or `rg` over `.lake/packages/mathlib/Mathlib/`.
- Pre-stage uncertain API with `example` blocks that pin lemma names/types; keep them as durable contracts.

## Mathlib gotchas (v4.29 pin)
Toolchain-generic notes that transfer at this pin. Accumulate new, DLN-specific ones here as they are found
(the ReLU programme's proof-specific notes were intentionally not ported — they were about a different theory).

- **`Basis` is `Module.Basis` at the v4.29 pin.** Bare `Basis` is unknown even with full Mathlib imports;
  ascribe `Module.Basis (Fin _) ℝ _` (e.g. from `Pi.basisFun`). Dot-notation (`b.tensorProduct b'`) is
  unaffected. Likely to recur in any `Matrix.rank` / column-span work.
- **`decide +kernel`, never `native_decide`.** Kernel `decide` is axiom-clean; `native_decide` trusts the
  compiler and breaks `#print axioms` hygiene. Kernel-reduction cost is **heartbeat-invisible** (a
  `maxHeartbeats` bump does not speed it), so a heartbeat timeout on a `decide` is not the symptom to chase.
- **Matrix-product identities over `ℤ` by `decide`, then cast.** An `ℝ` matrix-product identity is a
  `Matrix.ext` blow-up (per-entry `simp`, times out at scale). Write the matrices over `ℤ`
  (`DecidableEq` ⟹ `Matrix.mul` decides by kernel reduction, `by decide`), define the `ℝ` ones via
  `· .map (Int.castRingHom ℝ)`, and transfer products with `← Matrix.map_mul` (cast is a ring hom). No `ℝ`
  `Matrix.ext` at all.
- **`Fin`-vector `![…]` + `fin_cases` friction.** `fin_cases i` leaves the index as `⟨k, ⋯⟩` (a `Fin.mk`),
  so `Matrix.cons_val_one`/`_two`/… do not fire on the outer selection. Normalize first with
  `rw [show (⟨k, by omega⟩ : Fin n) = (k : Fin n) from rfl]`, then the `cons_val_*` simp set fires; or prove
  the components as separate `have`s and assemble with `funext i; fin_cases i`.
- **`φ` (U+03C6) as a binder name can hit a lexer reject** (`unexpected token 'φ'; expected identifier`)
  when an editing tool inserts a confusable/variant codepoint. If a `∃ φ …` / `obtain ⟨φ, …⟩` line fails
  to parse despite looking right, rename the binder to ASCII (`phi`) or `ψ`; capital `Φ` (U+03A6) has not
  shown the problem. Cost two build cycles on `NoetherMonicPositioning.lean`.
- **No off-the-shelf rank-normal-form / "equal rank ⟹ equivalent matrices" in v4.29.** Built at the
  linear-map level in `Core.FibreNormalForm` (`exists_conj`, `exists_baseChange_of_rank_eq`): for a
  rank-`r` `f : (Fin n → k) →ₗ (Fin m → k)`, restrict to `fU : U ≃ range f` (`U` a `ker`-complement,
  via `Submodule.quotientEquivOfIsCompl _.symm ≪≫ LinearMap.quotKerEquivRange`); two maps with equal
  ker+range finrank are conjugate (`prodEquivOfIsCompl` kernel/range decompositions glued by
  `LinearEquiv.ofFinrankEq`), transferred to matrices by `LinearMap.toMatrix'_comp` +
  `LinearMap.toMatrix'_toLin'`. Useful `rfl`s: `Matrix.rank A = finrank (range (toLin' A))` and
  `toLin' A = A.mulVecLin`. The `IsCompl` finrank lemma is `Submodule.finrank_add_eq_of_isCompl`.
- **`RingEquiv.height_comap` is the clean `Ideal.height` transport** (`(I.comap e).height = I.height`,
  any ideal, no `IsPrime`). For codim-invariance of a locus under a *linear* coordinate change, the
  set-level route `vanishingIdeal (shifted) = comap (algEquiv) (vanishingIdeal)` + `height_comap` is
  cleaner than re-deriving an `Ideal.map` identity. Used in `Core.FibreNormalForm.codimRep_baseChange_image`
  — this closes the linear-coordinate-invariance gap `Core.OrbitCodim`'s docstring flagged, for the
  base-change family of isos.
- **The end-factor (`GL_{d_N}×GL_{d_0}`) action is just `Core.BaseChange.baseChange` with inner units
  `= 1`.** No new action needed: mult-equivariance `mult (P•A) = P_N·(mult A)·(P_0)⁻¹` is
  `mult_eq_submult` + the LANDED `submult_smul` at the full interval `(0, last)`. Caveat: the
  same-rank ⟹ same-fibre-codim headline genuinely needs `N ≥ 1` (`hN : (0 : Fin (N+1)) ≠ Fin.last N`)
  — for `N = 0` `mult` is the constant `1`, the end vertices coincide, the action only conjugates, and
  the claim is false.

## θ-count discharge findings (`Core.CCodimCornerMono`, thread 06)
- **The θ-count headline reduces to ONE combinatorial inequality**: the dimension-monotonicity of
  `cCodim · 0` (`cCodim e 0 ≤ cCodim e' 0` for `e ≤ e'`, + a strict all-vertex version). Both gating
  bricks (`hLowerBound`, `hRecover`) discharge from it via the LANDED rank-shift `cCodim d t = cCodim
  (d−t) 0` + the Gabriel→Kostant bridge `gabrielPartition` (a tuple's `kostantArrayOfRank (rankFn ·)`
  recast into the `CTheta` `Fin × Fin → ℕ` encoding via `finArrayOfSupp`).
- **The right construction for the dimension-monotonicity is the SHORTEST-interval split** (at an
  over-covered vertex `k`, split the shortest `[i,j] ∋ k` into `[i,k−1]+[k+1,j]`): verified to never
  increase `codimForm` (199/199), whereas splitting a non-shortest interval CAN increase it. The
  merge-up route (raise the corner per-partition) is DEAD — corner-`s` partitions often admit no
  corner-raise with non-increasing `codimForm` (71/252).
- **Strict SINGLE-vertex dimension-mono is FALSE** (e.g. `cCodim [1,1,0] 0 = cCodim [1,2,0] 0 = 0`);
  only the strict ALL-vertex version holds (`d−r < d−s` everywhere when `r > s`). Strict corner-
  monotonicity (needed for `hRecover`'s "corner = r") rides on the all-vertex strict version.
- **`codimForm` is the type-A `Ext`-pairing form**: reindexed, `= ∑_{A=[a,b],B=[c,e]: a<c≤b+1, b<e}
  m̄(A) m̄(B)`. The split delta is `∑_B coeff(B) m̄(B)` with the positive-coeff `B` being the shorter
  intervals covering `k` (absent when `I` is shortest). `codimForm` is also corner-blind
  (`codimForm_update_corner`, LANDED) — it never reads `m_{0N}`.

## `cCodim·0` weak monotonicity LANDED (`Core.CCodimZeroMono`, thread 07)
- **`cCodim_zero_mono` is PROVED sorry-free** (`e ≤ e' ⟹ cCodim e 0 ≤ cCodim e' 0`), discharging the
  weak gating hypothesis `hMono`. The θ-count headline is now `numTop_eq_ncard_topComponents_of_strict`
  — UNCONDITIONAL except for the strict `hMonoStrict`. Axiom-clean `[propext, Classical.choice,
  Quot.sound]`. `hLowerBound` is fully unconditional.
- **Reusable infrastructure** (all in `CCodimZeroMono`, built on `CThetaQIPConverse`'s `codimBil`):
  `codimBil_extendℤ_boxℤ_right`/`_left` (univ-sum collapse of `codimBil` vs a single box, via the
  clamped `rrInd`/`llInd` indicators), `codimBil_boxℤ_boxℤ` (the box-pairing value), `codimForm_add`
  (reused), `codimForm_congr_onbox` (codimForm reads only on-box values).
- **Four atomic shortest-split moves**, each with delta / sign / `_le` / `_cover` / `_mem`: interior
  `redMove` (`c = b+2` gap kills the self-term), `leftShrink` (omit left endpoint; handles `a=0` and
  singleton-via-empty-piece), `rightShrink` (omit right endpoint; handles `d'=N`), `removeMove`
  (singleton removal; coefficient ALWAYS `≤ 0`). Boundary lesson: there is NO `Fin` `b` with `b+1 = 0`,
  so `k=0` left-endpoint and `k=N` right-endpoint genuinely need the dedicated shrink moves (the
  interior `redMove`'s empty-piece guard `a≤b` can't be made false when `a=0`). `reduceStep` dispatches
  by `k`'s position; `exists_le_codimForm` is the recursion (strong induction on `∑ e'`).
## `cCodim·0` strict monotonicity LANDED → θ UNCONDITIONAL (`Core.CCodimZeroStrict`, thread 08)
- **`cCodim_zero_strict` is PROVED sorry-free** (`(∀ v, e v < e' v) → cCodim e 0 < cCodim e' 0`),
  discharging `hMonoStrict`. **`numTop_eq_ncard_topComponents` is now UNCONDITIONAL** (`θ =
  #top-dimensional irreducible components of Σ̄^r`, no open hypothesis); axiom-clean `[propext,
  Classical.choice, Quot.sound]`.
- **Route B (the landed route), reusing the four atomic moves + their `_le` sign lemmas:**
  - **Double sum** `codimForm_extendℤ_eq_sum_pairs`: `codimForm (extendℤ m) = ∑_{A,B} m(A) m(B) ·
    [pairBox A B]` (built from `codimBil_sum_right` + `codimBil_const_mul_right` + the existing
    right-rectangle collapse; `rrInd (B.1)(B.2) A ↔ pairBox A B` on the box). Gives `∃ active pair ⟺
    codimForm ≥ 1` (`codimForm_extendℤ_pos_of_exists_pair` / `exists_pair_of_codimForm_pos`).
  - **Lemma Y** `codimForm_extendℤ_pos_of_fullCover`: full coverage ⟹ `codimForm ≥ 1`, via the
    extremal longest-`[0,b]` argument (`b<N` from corner-`0`; maximality forces `c≥1` so `[0,b]→[c,d]`
    pairs).
  - **Lemma X** `reduceStep_strict`: select the active pair minimising `min(ilen A, ilen B)`; split the
    shorter member at the partner-adjacent vertex. **ClaimA** (`claimA_left`/`claimA_right`) — that
    member is shortest *active* covering that vertex — is the one non-mechanical step (the `y<d` vs
    `d≤y` / `a<x` vs `x≤a` interval-arithmetic case split; minimality MUST be over the shorter member,
    Codex-confirmed). The partner sits at split-coefficient EXACTLY `−1` (`splitCoeff_partner_le` &c.,
    `omega` on indicators), and `sum_coeff_le_neg_one` upgrades the `_le` ("≤0") to `_lt` ("≤ −1").
    8-way dispatch (left/right member × interior/leftShrink/rightShrink/removeMove); each move has TWO
    partner orientations (the partner can sit left or right of the split source).
  - **Wiring** (`cCodim_zero_strict`): a minimiser `m'` of `cCodim e' 0` is full-coverage (Lemma Y ⟹
    `codimForm ≥ 1`); `reduceStep_strict` drops it `≥ 1` to a partition of `e'` decremented at `k`,
    which still dominates `e` (`e ≤ e''` since `e < e'` everywhere), so LANDED `exists_le_codimForm`
    gives `cCodim e 0 ≤ cCodim e' 0 − 1`. (No `+1`-step vector needed — the minimiser-of-`e'` route is
    cleaner and uses only the two given nonemptiness hypotheses.)
  - RULED OUT (don't re-explore): Route A (simple `Φ` with `codimForm ≥ Φ ≥ cCodim+1`) — the gap is
    often exactly 1, no simple `Φ` carries it; every deterministic LOCAL step-selection rule fails —
    the strict step's location is config-dependent (the "involved-in-a-pair + extremal-by-length"
    refinement is load-bearing).

exec
/bin/bash -lc 'rg -n "varietyDim_eq_of_coordRingAlgEquiv|ringKrullDim_quotient_radical|gaugeEquiv|noncomputable def SchurLoc|abbrev SchurLoc|noncomputable abbrev Sred|schurToSred|fibreGenIdeal|FibreAlg|basePresentationEquiv|AlgEquiv|e : S|hSweep|krullDim" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre' in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
exec
/bin/bash -lc "rg --files -g '*.lean' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesOrth.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroStrict.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BaseChange.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndBaseChangeSweep.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaDropM.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaGeometricPerm.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GenericFreeness.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoffGeneral.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitClosure.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VoigtDischarge.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Setup.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/RlctPayoff.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferential.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/DLN/Basic.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ThetaComponentCount.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Barcode.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaComponents.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaQIP.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GenericTuple.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaArbitrary.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalStratumDim.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultDifferential.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Gabriel.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaPermInvariance.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesThm55.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesExtraction.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Basic.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneration.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaValue.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MvPolynomialKerAeval.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialCurveLimit.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimZeroMono.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaStratification.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaThetaBridge.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesFivegon.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitLinearCodim.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaExplicit.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Submult.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/JacobianTrdeg.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveDegeneration.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaGeometric.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SigmaCodim.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeries.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CCodimCornerMono.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesPeel.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Orbit.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesDurfee.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitCodim.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/QSeriesShift.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankPattern.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CThetaQIPConverse.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CTheta.lean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean

 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Barcode.lean:465:  have hSne : S.Nonempty := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/Barcode.lean:481:  have hSne : S.Nonempty := ⟨s, hsS⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:120:outer (eliminated) coordinates under `blockAlgEquiv`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:189:only. Pushing further through `sumAlgEquiv` (with `B22block` outermost), `detΔ` becomes the constant
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:205:  rw [detPivotPoly, detSchurS, AlgEquiv.map_det, AlgHom.map_det (rename Sum.inr)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:208:  rw [AlgEquiv.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.map_apply,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:216:(`renameEquiv (repCoordReindex)`) then split off the `B22` block (`sumAlgEquiv`, `B22block`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:218:noncomputable def blockAlgEquiv (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:221:  (renameEquiv k (repCoordReindex q p r hp hq)).trans (sumAlgEquiv k _ _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:223:/-- Under `blockAlgEquiv`, the pivot minor `detΔ` becomes the constant `C detSchurS`: it lives
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:224:purely in the `SchurVar` coefficient ring (`sumAlgEquiv` sends `rename Sum.inr` into the constants).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:227:theorem blockAlgEquiv_detPivot (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:228:    blockAlgEquiv (k := k) q p r hp hq (detPivotPoly (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:230:  rw [blockAlgEquiv, AlgEquiv.trans_apply, renameEquiv_detPivot]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:231:  have h := sumAlgEquiv_comp_rename_inr (R := k) (S₁ := B22block q p r) (S₂ := SchurVar q p r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:235:/-! ### `blockAlgEquiv` on the four block coordinate variables
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:237:Under `blockAlgEquiv`, a `B22` coordinate becomes the outer (eliminated) variable `X (a,b)`; the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:241:/-- `blockAlgEquiv` sends a `B22` coordinate to the outer eliminated variable `X (a, b)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:242:theorem blockAlgEquiv_X_b22 (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:244:    blockAlgEquiv (k := k) q p r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:248:  rw [blockAlgEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, repCoordReindex_b22]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:251:/-- `blockAlgEquiv` sends a `Δ`-pivot coordinate to the inner constant `C (X (Sum.inl (i, j)))`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:252:theorem blockAlgEquiv_X_pivot (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (i j : Fin r) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:253:    blockAlgEquiv (k := k) q p r hp hq (X ⟨0, (Fin.castLE hp i, Fin.castLE hq j)⟩)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:255:  rw [blockAlgEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, repCoordReindex_pivot]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:258:/-- `blockAlgEquiv` sends a `B12` coordinate to `C (X (Sum.inr (Sum.inl (i, b))))`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:259:theorem blockAlgEquiv_X_b12 (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (i : Fin r) (b : Fin (q - r)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:260:    blockAlgEquiv (k := k) q p r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:263:  rw [blockAlgEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, repCoordReindex_b12]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:266:/-- `blockAlgEquiv` sends a `B21` coordinate to `C (X (Sum.inr (Sum.inr (a, i))))`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:267:theorem blockAlgEquiv_X_b21 (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (a : Fin (p - r)) (i : Fin r) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:268:    blockAlgEquiv (k := k) q p r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBaseElimination.lean:271:  rw [blockAlgEquiv, AlgEquiv.trans_apply, renameEquiv_apply, rename_X, repCoordReindex_b21]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:106:    simp only [Ideal.mem_comap, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:115:    simp only [Ideal.mem_comap, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:28:localized Schur `AlgEquiv` (G2-3). It is NOT itself that `AlgEquiv`: the flatness route consumes a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:171:localized Schur `AlgEquiv`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitCodim.lean:54:lemma for `Ideal.height` under a `RingEquiv`/`comap`; proving it needs (i) the `AlgEquiv` of the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:54:  rw [ringKrullDim, Order.krullDim_eq_of_orderIso (primeSpectrumQuotientOrderIsoIci p),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:55:    ← coheight_eq_krullDim_Ici]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:74:  exact krullDim_le_of_strictMono _ strictMono_comap_of_isIntegral
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:114:  rw [ringKrullDim, ringKrullDim, krullDim, iSup_le_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:118:  exact q.length_le_krullDim
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:15:`Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd` (localizing the LANDED `blockAlgEquiv` at `detΔ ↦
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:51:abbrev SchurLoc (q p r : ℕ) : Type u :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:55:LANDED `blockAlgEquiv` at `detΔ` (which maps to `C detSchurS`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:56:noncomputable def blockAlgEquivLoc (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:81:  have H : Submonoid.map (blockAlgEquiv (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:84:    rw [Submonoid.map_powers, blockAlgEquiv_detPivot]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:85:  exact IsLocalization.algEquivOfAlgEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:88:    (blockAlgEquiv q p r hp hq) H
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:90:/-! ## The bordered `(r+1)`-minor `m_b` and its `blockAlgEquiv` image `(*)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:94:`blockAlgEquiv` becomes `C detSchurS · X (a', b') − C (forcedNum a' b')` (the bordered Schur minor
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:171:/-- Each bordered block maps under `blockAlgEquiv` to the `C`-image of its `SchurVar`-side block
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:173:theorem blockAlgEquiv_borderΔ (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:174:    (borderΔ (k := k) q p r hp hq).map (blockAlgEquiv (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:179:  exact blockAlgEquiv_X_pivot q p r hp hq i j
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:181:theorem blockAlgEquiv_borderU (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (b' : Fin (q - r)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:182:    (borderU (k := k) q p r hp hq b').map (blockAlgEquiv (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:187:  exact blockAlgEquiv_X_b12 q p r hp hq i b'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:189:theorem blockAlgEquiv_borderV (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (a' : Fin (p - r)) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:190:    (borderV (k := k) q p r hp hq a').map (blockAlgEquiv (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:195:  exact blockAlgEquiv_X_b21 q p r hp hq a' j
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:197:theorem blockAlgEquiv_borderD (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:199:    (borderD (k := k) q p r hp hq a' b').map (blockAlgEquiv (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:204:  exact blockAlgEquiv_X_b22 q p r hp hq a' b'
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:215:/-- **`(*)` the bordered Schur minor identity, transported.** `blockAlgEquiv (m_b) =
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:216:C detSchurS · X (a', b') − C (forcedNum a' b')`. Via `AlgEquiv.map_det` + `Matrix.fromBlocks_map` +
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:219:theorem blockAlgEquiv_borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:221:    blockAlgEquiv (k := k) q p r hp hq (borderMinor q p r hp hq a' b')
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:223:  rw [borderMinor_eq_fromBlocks, AlgEquiv.map_det, AlgEquiv.mapMatrix_apply,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:224:    Matrix.fromBlocks_map, blockAlgEquiv_borderΔ, blockAlgEquiv_borderU, blockAlgEquiv_borderV,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:225:    blockAlgEquiv_borderD, det_fromBlocks_scalar_eq, Matrix.of_apply,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:234:`Ψ` carries `algebraMap A_eng A_loc x` to `algebraMap B Q (blockAlgEquiv x)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:235:(`algEquivOfAlgEquiv_eq`). Each generator `X (a',b') − C (forcedB22 (a',b'))` of `J`, multiplied by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:240:(blockAlgEquiv x)`. (`Ψ = IsLocalization.algEquivOfAlgEquiv blockAlgEquiv`.) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:241:theorem blockAlgEquivLoc_algebraMap (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:243:    blockAlgEquivLoc (k := k) q p r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:248:          (blockAlgEquiv (k := k) q p r hp hq x) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:267:  exact IsLocalization.algEquivOfAlgEquiv_eq _ x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:287:      = blockAlgEquivLoc (k := k) q p r hp hq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:291:  rw [blockAlgEquivLoc_algebraMap, blockAlgEquiv_borderMinor, map_sub, map_mul]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:306:      ≤ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:311:      ∈ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:333:    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:337:    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) with hK
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:350:  haveI hKprime : K.IsPrime := Ideal.map_isPrime_of_equiv (blockAlgEquivLoc (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:357:    height_map_algEquiv (blockAlgEquivLoc (k := k) q p r hp hq) ((Iad (k := k) q p r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:378:noncomputable def basePresentationEquiv [IsAlgClosed k] [CharZero k] (q p r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:387:      (blockAlgEquivLoc (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:414:  basePresentationEquiv 2 2 1 h h
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:28:`vanishingIdeal`s — so the Schur section cannot be exhibited as an `AlgEquiv` without first building
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:92:the trivializing `AlgEquiv` from the engine's opaque `vanishingIdeal`-quotients, not the closer. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:101:`Rb` — the one-liner the route ends on, once the trivializing `AlgEquiv` exists. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:5:# `DLNFibre.Core.EndpointNormalization` — the gauge-change `AlgEquiv` (R2-3b-3)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:23:2. `gaugeEquiv d P` — the coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R`, assembled by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:24:   `AlgEquiv.ofAlgHom` from `aeval (gaugeSub P)` and `aeval (gaugeSub P⁻¹)`. The round-trips collapse
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:155:/-! ## The composition law and the gauge `AlgEquiv` -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:216:/-- **The gauge `AlgEquiv`** of `MvPolynomial (RepCoord d) R`: `aeval (gaugeSub P)`, with inverse
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:219:noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:221:  AlgEquiv.ofAlgHom (aeval (gaugeSub d P)) (aeval (gaugeSub d P⁻¹))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:233:/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:234:@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:236:    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:238:/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:242:theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:244:    gaugeEquiv d P (multPoly d r c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:248:  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:252:(i) The identity gauge `P = 1` reproduces the identity `AlgEquiv` — the construction is honest at
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:263:/-- At the identity gauge the `AlgEquiv` is the identity (`H = L = 1` reproduces the identity) —
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:266:    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:267:  rw [gaugeEquiv_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:282:/-- The gauge `AlgEquiv` is available at the concrete non-identity `(2,2,2)` gauge `witnessGauge` over
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:286:  gaugeEquiv dConst witnessGauge
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:288:/-- The mult-transport fires at the concrete non-identity gauge `witnessGauge`: `gaugeEquiv` carries
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:292:    gaugeEquiv (R := ℤ) dConst witnessGauge (multPoly dConst r c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean:294:  gaugeEquiv_apply dConst witnessGauge (multPoly dConst r c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:59:noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:75:    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:101:    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:103:    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:135:      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:250:    · -- `coheight ⊥ = krullDim (Spec R) = dim R = d+1`, so the bound holds with `height ≥ 0`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:257:        rw [hpt, ← WithBot.coe_inj, Order.coheight_bot_eq_krullDim]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:17:identity `varietyDim Σ^r = δ + varietyDim F` (`hSweep`) — and the Cited closure/density bridge
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:44:identity `hSweep`, the Cited closure bridge `hClosure`, and the two reducible-locus catenary
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:50:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:70:    rw [← hClosure, hSweep]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:98:homogeneous-sweep dimension identity `hSweep` and the Cited closure bridge `hClosure` as named
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:107:    (hSweep : varietyDim (canonicalCoord d '' productRankLocus (k := k) d r)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RouteCAssembly.lean:114:  codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep d r h B hB hSweep hClosure
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:10:`codimRepCanonical (fibre d B) = Ideal.height (fibreGenIdeal d B)` (H1, radical-insensitive), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:18:* `hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height` — every component has codim `≥ v`;
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:19:* `hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v` — one (top) component has codim `≤ v`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:62:per-component height bounds on `fibreGenIdeal d B` — every minimal prime `height ≥ v`, one `≤ v` — the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:64:height (fibreGenIdeal d B)`) and the min-over-components closer. The route-B tide discharges `hge`/`hle`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:68:    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes, v ≤ J.height)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:69:    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes, J.height ≤ v) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:71:  rw [codimRepCanonical_fibre_eq_height_fibreGenIdeal]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:72:  exact height_eq_of_minimalPrimes_bounds (fibreGenIdeal d B) v hge hle
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:77:target `B` over an algebraically closed field, given that every minimal prime of `fibreGenIdeal d B`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:85:    (hge : ∀ J ∈ (fibreGenIdeal d B).minimalPrimes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:87:    (hle : ∃ J ∈ (fibreGenIdeal d B).minimalPrimes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:108:    (hge : ∀ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, v ≤ J.height)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodimMinPrimes.lean:109:    (hle : ∃ J ∈ (fibreGenIdeal d Bstar).minimalPrimes, J.height ≤ v) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:12:inclusion `sigmaIdeal ≤ ker`, available only as `≤ radical`. The **dimension** identity `hSweep`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:16:through `vanishingIdeal` (radical by construction) and never needs `fibreGenIdeal` to be radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:19:(thread 31 rung 2): `varietyDim` transports across a **coordinate-ring `AlgEquiv`**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:20:(`varietyDim_eq_of_coordRingAlgEquiv`) — even between varieties in *different* ambient affine
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:21:spaces. A regular isomorphism of affine varieties induces such an `AlgEquiv`, so this is the bridge
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:26:- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:28:- `varietyDim_eq_of_coordRingAlgEquiv` — `varietyDim` transport across a coordinate-ring `AlgEquiv`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:40:theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:46:presentation may hand it the generator ideal `fibreGenIdeal`, equal only up to radical). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:50:  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:52:/-- **`varietyDim` transports across a coordinate-ring `AlgEquiv`.** If the coordinate rings
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean:57:theorem varietyDim_eq_of_coordRingAlgEquiv {k : Type u} [Field k] {σ τ : Type u}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:25:  `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty` and the polynomial dimension `= n`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:74:  have hk : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) = (n : WithBot ℕ∞) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:76:  have hsup : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) k))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:79:    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:27:4. **`vanishingIdeal(fibre) = radical(fibreGenIdeal)`** — over `[IsAlgClosed k]`, the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:29:   radical of `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:31:   `fibreGenIdeal d B = Ideal.map (multComap d) (maxIdealOfPoint B)`: the fibre generator-ideal is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:153:noncomputable def fibreGenIdeal (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:159:vanishing ideal of the fibre's image as the radical of `fibreGenIdeal d B`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:162:    vanishingIdeal k (canonicalCoord d '' (fibre d B)) = (fibreGenIdeal d B).radical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:163:  rw [image_fibre_eq_zeroLocus, fibreGenIdeal,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:188:`fibreGenIdeal d B = Ideal.map (multComap d) (maxIdealOfPoint d B)`: the fibre coordinate ring is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:190:theorem fibreGenIdeal_eq_map_maxIdealOfPoint (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:192:    fibreGenIdeal d B = Ideal.map (multComap d).toRingHom (maxIdealOfPoint d B) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MultComorphism.lean:193:  rw [maxIdealOfPoint, Ideal.map_span, fibreGenIdeal, fibreGenSet]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:108:  have : Subsingleton (Fin (intervalDim i j i')) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:152:    have : Subsingleton (n → k) := inferInstance
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntervalModule.lean:161:  have : Subsingleton (m → k) := inferInstance
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:60:/-- **L3.0 — the `G_d`-action as a `k`-algebra automorphism.** `baseChangeAlgEquiv P` is the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:64:noncomputable def baseChangeAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:67:  AlgEquiv.ofAlgHom (baseChangePullback P) (baseChangePullback P⁻¹)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:75:@[simp] theorem baseChangeAlgEquiv_apply [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:77:    baseChangeAlgEquiv P f = baseChangePullback P f := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:84:domain. The `G_d`-automorphism `baseChangeAlgEquiv P` stabilises `I`, descending to `A ≃ₐ[k] A`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:102:/-- The orbit ideal is `G_d`-stable: `baseChangeAlgEquiv P` maps `I` into `I`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:106:    (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:113:/-- The orbit ideal is **invariant** under `baseChangeAlgEquiv P`: `I.map (α_P) = I`. Both `α_P` and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:117:    (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:122:      (baseChangeAlgEquiv P⁻¹ : MvPolynomial (RepCoord d) k →+* _) ≤ orbitIdeal M :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:126:          (baseChangeAlgEquiv P⁻¹ : MvPolynomial (RepCoord d) k →+* _)).map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:127:          (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:135:    _ ≤ (orbitIdeal M).map (baseChangeAlgEquiv P : MvPolynomial (RepCoord d) k →+* _) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:139:from the polynomial-ring automorphism `baseChangeAlgEquiv P` (which stabilises `I`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:141:noncomputable def orbitRingAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:144:  Ideal.quotientEquivAlg (orbitIdeal M) (orbitIdeal M) (baseChangeAlgEquiv P)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:149:@[simp] theorem orbitRingAlgEquiv_mk [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:151:    orbitRingAlgEquiv M P (Ideal.Quotient.mk (orbitIdeal M) f)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:219:theorem orbitEval_comp_orbitRingAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:221:    (orbitEval M 1).comp (orbitRingAlgEquiv M P).toAlgHom = orbitEval M P := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:225:  change orbitEval M 1 (orbitRingAlgEquiv M P (Ideal.Quotient.mk (orbitIdeal M) f))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:227:  rw [orbitRingAlgEquiv_mk, orbitEval_mk, orbitEval_mk, one_smul,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:238:      = (normalFormIdeal M).comap (orbitRingAlgEquiv M P).toAlgHom.toRingHom := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:240:      = (orbitEval M 1).toRingHom.comp (orbitRingAlgEquiv M P).toAlgHom.toRingHom := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:243:    exact congrFun (congrArg DFunLike.coe (orbitEval_comp_orbitRingAlgEquiv M P).symm) a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:257:        (orbitRingAlgEquiv M P : orbitRing M ≃+* orbitRing M).toMonoidHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:262:      x ∈ orbitPointIdeal M P ↔ orbitRingAlgEquiv M P x ∈ normalFormIdeal M := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:268:    have : orbitRingAlgEquiv M P x ∉ normalFormIdeal M := fun h ↦ hx ((hmem x).mpr h)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:271:    refine ⟨(orbitRingAlgEquiv M P).symm y, ?_, by simp⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:274:    exact hy (by simpa [(hmem _).mp h] using (hmem ((orbitRingAlgEquiv M P).symm y)).mp h)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:277:noncomputable def localizationAtPrimeAlgEquiv [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:280:  AlgEquiv.ofRingEquiv
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:283:      (orbitRingAlgEquiv M P : orbitRing M ≃+* orbitRing M) (map_orbitPointIdeal_primeCompl M P))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:289:        IsLocalization.ringEquivOfRingEquiv_eq, AlgEquiv.coe_ringEquiv,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:290:        AlgEquiv.commutes,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:294:localizations are `k`-algebra isomorphic (`localizationAtPrimeAlgEquiv`), and
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:299:  Algebra.FormallySmooth.iff_of_equiv (localizationAtPrimeAlgEquiv M P)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:374:noncomputable abbrev orbitScheme : Scheme := Spec (.of (orbitRing M))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:458:      rw [AlgEquiv.symm_apply_apply]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:515:  Ideal.quotientKerAlgEquivOfSurjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:529:evaluation is `G_d`-invariant under the identity base change (`orbitEval_comp_orbitRingAlgEquiv` at
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:532:    (orbitRingAlgEquiv (k := ℚ) tupleWitnessQ 1).toAlgHom = orbitEval tupleWitnessQ 1 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:533:  orbitEval_comp_orbitRingAlgEquiv tupleWitnessQ 1
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:11:`fibreGenIdeal d B` (`Core.MultComorphism.vanishingIdeal_image_fibre_eq_radical`). The point of this
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:16:So `codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height` — **unconditionally** (no radicality
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:17:of `fibreGenIdeal` needed). This decouples the codimension from the scheme-structure / cut-ideal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:19:never depends on whether `fibreGenIdeal` is its own radical.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:45:ideal `fibreGenIdeal d B = span {multPoly d r c − C (B r c)}`. The chain:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:47:(definition of `codimRepCanonical`/`codimRep`); `vanishingIdeal (…) = (fibreGenIdeal d B).radical`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:49:(`Ideal.height_radical`). The codimension does **not** depend on whether `fibreGenIdeal` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:51:theorem codimRepCanonical_fibre_eq_height_fibreGenIdeal [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:53:    codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:61:height of the explicit fibre generator ideal — `codimRepCanonical_fibre_eq_height_fibreGenIdeal` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:64:    codimRepCanonical (fibre dWitness B) = (fibreGenIdeal dWitness B).height :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreHeightDirect.lean:65:  codimRepCanonical_fibre_eq_height_fibreGenIdeal dWitness B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:20:   matrix-entry coordinates, so it induces the `k`-algebra automorphism `baseChangeAlgEquiv P` of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:30:**Typeclass.** `[Field k] [Infinite k]` — `Infinite` carries `baseChangeAlgEquiv` (the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:139:ideal as a `comap` along `baseChangeAlgEquiv P` (a ring equiv), and `RingEquiv.height_comap`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:146:      = ((baseChangeAlgEquiv P).toRingEquiv.toRingHom) := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:148:  exact RingEquiv.height_comap (baseChangeAlgEquiv P).toRingEquiv _
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:20:(`renameEquiv`), so both invariants transport (`ringKrullDim_eq_of_ringEquiv`, `AlgEquiv.trdeg_eq`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:80:`ringKrullDim_eq_of_ringEquiv` and `AlgEquiv.trdeg_eq`. Char-free. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:104:  rw [ringKrullDim_eq_of_ringEquiv Ψ.toRingEquiv, AlgEquiv.trdeg_eq Ψ,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:10:MvPolynomial σ (MvPolynomial τ k)` (`sumAlgEquiv`), for a forced map `c : σ → MvPolynomial τ k` the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:47:`height + dim(quotient) = #vars`: `#vars = Nat.card σ + Nat.card τ` (via `sumAlgEquiv` to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:55:    sumAlgEquiv k σ τ with he
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:132:/-- The **translation automorphism** `X b ↦ X b + C (c b)` of `MvPolynomial σ R`, an `AlgEquiv` with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:137:  AlgEquiv.ofAlgHom (aeval (fun b ↦ X b + C (c b))) (aeval (fun b ↦ X b - C (c b)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:43:/-- LANDED: H1 retarget — `codim(fibre B) = height(fibreGenIdeal B)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:46:    codimRepCanonical (fibre d B) = (fibreGenIdeal d B).height :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibrationProbe.lean:47:  codimRepCanonical_fibre_eq_height_fibreGenIdeal d B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:21:* **`fibreGen`** — the generator family; `span (range (fibreGen d B)) = fibreGenIdeal d B`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:62:/-- The span of the fibre generators is the fibre generator ideal `fibreGenIdeal d B`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:65:    Ideal.span (Set.range (fibreGen d B)) = fibreGenIdeal d B := rfl
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:113:localisation of `fibreGenIdeal d B` (`span (range (fibreGen d B)) = fibreGenIdeal d B`) at `A`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:10:presentation (`Core.DeterminantalBasePresentation`) is `N = 1` only: `basePresentationEquiv` lives
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:40:   fibreGenIdeal`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:41:7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:43:   (`Ideal.quotientMapₐ`), then composed with `basePresentationEquiv.symm` to give a `k`-algebra map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:47:**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:48:endpoint-normalization `AlgEquiv`, and the descent of the iso to the reduced chart quotient are
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:53:arbitrary coefficient ring `R`, via `AlgEquiv.ofAlgHom`, **not** `baseChangeAlgEquiv` which carries
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:99:  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, renameEquiv_apply,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:124:noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:131:`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:229:Does **not** assume the circular `sigmaIdeal ≤ fibreGenIdeal`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:251:discharged by `deepBaseComap_sigmaIdeal_le`), then composed with `basePresentationEquiv.symm`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:316:`baseQuotMap` precomposed with `basePresentationEquiv.symm`. This is the morphism whose induced
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:318:R2-3a's product iso `e` needs). `[IsAlgClosed k] [CharZero k]` (for `basePresentationEquiv`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:319:noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:323:    (basePresentationEquiv (k := k) (d 0) (d (Fin.last N)) r hp hq).symm.toAlgHom
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:327:The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:329:`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:331:/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:336:  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:339:tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:347:  -- `algebraMap (SchurLoc …) Sred = schurToSred.toRingHom` (by `toAlgebra`); `schurToSred` is a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:350:      = (schurToSred (k := k) d r hp hq).toRingHom (algebraMap k _ x)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:351:  exact (AlgHom.commutes (schurToSred (k := k) d r hp hq) x).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:355:The endpoint-normalization `AlgEquiv` for R2-3b-3 is an `aeval`-substitution on the **unquotiented**
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:357:`baseChangeAlgEquiv`, which carries `[Infinite k]` from polynomial-function ext). The contract — two
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:358:`aeval` substitutions that round-trip on generators, assembled by `AlgEquiv.ofAlgHom` — is pinned
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:364:generators, assemble to a coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R` via
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:365:`AlgEquiv.ofAlgHom` (each direction an `aeval`; the round-trips by `MvPolynomial.algHom_ext` +
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:372:  AlgEquiv.ofAlgHom (aeval toSub) (aeval fromSub)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:417:`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:28:2. **`fibreGenIdeal_isRadical_of_trivialization`** — the full route-(b) chain: given the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:29:   trivialization `e : S ≃ₐ[k] R ⊗_k FibreAlg d B` and `IsReduced S` (the reduced chart ring),
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:31:   `fibreGenIdeal d B` is **radical** (`Ideal.isRadical_iff_quotient_reduced`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:33:3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:35:   radical (fibreGenIdeal d B) = fibreGenIdeal d B` — the `radical (·)` wrapper drops. This is the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:39:`e : S ≃ₐ[k] R ⊗_k F_B` and `IsReduced S`, which are carried as **explicit hypotheses** — never as a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:68:abbrev FibreAlg (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:70:  MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:72:/-- `fibreGenIdeal d B` is radical **iff** `F_B` is reduced — the engine restatement of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:75:theorem fibreGenIdeal_isRadical_iff_isReduced_fibreAlg (d : Fin (N + 1) → ℕ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:77:    (fibreGenIdeal d B).IsRadical ↔ IsReduced (FibreAlg d B) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:78:  Ideal.isRadical_iff_quotient_reduced (fibreGenIdeal d B)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:101:/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:102:trivialization `e : S ≃ₐ[k] R ⊗_k F_B` (the endpoint-normalization product iso) and that the chart
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:104:a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:106:⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:107:theorem fibreGenIdeal_isRadical_of_trivialization
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:111:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:112:    (fibreGenIdeal d B).IsRadical := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:115:  have hRF : IsReduced (R ⊗[k] FibreAlg d B) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:117:  -- ⟹ `F_B` reduced (tensor-with-a-field descent) ⟹ `fibreGenIdeal` radical
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:118:  exact (fibreGenIdeal_isRadical_iff_isReduced_fibreAlg d B).mpr (isReduced_of_tensor (R := R) hRF)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:121:ideal radical (`fibreGenIdeal_isRadical_of_trivialization`), the engine's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:122:`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:123:`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:126:theorem vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization [IsAlgClosed k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:130:    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:131:    vanishingIdeal k (canonicalCoord d '' fibre d B) = fibreGenIdeal d B := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:133:    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:138:and the identity equiv `e := AlgEquiv.refl` — exhibiting that the hypotheses are jointly satisfiable
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:149:domain and `F_B` reduced, the identity equiv `e := AlgEquiv.refl` and `IsReduced S` discharge the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:150:hypotheses of `fibreGenIdeal_isRadical_of_trivialization` — so the theorem is not vacuous. (Here the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:154:    [Algebra k R] [IsReduced (R ⊗[k] FibreAlg d B)] :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:155:    (fibreGenIdeal d B).IsRadical :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:156:  fibreGenIdeal_isRadical_of_trivialization d B R (R ⊗[k] FibreAlg d B)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean:157:    (AlgEquiv.refl) ‹_›
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/JacobianTrdeg.lean:199:(`AlgEquiv.trdeg_eq` through the injective `B ↪ FractionRing B`). This is the routine reduction; all
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/JacobianTrdeg.lean:215:    rw [himg, AlgEquiv.trdeg_eq (Subalgebra.equivMapOfInjective _ ψ hψinj)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:88:    rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum (R ⧸ I))]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:93:    rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MvPolynomialKerAeval.lean:94:    (Ideal.quotientKerAlgEquivOfSurjective (aeval_surjective c))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:141:  have hle : Submonoid.powers f ≤ m.primeCompl := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:134:  exact (AlgEquiv.restrictScalars k (AlgEquiv.ofBijective

codex
The declarations confirm the product iso is deliberately absent: `DeepChartRing` names it as out of scope and `FibreReducedTrivialization` still takes it as a hypothesis. I’m checking the dimension support now, because the answer turns on whether a one-way ring-map proof already has usable Krull-dimension infrastructure.
exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/VarietyDimRadical.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.NullstellensatzCodim
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# `DLNFibre.Core.VarietyDimRadical` — `varietyDim`/`ringKrullDim` is radical-insensitive

The formal linchpin of the route-(c) non-circularity de-risk (thread 31). The earlier scheme-level
product-iso route (R2-3b-4) was circular *for reducedness*: the forward map needed the strict ideal
inclusion `sigmaIdeal ≤ ker`, available only as `≤ radical`. The **dimension** identity `hSweep`
(`varietyDim Σ^r = δ + varietyDim F`) never touches that question, because `varietyDim` reads only
the **reduced / closed-set** structure: `ringKrullDim (R ⧸ I)` depends on `I` only through its
radical (both quotients have the same prime spectrum). So the route-(c) dimension build works
through `vanishingIdeal` (radical by construction) and never needs `fibreGenIdeal` to be radical.

A companion `varietyDim` invariance, the foundation of the route-(c) chart trivialization
(thread 31 rung 2): `varietyDim` transports across a **coordinate-ring `AlgEquiv`**
(`varietyDim_eq_of_coordRingAlgEquiv`) — even between varieties in *different* ambient affine
spaces. A regular isomorphism of affine varieties induces such an `AlgEquiv`, so this is the bridge
that carries the pivot-chart trivialization `mult⁻¹(U) ∩ Σ^r ≅ U × F` to a `varietyDim` equality
without ever realizing both sides in one ambient space.

## Main results
- `ringKrullDim_quotient_radical` — `ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical)`.
- `ringKrullDim_quotient_eq_of_radical_eq` — same Krull dim for two ideals with equal radical.
- `varietyDim_eq_of_coordRingAlgEquiv` — `varietyDim` transport across a coordinate-ring `AlgEquiv`.
-/

namespace DLNFibre.Core

open PrimeSpectrum MvPolynomial

universe u

/-- **Radical-insensitivity of the quotient Krull dimension.** `ringKrullDim (R ⧸ I)` depends on `I`
only through its radical: `Spec (R ⧸ I) = zeroLocus I = zeroLocus I.radical = Spec (R ⧸ I.radical)`
as ordered sets, and Krull dimension is a spectrum invariant. -/
theorem ringKrullDim_quotient_radical {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ I.radical) := by
  rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]

/-- Two ideals with the same radical give the same quotient Krull dimension — the form the route-(c)
fibre-dimension build consumes (it reads `varietyDim` off `vanishingIdeal`, while a chart
presentation may hand it the generator ideal `fibreGenIdeal`, equal only up to radical). -/
theorem ringKrullDim_quotient_eq_of_radical_eq {R : Type*} [CommRing R] {I J : Ideal R}
    (h : I.radical = J.radical) :
    ringKrullDim (R ⧸ I) = ringKrullDim (R ⧸ J) := by
  rw [ringKrullDim_quotient_radical I, ringKrullDim_quotient_radical J, h]

/-- **`varietyDim` transports across a coordinate-ring `AlgEquiv`.** If the coordinate rings
`MvPolynomial σ k ⧸ vanishingIdeal Z` and `MvPolynomial τ k ⧸ vanishingIdeal W` are `k`-algebra
isomorphic (the algebraic content of a regular isomorphism `Z ≅ W` of affine varieties, possibly in
different ambient spaces `σ`, `τ`), then `varietyDim Z = varietyDim W`. The Krull dimension is a
ring-isomorphism invariant (`ringKrullDim_eq_of_ringEquiv`); the `unbotD 0` wrapper is preserved. -/
theorem varietyDim_eq_of_coordRingAlgEquiv {k : Type u} [Field k] {σ τ : Type u}
    {Z : Set (σ → k)} {W : Set (τ → k)}
    (e : (MvPolynomial σ k ⧸ vanishingIdeal k Z) ≃ₐ[k]
          (MvPolynomial τ k ⧸ vanishingIdeal k W)) :
    varietyDim Z = varietyDim W := by
  unfold varietyDim
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]

end DLNFibre.Core

/-- Non-vacuity witness: in `ℚ[X]`, the square `(X)^2` of the prime `(X)` shares its radical, so the
two quotient Krull dimensions agree — a genuinely non-reduced ideal `(X)^2` reduced to `(X)` without
changing the dimension. -/
example :
    ringKrullDim (Polynomial ℚ ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ)) ^ 2)
      = ringKrullDim (Polynomial ℚ ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ))) := by
  apply DLNFibre.Core.ringKrullDim_quotient_eq_of_radical_eq
  exact Ideal.radical_pow (I := (Ideal.span {Polynomial.X} : Ideal (Polynomial ℚ))) (by norm_num)

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreReducedTrivialization.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.MultComorphism
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# `DLNFibre.Core.FibreReducedTrivialization` — route-(b) reducedness via the trivialization

The route-(b) reducedness chain of `G2-3` (thread 17, R2-3), wired against the **trivialization** of
the rank-`r` chart as a hypothesis. The certified pen-and-paper input (thread 16) is that the fibre
ideal `I_E = (mult(Ã) − E)` is **radical** (`F_E = k[Ã]/I_E` **reduced**), for every `N ≥ 1`, every
dimension vector, every target (it depends only on `rank E`). The MECHANISM is that reducedness is
**inherited** from the reduced ambient rank-locus chart `Sred` via the **faithfully-flat product
trivialization** `S ≅ₐ[k] R ⊗_k F_E` (endpoint normalization), then **descends** to `F_E` over the
field `k`.

This module supplies, sorry-free and unconditionally, the **two ends of that chain** plus the
**closer that consumes it**, leaving the single open rung — the deep product trivialization `e`
itself, together with the reducedness `IsReduced S` of the chart ring — as an explicit
**hypothesis**, not an asserted fact:

1. **`isReduced_of_tensor`** — the tensor-with-a-field reducedness **descent** `F` reduced ⟸
   `R ⊗_k F` reduced (over a field `k`, any nontrivial `k`-algebra `R`). The "one open dependency"
   the thread-16 certificate flagged; here it is the direct `includeRight` injection
   (`Algebra.TensorProduct.includeRight_injective` + `isReduced_of_injective`), **not** the
   geometric `IsGeometricallyReduced` (which descends in the opposite direction).

2. **`fibreGenIdeal_isRadical_of_trivialization`** — the full route-(b) chain: given the
   trivialization `e : S ≃ₐ[k] R ⊗_k FibreAlg d B` and `IsReduced S` (the reduced chart ring),
   `R ⊗_k F_E` is reduced (transfer along `e`), hence `F_E` is reduced (descent (1)), hence
   `fibreGenIdeal d B` is **radical** (`Ideal.isRadical_iff_quotient_reduced`).

3. **`vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization`** — the **radical-collapse** of
   `MultComorphism` point 4: with the cut ideal radical, `vanishingIdeal (fibre d B) =
   radical (fibreGenIdeal d B) = fibreGenIdeal d B` — the `radical (·)` wrapper drops. This is the
   identity the height-squeeze (R2-5/R2-6, `height m_B = δ`) consumes.

**What is Proved vs Assumed here.** Everything above is proved sorry-free *given* the trivialization
`e : S ≃ₐ[k] R ⊗_k F_B` and `IsReduced S`, which are carried as **explicit hypotheses** — never as a
`sorry` or a global axiom. The deep trivialization `e` itself (the endpoint-normalization product
iso, built from a deep localized chart ring `S = O(Σ̄^r ∩ chart)`) is **not** constructed here: it
is the **open residual `G2-3` wall, R2-3b** (new scheme-free affine scaffolding — no deep localized
total ring exists in the engine yet, G2-2's machinery is `N = 1` only; ~5–8 modules). No downstream
result may claim `codim (fibre) = C + δ` or discharge `BundleShiftInterface` on the strength of
these conditional theorems while `e` is a hypothesis — that discharge waits for R2-3b to prove `e`.
The theorems here are an honest, clearly-labelled *conditional* pre-build of the downstream: every
consumer of `e` is **already proved against the hypothesis**, so R2-3b closes the chain with no
further reducedness work. (Codex's recommended build order for `e` is recorded in the thread's
`codex/algequiv-answer.md`.)

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial
open scoped TensorProduct

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The fibre coordinate algebra `F_E` -/

/-- The **fibre coordinate algebra** `F_B = k[Ã] / (mult(Ã) − B)`: the coordinate ring of the cut
scheme `mult⁻¹(B)`, i.e. `MvPolynomial (RepCoord d) k` modulo the fibre generator ideal. (`F_E` in
the certificate is this at the rank normal form `B = E`; the construction is uniform in `B`.) -/
abbrev FibreAlg (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) : Type u :=
  MvPolynomial (RepCoord d) k ⧸ fibreGenIdeal d B

/-- `fibreGenIdeal d B` is radical **iff** `F_B` is reduced — the engine restatement of
`Ideal.isRadical_iff_quotient_reduced` for the fibre algebra. The bridge route-(b) crosses (the
geometric reducedness of `F_B` is exactly the radical-collapse the height-squeeze wants). -/
theorem fibreGenIdeal_isRadical_iff_isReduced_fibreAlg (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) :
    (fibreGenIdeal d B).IsRadical ↔ IsReduced (FibreAlg d B) :=
  Ideal.isRadical_iff_quotient_reduced (fibreGenIdeal d B)

/-! ## The tensor-with-a-field reducedness descent (the pinned dependency)

`F` reduced ⟸ `R ⊗_k F` reduced over a field `k`. Direct via the **injection**
`includeRight : F →ₐ[k] R ⊗_k F` (a nonzero `k`-algebra `R` makes `algebraMap k R` injective, and
`F` is `k`-flat as a vector space, so `includeRight` is injective by
`Algebra.TensorProduct.includeRight_injective`), then `isReduced_of_injective`. This is the standard
char-0 descent the certificate named — but it needs only a field base and a nontrivial `R`. -/

/-- **Tensor-with-a-field reducedness descent.** Over a field `k`, for any nontrivial commutative
`k`-algebra `R` and commutative `k`-algebra `F`: if `R ⊗_k F` is reduced then `F` is reduced. The
injection `F ↪ R ⊗_k F` (`includeRight`, injective since `F` is `k`-flat and `algebraMap k R` is
injective) pulls back reducedness. -/
theorem isReduced_of_tensor {R F : Type u} [CommRing R] [Nontrivial R] [CommRing F]
    [Algebra k R] [Algebra k F] (h : IsReduced (R ⊗[k] F)) : IsReduced F :=
  letI := h
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : F →ₐ[k] R ⊗[k] F)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k R).injective)

/-! ## The route-(b) chain through the trivialization (the open rung as a hypothesis) -/

/-- **Route (b): `fibreGenIdeal` radical, through the trivialization.** Given the chart
trivialization `e : S ≃ₐ[k] R ⊗_k F_B` (the endpoint-normalization product iso) and that the chart
ring `S` is **reduced** (the engine's `Sred = (MvPol / sigmaIdeal)[1/ΔP]` is reduced, `sigmaIdeal`
a `vanishingIdeal`), the fibre ideal `fibreGenIdeal d B` is **radical**. The certified mechanism:
`S` reduced ⟹ `R ⊗_k F_B` reduced (transfer along `e.symm`) ⟹ `F_B` reduced (`isReduced_of_tensor`)
⟹ `fibreGenIdeal d B` radical. `[Nontrivial R]` (`R = SchurLoc` is a domain). -/
theorem fibreGenIdeal_isRadical_of_trivialization
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (R S : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
    (fibreGenIdeal d B).IsRadical := by
  letI := hSred
  -- `S` reduced ⟹ `R ⊗ F_B` reduced (it injects into `S` via `e.symm`)
  have hRF : IsReduced (R ⊗[k] FibreAlg d B) :=
    isReduced_of_injective e.symm.toRingEquiv e.symm.injective
  -- ⟹ `F_B` reduced (tensor-with-a-field descent) ⟹ `fibreGenIdeal` radical
  exact (fibreGenIdeal_isRadical_iff_isReduced_fibreAlg d B).mpr (isReduced_of_tensor (R := R) hRF)

/-- **The radical-collapse of `MultComorphism` point 4** (through the trivialization). With the cut
ideal radical (`fibreGenIdeal_isRadical_of_trivialization`), the engine's
`vanishingIdeal (fibre d B) = radical (fibreGenIdeal d B)` collapses to
`vanishingIdeal (fibre d B) = fibreGenIdeal d B`: the `radical (·)` wrapper drops. The clean
identity the height-squeeze (`height m_B = δ`, R2-5/R2-6) consumes. `[IsAlgClosed k]` (the
Nullstellensatz bridge). -/
theorem vanishingIdeal_fibre_eq_fibreGenIdeal_of_trivialization [IsAlgClosed k]
    (d : Fin (N + 1) → ℕ) (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k)
    (R S : Type u) [CommRing R] [Nontrivial R] [CommRing S]
    [Algebra k R] [Algebra k S]
    (e : S ≃ₐ[k] R ⊗[k] FibreAlg d B) (hSred : IsReduced S) :
    vanishingIdeal k (canonicalCoord d '' fibre d B) = fibreGenIdeal d B := by
  rw [vanishingIdeal_image_fibre_eq_radical,
    (fibreGenIdeal_isRadical_of_trivialization d B R S e hSred).radical]

/-! ## Non-vacuity witnesses

The descent (1) is non-vacuous over any field. The chain (2)/(3) is non-vacuous with `S := R ⊗ F_B`
and the identity equiv `e := AlgEquiv.refl` — exhibiting that the hypotheses are jointly satisfiable
(a reduced `S` admitting the iso), so the conclusions are not vacuously
derived from contradictory hypotheses. -/

section Witness

/-- The tensor-descent fires over `ℚ` (a field) for `R = ℚ`, `F = ℚ`: `ℚ ⊗_ℚ ℚ` reduced ⟹ `ℚ`
reduced — non-vacuous. -/
example (h : IsReduced (ℚ ⊗[ℚ] ℚ)) : IsReduced ℚ := isReduced_of_tensor (k := ℚ) h

/-- The chain's hypotheses are jointly satisfiable: with `S := R ⊗_k F_B`, `R` a nontrivial reduced
domain and `F_B` reduced, the identity equiv `e := AlgEquiv.refl` and `IsReduced S` discharge the
hypotheses of `fibreGenIdeal_isRadical_of_trivialization` — so the theorem is not vacuous. (Here the
content is the *shape* of the contract; the genuine `e` for the rank chart is the deferred rung.) -/
example [IsAlgClosed k] (d : Fin (N + 1) → ℕ)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) k) (R : Type u) [CommRing R] [Nontrivial R]
    [Algebra k R] [IsReduced (R ⊗[k] FibreAlg d B)] :
    (fibreGenIdeal d B).IsRadical :=
  fibreGenIdeal_isRadical_of_trivialization d B R (R ⊗[k] FibreAlg d B)
    (AlgEquiv.refl) ‹_›

end Witness

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,440p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.DeterminantalBasePresentation
import DLNFibre.Core.FibreReducedTrivialization

/-!
# `DLNFibre.Core.DeepChartRing` — the deep chart ring `Sred` + the localized base→total map
# (R2-3b-1+2)

The first rungs of the **deep** product trivialization `e` that R2-3a
(`Core.FibreReducedTrivialization`) carries as a hypothesis. The engine's localized determinantal
presentation (`Core.DeterminantalBasePresentation`) is `N = 1` only: `basePresentationEquiv` lives
over `dStratum q p = ![q, p]`, a single matrix. This module builds, for a **general** dimension
vector `d : Fin (N + 1) → ℕ`, the deep localized chart ring `Sred` of the rank-`≤ r` product locus
on the pivot chart, and the localized base→total `k`-algebra map that gives `Sred` its
`SchurLoc`-algebra structure (the `R = SchurLoc`-algebra structure that R2-3a's `e` needs).

The deliverables, with `q = d 0` (source dimension) and `p = d (Fin.last N)` (target dimension):

**R2-3b-1 — the deep chart ring (definitions + instances + bridges).**
1. `ΔPdeep d r hp hq` — the deep pivot minor: the determinant of the top-left `r×r` submatrix of the
   **deep** generic product `Matrix.of (multPoly d)` (the deep analog of `N = 1`'s `detPivotPoly`).
2. `IadDeep d r hp hq` — the localized base ideal `(sigmaIdeal d r).map (algebraMap …)` pushed into
   `Localization.Away (ΔPdeep …)` (the deep analog of `Iad`).
3. `Sred d r hp hq := Localization.Away (ΔPdeep …) ⧸ IadDeep …` — the deep chart quotient ring, with
   its `CommRing` / `Algebra k` instances inherited, and `isReduced_Sred` : `IsReduced (Sred …)`
   (over `[IsAlgClosed k]`, justifying the name — this is R2-3a's `hSred`, now discharged).
4. The **type bridge** `repStratumEquiv : RepCoord (dStratum q p) ≃ Fin p × Fin q` (the
   single-matrix stratum coords), via `Equiv.uniqueSigma` (the `Sigma` over the `Unique` base
   `Fin 1`), and the deep base comorphism `deepBaseComap d` carrying the `N = 1` base coordinate
   ring into the deep total coordinate ring (`multComap d` after the rename).

**R2-3b-2 — the localized base→total map + the `SchurLoc`-algebra structure.**
5. `deepBaseComap_detPivot` — the load-bearing transport: `deepBaseComap d` carries the `N = 1`
   pivot minor `detPivotPoly` to the deep `ΔPdeep` (det commutes with `aeval`, `AlgHom.map_det`),
   making the localized map well-typed.
6. `deepBaseComap_sigmaIdeal_le` — the (non-circular) ideal direction: `deepBaseComap d` maps the
   base `sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Mechanism: a **deep** total
   point
   `A ∈ Σ̄^r_d` maps by `mult` to a single-matrix **base** point in `Σ̄^r_{(q,p)}` (chase via
   `aeval_deepBaseComap` + `singleTuple`). It does **not** assume the circular `sigmaIdeal ≤
   fibreGenIdeal`.
7. `baseLocMap` / `schurToSred` — the localized base map `Localization.Away detPivotPoly →ₐ[k]
   Localization.Away (ΔPdeep …)` (`IsLocalization.Away.mapₐ`), lifted to the quotients
   (`Ideal.quotientMapₐ`), then composed with `basePresentationEquiv.symm` to give a `k`-algebra map
   `SchurLoc q p r →ₐ[k] Sred d r hp hq`. The resulting `SchurLoc`-algebra structure on `Sred`
   (`RingHom.toAlgebra`) + the `IsScalarTower k (SchurLoc …) (Sred …)` instance.

**Scope (what is NOT here).** The full product iso `e : Sred ≃ₐ[k] SchurLoc ⊗_k FibreAlg`, the
endpoint-normalization `AlgEquiv`, and the descent of the iso to the reduced chart quotient are
**R2-3b-3 and R2-3b-4** (later tides). No result here claims `codim (fibre) = C + δ` or discharges
`BundleShiftInterface` — `e` is not yet built. (R2-3a's *other* hypothesis, `IsReduced S`, **is**
discharged here: `isReduced_Sred`, so R2-3b-4 needs only `e` itself.) The R2-3b-3
endpoint-normalization `aeval`-substitution contract is pre-staged below as an `example` block (an
arbitrary coefficient ring `R`, via `AlgEquiv.ofAlgHom`, **not** `baseChangeAlgEquiv` which carries
`[Infinite k]`).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## R2-3b-1 — the type bridge and the deep base comorphism

For the single-arrow stratum `dStratum q p = ![q, p]`, the coordinate index
`RepCoord (dStratum q p)` is a `Sigma` over `Fin 1`; collapsing it gives `Fin p × Fin q` (the
single-matrix entry coords). The deep base comorphism is the `N = 1` base coordinate map
`multComap d` precomposed with this rename. -/

/-- **The single-matrix stratum-coordinate bridge** `RepCoord (dStratum q p) ≃ Fin p × Fin q`. The
coordinate index of `dStratum q p = ![q, p]` is `Σ i : Fin 1, Fin (dStratum q p i.succ) ×
Fin (dStratum q p i.castSucc)`; over the `Unique` base `Fin 1` this is the single fibre
`Fin p × Fin q` (`default = 0`, `dStratum q p (0).succ = p`, `dStratum q p (0).castSucc = q`). -/
def repStratumEquiv (q p : ℕ) : RepCoord (dStratum q p) ≃ Fin p × Fin q :=
  Equiv.uniqueSigma (fun i : Fin 1 ↦ Fin (dStratum q p i.succ) × Fin (dStratum q p i.castSucc))

@[simp] theorem repStratumEquiv_mk (q p : ℕ) (x : Fin p × Fin q) :
    repStratumEquiv q p ⟨0, x⟩ = x := rfl

/-- **The deep base comorphism** `MvPolynomial (RepCoord (dStratum q p)) k →ₐ[k]
MvPolynomial (RepCoord d) k` (`q = d 0`, `p = d (last N)`): the `mult` comorphism `multComap d`
precomposed with the single-matrix coordinate rename. Carries the `N = 1` base coordinate ring into
the deep total coordinate ring. -/
noncomputable def deepBaseComap (d : Fin (N + 1) → ℕ) :
    MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k →ₐ[k]
      MvPolynomial (RepCoord d) k :=
  (multComap d).comp (renameEquiv k (repStratumEquiv (d 0) (d (Fin.last N)))).toAlgHom

/-- `deepBaseComap d` sends the single-matrix coordinate variable `X ⟨0, (a, b)⟩` to the deep
generic product entry `multPoly d a b`. -/
@[simp] theorem deepBaseComap_X (d : Fin (N + 1) → ℕ)
    (a : Fin (d (Fin.last N))) (b : Fin (d 0)) :
    deepBaseComap (k := k) d (X ⟨0, (a, b)⟩) = multPoly d a b := by
  rw [deepBaseComap]
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, renameEquiv_apply,
    rename_X, repStratumEquiv_mk, multComap_X]

/-! ## R2-3b-1 — the deep chart ring `Sred` -/

/-- **The deep pivot minor** `ΔPdeep d r`: the determinant of the top-left `r×r` submatrix of the
deep generic product `Matrix.of (multPoly d)`. The deep analog of `N = 1`'s `detPivotPoly`;
inverting it is the pivot chart. -/
noncomputable def ΔPdeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : MvPolynomial (RepCoord d) k :=
  ((Matrix.of (multPoly d)).submatrix
    (fun i : Fin r ↦ (Fin.castLE hp i : Fin (d (Fin.last N))))
    (fun j : Fin r ↦ (Fin.castLE hq j : Fin (d 0)))).det

/-- **The deep localized base ideal** `IadDeep d r`: the determinantal base ideal `sigmaIdeal d r`
pushed into the localized total ring `Localization.Away (ΔPdeep …)`. The deep analog of `Iad`. -/
noncomputable def IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Ideal (Localization.Away (ΔPdeep (k := k) d r hp hq)) :=
  (sigmaIdeal d r).map (algebraMap (MvPolynomial (RepCoord d) k)
    (Localization.Away (ΔPdeep (k := k) d r hp hq)))

/-- **The deep chart ring** `Sred d r := Localization.Away (ΔPdeep …) ⧸ IadDeep …`: the localized
chart quotient of the rank-`≤ r` product locus for general `d`, on the pivot chart. The `CommRing` /
`Algebra k` instances are inherited from the localization-quotient. -/
noncomputable abbrev Sred (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) : Type u :=
  Localization.Away (ΔPdeep (k := k) d r hp hq) ⧸ IadDeep (k := k) d r hp hq

/-! ## R2-3b-1 — `Sred` is reduced (justifying the name; discharges R2-3a's `hSred`)

The name `Sred` asserts reducedness, and that reducedness is precisely R2-3a's second hypothesis
`hSred : IsReduced S` (`Core.FibreReducedTrivialization.fibreGenIdeal_isRadical_of_trivialization`).
It is **cheap** here: `IadDeep = (sigmaIdeal d r).map (algebraMap …)` is radical because
`sigmaIdeal` is radical (`vanishingIdeal_isRadical`, over `[IsAlgClosed k]`) and localization
carries radical
ideals to radical ideals (`IsLocalization.map_radical`); a quotient by a radical ideal is reduced
(`Ideal.isRadical_iff_quotient_reduced`). No quotient↔localization interchange iso is needed. -/

/-- **`IadDeep` is radical** (`[IsAlgClosed k]`): the localized image of the radical determinantal
base ideal `sigmaIdeal d r`. Via `IsLocalization.map_radical`
(`(I.map …).radical = I.radical.map …`) and `sigmaIdeal`'s radicality
(`vanishingIdeal_isRadical`). -/
theorem IadDeep_isRadical [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (IadDeep (k := k) d r hp hq).IsRadical := by
  have hsig : (sigmaIdeal (k := k) d r).IsRadical := by
    rw [sigmaIdeal]; exact vanishingIdeal_isRadical _
  rw [← Ideal.radical_eq_iff, IadDeep,
    ← IsLocalization.map_radical (M := Submonoid.powers (ΔPdeep (k := k) d r hp hq)),
    hsig.radical]

/-- **`Sred` is reduced** (`[IsAlgClosed k]`), justifying the name.
`Sred = Localization.Away ΔPdeep ⧸ IadDeep` with `IadDeep` radical (`IadDeep_isRadical`); a quotient
by a radical ideal is reduced
(`Ideal.isRadical_iff_quotient_reduced`). This is exactly R2-3a's `hSred : IsReduced S` for
`S = Sred` — so R2-3b-4 needs to build only `e` itself, not also `IsReduced S`. -/
theorem isReduced_Sred [IsAlgClosed k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    IsReduced (Sred (k := k) d r hp hq) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (IadDeep_isRadical d r hp hq)

/-! ## R2-3b-2 — the load-bearing transports

`deepBaseComap` carries the `N = 1` pivot minor `detPivotPoly` to the deep `ΔPdeep` (making the
localized map well-typed), and the base `sigmaIdeal` into the deep `sigmaIdeal` (making the quotient
lift well-typed). -/

/-- **The pivot-minor transport** (load-bearing): `deepBaseComap d` carries the `N = 1` pivot minor
`detPivotPoly (d 0) (d last) r` to the deep pivot minor `ΔPdeep d r`. The determinant commutes with
the algebra map (`AlgHom.map_det`); each pivot entry `X ⟨0, (castLE i, castLE j)⟩` goes to
`multPoly d (castLE i) (castLE j)` (`deepBaseComap_X`), the corresponding entry of `Matrix.of
(multPoly d)`. (Exact analog of the landed `renameEquiv_detPivot`.) -/
theorem deepBaseComap_detPivot (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    deepBaseComap (k := k) d
        (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
      = ΔPdeep (k := k) d r hp hq := by
  rw [detPivotPoly, ΔPdeep, AlgHom.map_det]
  congr 1
  funext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    show (Matrix.of (multPoly (k := k) (dStratum (d 0) (d (Fin.last N)))))
        (Fin.castLE hp i) (Fin.castLE hq j)
        = X ⟨0, (Fin.castLE hp i, Fin.castLE hq j)⟩ from multPoly_stratum_apply _ _ _ _,
    deepBaseComap_X]
  rfl

/-! ### The single-matrix tuple and the comorphism chase -/

/-- The **single-matrix tuple** over `dStratum q p` from a matrix `M : Mat (p × q)`: the `N = 1`
`Tuple` whose lone factor is `M`. -/
def singleTuple (k : Type u) [Field k] (q p : ℕ) (M : Matrix (Fin p) (Fin q) k) :
    Tuple (k := k) (dStratum q p) :=
  fun i ↦ match i with | 0 => M

/-- `mult` of the single-matrix tuple is its matrix (the `N = 1` product is the lone factor). -/
theorem mult_singleTuple (q p : ℕ) (M : Matrix (Fin p) (Fin q) k) :
    mult (dStratum q p) (singleTuple k q p M) = M := by
  rw [mult_stratum_eq q p (singleTuple k q p M)]; rfl

/-- **The comorphism chase.** Evaluating `deepBaseComap d f` at the coordinates of a deep tuple `A`
equals evaluating `f` at the coordinates of the single-matrix base tuple of `mult d A`. Both are
`k`-algebra maps in `f`; on the generator `X ⟨0, (a, b)⟩` both give `(mult d A) a b`
(`eval_multPoly`). -/
theorem aeval_deepBaseComap (d : Fin (N + 1) → ℕ) (A : Tuple (k := k) d)
    (f : MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k) :
    aeval (canonicalCoord d A) (deepBaseComap d f)
      = aeval (R := k) (canonicalCoord (dStratum (d 0) (d (Fin.last N)))
          (singleTuple k (d 0) (d (Fin.last N)) (mult (k := k) d A))) f := by
  have hgen : (aeval (canonicalCoord d A)).comp (deepBaseComap d)
      = aeval (R := k) (canonicalCoord (dStratum (d 0) (d (Fin.last N)))
          (singleTuple k (d 0) (d (Fin.last N)) (mult (k := k) d A))) := by
    apply MvPolynomial.algHom_ext
    intro x
    obtain ⟨i, a, b⟩ := x
    obtain rfl : i = 0 := Subsingleton.elim i 0
    simp only [AlgHom.comp_apply, deepBaseComap_X]
    rw [show aeval (R := k) (canonicalCoord d A) (multPoly d a b)
          = eval (canonicalCoord d A) (multPoly d a b) from by rw [aeval_def, eval]; rfl,
      eval_multPoly, aeval_X, canonicalCoord_apply]
    rfl
  exact DFunLike.congr_fun hgen f

/-- **The base→deep `sigmaIdeal` direction** (non-circular): `deepBaseComap d` maps the base
`sigmaIdeal (dStratum q p) r` into the deep `sigmaIdeal d r`. Via `Ideal.map_le_iff_le_comap`: a
base generator `f` vanishing on `Σ̄^r_{(q,p)}` pulls back to a polynomial vanishing on `Σ̄^r_d`,
because a **deep** total point `A ∈ Σ̄^r_d` maps by `mult` to a single-matrix **base** point in
`Σ̄^r_{(q,p)}` (`mult_singleTuple`, `rank (mult d A) ≤ r`), where `f` vanishes
(`aeval_deepBaseComap`).
Does **not** assume the circular `sigmaIdeal ≤ fibreGenIdeal`. -/
theorem deepBaseComap_sigmaIdeal_le (d : Fin (N + 1) → ℕ) (r : ℕ) :
    (sigmaIdeal (k := k) (dStratum (d 0) (d (Fin.last N))) r).map
        (deepBaseComap (k := k) d).toRingHom
      ≤ sigmaIdeal (k := k) d r := by
  rw [Ideal.map_le_iff_le_comap]
  intro f hf
  rw [Ideal.mem_comap, sigmaIdeal, mem_vanishingIdeal_iff]
  intro x hx
  obtain ⟨A, hA, rfl⟩ := hx
  rw [mem_productRankLocusLE] at hA
  change aeval (R := k) (canonicalCoord d A) ((deepBaseComap d).toRingHom f) = 0
  rw [show (deepBaseComap d).toRingHom f = deepBaseComap d f from rfl, aeval_deepBaseComap]
  rw [sigmaIdeal, mem_vanishingIdeal_iff] at hf
  exact hf _ ⟨singleTuple k (d 0) (d (Fin.last N)) (mult d A), by
    rw [mem_productRankLocusLE, mult_singleTuple]; exact hA, rfl⟩

/-! ## R2-3b-2 — the localized base map and the `SchurLoc`-algebra structure on `Sred`

The localized base map `Localization.Away detPivotPoly →ₐ[k] Localization.Away (ΔPdeep …)`
(`IsLocalization.Away.mapₐ deepBaseComap detPivotPoly`, well-typed by the transport
`deepBaseComap_detPivot`), lifted to the quotients (`Ideal.quotientMapₐ`, the ideal hypothesis
discharged by `deepBaseComap_sigmaIdeal_le`), then composed with `basePresentationEquiv.symm`. -/

/-- **The localized base map** `Localization.Away (detPivotPoly …) →ₐ[k]
Localization.Away (ΔPdeep …)`, `IsLocalization.Away.mapₐ` of the deep base comorphism
`deepBaseComap d` at `detPivotPoly`. The
codomain localization instance at `deepBaseComap d (detPivotPoly …)` is `ΔPdeep`'s (the transport
`deepBaseComap_detPivot`). -/
noncomputable def baseLocMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq) →ₐ[k]
      Localization.Away (ΔPdeep (k := k) d r hp hq) := by
  haveI : IsLocalization.Away
      (deepBaseComap (k := k) d (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
    rw [deepBaseComap_detPivot]; infer_instance
  exact IsLocalization.Away.mapₐ _ _ (deepBaseComap d)
    (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)

/-- `baseLocMap` sends `algebraMap … x` to `algebraMap … (deepBaseComap d x)` — it intertwines the
two localization maps (`IsLocalization.Away.mapₐ` / `IsLocalization.map` on the base ring). -/
theorem baseLocMap_algebraMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0)
    (x : MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k) :
    baseLocMap (k := k) d r hp hq
        (algebraMap (MvPolynomial (RepCoord (dStratum (d 0) (d (Fin.last N)))) k)
          (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)) x)
      = algebraMap (MvPolynomial (RepCoord d) k) (Localization.Away (ΔPdeep (k := k) d r hp hq))
          (deepBaseComap d x) := by
  haveI : IsLocalization.Away
      (deepBaseComap (k := k) d (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq))
      (Localization.Away (ΔPdeep (k := k) d r hp hq)) := by
    rw [deepBaseComap_detPivot]; infer_instance
  rw [baseLocMap, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    IsLocalization.map_eq]
  rfl

/-- The base ideal `Iad` is carried into `IadDeep` by `baseLocMap`
(`Iad ≤ IadDeep.comap baseLocMap`), the hypothesis the quotient lift needs. `Iad`/`IadDeep` are the
localized images of the base / deep
`sigmaIdeal`s; `baseLocMap` intertwines the localization maps (`baseLocMap_algebraMap`) and carries
the base `sigmaIdeal` into the deep one (`deepBaseComap_sigmaIdeal_le`). -/
theorem Iad_le_comap_IadDeep (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Iad (k := k) (d 0) (d (Fin.last N)) r hp hq
      ≤ (IadDeep (k := k) d r hp hq).comap (baseLocMap (k := k) d r hp hq) := by
  rw [Iad, Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, Ideal.mem_comap, baseLocMap_algebraMap, IadDeep]
  -- `deepBaseComap g ∈ sigmaIdeal d r` (the base → deep direction), then push into the localization
  have hmem : deepBaseComap (k := k) d g ∈ sigmaIdeal (k := k) d r :=
    deepBaseComap_sigmaIdeal_le d r (Ideal.mem_map_of_mem _ hg)
  exact Ideal.mem_map_of_mem _ hmem

/-- **The localized base→total map on the quotients** `(Localization.Away detPivotPoly ⧸ Iad) →ₐ[k]
Sred d r`: the quotient lift of `baseLocMap` (`Ideal.quotientMapₐ`, the ideal hypothesis from
`Iad_le_comap_IadDeep`). -/
noncomputable def baseQuotMap (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    (Localization.Away (detPivotPoly (k := k) (d 0) (d (Fin.last N)) r hp hq)
        ⧸ Iad (k := k) (d 0) (d (Fin.last N)) r hp hq)
      →ₐ[k] Sred (k := k) d r hp hq :=
  Ideal.quotientMapₐ (IadDeep (k := k) d r hp hq) (baseLocMap (k := k) d r hp hq)
    (Iad_le_comap_IadDeep d r hp hq)

/-- **The base→total `k`-algebra map** `SchurLoc q p r →ₐ[k] Sred d r` (`q = d 0`, `p = d last`):
`baseQuotMap` precomposed with `basePresentationEquiv.symm`. This is the morphism whose induced
algebra structure makes `Sred` a `SchurLoc`-algebra (the `R = SchurLoc`-algebra structure that
R2-3a's product iso `e` needs). `[IsAlgClosed k] [CharZero k]` (for `basePresentationEquiv`). -/
noncomputable def schurToSred [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    SchurLoc (k := k) (d 0) (d (Fin.last N)) r →ₐ[k] Sred (k := k) d r hp hq :=
  (baseQuotMap (k := k) d r hp hq).comp
    (basePresentationEquiv (k := k) (d 0) (d (Fin.last N)) r hp hq).symm.toAlgHom

/-! ## R2-3b-2 — the `SchurLoc`-algebra structure on `Sred` and the scalar tower

The base→total map `schurToSred` induces (via `RingHom.toAlgebra`) the `SchurLoc q p r`-algebra
structure on `Sred`, with `k → SchurLoc → Sred` a scalar tower. These instances are the
`[Algebra R S]` slot that R2-3a's `e : S ≃ₐ[k] R ⊗_k FibreAlg` consumes (`R = SchurLoc q p r`). -/

/-- **The `SchurLoc`-algebra structure on `Sred`**, induced by the base→total map `schurToSred`
(`RingHom.toAlgebra`). The `R = SchurLoc q p r`-algebra structure R2-3a's product iso `e` needs. -/
@[reducible] noncomputable def sredSchurAlgebra [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ)
    (r : ℕ) (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    Algebra (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq) :=
  (schurToSred (k := k) d r hp hq).toRingHom.toAlgebra

/-- The induced `SchurLoc`-algebra structure on `Sred` makes `k → SchurLoc q p r → Sred` a scalar
tower: `algebraMap k Sred` factors through `algebraMap k (SchurLoc …)` (both `schurToSred` and the
localization-quotient maps are `k`-algebra maps). -/
theorem sredSchur_isScalarTower [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last N)) (hq : r ≤ d 0) :
    @IsScalarTower k (SchurLoc (k := k) (d 0) (d (Fin.last N)) r) (Sred (k := k) d r hp hq)
      _ (sredSchurAlgebra (k := k) d r hp hq).toSMul _ := by
  letI := sredSchurAlgebra (k := k) d r hp hq
  refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
  -- `algebraMap (SchurLoc …) Sred = schurToSred.toRingHom` (by `toAlgebra`); `schurToSred` is a
  -- `k`-algebra map, so it commutes with `algebraMap k (SchurLoc …)` (`AlgHom.commutes`).
  change algebraMap k (Sred (k := k) d r hp hq) x
      = (schurToSred (k := k) d r hp hq).toRingHom (algebraMap k _ x)
  exact (AlgHom.commutes (schurToSred (k := k) d r hp hq) x).symm

/-! ## R2-3b-3 pre-stage (durable contract, NOT proved here)

The endpoint-normalization `AlgEquiv` for R2-3b-3 is an `aeval`-substitution on the **unquotiented**
`MvPolynomial (RepCoord d) R` over an **arbitrary** coefficient ring `R` (Codex: NOT
`baseChangeAlgEquiv`, which carries `[Infinite k]` from polynomial-function ext). The contract — two
`aeval` substitutions that round-trip on generators, assembled by `AlgEquiv.ofAlgHom` — is pinned
here so R2-3b-3 inherits the exact shape. (`example`: the contract, not the genuine
substitution.) -/

/-- **R2-3b-3 pre-stage contract.** Two coordinate substitutions `toSub`, `fromSub : RepCoord d →
MvPolynomial (RepCoord d) R` over an arbitrary commutative ring `R`, mutually inverse on the
generators, assemble to a coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R` via
`AlgEquiv.ofAlgHom` (each direction an `aeval`; the round-trips by `MvPolynomial.algHom_ext` +
`aeval_X`). The endpoint-normalization substitution of R2-3b-3 instantiates this. -/
noncomputable example {R : Type u} [CommRing R] (d : Fin (N + 1) → ℕ)
    (toSub fromSub : RepCoord d → MvPolynomial (RepCoord d) R)
    (h_to_from : ∀ x, aeval toSub (fromSub x) = (X x : MvPolynomial (RepCoord d) R))
    (h_from_to : ∀ x, aeval fromSub (toSub x) = (X x : MvPolynomial (RepCoord d) R)) :
    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom (aeval toSub) (aeval fromSub)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change aeval toSub (aeval fromSub (X x)) = _
      rw [aeval_X]; exact h_to_from x)
    (by
      apply MvPolynomial.algHom_ext
      intro x
      change aeval fromSub (aeval toSub (X x)) = _
      rw [aeval_X]; exact h_from_to x)

/-! ## Non-vacuity witnesses

The deep constructions fire on the `N = 1` specialization `(d 0, d last) = (q, p)`, where they
reproduce the `N = 1` base data. We exhibit (i) the type bridge at `(2, 2)`, (ii) `deepBaseComap` /
`deepBaseComap_detPivot` at the `N = 1` stratum `dStratum 2 2`, `r = 1`, where the deep pivot minor
**is** the `N = 1` `detPivotPoly` (`deepBaseComap` is the identity-up-to-rename there), and (iii)
the localized base→total quotient map `baseQuotMap` available at that anchor over
`AlgebraicClosure ℚ`. -/

section Witness

/-- The type bridge `RepCoord (dStratum 2 2) ≃ Fin 2 × Fin 2` round-trips on a concrete coordinate
(the `(1, 0)` entry of the single matrix). -/
example : repStratumEquiv 2 2 ⟨0, (⟨1, by norm_num⟩, ⟨0, by norm_num⟩)⟩
    = (⟨1, by norm_num⟩, ⟨0, by norm_num⟩) := rfl

/-- `deepBaseComap` at the `N = 1` stratum `dStratum 2 2` sends `X ⟨0, (a, b)⟩` to the deep generic
product entry `multPoly (dStratum 2 2) a b` — non-vacuous (`N = 1` specialization). -/
example (a : Fin (dStratum 2 2 (Fin.last 1))) (b : Fin (dStratum 2 2 0)) :
    deepBaseComap (k := AlgebraicClosure ℚ) (dStratum 2 2) (X ⟨0, (a, b)⟩)
      = multPoly (dStratum 2 2) a b :=
  deepBaseComap_X _ a b

/-- The pivot-minor transport fires at the `N = 1` stratum `dStratum 2 2`, `r = 1`:
`deepBaseComap (detPivotPoly …) = ΔPdeep …`. -/
example (h : (1 : ℕ) ≤ 2) :
    deepBaseComap (k := AlgebraicClosure ℚ) (dStratum 2 2)
        (detPivotPoly (k := AlgebraicClosure ℚ) (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
      = ΔPdeep (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
  deepBaseComap_detPivot (dStratum 2 2) 1 h h

/-- The localized base→total quotient map `baseQuotMap` is available at the `N = 1` anchor
`dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — non-vacuous. (It needs no `IsAlgClosed` /
`CharZero`; `schurToSred` composes this with `basePresentationEquiv.symm`.) -/
noncomputable example (h : (1 : ℕ) ≤ 2) :
    (Localization.Away
          (detPivotPoly (k := AlgebraicClosure ℚ)
            (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
        ⧸ Iad (k := AlgebraicClosure ℚ) (dStratum 2 2 0) (dStratum 2 2 (Fin.last 1)) 1 h h)
      →ₐ[AlgebraicClosure ℚ] Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h :=
  baseQuotMap (dStratum 2 2) 1 h h

/-- `Sred` is reduced at the `N = 1` anchor `dStratum 2 2`, `r = 1`, over `AlgebraicClosure ℚ` — the
name is honest there, and R2-3a's `hSred` is discharged. -/
example (h : (1 : ℕ) ≤ 2) :
    IsReduced (Sred (k := AlgebraicClosure ℚ) (dStratum 2 2) 1 h h) :=
  isReduced_Sred (dStratum 2 2) 1 h h

end Witness

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,340p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/EndpointNormalization.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.MultComorphism
import DLNFibre.Core.BaseChange

/-!
# `DLNFibre.Core.EndpointNormalization` — the gauge-change `AlgEquiv` (R2-3b-3)

The second rung of the deep product trivialization `e`. On the **unquotiented** coordinate ring
`MvPolynomial (RepCoord d) R` over an **arbitrary** commutative ring `R`, the gauge-change map is the
linear coordinate substitution implementing the vertex-unit conjugation action
`Aᵢ ↦ P_{i+1} · Aᵢ · P_i⁻¹` of `Core.BaseChange.baseChange` on the generic tuple. For the endpoint
normalization of the paper's route, the gauge `P` is identity at every interior vertex and carries
`H` at the source vertex `0`, `L⁻¹` at the target vertex `Fin.last N`: then
`mult(Ã) = L⁻¹ · mult(A) · H⁻¹`, normalizing the two endpoint factors only. Kept GENERAL in the gauge
`P` (one invertible matrix per vertex over `R`) so R2-3b-4 instantiates it with the Schur-data
unipotents.

The deliverables, for a fixed dimension vector `d : Fin (N + 1) → ℕ` over `[CommRing R]` and a gauge
`P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ`:

1. `gaugeSub d P` — the coordinate substitution `RepCoord d → MvPolynomial (RepCoord d) R`: the
   `⟨i, (r, c)⟩` entry of `baseChange (P.map C) (genericTuple d)`, i.e. the entries of
   `P_{i+1} · Xᵢ · P_i⁻¹` with the unit matrices pushed into the coefficient ring by `C`.
2. `gaugeEquiv d P` — the coordinate-change `AlgEquiv` of `MvPolynomial (RepCoord d) R`, assembled by
   `AlgEquiv.ofAlgHom` from `aeval (gaugeSub P)` and `aeval (gaugeSub P⁻¹)`. The round-trips collapse
   by the group-action laws `baseChange_mul` / `baseChange_one` on the generic tuple.
3. The **mult-transport** `aeval_gaugeSub_multPoly` : `aeval (gaugeSub P) (multPoly d r c) =
   (P_last.val.map C · Matrix.of (multPoly d) · (P 0)⁻¹.val.map C) r c` — the generic product matrix
   transforms by the two end-vertex gauges (interior units telescope away, `mult_smul`). For the
   endpoint normalization this is `L⁻¹ · multPoly · H⁻¹` (the bridge R2-3b-4 needs to turn
   `mult(A) = LEH` into `mult(Ã) = E`).

The `N = 1` coincidence (first factor = last factor) is automatic: `baseChange` is defined uniformly
per edge from both endpoint vertices, so the single edge `0` of `Fin 1` already carries both end
gauges.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`. The gauge is over the arbitrary
coefficient ring `R`; nothing here needs a field, `IsAlgClosed`, or `Infinite` (in particular we
avoid `baseChangePullback`, which carries `[Infinite k]` from polynomial-function ext).
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {R : Type u} [CommRing R] {N : ℕ}

/-! ## Lifting a gauge into the coefficient ring -/

/-- Lift a gauge `P : ∀ v, (Matrix (Fin (d v)) (Fin (d v)) R)ˣ` to one over the coordinate ring
`MvPolynomial (RepCoord d) R` by pushing each unit matrix through `C` (the `RingHom.mapMatrix` of the
inclusion `C : R →+* MvPolynomial (RepCoord d) R`). -/
noncomputable def liftGauge (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    BaseChangeGroup (k := MvPolynomial (RepCoord d) R) d :=
  fun v ↦ Units.map (RingHom.mapMatrix (C : R →+* MvPolynomial (RepCoord d) R)).toMonoidHom (P v)

/-- `liftGauge` is a group homomorphism on the gauge group (it lifts `Units.map` of a monoid hom,
pointwise). Stated as the two facts the round-trip needs: it preserves `1` and `⁻¹` pointwise via the
defining `Units.map`. -/
theorem liftGauge_mul (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d) :
    liftGauge d (P * Q) = liftGauge d P * liftGauge d Q := by
  funext v
  simp only [liftGauge, Pi.mul_apply, map_mul]

@[simp] theorem liftGauge_one (d : Fin (N + 1) → ℕ) :
    liftGauge d (1 : BaseChangeGroup (k := R) d) = 1 := by
  funext v
  simp only [liftGauge, Pi.one_apply, map_one]

theorem liftGauge_inv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    liftGauge d (P⁻¹) = (liftGauge d P)⁻¹ := by
  funext v
  simp only [liftGauge, Pi.inv_apply, map_inv]

/-! ## The gauge substitution -/

/-- **The gauge substitution** `gaugeSub d P : RepCoord d → MvPolynomial (RepCoord d) R`: the
`⟨i, (r, c)⟩` coordinate maps to the `(r, c)` entry of the gauged generic factor
`baseChange (liftGauge d P) (genericTuple d) i = P_{i+1} · Xᵢ · P_i⁻¹` (units lifted by `C`). -/
noncomputable def gaugeSub (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    RepCoord d → MvPolynomial (RepCoord d) R :=
  fun x ↦ baseChange (liftGauge d P) (genericTuple d) x.1 x.2.1 x.2.2

/-- `aeval (gaugeSub P)` carries the generic factor `genericTuple i` to the gauged factor
`baseChange (liftGauge d P) (genericTuple d) i`. The generator goes to the corresponding entry by
definition of `gaugeSub`; `aeval_X` evaluates it. -/
theorem aeval_gaugeSub_genericTuple (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (i : Fin N) :
    (genericTuple d i).map (aeval (R := R) (gaugeSub d P))
      = baseChange (liftGauge d P) (genericTuple d) i := by
  funext r c
  rw [Matrix.map_apply, genericTuple_apply, aeval_X, gaugeSub]

/-! ## The ring hom commutes with the prefix product -/

/-- A coordinate substitution commutes with the generic prefix product: applying `aeval φ`
(rectangular `Matrix.map`) to `multPrefix (genericTuple d) j` gives the prefix product of the image
tuple `Ã i = (genericTuple d i).map (aeval φ)`. The `aeval`-analog of
`Core.MultComorphism.map_eval_multPrefix`. -/
theorem map_aeval_multPrefix (d : Fin (N + 1) → ℕ)
    (φ : RepCoord d → MvPolynomial (RepCoord d) R) (j : Fin (N + 1)) :
    (multPrefix d (genericTuple d) j).map (aeval (R := R) φ)
      = multPrefix d (fun i ↦ (genericTuple d i).map (aeval (R := R) φ)) j := by
  induction j using Fin.induction with
  | zero =>
    simp only [multPrefix_zero]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | succ i ih =>
    rw [multPrefix_succ, multPrefix_succ, Matrix.map_mul, ih]

/-- The full generic product under `aeval (gaugeSub P)` is `mult` of the gauged generic tuple:
`(Matrix.of (multPoly d)).map (aeval (gaugeSub P)) = mult d (baseChange (liftGauge d P)
(genericTuple d))`. Combines `map_aeval_multPrefix` with `aeval_gaugeSub_genericTuple`. -/
theorem map_aeval_gaugeSub_mult (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    (Matrix.of (multPoly d)).map (aeval (R := R) (gaugeSub d P))
      = mult d (baseChange (liftGauge d P) (genericTuple d)) := by
  have hof : (Matrix.of (multPoly d) : Matrix _ _ (MvPolynomial (RepCoord d) R))
      = multPrefix d (genericTuple d) (Fin.last N) := by
    funext r c; rfl
  have htup : (fun i ↦ (genericTuple d i).map (aeval (R := R) (gaugeSub d P)))
      = baseChange (liftGauge d P) (genericTuple d) := by
    funext i; exact aeval_gaugeSub_genericTuple d P i
  rw [hof, map_aeval_multPrefix d (gaugeSub d P) (Fin.last N), htup]
  rfl

/-! ## The mult-transport -/

/-- **mult-equivariance over a `CommRing`.** `mult d (P • A) = P_last · mult d A · P_0⁻¹`: the
interior units of the base change telescope away (`submult_baseChange` at the full interval,
through `mult_eq_submult`). The `Core.FibreNormalForm.mult_smul` proof is over a `Field`; this is
the same statement over the weaker `CommRing` (the proof uses only `CommRing` facts). -/
theorem mult_smul_commRing (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (A : Tuple (k := R) d) :
    mult d (baseChange P A)
      = Units.val (P (Fin.last N)) * mult d A * Units.val ((P 0)⁻¹) := by
  rw [mult_eq_submult, mult_eq_submult, submult_baseChange]

/-- **The mult-transport.** Applying `aeval (gaugeSub P)` to the generic product entry `multPoly d r
c` gives the `(r, c)` entry of `P_last · Matrix.of (multPoly d) · P_0⁻¹` (the end-vertex units lifted
by `C`); the interior units telescope away (`mult_smul`). For the endpoint normalization
(`P_0 = H`, `P_last = L⁻¹`, interior `= 1`) this is `L⁻¹ · multPoly · H⁻¹`. -/
theorem aeval_gaugeSub_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    aeval (R := R) (gaugeSub d P) (multPoly d r c)
      = ((Units.val (liftGauge d P (Fin.last N)) * Matrix.of (multPoly d)
            * Units.val ((liftGauge d P 0)⁻¹)
          : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) (MvPolynomial (RepCoord d) R)) r c) := by
  have h : aeval (R := R) (gaugeSub d P) (multPoly d r c)
      = ((Matrix.of (multPoly d)).map (aeval (R := R) (gaugeSub d P))) r c := rfl
  rw [h, map_aeval_gaugeSub_mult d P,
    mult_smul_commRing d (liftGauge d P) (genericTuple d)]
  rfl

/-! ## The composition law and the gauge `AlgEquiv` -/

/-- The entries of `Units.val (liftGauge d Q v)` are `C`-images: `(liftGauge d Q v).val = (Q v).val.map
C` (it is `Units.map (C.mapMatrix)` of `Q v`). -/
theorem liftGauge_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d) (v : Fin (N + 1)) :
    Units.val (liftGauge d Q v)
      = (Units.val (Q v)).map (C : R →+* MvPolynomial (RepCoord d) R) := by
  show Units.val (Units.map _ (Q v)) = _
  rw [Units.coe_map]
  rfl

/-- The entries of `Units.val ((liftGauge d Q v)⁻¹)` are `C`-images: `= (Q v)⁻¹.val.map C`. -/
theorem liftGauge_inv_val_eq (d : Fin (N + 1) → ℕ) (Q : BaseChangeGroup (k := R) d)
    (v : Fin (N + 1)) :
    Units.val ((liftGauge d Q v)⁻¹)
      = (Units.val ((Q v)⁻¹)).map (C : R →+* MvPolynomial (RepCoord d) R) := by
  show Units.val (Units.map _ (Q v))⁻¹ = _
  rw [Units.coe_map_inv]
  rfl

/-- A `C`-lifted (constant) gauge matrix is fixed by `aeval (gaugeSub P)`: its entries are `C`-images
in the coefficient ring, and `aeval` fixes constants (`aeval_C`). -/
theorem map_aeval_gaugeSub_liftGauge (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (v : Fin (N + 1)) :
    (Units.val (liftGauge d Q v)).map (aeval (R := R) (gaugeSub d P)) = Units.val (liftGauge d Q v)
    ∧ (Units.val ((liftGauge d Q v)⁻¹)).map (aeval (R := R) (gaugeSub d P))
        = Units.val ((liftGauge d Q v)⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [liftGauge_val_eq]
    funext a b
    rw [Matrix.map_apply, Matrix.map_apply, aeval_C, MvPolynomial.algebraMap_eq]
  · rw [liftGauge_inv_val_eq]
    funext a b
    rw [Matrix.map_apply, Matrix.map_apply, aeval_C, MvPolynomial.algebraMap_eq]

/-- **The composition law on the generic tuple.** Applying `aeval (gaugeSub P)` to the gauged
generic factor `baseChange (liftGauge Q) (genericTuple) i` re-gauges by `P` inside: the result is
`baseChange (liftGauge Q) (baseChange (liftGauge P) (genericTuple)) i`. The constant `C`-lifted
`Q`-matrices are fixed (`map_aeval_gaugeSub_liftGauge`), the variable block re-gauges
(`aeval_gaugeSub_genericTuple`). -/
theorem map_aeval_gaugeSub_baseChange (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (i : Fin N) :
    (baseChange (liftGauge d Q) (genericTuple d) i).map (aeval (R := R) (gaugeSub d P))
      = baseChange (liftGauge d Q) (baseChange (liftGauge d P) (genericTuple d)) i := by
  rw [baseChange_apply, baseChange_apply, Matrix.map_mul, Matrix.map_mul,
    (map_aeval_gaugeSub_liftGauge d P Q i.succ).1,
    (map_aeval_gaugeSub_liftGauge d P Q i.castSucc).2,
    aeval_gaugeSub_genericTuple d P i]

/-- The two `aeval (gaugeSub …)` directions compose to the identity on the generators: for any gauges
`P`, `Q`, `aeval (gaugeSub P) (gaugeSub Q x)` is the `x`-entry of `baseChange (liftGauge (Q * P))
(genericTuple)`. Specialized to `Q = P⁻¹` (resp. `P = Q⁻¹`) it collapses to `X x`. -/
theorem aeval_gaugeSub_gaugeSub (d : Fin (N + 1) → ℕ) (P Q : BaseChangeGroup (k := R) d)
    (x : RepCoord d) :
    aeval (R := R) (gaugeSub d P) (gaugeSub d Q x)
      = baseChange (liftGauge d (Q * P)) (genericTuple d) x.1 x.2.1 x.2.2 := by
  have h : aeval (R := R) (gaugeSub d P) (gaugeSub d Q x)
      = ((baseChange (liftGauge d Q) (genericTuple d) x.1).map
          (aeval (R := R) (gaugeSub d P))) x.2.1 x.2.2 := rfl
  rw [h, map_aeval_gaugeSub_baseChange d P Q x.1, ← baseChange_mul, liftGauge_mul]

/-- **The gauge `AlgEquiv`** of `MvPolynomial (RepCoord d) R`: `aeval (gaugeSub P)`, with inverse
`aeval (gaugeSub P⁻¹)`. The round-trips collapse by the group-action laws (`baseChange_mul` /
`baseChange_one`) on the generic tuple. The endpoint normalization instantiates `P`. -/
noncomputable def gaugeEquiv (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d) :
    MvPolynomial (RepCoord d) R ≃ₐ[R] MvPolynomial (RepCoord d) R :=
  AlgEquiv.ofAlgHom (aeval (gaugeSub d P)) (aeval (gaugeSub d P⁻¹))
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, inv_mul_cancel,
        liftGauge_one, baseChange_one, genericTuple_apply])
    (by
      apply MvPolynomial.algHom_ext
      intro x
      rw [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, aeval_gaugeSub_gaugeSub, mul_inv_cancel,
        liftGauge_one, baseChange_one, genericTuple_apply])

/-- `gaugeEquiv d P` acts as `aeval (gaugeSub d P)` (the forward `AlgHom` of the `ofAlgHom`). -/
@[simp] theorem gaugeEquiv_apply (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (p : MvPolynomial (RepCoord d) R) :
    gaugeEquiv d P p = aeval (R := R) (gaugeSub d P) p := rfl

/-- **The mult-transport, in `gaugeEquiv` form.** `gaugeEquiv d P` sends the generic product entry
`multPoly d r c` to the `(r, c)` entry of `P_last · multPoly · P_0⁻¹`. This is the bridge R2-3b-4
needs: with the endpoint gauge (`P_0 = H`, `P_last = L⁻¹`), it turns the chart target `mult(A) = LEH`
into `mult(Ã) = E`. -/
theorem gaugeEquiv_multPoly (d : Fin (N + 1) → ℕ) (P : BaseChangeGroup (k := R) d)
    (r : Fin (d (Fin.last N))) (c : Fin (d 0)) :
    gaugeEquiv d P (multPoly d r c)
      = ((Units.val (liftGauge d P (Fin.last N)) * Matrix.of (multPoly d)
            * Units.val ((liftGauge d P 0)⁻¹)
          : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) (MvPolynomial (RepCoord d) R)) r c) := by
  rw [gaugeEquiv_apply, aeval_gaugeSub_multPoly]

/-! ## Non-vacuity witnesses

(i) The identity gauge `P = 1` reproduces the identity `AlgEquiv` — the construction is honest at
`H = L = 1`. (ii) The transport on the `(2,2,2)` witness with a non-identity end-vertex gauge over
`ℚ` is the genuine conjugation `P_last · M · P_0⁻¹` of the generic product. -/

section Witness

/-- The identity gauge substitution is the identity on coordinates: `gaugeSub d 1 x = X x`. -/
theorem gaugeSub_one (d : Fin (N + 1) → ℕ) (x : RepCoord d) :
    gaugeSub d (1 : BaseChangeGroup (k := R) d) x = X x := by
  rw [gaugeSub, liftGauge_one, baseChange_one, genericTuple_apply]

/-- At the identity gauge the `AlgEquiv` is the identity (`H = L = 1` reproduces the identity) —
the construction is non-vacuous and honest. -/
example (d : Fin (N + 1) → ℕ) (p : MvPolynomial (RepCoord d) R) :
    gaugeEquiv d (1 : BaseChangeGroup (k := R) d) p = p := by
  rw [gaugeEquiv_apply]
  have : aeval (R := R) (gaugeSub d (1 : BaseChangeGroup (k := R) d))
      = AlgHom.id R (MvPolynomial (RepCoord d) R) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [aeval_X, gaugeSub_one, AlgHom.id_apply]
  rw [this, AlgHom.id_apply]

/-- The constant dimension vector `(2, 2, 2)` (every `d v = 2` definitionally, so the uniform gauge
type-checks without `![…]`-reduction friction). -/
def dConst : Fin 3 → ℕ := fun _ ↦ 2

/-- The uniform `(2,2,2)` gauge over `ℤ` carrying `witnessUnit` (`!![1,1;0,1]`) at every vertex. -/
def witnessGauge : BaseChangeGroup (k := ℤ) dConst := fun _ ↦ witnessUnit

/-- The gauge `AlgEquiv` is available at the concrete non-identity `(2,2,2)` gauge `witnessGauge` over
`ℤ` — the construction is non-vacuous at a genuine `!![1,1;0,1]`-conjugation. -/
noncomputable example :
    MvPolynomial (RepCoord dConst) ℤ ≃ₐ[ℤ] MvPolynomial (RepCoord dConst) ℤ :=
  gaugeEquiv dConst witnessGauge

/-- The mult-transport fires at the concrete non-identity gauge `witnessGauge`: `gaugeEquiv` carries
each generic product entry to the conjugation `P_last · multPoly · P_0⁻¹` of the generic product.
Non-vacuous (the gauge is the genuine `!![1,1;0,1]` at every vertex, not the identity). -/
example (r : Fin (dConst (Fin.last 2))) (c : Fin (dConst 0)) :
    gaugeEquiv (R := ℤ) dConst witnessGauge (multPoly dConst r c)
      = aeval (R := ℤ) (gaugeSub dConst witnessGauge) (multPoly dConst r c) :=
  gaugeEquiv_apply dConst witnessGauge (multPoly dConst r c)

end Witness

end DLNFibre.Core

codex
So far: radical-insensitivity helps remove reducedness, not the need to identify the radical/vanishing ideal of the chart after gauge. The next check is whether the repo has a generic “split ideal dimension” theorem strong enough to replace an explicit coordinate-ring equivalence.
exec
/bin/bash -lc "sed -n '1,260p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import DLNFibre.Core.IntegralDimension

/-!
# Dimension data of primes in a polynomial ring over a field (network-free engine)

The L5.5–L5.7 layer of the dimension-formula ladder, built on the integral-extension
dimension-invariance headline `ringKrullDim_eq_of_integral_injective` (L5.4) and the polynomial
dimension `ringKrullDim_mvPolynomial_fin_field` (L5.0).

For `R = MvPolynomial (Fin n) k` (`k` any field — `IsAlgClosed` is *not* needed for these pure
dimension facts) and a prime `p`:

* **L5.5** `ringKrullDim_quotient_eq_noetherRank` — `dim (R ⧸ p)` equals the Noether-normalization
  rank `s` of `R ⧸ p` (the number of algebraically-independent generators of the polynomial subring
  `k[y₁..y_s]` over which `R ⧸ p` is integral). Proved from Noether normalization
  (`exists_integral_inj_algHom_of_quotient`) + L5.4 + L5.0.

* **L5.7 (`≤` direction)** `height_add_coheight_le` — `height p + coheight p ≤ n`, equivalently
  `Ideal.primeHeight p + dim (R ⧸ p) ≤ n`. Chain concatenation, via
  `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty` and the polynomial dimension `= n`.

* **The polynomial-tower additive brick** `height_eq_height_under_add_height_map_quotient` — for the
  *one-variable* extension `A → A[X]` (`A` Noetherian, flat hence going-down) and a prime `P` of
  `A[X]`, `height P = height (P.under A) + height (P / (P.under A)·A[X])`. This is the load-bearing
  additive half of the catenary content (the `≥` direction), proved unconditionally from the flat
  going-down instance and `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`.

**The full equality is closed downstream.** This module proves only the `≤` half
(`primeHeight_add_ringKrullDim_quotient_le`). The catenary `≥` direction `height p ≥ n − dim(R/p)`
and the full headline equality `height p + dim (R ⧸ p) = n` are closed in
`Core.NoetherMonicPositioning` (`height_add_ringKrullDim_quotient_eq`), which imports this module
and reuses its additive tower brick above. Its standard proof inducts on `n`, peeling one variable
via that brick after a *monic-coordinate-positioning* step — a `k`-algebra coordinate change making
a nonzero element of `p` monic in the top variable, so `(A[X] ⧸ P)` is integral over `(A ⧸ q)` and
the quotient dimension is preserved. That positioning is Mathlib's Noether-normalization `T`
argument, `private` in `RingTheory.NoetherNormalization`; `Core.NoetherMonicPositioning` re-derives
the one public consequence it needs (`exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`), over any
field.
-/

open Order PrimeSpectrum

namespace DLNFibre.Core

/-! ### L5.5 — `dim (R ⧸ p)` equals the Noether-normalization rank -/

/-- **L5.5.** For a prime `p` of `R = k[x₁,…,xₙ]` (`k` a field), the Krull dimension of `R ⧸ p`
equals the Noether-normalization rank `s ≤ n`: there is an injective integral `k`-algebra map
`k[y₁,…,y_s] →ₐ[k] (R ⧸ p)`, and `dim (R ⧸ p) = s`. -/
theorem ringKrullDim_quotient_eq_noetherRank
    (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    ∃ s ≤ n, (∃ g : (MvPolynomial (Fin s) k) →ₐ[k] ((MvPolynomial (Fin n) k) ⧸ p),
      Function.Injective g ∧ g.IsIntegral) ∧
      ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p) = (s : WithBot ℕ∞) := by
  obtain ⟨s, hsn, g, hg_inj, hg_int⟩ :=
    exists_integral_inj_algHom_of_quotient p (Ideal.IsPrime.ne_top ‹_›)
  refine ⟨s, hsn, ⟨g, hg_inj, hg_int⟩, ?_⟩
  rw [ringKrullDim_eq_of_integral_injective (f := g.toRingHom) hg_int hg_inj,
    ringKrullDim_mvPolynomial_fin_field]

/-! ### L5.7 (`≤` direction) — `height p + coheight p ≤ n` -/

/-- **L5.7, easy half.** For a prime `p` of `R = k[x₁,…,xₙ]`, the height plus the coheight of `p`
is at most `n`: a chain below `p` spliced with a chain above `p` is a chain in `Spec R`, whose
dimension is `n`. (Order level, on the spectrum point.) -/
theorem height_add_coheight_le
    (k : Type*) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    (Order.height p : ℕ∞) + Order.coheight p ≤ (n : ℕ∞) := by
  have hk : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) = (n : WithBot ℕ∞) :=
    ringKrullDim_mvPolynomial_fin_field k n
  have hsup : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) k))
      = ((⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k),
          Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) :=
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty
  have hmem : (Order.height p + Order.coheight p : ℕ∞)
      ≤ ⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k), Order.height a + Order.coheight a :=
    le_iSup (fun a ↦ Order.height a + Order.coheight a) p
  have hcoe : ((⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k),
        Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) :=
    hsup ▸ hk
  calc (Order.height p + Order.coheight p : ℕ∞)
      ≤ ⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k), Order.height a + Order.coheight a := hmem
    _ = (n : ℕ∞) := by exact_mod_cast hcoe

/-- **L5.7, easy half (ideal form).** For a prime `p` of `R = k[x₁,…,xₙ]`,
`Ideal.primeHeight p + dim (R ⧸ p) ≤ n`. -/
theorem primeHeight_add_ringKrullDim_quotient_le
    (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (Ideal.primeHeight p : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p)
      ≤ (n : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient_eq_coheight ⟨p, ‹_›⟩]
  have h := height_add_coheight_le k n ⟨p, ‹_›⟩
  rw [Ideal.primeHeight]
  exact_mod_cast h

/-! ### The polynomial-tower additive brick (the `≥`/catenary additive half) -/

/-- **Additive height law on the one-variable tower.** For `A` Noetherian and a prime `P` of `A[X]`
lying over `q = P.under A`, `height P = height q + height (image of P in (A ⧸ q)[X])`. The
extension `A → A[X]` is free hence flat, so it satisfies going-down
(`Algebra.HasGoingDown.of_flat`), and the equality is
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`. This is the load-bearing additive half of
the catenary content for polynomial rings. -/
theorem height_eq_height_under_add_height_map_quotient
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P : Ideal (Polynomial A)) [P.IsPrime] :
    P.height = (P.under A).height +
      (P.map (Ideal.Quotient.mk ((P.under A).map (algebraMap A (Polynomial A))))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under A) P

/-! ### Non-vacuity witnesses -/

/-- Witness for `ringKrullDim_quotient_eq_noetherRank`: for the zero prime of `k[x]` the Noether
rank `s` it produces is `1` (not the degenerate `0`), since `dim (k[x] ⧸ ⊥) = dim k[x] = 1`. -/
example (k : Type*) [Field k] :
    ∃ s : ℕ, (s : WithBot ℕ∞) = (1 : WithBot ℕ∞) ∧
      ringKrullDim ((MvPolynomial (Fin 1) k) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) k)))
        = (s : WithBot ℕ∞) := by
  obtain ⟨s, _, _, hdim⟩ := ringKrullDim_quotient_eq_noetherRank k 1 ⊥
  refine ⟨s, ?_, hdim⟩
  rw [← hdim, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    ringKrullDim_mvPolynomial_fin_field, Nat.cast_one]

/-- Witness that the additive tower law is non-vacuous: `ℤ[X]` is Noetherian, the law applies to its
prime `(X)`. -/
example : (Ideal.span {Polynomial.X} : Ideal (Polynomial ℤ)).IsPrime := by
  rw [Ideal.span_singleton_prime Polynomial.X_ne_zero]; exact Polynomial.prime_X

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Krull dimension of integral extensions (network-free engine)

General commutative-algebra bedrock for the L5 dimension-formula ladder: the Krull dimension is
invariant under an integral injective ring extension. The route is the integral-extension
(trdeg-light) one — strict-mono `comap` for going-up (`≤` one way) and lying-over surjectivity for
going-up the other way (`≤` the other way) — assembled into the dimension-invariance headline
`ringKrullDim_eq_of_integral_injective`. Two supporting general facts are also recorded:
`MvPolynomial` dimension over a field (`ringKrullDim_mvPolynomial_field`) and the quotient/coheight
identity (`ringKrullDim_quotient_eq_coheight`).

All statements are at `RingHom` / `Algebra` generality (commutative rings); `IsDomain` / `Field`
appear only where genuinely needed. No new cited interfaces — every step is a proved Mathlib lemma.
-/

open Order PrimeSpectrum

namespace DLNFibre.Core

variable {R S A : Type*}

/-! ### L5.0 — dimension of a polynomial ring over a field -/

/-- The Krull dimension of `k[x₁,…,xₙ]` over a field `k` is `n`. -/
theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (ι : Type*) [Finite ι] :
    ringKrullDim (MvPolynomial ι k) = Nat.card ι := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k, zero_add]

/-- Specialisation of `ringKrullDim_mvPolynomial_field` to `Fin n`: `dim k[x₁,…,xₙ] = n`. -/
theorem ringKrullDim_mvPolynomial_fin_field (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [ringKrullDim_mvPolynomial_field k (Fin n), Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### L5.1 — `dim (R ⧸ p) = coheight p` -/

/-- For a prime `p`, the closed subscheme `Spec (R ⧸ p)` is order-isomorphic to `Set.Ici p`. -/
noncomputable def primeSpectrumQuotientOrderIsoIci [CommRing R] (p : PrimeSpectrum R) :
    PrimeSpectrum (R ⧸ p.asIdeal) ≃o Set.Ici p :=
  (p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus).trans
    (OrderIso.setCongr _ _ (by
      ext x
      rw [Set.mem_Ici, mem_zeroLocus, ← PrimeSpectrum.asIdeal_le_asIdeal]
      rfl))

/-- The Krull dimension of `R ⧸ p` equals the coheight of `p` in `Spec R`. -/
theorem ringKrullDim_quotient_eq_coheight [CommRing R] (p : PrimeSpectrum R) :
    ringKrullDim (R ⧸ p.asIdeal) = (coheight p : WithBot ℕ∞) := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso (primeSpectrumQuotientOrderIsoIci p),
    ← coheight_eq_krullDim_Ici]

/-! ### L5.2 / L5.3 — the two inequalities for an integral injective extension -/

/-- For an integral extension, `comap` of the algebra map is strictly monotone on primes. -/
theorem strictMono_comap_of_isIntegral [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    StrictMono (comap (algebraMap R S)) := by
  intro a b hab
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hab ⊢
  obtain ⟨hle, x, hxb, hxa⟩ := SetLike.lt_iff_le_and_exists.mp hab
  simpa only [comap_asIdeal] using
    Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxb, hxa⟩ (Algebra.IsIntegral.isIntegral x)

/-- Integral extension: `dim S ≤ dim A` (going-up via strict-mono `comap`; injectivity unneeded). -/
theorem ringKrullDim_le_of_integral [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim A := by
  algebraize [f]
  exact krullDim_le_of_strictMono _ strictMono_comap_of_isIntegral

/-- Going-up chain lift: an integral extension lifts any prime chain in `A` to a prime chain in `S`
of the same length, with matching last element. -/
theorem exists_ltSeries_comap_last_of_isIntegral [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.IsIntegral A S] (hinj : Function.Injective (algebraMap A S))
    (p : LTSeries (PrimeSpectrum A)) :
    ∃ q : LTSeries (PrimeSpectrum S), q.length = p.length ∧
      comap (algebraMap A S) q.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨Q, _, hQ, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥
      (by rw [Ideal.comap_bot_of_injective (algebraMap A S) hinj]; exact bot_le)
    refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, ?_⟩
    apply PrimeSpectrum.ext
    simpa only [comap_asIdeal] using hcomap
  | snoc p x hx hp =>
    obtain ⟨q, hlen, hlast⟩ := hp
    have hle : (q.last.asIdeal.comap (algebraMap A S)) ≤ x.asIdeal := by
      rw [show q.last.asIdeal.comap (algebraMap A S) = (comap (algebraMap A S) q.last).asIdeal from
        rfl, hlast]
      exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hx |>.le
    obtain ⟨Q, hQge, hQ, hcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal q.last.asIdeal hle
    have hlt : q.last < ⟨Q, hQ⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine lt_of_le_of_ne hQge fun heq ↦ ?_
      have : (comap (algebraMap A S) q.last).asIdeal = x.asIdeal := by
        rw [comap_asIdeal, heq]; exact hcomap
      rw [hlast] at this
      exact absurd (PrimeSpectrum.ext this) (ne_of_lt hx)
    refine ⟨q.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], ?_⟩
    apply PrimeSpectrum.ext
    simpa only [RelSeries.last_snoc, comap_asIdeal] using hcomap

/-- Integral injective extension: `dim A ≤ dim S` (going-up chain lift). -/
theorem ringKrullDim_ge_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim A ≤ ringKrullDim S := by
  algebraize [f]
  rw [ringKrullDim, ringKrullDim, krullDim, iSup_le_iff]
  intro p
  obtain ⟨q, hlen, _⟩ := exists_ltSeries_comap_last_of_isIntegral (S := S) hinj p
  rw [← hlen]
  exact q.length_le_krullDim

/-! ### L5.4 — the headline: dimension invariance -/

/-- Krull dimension is invariant under an integral injective ring extension. -/
theorem ringKrullDim_eq_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim S = ringKrullDim A :=
  le_antisymm (ringKrullDim_le_of_integral hf)
    (ringKrullDim_ge_of_integral_injective hf hinj)

/-! ### Non-vacuity witnesses -/

/-- Witness for `ringKrullDim_mvPolynomial_fin_field`: `dim ℚ[x] = 1` (a nonzero, finite value). -/
example : ringKrullDim (MvPolynomial (Fin 1) ℚ) = 1 := by
  rw [ringKrullDim_mvPolynomial_fin_field ℚ 1, Nat.cast_one]

/-- Witness that the headline's hypothesis bundle is inhabited and its conclusion fires: the
identity ring hom is integral and injective, recovering `dim R = dim R`. (The substantive content —
that an integral injective extension can change the *ring* without changing the dimension — is
exercised downstream where Noether normalization is applied.) -/
example (R : Type*) [CommRing R] : ringKrullDim R = ringKrullDim R :=
  ringKrullDim_eq_of_integral_injective
    (RingHom.isIntegral_of_surjective (RingHom.id R) Function.surjective_id)
    Function.injective_id

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,180p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Ideal.GoingDown
import DLNFibre.Core.MultComorphism

/-!
# `DLNFibre.Core.ChartFlatnessProbe` — the G2a chart-flatness API-surface contract

**Status: API contract / thermometer artefact, NOT a theorem.** Thread 09 (2026-06-23) is the GATING
probe for route **M-goingdown** of the rank-chart fibre-codimension build: localize F1's `multComap`
at the pivot minor and ask whether the chart-localized total ring is **flat** (via free, through the
Schur section) over the chart-localized base ring — which would feed the LANDED going-down
additivity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`.

This module records the **verified-present localization + flatness API** as `example`-blocks
(durable pins), and states — without `sorry` — the precise SHAPE of the gating object, so the
verdict rests on confirmed contracts rather than recalled signatures.

**The verdict (in the thread report):** the localization + flatness *API* is present at v4.29
and the localized comorphism `Localization.Away.mapₐ` is constructible. But the *object* route
M-goingdown needs flat is NOT the global `multComap` — that map is provably **not flat** (the fibre
dimension jumps 4 → 5 as the target degenerates rank 1 → rank 0 on the `(2,2,2)` anchor, recorded in
`Core.FibreCodim`). The flatness lives only on the **exact-rank determinantal chart**, whose
base/total rings are quotients by determinantal ideals carried in the engine ONLY as opaque
`vanishingIdeal`s — so the Schur section cannot be exhibited as an `AlgEquiv` without first building
an explicit presentation of those quotient rings (a determinantal-algebra build). See the report.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core.ChartFlatProbe

open scoped TensorProduct
open MvPolynomial

universe u

/-! ## The localized comorphism exists (the chart-localized `algebraMap`)

`Localization.Away.mapₐ f a : Localization.Away a →ₐ[R] Localization.Away (f a)` is the localized
algebra map. Specialised to F1's `multComap d` and a pivot element `Δ` of the base coordinate ring,
it IS the chart-localized comorphism the route wants — its mere existence is not the wall. -/

/-- **The chart-localized comorphism exists.** For a base-ring element `Δ` (the pivot minor in
target coords), `Localization.Away.map` builds the localized comorphism of `mult`:
`(R_base)[1/Δ] →ₐ[k] (R_tot)[1/multComap Δ]`. Construction, not flatness. -/
noncomputable example {k : Type u} [Field k] {N : ℕ} (d : Fin (N + 1) → ℕ)
    (Δ : MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k)
    (Rb : Type u) [CommRing Rb] [Algebra (MvPolynomial (Fin (d (Fin.last N)) × Fin (d 0)) k) Rb]
    [IsLocalization.Away Δ Rb]
    (Rt : Type u) [CommRing Rt] [Algebra (MvPolynomial (RepCoord d) k) Rt]
    [IsLocalization.Away (multComap d Δ) Rt] :
    Rb →+* Rt :=
  IsLocalization.Away.map Rb Rt (multComap d).toRingHom Δ

/-! ## Localization is always flat over the base (`IsLocalization.flat`)

The localization `R[1/Δ]` is flat over `R` — present and unconditional. This is the EASY flatness
(localizing a single ring); it is NOT the route's flatness (total-over-base via the comorphism). -/

/-- A localization is flat over the ring it localizes (`IsLocalization.flat`). -/
example {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] : Module.Flat R S :=
  IsLocalization.flat S M

/-! ## The route's flatness, stated honestly as a hypothesis (the gating object)

The fact route M-goingdown needs: total-localized FLAT over base-localized THROUGH the comorphism,
with the base/total being the EXACT-RANK quotient rings (not the full polynomial rings). The engine
has no explicit presentation of those quotient rings, so we can only *state* the target as a
hypothesis here — this `example` pins its TYPE (the going-down consumer), not a proof. -/

/-- **The going-down consumer.** Given the route's flatness as a `[Module.Flat]` instance on a tower
`Rb → Rt`, the LANDED height-additivity fires — confirming the gating fact, once proved, needs no
hypothesis beyond Noetherianity. This is the contract the chart-flatness proof must discharge. -/
example {Rb Rt : Type u} [CommRing Rb] [CommRing Rt] [Algebra Rb Rt] [IsNoetherianRing Rb]
    [IsNoetherianRing Rt] [Module.Flat Rb Rt]
    (p : Ideal Rb) [p.IsPrime] (P : Ideal Rt) [P.IsPrime] [P.LiesOver p] :
    P.height = p.height + (P.map (Ideal.Quotient.mk (p.map (algebraMap Rb Rt)))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P

/-! ## The Schur-freeness model shape (free total over base on a TRIVIALIZED chart)

The correct trivialization (decorrelated-Codex, 2026-06-23) is NOT a polynomial algebra: the fibre
over `E` is **reducible** (`F_E = k[u,v,X,Z,ℓ,m]/(uX+vZ−1, ℓm)` for the anchor — note the `ℓm = 0`
relation), so the chart is the BASE CHANGE `Rt ≃ₐ[Rb] Rb ⊗[k] F_E`, not `MvPolynomial _ Rb`. Over a
field `k` the fibre `F_E` is free as a `k`-module (every vector space is free), so the base change
is free, hence flat, over `Rb`. This pins what the Schur section must DELIVER; the wall is building
the trivializing `AlgEquiv` from the engine's opaque `vanishingIdeal`-quotients, not the closer. -/

/-- The base change `Rb ⊗[k] F` of a `k`-module `F` is free over `Rb` (over a field, `F` is free) —
the `Algebra.TensorProduct.instFree` lever the corrected Schur trivialization closes on. -/
example {k : Type u} [Field k] (Rb F : Type u) [CommRing Rb] [Algebra k Rb]
    [AddCommGroup F] [Module k F] : Module.Free Rb (Rb ⊗[k] F) := inferInstance

/-- **The Schur closer (model, corrected).** A chart trivialization `Rt ≃ₐ[Rb] Rb ⊗[k] F_E` to the
base change of the (reducible, free-over-`k`) fibre algebra `F_E` makes `Rt` free, hence flat, over
`Rb` — the one-liner the route ends on, once the trivializing `AlgEquiv` exists. -/
example {k : Type u} [Field k] (Rb Rt F : Type u) [CommRing Rb] [CommRing Rt] [Algebra k Rb]
    [AddCommGroup F] [Module k F] [Algebra Rb Rt] (e : Rt ≃ₗ[Rb] Rb ⊗[k] F) :
    Module.Flat Rb Rt :=
  Module.Flat.of_linearEquiv e

end DLNFibre.Core.ChartFlatProbe

exec
/bin/bash -lc "sed -n '1,220p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# `DLNFibre.Core.FlatTrivialProductProbe` — the L1-0 `Module.Flat` API-surface contract

**Status: API contract / checkpoint artefact, NOT the L1-0 theorem.** L1-0 (flatness of `mult`
restricted to a rank-`r` chart) was **checkpointed, not proved** (thread 04, 2026-06-23): the
`Module.Flat` *API* is fully viable at Mathlib v4.29 — every lever the local-triviality⟹trivial-
product⟹free⟹flat route needs is present and compiles (the `example`-blocks below are the durable
pins) — but the route is **unreachable this run** because the prerequisite object is missing: there
is no coordinate-ring pullback `A →+* B` of `mult` (the engine carries `mult` only as a *set-level*
function on `Tuple d`, with codim read through `vanishingIdeal`/`Ideal.height`; no `Spec`, no
scheme, no algebra map between the base/total coordinate quotient rings). Building that ring map +
the
determinantal chart localisation + the section-of-the-torsor trivialisation is a from-scratch
affine-AG construction (≈ 8–12 modules), not an API gap. See the thread-04 report for the verdict
and the recommended fallback (the two-inequality dimension sandwich).

This module records the **verified-present API** as `example`-blocks so the next attempt (or the
real L1-0, once the ring map exists) can stand on confirmed contracts rather than re-probing.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core.FlatProbe

open scoped TensorProduct

universe u

/-! ## Free ⟹ flat, and the polynomial / tensor trivial-product shapes -/

/-- Free modules are flat (instance), the base of the route. -/
example (A M : Type u) [CommRing A] [AddCommGroup M] [Module A M] [Module.Free A M] :
    Module.Flat A M := inferInstance

/-- `MvPolynomial (Fin r) A` is free, hence flat, over `A` — the trivial-product model fibre. -/
example (A : Type u) [CommRing A] (r : ℕ) :
    Module.Flat A (MvPolynomial (Fin r) A) := inferInstance

/-- Tensor of frees is free over the base — the `A ⊗ F` trivial-product shape. -/
example (A F : Type u) [CommRing A] [AddCommGroup F] [Module A F] [Module.Free A F] :
    Module.Free A (A ⊗[A] F) := inferInstance

/-! ## Transport flatness across an equivalence (the "B ≃ free" closer) -/

/-- Flatness transports across a linear equivalence. -/
example (A M N : Type u) [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Flat A M] (e : N ≃ₗ[A] M) : Module.Flat A N :=
  Module.Flat.of_linearEquiv e

/-- Flatness transports across an *algebra* equivalence: `B ≃ₐ[A] (free A-algebra)` gives
`Module.Flat A B` — the one-liner the route ends on, once such an equivalence exists. -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (e : B ≃ₐ[A] MvPolynomial (Fin r) A) : Module.Flat A B :=
  Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Flatness composes along a tower `A → S → M` (`Module.Flat.trans`). -/
example (A S M : Type u) [CommRing A] [CommRing S] [AddCommGroup M] [Algebra A S]
    [Module A M] [Module S M] [IsScalarTower A S M] [Module.Flat A S] [Module.Flat S M] :
    Module.Flat A M := Module.Flat.trans A S M

/-! ## Flat-local-on-base, scheme-free (the local-triviality lever, when the ring map exists)

`mult : Σ^r → Mat^{rk=r}` is Zariski-*locally* (not globally) trivial, so the route needs a
flat-local-on-base lemma. Mathlib v4.29 has it at the **ring/module level, no schemes** — the
levers to glue per-chart freeness into global flatness over the base. They are unusable here only
because no `algebraMap A B` for `mult` exists yet. -/

/-- **Module-level flat-local-on-base.** To prove `Module.Flat R M` it suffices to prove flatness of
`LocalizedModule.Away r M` for each `r` in a spanning set `s ⊆ S` (a principal-open cover) — the
scheme-free local-triviality lever (`Module.flat_of_localized_span`). -/
example (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    (s : Set R) (spn : Ideal.span s = ⊤)
    (h : ∀ r : s, Module.Flat R (LocalizedModule.Away r.1 M)) : Module.Flat R M :=
  Module.flat_of_localized_span (S := R) (M := M) s spn h

/-- **Ring-hom-level flat-local-on-base.** `RingHom.Flat` is a local property: its `propertyIsLocal`
bundles `ofLocalizationSpanTarget`, `ofLocalizationSpan`, composition stability, and iso-respect —
the descent package for gluing per-chart flatness of a ring map. -/
example : RingHom.PropertyIsLocal @RingHom.Flat := RingHom.Flat.propertyIsLocal

/-! ## Downstream levers (NOT in L1-0 scope — confirming they sit on `Module.Flat`)

These belong to L1-1 (a later tide); pinned here only to confirm the flatness fact, once proved,
feeds the height-additivity squeeze with no further hypothesis beyond Noetherianity. -/

/-- Flat ⟹ going-down (instance). -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] :
    Algebra.HasGoingDown A B := inferInstance

/-- The height-additivity lemma sits on going-down + Noetherianity (both rings Noetherian). -/
example (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [IsNoetherianRing B] [Algebra.HasGoingDown A B]
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    P.height = p.height + (P.map (Ideal.Quotient.mk (p.map (algebraMap A B)))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P

end DLNFibre.Core.FlatProbe

codex
The probe modules are consistent with a negative answer for the inequality squeeze: flatness and the product/free closer are easy only after a trivializing equivalence exists. I’m checking the base chart presentation to see whether a “polynomial extension instead of tensor” target would avoid any of the hard part.
exec
/bin/bash -lc "sed -n '1,430p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.DeterminantalBaseElimination
import DLNFibre.Core.DeterminantalChartRing
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# `DLNFibre.Core.DeterminantalBasePresentation` — the localized base presentation `A_loc/Iad ≅ Sd`

The final identification of `G2-2`: the localized determinantal base ring `A_loc = Localization.Away
detΔ`, modulo its base ideal `Iad`, is the free Schur localization `Sd` (`= Localization.Away
detSchurS`) — a regular ring of dimension `δ`. The eliminated `B22` block (`B22 = B21 Δ⁻¹ B12`) is
forced by the Schur relation once `detΔ` is inverted.

**The route (Codex-vetted, thread-13 `codex-g22c-route` consult).** The localized block equivalence
`Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd` (localizing the LANDED `blockAlgEquiv` at `detΔ ↦
C detSchurS`) carries `Iad` to a prime of `MvPolynomial B22block Sd`. The forced-block graph ideal
`J = graphIdeal forcedB22` (the genuine forced value `B21 adjΔ B12 / detΔ ∈ Sd`) satisfies:

1. **`height J = C`** — the translation automorphism maps `J` to the coordinate ideal, whose height
   is `#B22block = C` (LANDED `height_coordIdeal_localization_eq`).
2. **`J ⊆ Ψ(Iad)`** — each generator `X_b − C(forcedB22 b)` is, up to the unit `C detSchurS`, the
   image under `Ψ` of the bordered `(r+1)`-minor (LANDED `det_submatrix_multPoly_mem_sigmaIdeal`),
   which lies in `Iad`. This carries the actual Schur content.
3. **`Iad = J`** — by `Ideal.height_strict_mono_of_is_prime` (both prime, `height Ψ(Iad) = height
   Iad = C = height J`, `J ⊆ Ψ(Iad)` ⟹ no strict containment ⟹ equal). This honestly **earns** the
   hard direction `Iad ⊆ J`.

Then `A_loc/Iad ≅ (MvPolynomial B22block Sd)/J ≅ Sd` via `graphIdealQuotientEquiv`. `J` stays
internal; the domain / dimension `δ` follow from `Sd` being a polynomial localization.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

universe u

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The localized block equivalence `Ψ`

`Sd := Localization.Away detSchurS`, `Q := MvPolynomial B22block Sd`. We use `Localization` (the
canonical localization) so the `k`-algebra instances on `Sd` and `Q` resolve automatically. -/

/-- The free Schur localization `Sd = Localization.Away detSchurS` — the downstream-composable base
ring (a regular ring of dimension `δ`). -/
abbrev SchurLoc (q p r : ℕ) : Type u :=
  Localization.Away (detSchurS (k := k) q p r)

/-- **The localized block equivalence** `Ψ : A_loc ≃ₐ[k] MvPolynomial B22block Sd`, localizing the
LANDED `blockAlgEquiv` at `detΔ` (which maps to `C detSchurS`). -/
noncomputable def blockAlgEquivLoc (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Localization.Away (detPivotPoly (k := k) q p r hp hq)
      ≃ₐ[k] MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r) := by
  -- the scalar tower `k → B → Q`
  haveI tower : IsScalarTower k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
    have hkB : (algebraMap k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))) x
        = C (algebraMap k (MvPolynomial (SchurVar q p r) k) x) := by
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (SchurVar q p r) k)
        (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))]; rfl
    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) x
        = C (algebraMap k (SchurLoc (k := k) q p r) x) := by
      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
    rw [hkB, hkQ, algebraMap_def, MvPolynomial.map_C]
    congr 1
  -- `Q` is the localization of `B` at `powers (C detSchurS)`
  haveI hloc : IsLocalization (Submonoid.powers (C (detSchurS (k := k) q p r) :
      MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k)))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    simpa [Submonoid.map_powers] using
      (MvPolynomial.isLocalization (σ := B22block q p r)
        (M := Submonoid.powers (detSchurS (k := k) q p r))
        (S := SchurLoc (k := k) q p r))
  have H : Submonoid.map (blockAlgEquiv (k := k) q p r hp hq)
        (Submonoid.powers (detPivotPoly q p r hp hq))
      = Submonoid.powers (C (detSchurS (k := k) q p r)) := by
    rw [Submonoid.map_powers, blockAlgEquiv_detPivot]
  exact IsLocalization.algEquivOfAlgEquiv
    (Localization.Away (detPivotPoly (k := k) q p r hp hq))
    (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
    (blockAlgEquiv q p r hp hq) H

/-! ## The bordered `(r+1)`-minor `m_b` and its `blockAlgEquiv` image `(*)`

For a `B22` entry `(a', b')` the bordered `(r+1)×(r+1)` minor `m_b` of the generic product (rows
`[pivots, r+a']`, columns `[pivots, r+b']`) lies in the base ideal (an `(r+1)`-minor), and under
`blockAlgEquiv` becomes `C detSchurS · X (a', b') − C (forcedNum a' b')` (the bordered Schur minor
identity, transported). Dividing by the unit `C detSchurS` lands `X (a', b') − C (forcedB22 …)` in
`Ψ(Iad)`. -/

/-- The four blocks of the bordered minor at the `B22` entry `(a', b')` (entries are coordinate
variables of `multPoly`). Pivot block `Δ`, pivot-row × non-pivot-col `u`, non-pivot-row × pivot-col
`v`, corner `d`. The non-pivot index is the landed reindex form `Fin.cast (natAdd r ·)`. -/
noncomputable def borderΔ (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Matrix (Fin r) (Fin r) (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun i j ↦ (Matrix.of (multPoly (dStratum q p))) (Fin.castLE hp i) (Fin.castLE hq j)

noncomputable def borderU (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (b' : Fin (q - r)) :
    Matrix (Fin r) Unit (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun i _ ↦ (Matrix.of (multPoly (dStratum q p))) (Fin.castLE hp i)
    (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b'))

noncomputable def borderV (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (a' : Fin (p - r)) :
    Matrix Unit (Fin r) (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun _ j ↦ (Matrix.of (multPoly (dStratum q p)))
    (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a')) (Fin.castLE hq j)

noncomputable def borderD (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    Matrix Unit Unit (MvPolynomial (RepCoord (dStratum q p)) k) :=
  Matrix.of fun _ _ ↦ (Matrix.of (multPoly (dStratum q p)))
    (Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a'))
    (Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b'))

/-- The `SchurVar`-side pivot block `ΔS` (whose determinant is `detSchurS`). -/
noncomputable def schurΔ (q p r : ℕ) : Matrix (Fin r) (Fin r) (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun i j ↦ X (Sum.inl (i, j))

/-- The `SchurVar`-side `B12` column `uS` at non-pivot column `b'` (the `b'`-th column of `B12`). -/
noncomputable def schurU (q p r : ℕ) (b' : Fin (q - r)) :
    Matrix (Fin r) Unit (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun i _ ↦ X (Sum.inr (Sum.inl (i, b')))

/-- The `SchurVar`-side `B21` row `vS` at non-pivot row `a'` (the `a'`-th row of `B21`). -/
noncomputable def schurV (q p r : ℕ) (a' : Fin (p - r)) :
    Matrix Unit (Fin r) (MvPolynomial (SchurVar q p r) k) :=
  Matrix.of fun _ j ↦ X (Sum.inr (Sum.inr (a', j)))

/-- The bordered minor `m_b`: the determinant of the `multPoly` submatrix on rows `[pivots, r+a']`
and columns `[pivots, r+b']`. -/
noncomputable def borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) : MvPolynomial (RepCoord (dStratum q p)) k :=
  ((Matrix.of (multPoly (dStratum q p))).submatrix
    (Sum.elim (fun i : Fin r ↦ Fin.castLE hp i)
      (fun _ : Unit ↦ Fin.cast (show r + (p - r) = p by omega) (Fin.natAdd r a')))
    (Sum.elim (fun j : Fin r ↦ Fin.castLE hq j)
      (fun _ : Unit ↦ Fin.cast (show r + (q - r) = q by omega) (Fin.natAdd r b')))).det

/-- The bordered minor is the determinant of `fromBlocks borderΔ borderU borderV borderD`. -/
theorem borderMinor_eq_fromBlocks (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    borderMinor (k := k) q p r hp hq a' b'
      = (Matrix.fromBlocks (borderΔ (k := k) q p r hp hq) (borderU q p r hp hq b')
          (borderV q p r hp hq a') (borderD q p r hp hq a' b')).det := by
  rw [borderMinor]
  congr 1
  refine Matrix.ext (fun i j ↦ ?_)
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.submatrix_apply, Sum.elim_inl, Sum.elim_inr,
      borderΔ, borderU, borderV, borderD, Matrix.of_apply]

/-- **The bordered minor lies in the base ideal `sigmaIdeal`** (it is an `(r+1)`-minor of the
product, `det_submatrix_multPoly_mem_sigmaIdeal` after the `Fin r ⊕ Unit ≃ Fin (r+1)` reindex). -/
theorem borderMinor_mem_sigmaIdeal (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    borderMinor (k := k) q p r hp hq a' b' ∈ sigmaIdeal (k := k) (dStratum q p) r := by
  rw [borderMinor]
  set e : (Fin r ⊕ Unit) ≃ Fin (r + 1) :=
    (Equiv.sumCongr (Equiv.refl (Fin r)) finOneEquiv.symm).trans finSumFinEquiv with he
  rw [← det_submatrix_equiv_self e.symm, submatrix_submatrix]
  exact det_submatrix_multPoly_mem_sigmaIdeal (dStratum q p) _ _

/-- Each bordered block maps under `blockAlgEquiv` to the `C`-image of its `SchurVar`-side block
landed coordinate-image lemmas), or to the `B22` corner variable. -/
theorem blockAlgEquiv_borderΔ (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    (borderΔ (k := k) q p r hp hq).map (blockAlgEquiv (k := k) q p r hp hq)
      = (schurΔ (k := k) q p r).map C := by
  refine Matrix.ext (fun i j ↦ ?_)
  rw [Matrix.map_apply, Matrix.map_apply, borderΔ, Matrix.of_apply, multPoly_stratum_apply,
    schurΔ, Matrix.of_apply]
  exact blockAlgEquiv_X_pivot q p r hp hq i j

theorem blockAlgEquiv_borderU (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (b' : Fin (q - r)) :
    (borderU (k := k) q p r hp hq b').map (blockAlgEquiv (k := k) q p r hp hq)
      = (schurU (k := k) q p r b').map C := by
  refine Matrix.ext (fun i u ↦ ?_)
  rw [Matrix.map_apply, Matrix.map_apply, borderU, Matrix.of_apply, multPoly_stratum_apply,
    schurU, Matrix.of_apply]
  exact blockAlgEquiv_X_b12 q p r hp hq i b'

theorem blockAlgEquiv_borderV (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) (a' : Fin (p - r)) :
    (borderV (k := k) q p r hp hq a').map (blockAlgEquiv (k := k) q p r hp hq)
      = (schurV (k := k) q p r a').map C := by
  refine Matrix.ext (fun u j ↦ ?_)
  rw [Matrix.map_apply, Matrix.map_apply, borderV, Matrix.of_apply, multPoly_stratum_apply,
    schurV, Matrix.of_apply]
  exact blockAlgEquiv_X_b21 q p r hp hq a' j

theorem blockAlgEquiv_borderD (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    (borderD (k := k) q p r hp hq a' b').map (blockAlgEquiv (k := k) q p r hp hq)
      = Matrix.of fun _ _ : Unit ↦ (X (a', b') : MvPolynomial (B22block q p r)
          (MvPolynomial (SchurVar q p r) k)) := by
  refine Matrix.ext (fun u v ↦ ?_)
  rw [Matrix.map_apply, borderD, Matrix.of_apply, multPoly_stratum_apply, Matrix.of_apply]
  exact blockAlgEquiv_X_b22 q p r hp hq a' b'

/-- The numerator bridge: the bordered Schur numerator (row `a'` of `B21`, `adjugate Δ`, column `b'`
of `B12`) is the `(a', b')` entry of the full `forcedNum = B21 · adjugate Δ · B12`. -/
theorem schurNum_eq_forcedNum (q p r : ℕ) (a' : Fin (p - r)) (b' : Fin (q - r)) :
    (schurV (k := k) q p r a' * (schurΔ (k := k) q p r).adjugate * schurU (k := k) q p r b')
        default default
      = (forcedNum (k := k) q p r) a' b' := by
  rw [forcedNum, schurΔ, schurU, schurV]
  simp [Matrix.mul_apply]

/-- **`(*)` the bordered Schur minor identity, transported.** `blockAlgEquiv (m_b) =
C detSchurS · X (a', b') − C (forcedNum a' b')`. Via `AlgEquiv.map_det` + `Matrix.fromBlocks_map` +
`det_fromBlocks_scalar_eq` on the mapped (`SchurVar`-`C`) blocks; `det (ΔS.map C) = C detSchurS`,
the numerator collapses to `C (forcedNum a' b')` (`schurNum_eq_forcedNum`). -/
theorem blockAlgEquiv_borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    blockAlgEquiv (k := k) q p r hp hq (borderMinor q p r hp hq a' b')
      = C (detSchurS (k := k) q p r) * X (a', b') - C ((forcedNum (k := k) q p r) a' b') := by
  rw [borderMinor_eq_fromBlocks, AlgEquiv.map_det, AlgEquiv.mapMatrix_apply,
    Matrix.fromBlocks_map, blockAlgEquiv_borderΔ, blockAlgEquiv_borderU, blockAlgEquiv_borderV,
    blockAlgEquiv_borderD, det_fromBlocks_scalar_eq, Matrix.of_apply,
    show ((schurΔ (k := k) q p r).map C).det = C (detSchurS (k := k) q p r) from
      (RingHom.map_det C (schurΔ (k := k) q p r)).symm,
    show ((schurΔ (k := k) q p r).map C).adjugate = ((schurΔ (k := k) q p r).adjugate).map C from
      (RingHom.map_adjugate _ _).symm,
    ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply, schurNum_eq_forcedNum, mul_comm]

/-! ## Step (2): `J ⊆ Ψ(Iad)` — the localized inclusion

`Ψ` carries `algebraMap A_eng A_loc x` to `algebraMap B Q (blockAlgEquiv x)`
(`algEquivOfAlgEquiv_eq`). Each generator `X (a',b') − C (forcedB22 (a',b'))` of `J`, multiplied by
the unit `C (algebraMap detSchurS)`, is the `Ψ`-image of the bordered minor (in `Iad`), so it
`Ψ(Iad)`; dividing by the unit gives the generator. -/

/-- `Ψ` intertwines the two localization maps: `Ψ (algebraMap A_eng A_loc x) = algebraMap B Q
(blockAlgEquiv x)`. (`Ψ = IsLocalization.algEquivOfAlgEquiv blockAlgEquiv`.) -/
theorem blockAlgEquivLoc_algebraMap (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (x : MvPolynomial (RepCoord (dStratum q p)) k) :
    blockAlgEquivLoc (k := k) q p r hp hq
        (algebraMap (MvPolynomial (RepCoord (dStratum q p)) k)
          (Localization.Away (detPivotPoly (k := k) q p r hp hq)) x)
      = algebraMap (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
          (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))
          (blockAlgEquiv (k := k) q p r hp hq x) := by
  haveI tower : IsScalarTower k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    refine IsScalarTower.of_algebraMap_eq (fun y ↦ ?_)
    have hkB : (algebraMap k (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))) y
        = C (algebraMap k (MvPolynomial (SchurVar q p r) k) y) := by
      rw [IsScalarTower.algebraMap_apply k (MvPolynomial (SchurVar q p r) k)
        (MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k))]; rfl
    have hkQ : (algebraMap k (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))) y
        = C (algebraMap k (SchurLoc (k := k) q p r) y) := by
      rw [IsScalarTower.algebraMap_apply k (SchurLoc (k := k) q p r)
        (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r))]; rfl
    rw [hkB, hkQ, algebraMap_def, MvPolynomial.map_C]; congr 1
  haveI hloc : IsLocalization (Submonoid.powers (C (detSchurS (k := k) q p r) :
      MvPolynomial (B22block q p r) (MvPolynomial (SchurVar q p r) k)))
      (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) := by
    simpa [Submonoid.map_powers] using
      (MvPolynomial.isLocalization (σ := B22block q p r)
        (M := Submonoid.powers (detSchurS (k := k) q p r)) (S := SchurLoc (k := k) q p r))
  exact IsLocalization.algEquivOfAlgEquiv_eq _ x

/-- The localized base ideal `Iad = (sigmaIdeal …).map (algebraMap A_eng A_loc)`: the determinantal
base ideal pushed into the localized base ring `A_loc = Localization.Away detΔ`. -/
noncomputable def Iad (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    Ideal (Localization.Away (detPivotPoly (k := k) q p r hp hq)) :=
  (sigmaIdeal (dStratum q p) r).map
    (algebraMap (MvPolynomial (RepCoord (dStratum q p)) k)
      (Localization.Away (detPivotPoly (k := k) q p r hp hq)))

/-- **The cleared Schur relation in `Q = MvPolynomial B22block Sd`.** The unit `C (algebraMap
detSchurS)` times the graph generator `X (a',b') − C (forcedB22 (a',b'))` equals
`Ψ (algebraMap A_eng A_loc (borderMinor …))` — the `Ψ`-image of a bordered minor (hence in
`Ψ(Iad)`). The `mk'` denominator clears: `algebraMap detSchurS · forcedB22 = algebraMap
forcedNum`. -/
theorem unit_mul_graphGen_eq_psi_borderMinor (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q)
    (a' : Fin (p - r)) (b' : Fin (q - r)) :
    C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
          (detSchurS (k := k) q p r))
        * (X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b')))
      = blockAlgEquivLoc (k := k) q p r hp hq
          (algebraMap (MvPolynomial (RepCoord (dStratum q p)) k)
            (Localization.Away (detPivotPoly (k := k) q p r hp hq))
            (borderMinor q p r hp hq a' b')) := by
  rw [blockAlgEquivLoc_algebraMap, blockAlgEquiv_borderMinor, map_sub, map_mul]
  simp only [algebraMap_def, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [mul_sub]
  congr 1
  rw [← C_mul]
  congr 1
  rw [forcedB22,
    IsLocalization.mk'_spec' (SchurLoc (k := k) q p r) ((forcedNum (k := k) q p r) a' b')
      (⟨detSchurS q p r, Submonoid.mem_powers _⟩ : Submonoid.powers (detSchurS (k := k) q p r))]

/-- **Step (2): `J ⊆ Ψ(Iad)`.** Each generator `X (a',b') − C (forcedB22 (a',b'))` of the forced
graph ideal lies in `Ψ(Iad)`: it is the unit `C (algebraMap detSchurS)⁻¹` times the `Ψ`-image of the
bordered minor (which is in `Iad`, `borderMinor_mem_sigmaIdeal`). -/
theorem graphIdeal_forcedB22_le_map_Iad (q p r : ℕ) (hp : r ≤ p) (hq : r ≤ q) :
    graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))
      ≤ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) := by
  rw [graphIdeal, Ideal.span_le]
  rintro _ ⟨ab, rfl⟩
  obtain ⟨a', b'⟩ := ab
  show X (a', b') - C (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r) (a', b'))
      ∈ ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
  -- the generator × the unit `C (algebraMap detSchurS)` is `Ψ (algebraMap borderMinor) ∈ Ψ(Iad)`
  have hunit : IsUnit (C (algebraMap (MvPolynomial (SchurVar q p r) k) (SchurLoc (k := k) q p r)
      (detSchurS (k := k) q p r)) : MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)) :=
    (IsLocalization.Away.algebraMap_isUnit (detSchurS (k := k) q p r)).map
      (C : SchurLoc (k := k) q p r →+* _)
  rw [← Ideal.unit_mul_mem_iff_mem _ hunit, unit_mul_graphGen_eq_psi_borderMinor q p r hp hq a' b']
  exact Ideal.mem_map_of_mem _
    (Ideal.mem_map_of_mem _ (borderMinor_mem_sigmaIdeal q p r hp hq a' b'))

/-! ## Step (3): the height squeeze `Iad = J` and the presentation `A_loc/Iad ≅ Sd`

Both `Ψ(Iad)` and `J = graphIdeal forcedB22` are prime of height `C`, and `J ⊆ Ψ(Iad)`
(step 2). `Ideal.height_strict_mono_of_is_prime` rules out `J ⊊ Ψ(Iad)`, so `J = Ψ(Iad)` — this
**earns** the hard direction `Iad ⊆ Ψ.symm J` (= injectivity). The presentation `A_loc/Iad ≅ Sd`
then follows from `graphIdealQuotientEquiv`. -/

/-- **`Ψ(Iad) = J`** (`[IsAlgClosed k] [CharZero k]`): the height squeeze. Both ideals are prime;
landed `height Iad = C` (transported by `Ψ`) and `height J = C` are equal; `J ⊆ Ψ(Iad)` (step 2)
plus `height_strict_mono_of_is_prime` forces equality. This is the honest hard direction. -/
theorem map_Iad_eq_graphIdeal_forcedB22 [IsAlgClosed k] [CharZero k] (q p r : ℕ)
    (hp : r ≤ p) (hq : r ≤ q) :
    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq)
      = graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) := by
  set Q := MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
  set K : Ideal Q :=
    ((Iad (k := k) q p r hp hq)).map (blockAlgEquivLoc (k := k) q p r hp hq) with hK
  set J : Ideal Q := graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)) with hJ
  -- both ideals are prime
  haveI hsigmaPrime : (sigmaIdeal (k := k) (dStratum q p) r).IsPrime := by
    rw [sigmaIdeal]; exact isPrime_vanishingIdeal_productRankLocusLE_stratum q p r hq hp
  haveI hIadPrime : ((Iad (k := k) q p r hp hq)).IsPrime := by
    have hdisj := (Ideal.disjoint_powers_iff_notMem
        (detPivotPoly (k := k) q p r hp hq) hsigmaPrime.isRadical).2
      (detPivotPoly_notMem_sigmaIdeal q p r hp hq)
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (S := Localization.Away (detPivotPoly (k := k) q p r hp hq))
      (Submonoid.powers (detPivotPoly q p r hp hq))
      (sigmaIdeal (dStratum q p) r) hsigmaPrime hdisj
  haveI hKprime : K.IsPrime := Ideal.map_isPrime_of_equiv (blockAlgEquivLoc (k := k) q p r hp hq)
  haveI : IsDomain (SchurLoc (k := k) q p r) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (SchurLoc (k := k) q p r)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (detSchurS_ne_zero (k := k) q p r))
  haveI hJprime : J.IsPrime := graphIdeal_isPrime _
  -- `height K = height Iad` (Ψ an equiv); `height Iad = C` (landed); `height J = C` (landed)
  have hKIad : K.height = ((Iad (k := k) q p r hp hq)).height :=
    height_map_algEquiv (blockAlgEquivLoc (k := k) q p r hp hq) ((Iad (k := k) q p r hp hq))
  have hIadC : ((Iad (k := k) q p r hp hq)).height = ((q - r) * (p - r) : ℕ) := by
    rw [Iad, height_map_sigmaIdeal_away_eq_cCodim q p r hp hq
        (kostantPartitions_stratum_nonempty q p r hq hp), cCodim_stratum_eq q p r hq hp
        (kostantPartitions_stratum_nonempty q p r hq hp), Int.toNat_natCast]
  have hheightJ : J.height = ((p - r) * (q - r) : ℕ) :=
    height_graphIdeal_forcedB22_eq q p r (SchurLoc (k := k) q p r)
  have hJK : J.height = K.height := by
    rw [hheightJ, hKIad, hIadC, Nat.mul_comm]
  -- the squeeze: `J ⊆ K`, equal finite heights, both prime ⟹ `J = K`
  refine (eq_of_le_of_not_lt (graphIdeal_forcedB22_le_map_Iad q p r hp hq) (fun hlt ↦ ?_)).symm
  haveI : J.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]; right; rw [hheightJ]; exact ENat.coe_ne_top _
  exact absurd ((Ideal.height_strict_mono_of_is_prime hlt).trans_le hJK.ge)
    (lt_irrefl _)

/-- **The localized base presentation `A_loc / Iad ≅ₐ[k] Sd`** (`G2-2`). The localized determinantal
base ring `A_loc = Localization.Away detΔ`, modulo its base ideal `Iad = (sigmaIdeal …).map …`, is
the free Schur localization `Sd = Localization.Away detSchurS` — a regular ring of dimension `δ`.
Via the height squeeze `Ψ(Iad) = J` (`map_Iad_eq_graphIdeal_forcedB22`) and the graph-ideal quotient
`Q ⧸ J ≅ Sd` (`graphIdealQuotientEquiv`, the `B22`-block elimination). -/
noncomputable def basePresentationEquiv [IsAlgClosed k] [CharZero k] (q p r : ℕ)
    (hp : r ≤ p) (hq : r ≤ q) :
    (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
      ≃ₐ[k] SchurLoc (k := k) q p r := by
  have e₁ : (Localization.Away (detPivotPoly (k := k) q p r hp hq) ⧸ (Iad (k := k) q p r hp hq))
      ≃ₐ[k] (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))) :=
    Ideal.quotientEquivAlg ((Iad (k := k) q p r hp hq))
      (graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
      (blockAlgEquivLoc (k := k) q p r hp hq)
      (map_Iad_eq_graphIdeal_forcedB22 q p r hp hq).symm
  have e₂ : (MvPolynomial (B22block q p r) (SchurLoc (k := k) q p r)
        ⧸ graphIdeal (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r)))
      ≃ₐ[k] SchurLoc (k := k) q p r :=
    (graphIdealQuotientEquiv (forcedB22 (k := k) q p r (SchurLoc (k := k) q p r))).restrictScalars k
  exact e₁.trans e₂

/-! ## Non-vacuity witness — `(q, p, r) = (2, 2, 1)`

The `2 × 2` rank-`≤ 1` determinantal base: `#B22block = (2−1)(2−1) = 1 = C` eliminated coordinate,
`#SchurVar = 1·(2 + 2 − 1) = 3 = δ` free coordinates. The presentation exhibits `A_loc/Iad` as the
free Schur localization `Sd` (a regular ring of dimension `δ = 3`). -/

/-- **Witness (`2 × 2`, `r = 1`).** `#B22block = 1 = C` (one eliminated `B22` coordinate),
`#SchurVar = 3 = δ` (three free Schur coordinates). -/
example : Nat.card (B22block 2 2 1) = 1 ∧ Nat.card (SchurVar 2 2 1) = 3 := by
  refine ⟨?_, ?_⟩
  · rw [card_B22block]
  · rw [card_SchurVar 2 2 1 (by norm_num) (by norm_num)]

/-- The presentation equivalence is available at `(2, 2, 1)` for any algebraically closed field of
characteristic `0` — non-vacuous. -/
noncomputable example [IsAlgClosed k] [CharZero k]
    (h : (1 : ℕ) ≤ 2) :
    (Localization.Away (detPivotPoly (k := k) 2 2 1 h h) ⧸ Iad (k := k) 2 2 1 h h)
      ≃ₐ[k] SchurLoc (k := k) 2 2 1 :=
  basePresentationEquiv 2 2 1 h h

end DLNFibre.Core

exec
/bin/bash -lc "sed -n '1,170p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.MvPolynomial.Division
import DLNFibre.Core.IntegralDimension
import DLNFibre.Core.PolynomialDimension

/-!
# Monic-coordinate positioning for a nonzero polynomial (network-free engine)

The catenary `≥` direction for `MvPolynomial (Fin n) k` (`k` any field) needs a
**monic-coordinate-positioning** lemma: a nonzero `f` becomes monic in one variable after a
`k`-algebra coordinate change. Mathlib proves exactly this inside its Noether-normalization file via
the substitution `T : Xᵢ ↦ Xᵢ + X₀ ^ (N ^ i)` (`i ≠ 0`, `X₀ ↦ X₀`) with `N = 2 + f.totalDegree`,
but the construction (`T`, `T_leadingcoeff_isUnit`) is **`private`**. This module re-derives the one
public consequence we need — `exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit` — by re-exposing the
private machinery, valid over **any field** (the substitution uses `X₀` powers, not generic linear
combinations, so finite fields are fine; no `Infinite k` / `IsAlgClosed`).

The substitution and its degree bookkeeping are copied from
`Mathlib.RingTheory.NoetherNormalization` (Brasca–Su–Lin–Su, `@[stacks 00OW]`); only the visibility
changes (the originals are `private`). Everything is over `MvPolynomial (Fin (n+1)) k` and uses
`finSuccEquiv k n : MvPolynomial (Fin (n+1)) k ≃ₐ[k] (MvPolynomial (Fin n) k)[X]` to read off the
degree in `X₀`.
-/

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace DLNFibre.Core

variable {k : Type*} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) k)
variable (v w : Fin (n + 1) →₀ ℕ)

namespace MonicPositioning

/-- `up` is `2 + f.totalDegree`; any large enough number works. -/
local notation3 "up" => 2 + f.totalDegree

variable {f v} in
private lemma lt_up (vlt : ∀ i, v i < up) : ∀ l ∈ ofFn v, l < up := by
  grind

/-- `r` maps `(i : Fin (n + 1))` to `up ^ i`. -/
local notation3 "r" => fun (i : Fin (n + 1)) ↦ up ^ i.1

/-- The algebra map `Xᵢ ↦ Xᵢ + c • X₀ ^ rᵢ` for `i ≠ 0`, `X₀ ↦ X₀`. -/
noncomputable abbrev T1 (c : k) :
    MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
  aeval fun i ↦ if i = 0 then X 0 else X i + c • X 0 ^ r i

private lemma t1_comp_t1_neg (c : k) : (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
  rw [comp_aeval, ← MvPolynomial.aeval_X_left]
  ext i v
  cases i using Fin.cases <;> simp

/-- `T1 f 1` and its negation assemble into an algebra automorphism `T f`. -/
noncomputable abbrev T := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1))
  (t1_comp_t1_neg f 1) (by simpa using t1_comp_t1_neg f (-1))

private lemma sum_r_mul_ne (vlt : ∀ i, v i < up) (wlt : ∀ i, w i < up) (ne : v ≠ w) :
    ∑ x : Fin (n + 1), r x * v x ≠ ∑ x : Fin (n + 1), r x * w x := by
  intro h
  refine ne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up vlt) (lt_up wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, get_ofFn, length_ofFn,
    Fin.val_cast, mul_comm, sum_ofFn] using h

private lemma degreeOf_zero_t {a : k} (ha : a ≠ 0) : ((T f) (monomial v a)).degreeOf 0 =
    ∑ i : Fin (n + 1), (r i) * v i := by
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
      (Polynomial.C (X (R := k) i) + Polynomial.X ^ r i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/-- `T` maps different monomials of `f` to polynomials with different degrees in `X₀`. -/
private lemma degreeOf_t_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (T f <| monomial v <| coeff v f).degreeOf 0 ≠
    (T f <| monomial w <| coeff w f).degreeOf 0 := by
  rw [degreeOf_zero_t _ _ <| mem_support_iff.mp hv, degreeOf_zero_t _ _ <| mem_support_iff.mp hw]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) ne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i))
    (by lia)

private lemma leadingCoeff_finSuccEquiv_t :
    (finSuccEquiv k n ((T f) ((monomial v) (coeff v f)))).leadingCoeff =
    algebraMap k _ (coeff v f) := by
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply,
      eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/-- `T` maps `f` to a polynomial in `X₀` whose `X₀`-leading coefficient is a unit. -/
private lemma T_leadingcoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (T f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (T f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((T f) (h x))).degree <
      (finSuccEquiv k n ((T f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_t_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have coeff : (finSuccEquiv k n ((T f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
      (finSuccEquiv k n ((T f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((T f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_t] at coeff
  simpa only [coeff, algebraMap_eq] using (mem_support_iff.mp vin).isUnit.map MvPolynomial.C

end MonicPositioning

/-- **Monic-coordinate positioning.** For a nonzero `f : MvPolynomial (Fin (n+1)) k` over any field
`k`, there is a `k`-algebra automorphism `φ` of `MvPolynomial (Fin (n+1)) k` such that the image of
`φ f` under `finSuccEquiv k n` (the isomorphism isolating variable `0`) has a **unit leading
coefficient** in `X₀` — i.e. up to a unit scalar, `φ f` is monic in `X₀` over `k[x₁,…,xₙ]`. -/
theorem exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit (fne : f ≠ 0) :
    ∃ ψ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k,
      IsUnit (finSuccEquiv k n (ψ f)).leadingCoeff :=
  ⟨MonicPositioning.T f, MonicPositioning.T_leadingcoeff_isUnit f fne⟩

/-! ### Dimension preservation under a monic peel -/

/-- An ideal of `A[X]` containing an element with unit leading coefficient contains a monic. -/
theorem exists_monic_mem_of_isUnit_leadingCoeff_mem {A : Type*} [CommRing A]
    {I : Ideal (Polynomial A)} {g : Polynomial A} (hg : g ∈ I) (h : IsUnit g.leadingCoeff) :
    ∃ g' ∈ I, g'.Monic :=
  ⟨h.unit⁻¹ • g, Submodule.smul_of_tower_mem _ _ hg, monic_of_isUnit_leadingCoeff_inv_smul h⟩

/-- **Quotient dimension is preserved by a monic peel.** If an ideal `P` of `A[X]` contains a monic
polynomial, then `A[X] ⧸ P` is integral over `A ⧸ (P.under A)` via an injective map, so the two
quotients have the same Krull dimension. -/
theorem ringKrullDim_quotient_eq_under_of_monic {A : Type*} [CommRing A]
    (P : Ideal (Polynomial A)) {g : Polynomial A} (mon : g.Monic) (hg : g ∈ P) :
    ringKrullDim (Polynomial A ⧸ P) = ringKrullDim (A ⧸ P.under A) := by
  have hint : (Ideal.quotientMap P (algebraMap A (Polynomial A)) le_rfl).IsIntegral := by
    rw [isIntegral_quotientMap_iff]
    exact mon.quotient_isIntegral hg
  exact ringKrullDim_eq_of_integral_injective hint Ideal.quotientMap_injective

exec
/bin/bash -lc "rg -n \"surjective|Injective|ringKrullDim.*le|le.*ringKrullDim|RingHom.Flat|HasGoingDown|height_eq_height|quotient.*AlgEquiv|AlgEquiv.quotient|quotientMapₐ|Ideal\\.map.*equiv|map_isPrime_of_equiv|height_map_algEquiv|range.*ker|quotientKer\" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 3ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:43:   (`Ideal.quotientMapₐ`), then composed with `basePresentationEquiv.symm` to give a `k`-algebra map
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:250:`deepBaseComap_detPivot`), lifted to the quotients (`Ideal.quotientMapₐ`, the ideal hypothesis
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:305:Sred d r`: the quotient lift of `baseLocMap` (`Ideal.quotientMapₐ`, the ideal hypothesis from
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeepChartRing.lean:312:  Ideal.quotientMapₐ (IadDeep (k := k) d r hp hq) (baseLocMap (k := k) d r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreCodim.lean:24:`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` does not apply to the comorphism at the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:91:    -- range (M.mulVecLin ∘ e'.symm) = range M.mulVecLin (e'.symm surjective)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChart.lean:93:        (LinearMap.range_eq_top.mpr e'.symm.surjective)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:4:import Mathlib.RingTheory.RingHom.Flat
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:85:/-- **Ring-hom-level flat-local-on-base.** `RingHom.Flat` is a local property: its `propertyIsLocal`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:88:example : RingHom.PropertyIsLocal @RingHom.Flat := RingHom.Flat.propertyIsLocal
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:97:    Algebra.HasGoingDown A B := inferInstance
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:101:    [IsNoetherianRing B] [Algebra.HasGoingDown A B]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatTrivialProductProbe.lean:104:  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:36:Mathlib's classical theorem `Algebra.HasGoingDown` for integral extensions of an integrally closed
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:57:direction is going-down (`Algebra.HasGoingDown`, present for integral extensions of an integrally
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:61:    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:99:    Function.Injective (Ideal.quotientMap p g le_rfl) ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineDomainDimension.lean:104:      (RingHom.isIntegral_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective)⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:81:    ∃ er : Fin s → Fin p, Function.Injective er ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:99:  have hιinj : Function.Injective (ι : Fin s → κ) := Function.Embedding.injective ι
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RankLocusClosed.lean:113:      Function.Injective er ∧ Function.Injective ec ∧ (A.submatrix er ec).det ≠ 0 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:9:quasi-finite, so heights are preserved along an étale map, reducing `ringKrullDim` of a local ring
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:36:  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:45:    Ideal.map_isPrime_of_surjective hsurj (hkerf.trans_le hpSQ)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:47:    rw [Ideal.comap_map_of_surjective f hsurj, hbot, sup_eq_left.mpr hpSQ]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:65:    calc K = (K.comap f).map f := (Ideal.map_comap_of_surjective f hsurj K).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FlatQuasiFiniteHeight.lean:75:  have := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.under R) Q
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:350:  haveI hKprime : K.IsPrime := Ideal.map_isPrime_of_equiv (blockAlgEquivLoc (k := k) q p r hp hq)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalBasePresentation.lean:357:    height_map_algEquiv (blockAlgEquivLoc (k := k) q p r hp hq) ((Iad (k := k) q p r hp hq))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:316:`μ_M^* g` is zero in the domain `𝒪(G_d)`: `vanishingIdeal (range μ_M) = ker μ_M^*`. The `⊇` is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:320:theorem vanishingIdeal_range_orbitMap_eq_ker [Infinite k] {d : Fin (N + 1) → ℕ}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:369:orbit map `μ_M`, so `vanishingIdeal O_M = ker μ_M^*` (`vanishingIdeal_range_orbitMap_eq_ker`) is a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitVariety.lean:376:  rw [← range_orbitMap, vanishingIdeal_range_orbitMap_eq_ker]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreJacobian.lean:134:    rw [LinearMap.finrank_range_add_finrank_ker]; simp
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:19:landed as `quotientKerEquivRangeOrbitPullback`), with the coordinate index reindexed `RepCoord d ≃ Fin n`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:41:    (g : MvPolynomial (Fin s) k →ₐ[k] B) (hinj : Function.Injective g) (hint : g.IsIntegral) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:77:The first iso (`quotientKerEquivRangeOrbitPullback`) presents `Aimg` as `R_RepCoord ⧸ ker`; the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:96:    rw [hp, Ideal.map_comap_of_equiv Rr]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/AffineNoetherRank.lean:103:    (quotientKerEquivRangeOrbitPullback M).symm.trans Φ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitLinearCodim.lean:20:the orbit-map differential is surjective onto `B¹`) and that `dim Ō = dim C¹ − dim Ext¹` (Voigt's
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:27:* **The polynomial-tower additive brick** `height_eq_height_under_add_height_map_quotient` — for the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:31:  going-down instance and `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:34:(`primeHeight_add_ringKrullDim_quotient_le`). The catenary `≥` direction `height p ≥ n − dim(R/p)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:36:`Core.NoetherMonicPositioning` (`height_add_ringKrullDim_quotient_eq`), which imports this module
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:58:      Function.Injective g ∧ g.IsIntegral) ∧
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:92:theorem primeHeight_add_ringKrullDim_quotient_le
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:106:(`Algebra.HasGoingDown.of_flat`), and the equality is
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:107:`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`. This is the load-bearing additive half of
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:109:theorem height_eq_height_under_add_height_map_quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/PolynomialDimension.lean:114:  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under A) P
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/JacobianTrdeg.lean:66:    Function.Injective (KaehlerDifferential.mapBaseChange k E K) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/JacobianTrdeg.lean:124:  have hxinj : Function.Injective (MvPolynomial.aeval x : P →ₐ[k] FractionRing B) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/JacobianTrdeg.lean:134:  have hmbc : Function.Injective (KaehlerDifferential.mapBaseChange k Pf (FractionRing B)) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/JacobianTrdeg.lean:207:  have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/JacobianTrdeg.lean:209:  have hψinj : Function.Injective ψ := hinj
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/JacobianTrdeg.lean:215:    rw [himg, AlgEquiv.trdeg_eq (Subalgebra.equivMapOfInjective _ ψ hψinj)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:123:    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:127:    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:184:  have hJ : finrank k (LinearMap.range (jacobian g a)) + finrank k (LinearMap.ker (jacobian g a))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:186:    rw [LinearMap.finrank_range_add_finrank_ker]; simp [Module.finrank_pi]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:195:/-- `span (range g) ≤ ker (aeval a)` since each `g i` vanishes at `a`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:196:theorem span_range_le_ker_aeval (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:197:    Ideal.span (Set.range g) ≤ RingHom.ker (MvPolynomial.aeval (R := k) a).toRingHom := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:208:  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval a) fun _ hx ↦ span_range_le_ker_aeval g a hg hx
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:213:/-- The augmentation is split by `algebraMap k _`, hence surjective. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:214:theorem aug_surjective (hg : ∀ i, MvPolynomial.eval a (g i) = 0) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:225:  RingHom.ker_isMaximal_of_surjective (aug g a hg).toRingHom (aug_surjective g a hg)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:234:`kerCotangentToTensor k A k : m_A.Cotangent →ₗ[A] k ⊗[A] Ω[A⁄k]` is bijective (surjective since
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:241:`kerCotangentToTensor k A k : (ker ε).Cotangent →ₗ[A] k ⊗[A] Ω[A⁄k]` is bijective: surjective since
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:243:`retractionKerCotangentToTensorEquivSection`). Stated for a general `k`-algebra `A` with a surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:257:  · -- surjectivity: range = ker(mapBaseChange) = everything since Ω[k/k] = 0
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:259:    have hrange := KaehlerDifferential.range_kerCotangentToTensor k A k hsurj
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:261:      KaehlerDifferential.subsingleton_of_surjective (R := k) (S := k) Function.surjective_id
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:271:range (kerCotangentToTensor)` of `B ⊗[R] Ω[R⁄k]`, tensored by `k ⊗[B] -` and restricted to `k`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:282:    KaehlerDifferential.mapBaseChange_surjective k R B hsurj
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:294:    LinearMap.lTensor_surjective k hfsurj
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:304:  obtain ⟨⟨y, hy⟩, rfl⟩ := I.toCotangent_surjective x
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:340:    Ideal.Quotient.mk_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:390:    have hconormalSpan : LinearMap.range (KaehlerDifferential.kerCotangentToTensor k
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:398:      (KaehlerDifferential.range_kerCotangentToTensor k _ _ hsurj).symm.trans hconormalSpan
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:442:  have hsurj_alg : Function.Surjective (algebraMap A k) := aug_surjective g a hg
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/CotangentJacobian.lean:464:`V(I)` (`I = span (range g)`) has `k`-dimension equal to the kernel of the Jacobian of the generators. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:66:theorem ringKrullDim_quotient_comap_etale_eq_zero {n : ℕ} {S : Type*} [CommRing S] [Algebra k S]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:77:    RingHom.FiniteType.comp_surjective (g := Ideal.Quotient.mk q) hgFT Ideal.Quotient.mk_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothLocalRelativeDimension.lean:102:  rw [ringKrullDim_quotient_comap_etale_eq_zero g hg q, add_zero] at hL5
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:101:    (hf : Function.Injective f) {Δ : Matrix (Fin r) (Fin r) β} {u : Matrix (Fin r) Unit β}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeterminantalChartRing.lean:138:    have hinj : Function.Injective (algebraMap D (FractionRing D)) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:19:   (`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:21:   (`Ideal.quotientKerEquivRange`), so `ringKrullDim (… ⧸ ker μ_M^*) = ringKrullDim ((μ_M^*).range)`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:50:(`range_orbitMap` + `vanishingIdeal_range_orbitMap_eq_ker`) rewrite the vanishing ideal to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:58:    vanishingIdeal_range_orbitMap_eq_ker M]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:62:noncomputable def quotientKerEquivRangeOrbitPullback {d : Fin (N + 1) → ℕ} (M : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:65:  Ideal.quotientKerEquivRange (orbitPullback M)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:71:first isomorphism theorem (`quotientKerEquivRangeOrbitPullback`) transported through
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:79:    ringKrullDim_eq_of_ringEquiv (quotientKerEquivRangeOrbitPullback M).toRingEquiv]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:90:tupleWitnessQ) = (ringKrullDim (orbitPullback tupleWitnessQ).range).unbotD 0`. The dimension
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:94:      = (ringKrullDim (orbitPullback tupleWitnessQ).range).unbotD 0 :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitPullbackDim.lean:95:  varietyDim_eq_ringKrullDim_range_orbitPullback tupleWitnessQ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:168:/-- The restriction isomorphism `U ≃ range f` for `U` a complement of `ker f`: through the quotient
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:288:    have e1 := LinearMap.finrank_range_add_finrank_ker (toLin' B)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreNormalForm.lean:289:    have e2 := LinearMap.finrank_range_add_finrank_ker (toLin' B')
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MvPolynomialKerAeval.lean:82:/-- `aeval c` is surjective (it hits every constant). Used with `ker_aeval_eq_graphIdeal` to get the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MvPolynomialKerAeval.lean:84:theorem aeval_surjective (c : ι → R) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MvPolynomialKerAeval.lean:89:via `aeval c` (surjective onto constants, kernel `= graphIdeal c`). This is the elimination: the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MvPolynomialKerAeval.lean:94:    (Ideal.quotientKerAlgEquivOfSurjective (aeval_surjective c))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:70:theorem ringKrullDim_le_of_integral [CommRing A] [CommRing S] {f : A →+* S}
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:79:    [Algebra.IsIntegral A S] (hinj : Function.Injective (algebraMap A S))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:111:    (hf : f.IsIntegral) (hinj : Function.Injective f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:114:  rw [ringKrullDim, ringKrullDim, krullDim, iSup_le_iff]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:124:    (hf : f.IsIntegral) (hinj : Function.Injective f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:126:  le_antisymm (ringKrullDim_le_of_integral hf)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:132:example : ringKrullDim (MvPolynomial (Fin 1) ℚ) = 1 := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:139:example (R : Type*) [CommRing R] : ringKrullDim R = ringKrullDim R :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/IntegralDimension.lean:141:    (RingHom.isIntegral_of_surjective (RingHom.id R) Function.surjective_id)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:19:  realizing tuple's orbit). Via `Setoid.quotientKerEquivRange` after identifying the orbit relation
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:103:invariant) and applying the first isomorphism theorem `Setoid.quotientKerEquivRange`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:107:    (Setoid.quotientKerEquivRange (rankFn d))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:172:theorem embedRank_injective {N : ℕ} : Function.Injective (embedRank (N := N)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitKostant.lean:195:    Function.Injective (diffArrayOfRank (N := N)) := fun _ _ h =>
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:22:smoothness, with the going-down equality `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:23:requiring `Algebra.HasGoingDown ⟸` flatness, which `mult` lacks globally since the fibre dimension
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:90:irreducible determinantal base, with `ringKrullDim O(Mat^{≤r}) = δ`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:126:  haveI : J.IsPrime := by rw [hJ]; exact Ideal.map_isPrime_of_equiv e
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:132:  haveI : p'.IsPrime := by rw [hp']; exact Ideal.map_isPrime_of_equiv Φ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean:135:  rw [hp', height_map_algEquiv Φ p,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/BoxMoveGeneral.lean:869:  obtain ⟨s', rfl⟩ := finSumFinEquiv.surjective s
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:79:theorem ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:104:  exact ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ M hA42 hA43_le
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:134:theorem ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ_of_criterion
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:141:  ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ M
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:154:theorem ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ_charZero
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitImageDim.lean:160:  ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ_of_criterion M
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:16:additivity `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`.
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/ChartFlatnessProbe.lean:83:  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:144:  Ideal.quotientEquivAlg (orbitIdeal M) (orbitIdeal M) (baseChangeAlgEquiv P)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:203:/-- `m_{P•M}` is **maximal**: the kernel of the surjective `k`-algebra hom `orbitEval M P : A → k`
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:210:  exact (RingHom.ker_isMaximal_of_surjective _ hsurj)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:223:  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:322:  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:511:`k`-rational point: the evaluation `orbitEval M 1 : A → k` is a surjective `k`-algebra hom with
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitSmooth.lean:515:  Ideal.quotientKerAlgEquivOfSurjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:9:The prime catenary `height p + ringKrullDim (R ⧸ p) = card` (`Core.NullstellensatzCodim`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:48:theorem exists_minimalPrime_height_eq_height {R : Type*} [CommRing R] [IsNoetherianRing R]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:78:`p`, and the chain's length is `≤ coheight p = ringKrullDim (R ⧸ p)`. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:85:    refine ⟨?_, ne_top_of_le_ne_top (ringKrullDim_ne_top (R := R)) (ringKrullDim_quotient_le I)⟩
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:92:  have hLlen : ringKrullDim (R ⧸ I) = (L.length : WithBot ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:93:    rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:96:    RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:108:  rw [hLlen, ringKrullDim_quotient_eq_coheight (⟨p, ‹_›⟩ : PrimeSpectrum R)]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:144:    obtain ⟨p₀, hp₀mem, hp₀ht⟩ := exists_minimalPrime_height_eq_height I hIne
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:148:    have hdimle : ringKrullDim (R ⧸ p₀) ≤ ringKrullDim (R ⧸ I) :=
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean:149:      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hIp₀)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:6:dimension bridge (`ringKrullDim R = n` via the étale-over-affine route, *non-circular*); the cotangent
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:53:    (f : I.Cotangent →ₗ[R] X) (hf : Function.Injective f) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:54:    Function.Injective (h ▸ f : J.Cotangent →ₗ[R] X) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:101:    rw [ResidueField.algebraMap_eq]; exact residue_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:104:  have hinj : Function.Injective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/SmoothPointRegular.lean:112:  have hginj : Function.Injective g := injective_cotangent_cast hker _ hinj
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:106:`f = subtype ∘ rangeRestrict`; base change preserves the surjection (`lTensor_surjective`, so the
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:120:    exact lTensor_surjective K f.surjective_rangeRestrict
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/MatrixKaehler.lean:122:  have hinj : Function.Injective ((LinearMap.range f).subtype.baseChange K) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:225:theorem height_map_algEquiv {R S : Type*} [CommRing R] [CommRing S] {k : Type*} [CommRing k]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:269:      haveI : P.IsPrime := by rw [hP]; exact Ideal.map_isPrime_of_equiv Φ
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:276:      have hheight : p.height = P.height := (height_map_algEquiv Φ p).symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:288:        height_eq_height_under_add_height_map_quotient P
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:346:`primeHeight_add_ringKrullDim_quotient_le`: for a prime `p` of `R = k[x₁,…,xₙ]`,
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NoetherMonicPositioning.lean:367:example : ringKrullDim ((MvPolynomial (Fin 2) ℚ) ⧸ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)))
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:28:   transport lemmas (`height_map_algEquiv`, `ringKrullDim_quotient_map_algEquiv`):
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:123:  haveI : q.IsPrime := by rw [hq]; exact Ideal.map_isPrime_of_equiv e
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/NullstellensatzCodim.lean:124:  have hheight : q.height = p.height := height_map_algEquiv e p
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:67:  haveI : J.IsPrime := by rw [hJ]; exact Ideal.map_isPrime_of_equiv e
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:79:    height_map_algEquiv Φ m, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL4d
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:102:  haveI : Module.Finite k κ := Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:132:      (IsFractionRing.surjective_iff_isField (R := orbitRing M ⧸ normalFormIdeal M)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:357:    rw [orbitIdeal, ← range_orbitMap, vanishingIdeal_range_orbitMap_eq_ker M] at hf
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:387:  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:388:  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:474:    obtain ⟨z, rfl⟩ := (normalFormIdeal M).toCotangent_surjective z
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:475:    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (z : orbitRing M)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:480:    obtain ⟨z, rfl⟩ := (normalFormIdeal M).toCotangent_surjective z
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:481:    obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (z : orbitRing M)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:521:    Module.Finite.of_surjective (normalFormIdeal M).toCotangent
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:522:      (normalFormIdeal M).toCotangent_surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:533:    Module.Finite.of_surjective (residueFieldNormalFormEquiv M).symm.toLinearMap
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:534:      (residueFieldNormalFormEquiv M).symm.surjective
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:549:    (deformationδ M M).finrank_range_add_finrank_ker
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:552:    (cotPairing M).finrank_range_add_finrank_ker
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:569:theorem exists_ringKrullDim_orbitRing_eq [IsAlgClosed k] (M : Tuple (k := k) d) :
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:576:  have hle : ringKrullDim (orbitRing M) ≤ (Nat.card (RepCoord d) : WithBot ℕ∞) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitTangentCotangent.lean:577:    refine le_trans (ringKrullDim_quotient_le (orbitIdeal M)) ?_
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:131:    (deformationδ M Nt).finrank_range_add_finrank_ker
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:541:`Fin a ⊕ Fin b ≃ Fin (a + b)` reindexed block matrix), so `range δ` — and hence the cokernel
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/DeformationExt.lean:674:the differential is block-diagonal under `dirSum`, so the range (and hence the cokernel) splits. -/
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:21:`Core.NullstellensatzCodim` (the field catenary `height_add_ringKrullDim_quotient_eq_card`).
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:47:`height + dim(quotient) = #vars`: `#vars = Nat.card σ + Nat.card τ` (via `sumAlgEquiv` to
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:63:  haveI : J₀.IsPrime := by rw [hmap]; exact Ideal.map_isPrime_of_equiv e.symm
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:65:    rw [hmap]; exact height_map_algEquiv e.symm (graphIdeal c)
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/GraphIdealHeight.lean:159:  rw [← htrans, height_map_algEquiv, height_coordIdeal_localization_eq f hf Sd]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:252:    Function.Injective (traceFun (k := k) (a := a) (b := b)) := by
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:281:        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:320:    exact (Submodule.equivMapOfInjective _ eV.injective _).symm.finrank_eq
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:323:    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr eW.surjective, Submodule.map_top]
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:652:theorem ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ_unconditional
/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/OrbitDifferentialRank.lean:656:  ringKrullDim_range_orbitPullback_le_finrank_range_deformationδ_charZero M

codex
One more issue surfaced: even if the split target is written as a polynomial extension, the base factor is localized at `detSchurS`. For reducible fibre rings, proving that this localization has dimension `dim F + δ` is another lemma, not a free consequence of `MvPolynomial.krullDim` unless the localization is shown to meet top-dimensional components.
exec
/bin/bash -lc "rg -n \"SchurLoc|detSchurS|Localization\\.Away.*ringKrullDim|ringKrullDim.*Localization|krullDim.*Localization|Away.*krullDim|dimension.*localization|localization.*dimension|MvPolynomial\\.ringKrullDim|ringKrullDim_mvPolynomial|varietyDim.*product|tensor.*ringKrullDim|ringKrullDim.*Tensor|TensorProduct.*krull\" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib 2>/dev/null" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
2026-06-24T18:05:17.961678Z ERROR codex_app_server::bespoke_event_handling: request failed with client error: JSONRPCErrorError { code: -32000, data: None, message: "command execution approval is not supported in exec mode for thread `019efacd-3505-7fb3-8af2-49e577913154`" }
 exited 1:
2026-06-24T18:05:17.962098Z ERROR codex_core::tools::router: error=exec_command failed for `/bin/bash -lc "rg -n \"SchurLoc|detSchurS|Localization\\.Away.*ringKrullDim|ringKrullDim.*Localization|krullDim.*Localization|Away.*krullDim|dimension.*localization|localization.*dimension|MvPolynomial\\.ringKrullDim|ringKrullDim_mvPolynomial|varietyDim.*product|tensor.*ringKrullDim|ringKrullDim.*Tensor|TensorProduct.*krull\" -S /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/.lake/packages/mathlib/Mathlib 2>/dev/null"`: CreateProcess { message: "Rejected(\"rejected by user\")" }
exec
/bin/bash -lc "sed -n '1,170p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/RadicalCatenary.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.NullstellensatzCodim
import DLNFibre.Core.IntegralDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# `DLNFibre.Core.RadicalCatenary` — the catenary identity for a reducible (radical) locus

The prime catenary `height p + ringKrullDim (R ⧸ p) = card` (`Core.NullstellensatzCodim`,
`height_add_ringKrullDim_quotient_eq_card`) extended to an **arbitrary proper** ideal `I ≠ ⊤` of a
polynomial ring `R = MvPolynomial σ k` (`σ` finite, `k` any field):

> `height I + ringKrullDim (R ⧸ I) = Nat.card σ`.

Geometrically: a reducible variety `V(I) = ⋃ V(pᵢ)` has codimension `= min` component codimension
and dimension `= max` component dimension, and the polynomial ring is catenary, so the two are dual.
The proof is a direct order/chain argument over `PrimeSpectrum`, two inequalities squeezed by
`le_antisymm` (no component-decomposition lemma, no radicality needed):

* **upper bound** `height I + dim (R ⧸ I) ≤ card`: a longest prime chain of `R ⧸ I` maps into the
  primes `⊇ I` of `R`; its head contains a minimal prime `p`, so `dim (R ⧸ I) ≤ coheight p =
  dim (R ⧸ p)`, while `height I ≤ height p`, and the per-prime catenary closes `≤ card`;
* **lower bound** `card ≤ height I + dim (R ⧸ I)`: a minimal prime `p₀` realises `height I`; the
  quotient surjection `R ⧸ I ↠ R ⧸ p₀` gives `dim (R ⧸ p₀) ≤ dim (R ⧸ I)`, and the per-prime
  catenary for `p₀` reads `card = height I + dim (R ⧸ p₀) ≤ height I + dim (R ⧸ I)`.

The headline specialises to `codimRepCanonical Z + varietyDim Z = card` for any **nonempty**
Zariski-closed `Z` (over an algebraically closed field its vanishing ideal is radical and proper),
discharging the reducible-locus catenary that `Core.RouteCAssembly` carries as the named hypotheses
`hCatFibre`/`hCatSigma`.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open MvPolynomial Ideal Order

namespace DLNFibre.Core

universe u

variable {k : Type u} [Field k] {σ : Type*}

/-! ## A minimal prime realising the height -/

/-- **A minimal prime realises `I.height`.** For a Noetherian ring and a proper ideal `I ≠ ⊤`, some
minimal prime `p ∈ I.minimalPrimes` has `p.height = I.height`. The infimum `I.height = ⨅_{p}
primeHeight p` over the finite nonempty set of minimal primes is attained. -/
theorem exists_minimalPrime_height_eq_height {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hIne : I ≠ ⊤) :
    ∃ p ∈ I.minimalPrimes, p.height = I.height := by
  obtain ⟨p₀, hp₀⟩ := Ideal.nonempty_minimalPrimes hIne
  obtain ⟨p, hp, hpmin⟩ :=
    Set.exists_min_image _ (fun J ↦ J.height)
      I.finite_minimalPrimes_of_isNoetherianRing ⟨p₀, hp₀⟩
  refine ⟨p, hp, ?_⟩
  haveI := Ideal.minimalPrimes_isPrime hp
  apply le_antisymm
  · -- `height p ≤ height I`: `p` minimises `height` over the minimal primes (the `⨅`).
    rw [Ideal.height]
    refine le_iInf₂ (fun J hJ ↦ ?_)
    haveI := Ideal.minimalPrimes_isPrime hJ
    have : @Ideal.primeHeight _ _ J (Ideal.minimalPrimes_isPrime hJ) = J.height :=
      (Ideal.height_eq_primeHeight J).symm
    rw [this]
    exact hpmin J hJ
  · -- `height I ≤ height p`: `height I` is the `⨅`, `p` is one of the minimal primes.
    rw [Ideal.height]
    refine iInf₂_le_of_le p hp ?_
    exact le_of_eq (by rw [← Ideal.height_eq_primeHeight])

/-! ## A top-dimensional component -/

/-- **A minimal prime carries the full quotient dimension.** For a finite-dimensional Noetherian
ring `R` and a proper ideal `I ≠ ⊤`, some minimal prime `p ∈ I.minimalPrimes` has
`ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ p)` — a top-dimensional component. A longest prime chain
of `R ⧸ I` maps (via the
quotient `comap`, strictly monotone) into the primes `⊇ I` of `R`; its head contains a minimal prime
`p`, and the chain's length is `≤ coheight p = ringKrullDim (R ⧸ p)`. -/
theorem exists_minimalPrime_ringKrullDim_quotient_ge {R : Type*} [CommRing R] [IsNoetherianRing R]
    [FiniteRingKrullDim R] (I : Ideal R) (hIne : I ≠ ⊤) :
    ∃ p ∈ I.minimalPrimes, ringKrullDim (R ⧸ I) ≤ ringKrullDim (R ⧸ p) := by
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  haveI : FiniteRingKrullDim (R ⧸ I) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top (R := R ⧸ I)]
    refine ⟨?_, ne_top_of_le_ne_top (ringKrullDim_ne_top (R := R)) (ringKrullDim_quotient_le I)⟩
    exact fun h ↦ by simpa [h] using ringKrullDim_nonneg_of_nontrivial (R := R ⧸ I)
  haveI : FiniteDimensionalOrder (PrimeSpectrum (R ⧸ I)) := by
    rw [Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum (R ⧸ I))]
    exact ⟨ringKrullDim_ne_bot, ringKrullDim_ne_top⟩
  -- a longest chain `L` of `Spec (R ⧸ I)`, realising the Krull dimension.
  set L := LTSeries.longestOf (PrimeSpectrum (R ⧸ I)) with hL
  have hLlen : ringKrullDim (R ⧸ I) = (L.length : WithBot ℕ∞) := by
    rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder]
  -- map the chain into `Spec R` via the (strictly monotone) quotient comap.
  have hsm : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.mk I)) :=
    RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective
  set Lmap := L.map (PrimeSpectrum.comap (Ideal.Quotient.mk I)) hsm with hLmap
  -- the head of the mapped chain is a prime `⊇ I`; pick a minimal prime `p` below it.
  have hheadge : I ≤ Lmap.head.asIdeal := by
    rw [hLmap, LTSeries.head_map, PrimeSpectrum.comap_asIdeal]
    exact (Ideal.mk_ker (I := I)).symm.trans_le (Ideal.ker_le_comap (Ideal.Quotient.mk I))
  obtain ⟨p, hpmem, hple⟩ := Ideal.exists_minimalPrimes_le hheadge
  haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hpmem
  refine ⟨p, hpmem, ?_⟩
  -- `L.length ≤ coheight ⟨p⟩ = dim (R ⧸ p)`.
  have hlen_le : (Lmap.length : ℕ∞) ≤ Order.coheight (⟨p, ‹_›⟩ : PrimeSpectrum R) :=
    Order.length_le_coheight (x := (⟨p, ‹_›⟩ : PrimeSpectrum R)) (p := Lmap) hple
  rw [hLlen, ringKrullDim_quotient_eq_coheight (⟨p, ‹_›⟩ : PrimeSpectrum R)]
  rw [hLmap, LTSeries.map_length] at hlen_le
  exact_mod_cast hlen_le

/-! ## The radical-locus catenary -/

/-- **The reducible-locus catenary.** For `R = MvPolynomial σ k` (`σ` finite, `k` any field) and a
proper ideal `I ≠ ⊤`, `height I + ringKrullDim (R ⧸ I) = Nat.card σ` — the per-prime catenary
carried across the components: `dim (R ⧸ I) = max` dim `= card − min` height `= card − height I`.
Direct chain/coheight squeeze; no radicality needed. -/
theorem height_add_ringKrullDim_quotient_eq_card_of_ne_top [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (hIne : I ≠ ⊤) :
    (I.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ I) = (Nat.card σ : WithBot ℕ∞) := by
  set R := MvPolynomial σ k with hR
  set n : WithBot ℕ∞ := (Nat.card σ : WithBot ℕ∞) with hn
  -- the per-prime catenary, restated as `dim (R ⧸ p) = card − height p` in the additive form.
  have hprime : ∀ p : Ideal R, p.IsPrime →
      (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) = n := fun p hp ↦
    height_add_ringKrullDim_quotient_eq_card (k := k) (σ := σ) p
  -- `R = MvPolynomial σ k` has finite Krull dimension `Nat.card σ`.
  have hRdim : ringKrullDim R = ((Nat.card σ : ℕ∞) : WithBot ℕ∞) := ringKrullDim_mvPolynomial_finite
  haveI : FiniteRingKrullDim R := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top (R := R), hRdim]
    refine ⟨WithBot.coe_ne_bot, ?_⟩
    rw [Ne, WithBot.coe_eq_top]
    exact ENat.coe_ne_top (Nat.card σ)
  apply le_antisymm
  · -- upper bound: a top-dimensional component `p` has `dim (R ⧸ I) ≤ dim (R ⧸ p)`.
    obtain ⟨p, hpmem, hpdim⟩ := exists_minimalPrime_ringKrullDim_quotient_ge I hIne
    haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hpmem
    have hIp : I ≤ p := hpmem.1.2
    calc (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I)
        ≤ (p.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p) :=
          add_le_add (WithBot.coe_le_coe.mpr (Ideal.height_mono hIp)) hpdim
      _ = n := hprime p ‹_›
  · -- lower bound: a minimal prime `p₀` realising `height I`, with `R ⧸ I ↠ R ⧸ p₀`.
    obtain ⟨p₀, hp₀mem, hp₀ht⟩ := exists_minimalPrime_height_eq_height I hIne
    haveI : p₀.IsPrime := Ideal.minimalPrimes_isPrime hp₀mem
    have hIp₀ : I ≤ p₀ := hp₀mem.1.2
    -- `dim (R ⧸ p₀) ≤ dim (R ⧸ I)` from the quotient surjection `R ⧸ I ↠ R ⧸ p₀`.
    have hdimle : ringKrullDim (R ⧸ p₀) ≤ ringKrullDim (R ⧸ I) :=
      ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hIp₀)
    -- the per-prime catenary for `p₀`, with `height p₀ = height I`.
    have := hprime p₀ ‹_›
    rw [hp₀ht] at this
    calc n = (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ p₀) := this.symm
      _ ≤ (I.height : WithBot ℕ∞) + ringKrullDim (R ⧸ I) := by
          gcongr

/-! ## Specialisation to the geometry layer (`codimRepCanonical Z + varietyDim Z = card`) -/

/-- The vanishing ideal of a **nonempty** set is proper: a polynomial vanishing on a point `x ∈ Z`
cannot be the unit `1` (which evaluates to `1 ≠ 0`), so `vanishingIdeal Z ≠ ⊤`. -/
theorem vanishingIdeal_ne_top_of_nonempty [Finite σ] {Z : Set (σ → k)} (hZ : Z.Nonempty) :
    (vanishingIdeal k Z : Ideal (MvPolynomial σ k)) ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hZ
  rw [Ideal.ne_top_iff_one]
  intro hone
  rw [MvPolynomial.mem_vanishingIdeal_iff] at hone
  have := hone x hx
  rw [map_one] at this
  exact one_ne_zero this


exec
/bin/bash -lc "sed -n '1,180p' /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/lean/DLNFibre/Core/FibreDimFibration.lean" in /home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/fibre-codim/expeditions/2026-06-23-fibre-codim/threads/31-relative-fibre-dim/codex
 succeeded in 0ms:
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.DeterminantalStratumDim
import DLNFibre.Core.FibreCodim
import DLNFibre.Core.FibreHeightDirect
import DLNFibre.Core.AffineDomainDimension
import DLNFibre.Core.OrbitTangentCotangent

/-!
# `DLNFibre.Core.FibreDimFibration` — the fibre-dimension count toward Lemma 4.6 (H4)

Rung **H4** of the HEIGHT-DIRECT route to Lehalleur–Rimányi Lemma 4.6's geometry: the dimension of
the multiplication-map fibre `mult⁻¹(E)` over a rank-`r` normal form `E`, via the fibration
`mult|_{Σ̄^r} : Σ̄^r ↠ Mat^{≤r}` (dominant) and the generic-fibre-dimension count

> `codimRepCanonical (mult⁻¹ E) = C + δ`,   `C = cCodim d r`,  `δ = r(d_0 + d_N − r)`.

This module banks the **base-stratum dimension brick** the count consumes, and the **easy
inequality** `codimRepCanonical (fibre E) ≤ C + δ` (the flatness-free half), proved via the no-
going-down height inequality (Stacks 00OM) — see the per-theorem docstrings. The **hard inequality**
`codimRepCanonical (fibre E) ≥ C + δ` is the genuine no-jump residual (it needs that `E` lies in the
exact-rank good locus where the fibre dimension does not jump — generic flatness / generic
smoothness, with the going-down equality `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`
requiring `Algebra.HasGoingDown ⟸` flatness, which `mult` lacks globally since the fibre dimension
jumps as the rank drops). It is **NOT** proved here and is named honestly as such; nothing in this
module claims the full identity.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial Ideal

universe u

variable {k : Type u} [Field k]

/-! ## The base-stratum Krull dimension brick: `ringKrullDim O(Mat^{≤r}) = δ`

The base of the fibration is the rank-`≤ r` determinantal variety in the target matrices
`Mat_{m × n}` (`n = d_0`, `m = d_N`), encoded as the `N = 1` product-rank locus
`productRankLocusLE (dStratum n m) r`. Its coordinate ring `O(Mat^{≤r}) = MvPolynomial (RepCoord
(dStratum n m)) k ⧸ vanishingIdeal(…)` is a finite-type domain (the vanishing ideal is prime —
irreducible determinantal variety) of Krull dimension `δ = r(n + m − r)`. From the LANDED thermometer
`varietyDim = δ`, lifting the `unbotD 0` to the genuine `WithBot ℕ∞` value (the quotient is
nontrivial, so `ringKrullDim ≠ ⊥`). -/

/-- **The base-stratum Krull dimension** `ringKrullDim O(Mat^{≤r}) = δ`. For `r ≤ n`, `r ≤ m`, over an
algebraically closed field of characteristic `0`, the coordinate ring of the rank-`≤ r` determinantal
variety `Mat^{≤r}_{m × n}` (the `N = 1` product-rank locus) has Krull dimension `r(n + m − r) = δ`.
The thermometer `varietyDim_productRankLocusLE_stratum` gives the `ℕ∞`-via-`unbotD` value; this lifts
it to the genuine `WithBot ℕ∞` Krull dimension, using that the vanishing ideal is prime (the quotient
is a nontrivial domain, so `ringKrullDim ≠ ⊥`). -/
theorem ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
    (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m) :
    ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸
        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r))
      = (r * (n + m - r) : ℕ) := by
  set I := MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
    (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r) with hI
  haveI hIp : I.IsPrime :=
    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
  -- the thermometer: `varietyDim = δ`, i.e. `(ringKrullDim (R ⧸ I)).unbotD 0 = δ`.
  have hvd : varietyDim (canonicalCoord (dStratum n m) ''
      productRankLocusLE (k := k) (dStratum n m) r) = (r * (n + m - r) : ℕ) :=
    varietyDim_productRankLocusLE_stratum n m r hn hm
  rw [varietyDim, ← hI] at hvd
  -- the quotient is a nontrivial domain, so `ringKrullDim ≠ ⊥`.
  haveI : Nontrivial (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr hIp.ne_top
  have hne : ringKrullDim (MvPolynomial (RepCoord (dStratum n m)) k ⧸ I) ≠ ⊥ :=
    fun h ↦ by simpa [h] using
      ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (RepCoord (dStratum n m)) k ⧸ I)
  obtain ⟨w, hw⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hw, WithBot.unbotD_coe] at hvd
  rw [← hw, hvd]
  norm_cast

/-! ## The base-stratum closed-point height: `height m = δ` for any maximal ideal of `O(Mat^{≤r})`

By equidimensionality at a closed point (`OrbitTangentCotangent.height_eq_ringKrullDim_of_isMaximal_fintype`,
`Fintype`-indexed) and the base Krull dimension `= δ` just established: every maximal ideal of the
irreducible base `O(Mat^{≤r})` has height `δ`. The base-side input to the going-down/00OM easy
direction. -/

/-- **The base-stratum closed-point height `= δ`.** For `r ≤ n`, `r ≤ m`, every maximal ideal `𝔪` of
the base coordinate ring `O(Mat^{≤r}_{m×n}) = MvPolynomial (RepCoord (dStratum n m)) k ⧸
vanishingIdeal(…)` has height `δ = r(n + m − r)` — equidimensionality at a closed point of the
irreducible determinantal base, with `ringKrullDim O(Mat^{≤r}) = δ`. -/
theorem height_maximal_quotient_vanishingIdeal_stratum_eq_delta [IsAlgClosed k] [CharZero k]
    (n m r : ℕ) (hn : r ≤ n) (hm : r ≤ m)
    (𝔪 : Ideal (MvPolynomial (RepCoord (dStratum n m)) k ⧸
        MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
          (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)))
    [𝔪.IsMaximal] :
    (𝔪.height : WithBot ℕ∞) = (r * (n + m - r) : ℕ) := by
  haveI : (MvPolynomial.vanishingIdeal (σ := RepCoord (dStratum n m)) (K := k) k
      (canonicalCoord (dStratum n m) '' productRankLocusLE (k := k) (dStratum n m) r)).IsPrime :=
    isPrime_vanishingIdeal_productRankLocusLE_stratum (k := k) n m r hn hm
  rw [height_eq_ringKrullDim_of_isMaximal_fintype,
    ringKrullDim_quotient_vanishingIdeal_stratum_eq_delta n m r hn hm]

/-! ## Affine-domain equidimensionality over a `Fintype` coordinate index

`affine_domain_height_add_ringKrullDim_quotient_eq` is over `MvPolynomial (Fin n) k`. Transport it to
`MvPolynomial σ k` (`σ` finite) through `renameEquiv`, exactly as
`height_eq_ringKrullDim_of_isMaximal_fintype` does for the maximal corollary. This is the engine the
nested catenary `height P = height Q + height_{R/Q}(P/Q)` (the `+C` composition for the easy
direction) is built from. -/

/-- **Affine-domain equidimensionality, finite index.** For `σ` finite, `I` a prime of
`MvPolynomial σ k`, the domain `A = MvPolynomial σ k ⧸ I`, and a prime `p` of `A`:
`height p + ringKrullDim (A ⧸ p) = ringKrullDim A`. Transports
`affine_domain_height_add_ringKrullDim_quotient_eq` through `renameEquiv` and the induced quotient
algebra equivalences. -/
theorem affine_domain_height_add_ringKrullDim_quotient_eq_fintype {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (p : Ideal (MvPolynomial σ k ⧸ I)) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim ((MvPolynomial σ k ⧸ I) ⧸ p)
      = ringKrullDim (MvPolynomial σ k ⧸ I) := by
  classical
  haveI : Fintype σ := Fintype.ofFinite _
  set e : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin (Fintype.card σ)) k :=
    MvPolynomial.renameEquiv k (Fintype.equivFin σ) with he
  set J : Ideal (MvPolynomial (Fin (Fintype.card σ)) k) := I.map (e : _ →+* _) with hJ
  haveI : J.IsPrime := by rw [hJ]; exact Ideal.map_isPrime_of_equiv e
  -- the induced quotient algebra equivalence `A ≃ₐ[k] A'`
  set Φ : (MvPolynomial σ k ⧸ I) ≃ₐ[k] (MvPolynomial (Fin (Fintype.card σ)) k ⧸ J) :=
    Ideal.quotientEquivAlg I J e rfl with hΦ
  -- transport `p` to a prime `p'` of `A'`
  set p' : Ideal (MvPolynomial (Fin (Fintype.card σ)) k ⧸ J) := p.map (Φ : _ →+* _) with hp'
  haveI : p'.IsPrime := by rw [hp']; exact Ideal.map_isPrime_of_equiv Φ
  have hL := affine_domain_height_add_ringKrullDim_quotient_eq k (Fintype.card σ) J p'
  -- transport the three terms back along `Φ` (heights, both quotient Krull dims) and `e`.
  rw [hp', height_map_algEquiv Φ p,
    ringKrullDim_quotient_map_algEquiv Φ p, hJ, ringKrullDim_quotient_map_algEquiv e I] at hL
  exact hL

end DLNFibre.Core

codex
**Verdict:** the dimension-only framing is only modestly lighter. It can avoid hand-building the full symmetric tensor `e : Sred ≃ₐ[k] SchurLoc ⊗[k] FibreAlg`, but it does **not** avoid the hard localized-quotient gauge descent. The irreducible core is proving that the normalized/localized chart ideal splits.

**Lightest path:** candidate 2, but sharpened:

Prove an ideal/radical identity after applying the localized Schur-gauge, then let Lean generate the quotient equivalence with `Ideal.quotientEquivAlg`. This avoids manually defining both quotient maps and proving round-trips. It does not avoid proving both ideal containments/equality.

Shape:

```lean
(gaugeEquiv ...).map localizedChartIdeal
  = splitBaseFibreIdeal
```

or, dimension-only:

```lean
((gaugeEquiv ...).map localizedChartIdeal).radical
  = splitBaseFibreIdeal.radical
```

Then use `ringKrullDim_quotient_eq_of_radical_eq` and the polynomial/localization dimension calculation.

**Candidate judgments:**

1. **Inequality squeeze:** not recommended. The surjection side may give one inequality, but the reverse inequality through an injection is fragile in the reducible setting and not supported by the existing API. Proving the injection has the right kernel/comap behavior is essentially proving the missing inverse/ideal equality in another language.

2. **Unquotiented gauge + ideal bookkeeping:** best formulation, but it only avoids quotient round-trip plumbing. The endpoint gauge lives after inverting the pivot/Schur determinant, so the localization is still present. Also `varietyDim` of a principal-open chart is controlled by saturation/radical of the open condition; proving that is localization descent in disguise.

3. **Polynomial-extension target:** slightly cleaner as a dimension closer, but not materially easier. It replaces
`SchurLoc ⊗[k] FibreAlg`
by something like a localized polynomial extension of `FibreAlg`; the coordinate split proof is the same. You also need a reducible-safe lemma that localizing at `detSchurS` preserves the top dimension.

4. **Stay unlocalized until the end:** no. The chart is a principal open. If you do not localize, you must prove a saturation/vanishing-ideal statement for `D(Δ)`, which is the same descent problem in set-level clothing.

**Module estimate for the lightest real path:** about **5-7 modules** for a robust Lean proof.

Likely breakdown:

- 1 module: define the Schur-valued endpoint gauge and normalize `multPoly`.
- 2-3 modules: prove the localized gauged chart ideal splits, at least up to radical.
- 1-2 modules: prove the split/localized polynomial-extension dimension formula over possibly reducible `FibreAlg`.
- 1 glue module: transport to `varietyDim` and chart/global statement.

So: dimension-only saves the reducedness/tensor-packaging tail and may avoid manual quotient-map round-trips, but it does **not** remove the stalled core. If the current scope cannot absorb the localized ideal-splitting descent, fallback to citing `hSweep` is the honest move.
tokens used
245,871
**Verdict:** the dimension-only framing is only modestly lighter. It can avoid hand-building the full symmetric tensor `e : Sred ≃ₐ[k] SchurLoc ⊗[k] FibreAlg`, but it does **not** avoid the hard localized-quotient gauge descent. The irreducible core is proving that the normalized/localized chart ideal splits.

**Lightest path:** candidate 2, but sharpened:

Prove an ideal/radical identity after applying the localized Schur-gauge, then let Lean generate the quotient equivalence with `Ideal.quotientEquivAlg`. This avoids manually defining both quotient maps and proving round-trips. It does not avoid proving both ideal containments/equality.

Shape:

```lean
(gaugeEquiv ...).map localizedChartIdeal
  = splitBaseFibreIdeal
```

or, dimension-only:

```lean
((gaugeEquiv ...).map localizedChartIdeal).radical
  = splitBaseFibreIdeal.radical
```

Then use `ringKrullDim_quotient_eq_of_radical_eq` and the polynomial/localization dimension calculation.

**Candidate judgments:**

1. **Inequality squeeze:** not recommended. The surjection side may give one inequality, but the reverse inequality through an injection is fragile in the reducible setting and not supported by the existing API. Proving the injection has the right kernel/comap behavior is essentially proving the missing inverse/ideal equality in another language.

2. **Unquotiented gauge + ideal bookkeeping:** best formulation, but it only avoids quotient round-trip plumbing. The endpoint gauge lives after inverting the pivot/Schur determinant, so the localization is still present. Also `varietyDim` of a principal-open chart is controlled by saturation/radical of the open condition; proving that is localization descent in disguise.

3. **Polynomial-extension target:** slightly cleaner as a dimension closer, but not materially easier. It replaces
`SchurLoc ⊗[k] FibreAlg`
by something like a localized polynomial extension of `FibreAlg`; the coordinate split proof is the same. You also need a reducible-safe lemma that localizing at `detSchurS` preserves the top dimension.

4. **Stay unlocalized until the end:** no. The chart is a principal open. If you do not localize, you must prove a saturation/vanishing-ideal statement for `D(Δ)`, which is the same descent problem in set-level clothing.

**Module estimate for the lightest real path:** about **5-7 modules** for a robust Lean proof.

Likely breakdown:

- 1 module: define the Schur-valued endpoint gauge and normalize `multPoly`.
- 2-3 modules: prove the localized gauged chart ideal splits, at least up to radical.
- 1-2 modules: prove the split/localized polynomial-extension dimension formula over possibly reducible `FibreAlg`.
- 1 glue module: transport to `varietyDim` and chart/global statement.

So: dimension-only saves the reducedness/tensor-packaging tail and may avoid manual quotient-map round-trips, but it does **not** remove the stalled core. If the current scope cannot absorb the localized ideal-splitting descent, fallback to citing `hSweep` is the honest move.
