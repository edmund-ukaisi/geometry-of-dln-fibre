# Thread 32 — Certificate: `hClosure` cheapest PROVABLE route

**Target** (`Core/RouteCAssembly.lean`, currently a named hypothesis labelled "Cited closure/density
bridge"):

```
hClosure : varietyDim (canonicalCoord d '' productRankLocus  (k:=k) d r)     -- Σ^r   (rank = r)
         = varietyDim (canonicalCoord d '' productRankLocusLE (k:=k) d r)     -- Σ̄^r  (rank ≤ r)
```

Operator removed the Cited fallback: this must be PROVED in-repo, zero-cite.

## One-line verdict

**Route 2 (codimension sandwich), ~7–10 small lemmas, PROVABLE at v4.29 from LANDED engine handles —
no Mathlib-absent theorem, no rank-raising/density theorem.** Hypotheses: `[IsAlgClosed k] [CharZero k]`
(already on the assembly), `(kostantPartitions d r).Nonempty` (already a parameter `h`), and the two
loci nonempty (already parameters `hFne`-style / derivable). The single biggest risk is the `ℕ∞`
left-cancellation bookkeeping — modest, mirrors the cancellation already done in `RouteCAssembly`.

---

## The exact subtlety verdict

The cheap radical-insensitive route **does hold at the level of `varietyDim`**, but the *naive* set-closure
form `Σ̄^r = repClosure(Σ^r)` is **NOT cheap** — it is the genuine subtlety, and it is a real (though
true) obstruction that would force an unbuilt theorem. The codimension sandwich **sidesteps it entirely**.

### Why the set-closure route (Route 1) hits a wall

`hClosure` is FREE the moment `vanishingIdeal(canonicalCoord '' Σ^r) = vanishingIdeal(canonicalCoord '' Σ̄^r)`
(then `varietyDim` reads off equal ideals; `varietyDim` is literally `(ringKrullDim (R ⧸ vanishingIdeal))
.unbotD 0`). Equivalently `Σ̄^r = repClosure(Σ^r)` as flattened sets. The `⊇` half is free
(`Σ^r ⊆ Σ̄^r`, `Σ̄^r` closed). The `⊆` half `Σ̄^r ⊆ repClosure(Σ^r)` is the wall:

- `mult⁻¹(closure S) ⊇ closure(mult⁻¹ S)` always, but equality is NOT automatic without flatness/openness
  of `mult` — so `Σ̄^r = repClosure(Σ^r)` is NOT free from `Mat^{≤r} = closure(Mat^{=r})` alone.
- Via the G2 stratification `Σ̄^r = ⋃_{corner M ≤ r} Ō_M`, every orbit closure `Ō_M` with corner `s ≤ r`
  must be shown `⊆ repClosure(Σ^r)`. The engine HAS the per-orbit closure identity
  `canonicalCoord '' orbitRankLocus M = repClosure(orbitSet M)` (`image_orbitRankLocus_eq_repClosure_orbitSet`,
  `[Infinite k]`) and the rank-pattern-order ⟹ closure-containment box-move engine
  (`canonicalCoord_mem_repClosure_orbitSet`: `rankPattern A ≤ rankPattern M ⟹ canonicalCoord A ∈ Ō_M`).
  BUT to cover the `s < r` strata you additionally need the **rank-raising / density theorem**:
  > every corner-`≤ r` achievable rank pattern is dominated by a corner-EXACTLY-`r` achievable one
  > (equivalently, every maximal component of `Σ̄^r` meets `Σ^r`).
  This is the quiver orbit-closure-order density statement, true for feasible `r` (`r ≤ min_i d_i`), but
  it is an **unbuilt sublemma** (call it `productRankLocusLE_subset_repClosure_productRankLocus` or
  `exists_corner_eq_dominating_rankPattern`). The mathematics is sound — the submodular rank inequalities
  baked into Kostant achievability (`kostantAt`) keep the corner from being trapped below `r` whenever the
  intermediate ranks are high — but formalising the domination construction is real extra work.

Decorrelated Codex (xhigh, full transcript in `codex/answer.md`) independently named the same wall and the
same escape: *"global vanishing-ideal equality is mathematically true for feasible `r` but not cheap from
facts 1–8 alone … you still need the rank-raising/density theorem … the cheap escape is codimension."*

### Why the codimension sandwich (Route 2) is provable cheaply — the precise reason

Two facts make `dim Σ^r = dim Σ̄^r` reduce to `codim Σ^r = codim Σ̄^r`, and the latter needs only ONE
corner-exactly-`r` orbit (NOT every stratum):

1. **Reducible-locus catenary, NO irreducibility needed** (`Core.RadicalCatenary`,
   `codimRepCanonical_add_varietyDim_eq_card_of_nonempty`): for ANY nonempty `Z`,
   `codimRepCanonical Z + varietyDim (canonicalCoord '' Z) = card`. So
   `dim Σ^r = card − codim Σ^r` and `dim Σ̄^r = card − codim Σ̄^r`, and `codim` finite (`≤ card`).
   Hence `dim Σ^r = dim Σ̄^r ⟺ codim Σ^r = codim Σ̄^r` (left-cancel the finite codim, as in
   `RouteCAssembly`'s existing `ENat.add_right_injective_of_ne_top` step).

2. `codim Σ̄^r = C` is LANDED (`Core.SigmaCodim`, `codimRepCanonical_productRankLocusLE_eq_cCodim_enat`),
   computed as the MIN over corner-`≤r` orbit codims, ATTAINED by a corner-EXACTLY-`r` realizer.

The sandwich:
- **`codim Σ̄^r ≤ codim Σ^r`**: `Σ^r ⊆ Σ̄^r` ⟹ (anti-mono `codimRepCanonical_mono`) `codim Σ̄^r ≤ codim Σ^r`,
  i.e. `C ≤ codim Σ^r`.
- **`codim Σ^r ≤ C`**: exhibit ONE `Tuple`-subset `W ⊆ Σ^r` with `codim W = C`. Take the minimising-Kostant
  realizer `M₀ := realizerD hm₀` (the very witness `SigmaCodim` already uses), and `W := the G_d-orbit of M₀`
  (`{A | ∃ P, P • M₀ = A}`). Then:
    - `W ⊆ Σ^r`: each `P • M₀` has the same rank pattern as `M₀` (`rankPattern_eq_of_smul`), so the same
      corner `= rank(mult)` (`corner_rankPattern_eq_rank`) `= r` (`rank_mult_realizerD hm₀`). [G_d-invariance
      of the corner — Σ^r is G_d-stable.]
    - `codim W = C`: `canonicalCoord '' W = orbitSet M₀`, and `vanishingIdeal(orbitSet M₀)
      = vanishingIdeal(canonicalCoord '' orbitRankLocus M₀)` (LANDED `vanishingIdeal_orbitRankLocus_eq_orbitSet`,
      `[Infinite k]`), so `codim W = (vanishingIdeal(orbitSet M₀)).height = codimRepCanonical(orbitRankLocus M₀)
      = C` (LANDED `codimRepCanonical_orbitRankLocus_eq_height` + the realizer-attains-`C` computation already
      inside `SigmaCodim`).
    - `codimRepCanonical_mono (W ⊆ Σ^r)`: `codim Σ^r ≤ codim W = C`.

Chain: `C = codim Σ̄^r ≤ codim Σ^r ≤ C` ⟹ `codim Σ^r = codim Σ̄^r = C` ⟹ (catenary) `dim Σ^r = dim Σ̄^r`.

**The single corner-`r` orbit is enough** because `varietyDim` is the dimension of the WHOLE closure of
`Σ^r`, which is `≥` the dimension of any one component, and `codim` is `card − dim` — lower-dimensional
"closed junk" (the `s < r` strata) cannot change `varietyDim`. So the sandwich never asserts that the lower
strata are in `repClosure(Σ^r)`; it only needs ONE top-dimensional piece of `Σ^r`, which is exactly the
realizer orbit. This is why it dodges the rank-raising theorem.

---

## Formaliser-facing lemma chain (engine vocabulary)

All in `Core`, `[IsAlgClosed k] [CharZero k]`, `d : Fin (N+1) → ℕ`, `r : ℕ`,
`h : (kostantPartitions d r).Nonempty`. Target shape: discharge `hClosure` so the
`…_of_sweep'` theorem carries ONLY `hSweep`.

| # | Statement | Status |
|---|---|---|
| L0 | `varietyDim Z` reads off `vanishingIdeal(canonicalCoord '' Z)`; radical-insensitive | LANDED `Core.VarietyDimRadical` (`ringKrullDim_quotient_radical`, `ringKrullDim_quotient_eq_of_radical_eq`) |
| L1 | `codimRepCanonical Z + varietyDim (canonicalCoord '' Z) = card`, any nonempty `Z` | LANDED `Core.RadicalCatenary.codimRepCanonical_add_varietyDim_eq_card_of_nonempty` |
| L2 | `codim Σ̄^r = (cCodim d r h).toNat` (`= C`) | LANDED `Core.SigmaCodim.codimRepCanonical_productRankLocusLE_eq_cCodim_enat` |
| L3 | `Z ⊆ Z' → codimRepCanonical Z' ≤ codimRepCanonical Z` | LANDED `Core.FibreCodim.codimRepCanonical_mono` |
| L4 | `productRankLocus d r ⊆ productRankLocusLE d r` (`Σ^r ⊆ Σ̄^r`) | PROVABLE-CHEAP (1 line: `rank = r ⟹ rank ≤ r`; cf. `fibre_subset_productRankLocusLE`) |
| L5 | `M₀ := realizerD hm₀` for a minimiser `m₀`, `rank(mult M₀) = r` | LANDED `Core.ThetaComponentCount.rank_mult_realizerD` (minimiser via `Finset.exists_mem_eq_inf'`, as in `SigmaCodim`) |
| L6 | `orbitAsTuples M₀ := {A | ∃ P, P • M₀ = A} ⊆ productRankLocus d r` | PROVABLE-CHEAP (`rankPattern_eq_of_smul` + `corner_rankPattern_eq_rank` + L5; ~3–4 lines) |
| L7 | `codimRepCanonical (orbitAsTuples M₀) = C` | PROVABLE-CHEAP: `canonicalCoord '' orbitAsTuples M₀ = orbitSet M₀` (defeq), then `vanishingIdeal_orbitRankLocus_eq_orbitSet` (LANDED, `[Infinite k]`) + `codimRepCanonical_orbitRankLocus_eq_height` (LANDED) + the realizer-`= C` value (lift the `hreal` block from `SigmaCodim`) |
| L8 | `codimRepCanonical (productRankLocus d r) = (cCodim d r h).toNat` (`= C`) | PROVABLE-CHEAP: `le_antisymm` of `L3 L4` (gives `C ≤ codim Σ^r` via L2) and `L3 (L6) ▸ L7` (gives `codim Σ^r ≤ C`) |
| L9 | **`hClosure`**: `varietyDim Σ^r = varietyDim Σ̄^r` | PROVABLE-CHEAP: from L1 (both loci, nonempty) + L8 + L2: equal codims ⟹ equal `card − codim` ⟹ equal `varietyDim`, by `ENat` left-cancellation of the finite codim (mirror `RouteCAssembly`'s `ENat.add_right_injective_of_ne_top` / `addLECancellable` step) |

Final wiring: replace the `hClosure` parameter in
`codimRepCanonical_fibre_eq_cCodim_add_shift_of_sweep'` with L9 (it needs the same `hSigmaNe` /
nonemptiness already in scope, plus `(canonicalCoord d '' productRankLocus d r).Nonempty` — derivable
from L5/L6: `M₀ ∈ Σ^r`).

### Module cost

One new module (e.g. `Core/SigmaExactCodim.lean` or appended to `SigmaCodim.lean`), L4 + L6 + L7 + L8 + L9
≈ 7–10 short lemmas, all leaning on LANDED handles. No new import beyond `SigmaCodim`, `RadicalCatenary`,
`OrbitClosure`, `ThetaComponentCount` (all already in the `RouteCAssembly` dependency cone).

---

## Engine handles VERIFIED to exist (file : name)

- `lean/DLNFibre/Core/VarietyDimRadical.lean` : `ringKrullDim_quotient_radical`,
  `ringKrullDim_quotient_eq_of_radical_eq`, `varietyDim_eq_of_coordRingAlgEquiv`.
- `lean/DLNFibre/Core/NullstellensatzCodim.lean` : `varietyDim` def (`(ringKrullDim (R ⧸ vanishingIdeal)).unbotD 0`),
  `codimRep_add_varietyDim_eq_card`, `codimRepCanonical_eq_card_sub_varietyDim`.
- `lean/DLNFibre/Core/RadicalCatenary.lean` : `codimRepCanonical_add_varietyDim_eq_card_of_nonempty`,
  `height_add_ringKrullDim_quotient_eq_card_of_ne_top`, `vanishingIdeal_ne_top_of_nonempty`.
- `lean/DLNFibre/Core/SigmaCodim.lean` : `codimRepCanonical_productRankLocusLE_eq_cCodim_enat`,
  `codimRepCanonical_productRankLocusLE_eq_iInf_orbitCodim`, and the inline realizer-attains-`C` block
  (`hreal`, lines ~107–125) — reusable verbatim for L7.
- `lean/DLNFibre/Core/FibreCodim.lean` : `codimRepCanonical_mono`, `fibre_subset_productRankLocusLE` (pattern for L4).
- `lean/DLNFibre/Core/OrbitClosure.lean` : `vanishingIdeal_orbitRankLocus_eq_orbitSet` (`[Infinite k]`),
  `vanishingIdeal_repClosure`, `image_orbitRankLocus_eq_repClosure_orbitSet`,
  `canonicalCoord_mem_repClosure_orbitSet` (the box-move degeneration — only needed for the abandoned Route 1).
- `lean/DLNFibre/Core/SigmaComponents.lean` : `codimRepCanonical_orbitRankLocus_eq_height` (defeq),
  `sigmaIdeal` def (`= vanishingIdeal Σ̄^r`).
- `lean/DLNFibre/Core/ThetaComponentCount.lean` : `realizerD`, `rank_mult_realizerD`,
  `codimRepCanonical_orbitRankLocus_realizerD`.
- `lean/DLNFibre/Core/Orbit.lean` : `rankPattern_eq_of_smul`.
- `lean/DLNFibre/Core/SigmaStratification.lean` : `corner_rankPattern_eq_rank`,
  `orbitRankLocus_subset_productRankLocusLE`, `productRankLocusLE_eq_iUnion_orbitRankLocus`.
- `lean/DLNFibre/Core/OrbitVariety.lean` : `orbitSet` def (`canonicalCoord '' {A | ∃ P, P • M = A}`),
  `range_orbitMap`.
- `lean/DLNFibre/Core/EndBaseChangeSweep.lean` : `productRankLocus_eq_iUnion_smul_fibre`,
  `mem_productRankLocus_iff_mem_sweep`, `rank_endpoint_conj` (H-sweep; NOT needed for Route 2).

### Searched for and did NOT find (do not exist in the engine)

- No landed fact about the EXACT locus `productRankLocus d r`'s vanishing ideal / codim / varietyDim for
  deep `d` (only the `hSweep`/`hClosure` HYPOTHESES in `RouteCAssembly`, and the H-sweep set identity).
- No `productRankLocusLE = repClosure productRankLocus` and no `vanishingIdeal Σ^r = vanishingIdeal Σ̄^r`.
- No `isPrime_vanishingIdeal_productRankLocusLE` for deep `d` (only the `N=1` stratum,
  `isPrime_vanishingIdeal_productRankLocusLE_stratum`) — Σ̄^r is reducible for deep `d`, which is exactly
  why L1's irreducibility-free reducible catenary is the right tool.
- No rank-raising / density lemma `exists_corner_eq_dominating_rankPattern` (the Route-1 sublemma).

---

## Kill-conditions for the chosen route (Route 2)

1. **`codim Σ^r = card − dim Σ^r` requires `Σ^r` nonempty.** KILL if `kostantPartitions d r` nonempty does
   NOT yield `Σ^r ≠ ∅`. → FALSE: `M₀ = realizerD hm₀ ∈ Σ^r` (L5+L6), so `Σ^r` nonempty whenever `h` holds.
   `h : (kostantPartitions d r).Nonempty` is already a parameter of the target theorem, and (for feasible
   `r ≤ min d`) is the same nonemptiness `hSigmaNe`/`hFne` the assembly already carries.
2. **The single-orbit witness must have codim EXACTLY `C`, not just `≤ C`.** KILL if the minimiser's orbit
   codim `> C`. → FALSE: `SigmaCodim` already proves `codimRepCanonical(orbitRankLocus(realizerD hm₀)) = C`
   (the `hreal` block); reused verbatim in L7.
3. **`ℕ∞` cancellation could be lossy.** KILL if `dim` could be `⊤`. → FALSE: catenary forces
   `codim + dim = card` finite, so `dim ≠ ⊤`; cancellation is the same `addLECancellable_of_ne_top` /
   `ENat.add_right_injective_of_ne_top` already used in `RouteCAssembly`.
4. **`codimRepCanonical_mono` direction.** KILL if mono is the wrong way. → CHECKED: it is anti-monotone
   (`Z ⊆ Z' → codim Z' ≤ codim Z`), which is exactly what L8 needs in both inequalities.

## Non-vacuity check at `(2,2,2)`, `r = 1` (on paper)

`card = card(RepCoord (2,2,2)) = 2·2 + 2·2 = 8`. `δ = r(d_N + d_0 − r) = 1·(2 + 2 − 1) = 3`.
`C = cCodim (2,2,2) 1 = 1` (the rank drop costs one corner condition). LANDED `dim Σ̄^1 = card − C = 7`.
Route 2: `dim Σ^1 = card − codim Σ^1 = 8 − 1 = 7 = dim Σ̄^1`. ✓ And via the sweep `dim Σ^1 = δ + dim F
= 3 + dim F`, so `dim F = 4`. ✓ matches the brief's δ=3, dim F=4, dim Σ^r = 7.

Component cross-check (why the set-closure Route 1 would also be TRUE here, but is overkill): the maximal
corner-`≤1` rank patterns on `(2,2,2)` are `(r_{01},r_{12},r_{02}) ∈ {(1,2,1),(2,1,1)}` — both corner
EXACTLY 1 (achievability forces `r_{02} ≥ r_{01}+r_{12}−d_1`, so corner `0` is impossible with a full
intermediate). So both top components of Σ̄^1 meet Σ^1; no component is trapped in Σ̄^0. The rank-raising
theorem holds here — but Route 2 never needs to know this.

Degenerate `r` kills: `r = 0` ⟹ `Σ^0 = Σ̄^0` (rank `= 0 ↔ ≤ 0`), `hClosure` is `rfl`-trivial.
`r = min_i d_i` ⟹ `Σ̄^r` is the whole space (corner can reach the max), still nonempty exact locus, route
gives `dim = card`. Infeasible `r > min d`: do NOT state without the `h`/feasibility hypothesis (Σ^r could
be empty; the target already carries `h`).
