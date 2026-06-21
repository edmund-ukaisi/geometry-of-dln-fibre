# Statement card — NullstellensatzCodim: the point-space ↔ PrimeSpectrum codimension bridge (L0)

Module `lean/DLNFibre/Core/NullstellensatzCodim.lean` (new file, imports `Core.NoetherMonicPositioning`,
`Core.OrbitCodim`, `Mathlib.RingTheory.Nullstellensatz`, `Mathlib.RingTheory.Spectrum.Prime.Topology`,
`Mathlib.Algebra.MvPolynomial.Funext`). Import appended to `DLNFibre.lean` (single-writer, no reorder).
Sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`). Commit `8b240be`.

**Scope (name = content).** Over `[Field k] [IsAlgClosed k]` and a finite coordinate index `σ` (our
`RepCoord d`), this file links the **geometric** codimension of a Zariski-closed `Z ⊆ (σ → k)` — the
`Ideal.height` of its vanishing ideal, the quantity `codimRep` reads — to the **variety dimension** of
`Z` (the Krull dimension of its coordinate ring `MvPolynomial σ k ⧸ vanishingIdeal Z`), via the
catenary identity `height p + dim (R/p) = n` for affine space. The catenary identity itself is the
L5 headline `height_add_ringKrullDim_quotient_eq` of `Core.NoetherMonicPositioning` (over `Fin n`,
any field); this file transports it to a `Fintype` index and reads it at `p = vanishingIdeal Z`. It
does **not** prove Voigt's lemma (`codimRep (orbitRankLocus M) = orbitLinearCodim M`) — that remains
`hVoigt`; this is the dimension↔codimension dictionary the eventual discharge will pair with the
orbit-closure variety-dimension count.

**Notation.** `vanishingIdeal k V`, `zeroLocus K I` = Mathlib's `MvPolynomial` Nullstellensatz objects
(I use `K := k`). `varietyDim Z := (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal k Z)).unbotD 0`
(`ℕ∞`; `⊥` → `0`, absent here since the relevant ideal is prime). `Nat.card σ` = ambient dimension.

`[IsAlgClosed k]` is a **hypothesis** (carried where the Nullstellensatz is used), not a citation.

---

> **Claim (bridge headline, additive, `ℕ∞`).** For an irreducible variety `Z ⊆ (σ → k)` (`σ` finite),
> i.e. `(vanishingIdeal k Z).IsPrime`, the geometric codimension (height of the vanishing ideal) plus
> the variety dimension equals the ambient dimension: `height (vanishingIdeal Z) + varietyDim Z =
> Nat.card σ`.
>
> - **Lean:** `height_vanishingIdeal_add_varietyDim_eq_card [Finite σ] {Z : Set (σ → k)}`
>   `(hp : (vanishingIdeal k Z).IsPrime) : (vanishingIdeal k Z).height + varietyDim Z = (Nat.card σ : ℕ∞)`.
> - **Gloss / proof.** Apply the finite-index catenary identity
>   `height_add_ringKrullDim_quotient_eq_card` at `p = vanishingIdeal Z` (a prime), giving the equality
>   in `WithBot ℕ∞`. The quotient is nontrivial (prime ⟹ `≠ ⊤`), so `ringKrullDim (R/p) ≥ 0`, hence
>   `≠ ⊥`, so `unbotD 0` recovers it; cast the `WithBot ℕ∞` equality down to `ℕ∞`.
> - **Proved.** Full additive equality. **Hypothesis:** `Finite σ`; `(vanishingIdeal Z).IsPrime` (the
>   algebraic content of "Z irreducible"). **Assumed / Cited / Deferred.** none — `[IsAlgClosed k]` is
>   not even needed for this additive form (it enters the radical/irreducibility/nonempty dictionary
>   pieces, not the catenary identity).

> **Claim (bridge headline, subtraction, `ℕ∞`).** Equivalent reading: `height (vanishingIdeal Z) =
> Nat.card σ − varietyDim Z` (`ℕ∞` subtraction; lossless since `varietyDim Z ≤ Nat.card σ`).
>
> - **Lean:** `height_vanishingIdeal_eq_card_sub_varietyDim [Finite σ] {Z}`
>   `(hp : (vanishingIdeal k Z).IsPrime) : (vanishingIdeal k Z).height = (Nat.card σ : ℕ∞) - varietyDim Z`.
> - **Gloss / proof.** From the additive identity; `varietyDim Z ≠ ⊤` (else the sum is `⊤ ≠ Nat.card σ`),
>   so `varietyDim Z` is `AddLECancellable` and `eq_tsub_of_add_eq` applies.
> - **Proved.** Full equality. **Hypothesis:** `Finite σ`, prime vanishing ideal. **Cited/Deferred.** none.

> **Claim (at `codimRep` / `codimRepCanonical`).** The bridge specialised to the geometry layer's
> consumer: `codimRep coord Z + varietyDim (coord '' Z) = Nat.card (RepCoord d)` and `codimRep coord Z
> = Nat.card (RepCoord d) − varietyDim (coord '' Z)` for `coord '' Z` an irreducible variety, plus the
> `canonicalCoord` specialisation `codimRepCanonical Z = Nat.card (RepCoord d) − varietyDim
> (canonicalCoord d '' Z)`.
>
> - **Lean:** `codimRep_add_varietyDim_eq_card`, `codimRep_eq_card_sub_varietyDim [IsAlgClosed k]`
>   `{d : Fin (N+1) → ℕ} (coord) (Z) (hp : (vanishingIdeal k (coord '' Z)).IsPrime)`;
>   `codimRepCanonical_eq_card_sub_varietyDim [IsAlgClosed k] {d} (Z) (hp : (vanishingIdeal k
>   (canonicalCoord d '' Z)).IsPrime)`.
> - **Gloss / proof.** `codimRep coord Z` is by definition `(vanishingIdeal (coord '' Z)).height`, so
>   these are the abstract bridge at `σ := RepCoord d` (Finite from `Core.OrbitCodim`), `Z := coord '' Z`.
> - **Proved.** Full equalities. **Hypothesis:** `(vanishingIdeal (coord '' Z)).IsPrime`. `[IsAlgClosed
>   k]` is carried (present on the corollaries for the geometric reading) but not consumed by the proof.
>   **Deferred.** the Voigt input `hVoigt` (geometric codim = `orbitLinearCodim`) and the orbit-closure
>   variety-dimension count are NOT here — this is the dictionary, not the discharge.

> **Claim (Nullstellensatz dictionary pieces).** Over `[IsAlgClosed k] [Finite σ]`: `vanishingIdeal Z`
> is radical; `Z` Zariski-irreducible ⟺ `vanishingIdeal Z` prime; a closed `Z` with prime vanishing
> ideal is nonempty.
>
> - **Lean:** `vanishingIdeal_isRadical [IsAlgClosed k] [Finite σ] (Z)`;
>   `isZariskiIrreducible_iff_isPrime_vanishingIdeal (Z) : IsZariskiIrreducible Z ↔ (vanishingIdeal k
>   Z).IsPrime` (no `Finite`/`IsAlgClosed` needed); `nonempty_of_isZariskiClosed_of_isPrime_vanishingIdeal
>   [IsAlgClosed k] [Finite σ] (hZ : IsZariskiClosed Z) (hp : prime) : Z.Nonempty`.
> - **Gloss / proof.** Radical: `vanishingIdeal Z = vanishingIdeal (zeroLocus (vanishingIdeal Z)) =
>   (vanishingIdeal Z).radical` (GaloisConnection `u_l_u_eq_u` + strong Nullstellensatz
>   `vanishingIdeal_zeroLocus_eq_radical`). Irreducible ⟺ prime: through the `pointToPoint` image, via
>   `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime` + `vanishingIdeal_pointToPoint`. Nonempty
>   (weak Nullstellensatz): if `Z = ∅` then `vanishingIdeal Z = ⊤`, but the strong Nullstellensatz forces
>   `(vanishingIdeal Z).radical = ⊤`, contradicting primality.
> - **Definitions.** `IsZariskiClosed Z := Z = zeroLocus k (vanishingIdeal k Z)` (topology-free closure
>   condition); `IsZariskiIrreducible Z := IsIrreducible (pointToPoint '' Z)` (point-space irreducibility
>   read through `Spec`). No topology installed on `σ → k` (Mathlib has none at this pin).
> - **Cited.** Mathlib's `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` /
>   `IsPrime.vanishingIdeal_zeroLocus` (strong Nullstellensatz, needs `[IsAlgClosed K] [Finite σ]`) and
>   `PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime` — these are Mathlib library results, used
>   not reproved.

> **Claim (finite-index dimension transport).** `ringKrullDim (MvPolynomial σ k) = Nat.card σ`; and the
> catenary identity over a `Fintype` index: `height p + ringKrullDim (R/p) = Nat.card σ` (`WithBot ℕ∞`)
> for prime `p`.
>
> - **Lean:** `ringKrullDim_mvPolynomial_finite [Finite σ]`;
>   `height_add_ringKrullDim_quotient_eq_card [Finite σ] (p) [p.IsPrime]`.
> - **Gloss / proof.** Dim: `MvPolynomial.ringKrullDim_of_isNoetherianRing` + `ringKrullDim k = 0`.
>   Transport: relabel `σ ≃ Fin (card σ)` (`Fintype.equivFin`), push the prime through `renameEquiv k e`,
>   apply the L5 `Fin n` headline `height_add_ringKrullDim_quotient_eq`, transport height and quotient
>   dim back by `height_map_algEquiv` / `ringKrullDim_quotient_map_algEquiv` (both from
>   `Core.NoetherMonicPositioning`), and rewrite `Nat.card = Fintype.card`.
> - **Cited.** `MvPolynomial.ringKrullDim_of_isNoetherianRing`, `ringKrullDim_eq_zero_of_field`,
>   `MvPolynomial.renameEquiv`, `Ideal.map_isPrime_of_equiv` (Mathlib). The L5 headline + transport
>   lemmas are our own committed engine.

> **Claim (non-vacuity witness).** At `Z = univ ⊆ (σ → k)` (`k` alg-closed, `σ` finite),
> `vanishingIdeal (univ) = ⊥` (prime), so the bridge fires: `0 + Nat.card σ = Nat.card σ`.
>
> - **Lean:** `vanishingIdeal_univ_eq_bot [IsAlgClosed k] : vanishingIdeal k (univ) = ⊥`; the witness is
>   the trailing `example` discharging `height (vanishingIdeal univ) + varietyDim univ = Nat.card σ`.
> - **Gloss.** A polynomial vanishing at every point of `σ → k` is `0` (`MvPolynomial.funext` over an
>   infinite integral domain; alg-closed ⟹ infinite). `⊥` is prime in the domain `MvPolynomial σ k`. The
>   dimension term (`= Nat.card σ`) carries the equality with a height-`0` ideal — non-vacuous, the
>   hypothesis is satisfiable.

---

## Audit

- `lean/scripts/sorries` → `0 sorry, 0 #exit, 0 native_decide, 0 axiom` (whole library).
- `lake build` green (2160 jobs); `lake build DLNFibre.Core.NullstellensatzCodim` green, no errors and
  no line-length / unused-variable warnings in the new code.
- `#print axioms` on `height_vanishingIdeal_add_varietyDim_eq_card`,
  `height_vanishingIdeal_eq_card_sub_varietyDim`, `codimRepCanonical_eq_card_sub_varietyDim`,
  `isZariskiIrreducible_iff_isPrime_vanishingIdeal`, `vanishingIdeal_isRadical`:
  `[propext, Classical.choice, Quot.sound]` only.
- Codex framing consult (`codex/framing-{prompt,answer}.md`, gpt-5.x xhigh): recommended (A)+hybrid —
  algebraic `IsPrime` hypothesis as the main, `IsZariskiClosed`/`IsZariskiIrreducible` predicates for the
  geometric reading, additive headline over lossy subtraction, no installed topology. Followed.
- Fidelity review (Lean ↔ informal claim): **PASS** (reviewer, 2026-06-19; decorrelated Codex at
  `codex/fidelity-review-{prompt,answer}.md`). All five checks survived: (1) bridge faithfully states
  "geometric codim + variety dim = ambient dim"; `varietyDim`/`unbotD 0` sound (never swallows a real
  `⊥`, excluded by the prime hypothesis); `codimRep coord Z` defeq `(vanishingIdeal (coord '' Z)).height`
  so the corollaries are honest specialisations; (2) `(vanishingIdeal Z).IsPrime` the right stand-in for
  irreducible; `[IsAlgClosed k]` on the `codimRep` corollaries verified carried-but-not-consumed;
  `[Finite σ]`-public / internal `Fintype.ofFinite` is the weakest-hypothesis choice; (3) all cited
  Mathlib lemmas used at their genuine signatures; (4) `Z = univ` witness genuine (non-vacuous); (5)
  build green, `scripts/sorries` = 0, `#print axioms` = `[propext, Classical.choice, Quot.sound]`. The
  headline is honestly about `Z`'s Zariski closure, caveat co-located in the docstrings. No discrepancy.
- **Status: sorry-free + reviewed.**

## Judgement calls

- **Headline additive, not subtraction (Codex-endorsed).** `ℕ∞`/`WithBot ℕ∞` truncated subtraction is
  lossy; the additive `height + dim = card` is the bedrock form. The subtraction corollaries are derived
  and labelled, lossless here because `varietyDim ≤ card`.
- **`[IsAlgClosed k]` carried, not consumed, by the catenary headlines.** The additive/subtraction
  dimension identities hold over any field (they ride the L5 catenary identity). `IsAlgClosed` is needed
  only for the radical / irreducible⟺prime / nonempty dictionary and the `Z = univ` witness. The
  `codimRep` corollaries carry `[IsAlgClosed k]` for the geometric reading (so the consumer states the
  hypothesis once), but the proof does not use it — an honest over-hypothesis on the corollary, not a hidden
  citation.
- **No topology on `σ → k`.** Mathlib v4.29 installs the Zariski topology only on `PrimeSpectrum`/`Proj`.
  Irreducibility is phrased through the `pointToPoint` image into `Spec`, matching the existing Mathlib
  dictionary, rather than inventing a point-space topology instance.
- **`varietyDim` as `ℕ∞` via `unbotD 0`.** Keeps the geometry-layer statement in `ℕ∞` (where `codimRep`
  lives); the `⊥` default never fires on a prime ideal (quotient nontrivial ⟹ dim `≥ 0`).

## Hardener pass (2026-06-19) — BEDROCK CONFIRMED

Independent principles/taste/bedrock pass (decorrelated from the fidelity reviewer). Verdict:
**BEDROCK CONFIRMED.** No critical findings; two minor hardening suggestions (controller's call).

Probed (all in-Lean, throwaway files, not committed):
- **Definitions honest, not gerrymandered (decorrelated Codex agreed).** `IsZariskiClosed Z = (Z =
  zeroLocus (vanishingIdeal Z))` is the closure-operator fixpoint (field-generic; correct at ∅/univ/finite).
  `IsZariskiIrreducible Z = IsIrreducible (pointToPoint '' Z)` is rescued to "closure of the image is
  irreducible" by Mathlib's `isIrreducible_iff_closure`, matching the genuine notion; ∅ correctly
  non-irreducible (`IsIrreducible` carries `Nonempty`). Image-not-closure is not a defect.
- **Non-vacuity at a GENUINE proper variety.** Bridge fires at a single point `{x}` (a real proper
  irreducible variety, prime by Mathlib instance): `varietyDim {x} = 0`, `height = Nat.card σ` (full
  codim) — both terms non-degenerate, strictly stronger than the `Z = univ` (height-0) in-file witness.
- **`unbotD 0` swallow confined off-hypothesis.** `varietyDim ∅ = 0` from a genuine `⊥` (`vanishingIdeal
  ∅ = ⊤`), but `⊤` not prime ⟹ no headline fires there; the in-file proof proves `ringKrullDim ≠ ⊥` from
  primality before unfolding. The default never bites under the stated hypothesis.
- **`[IsAlgClosed k]` placement verified by drop-probe.** Additive headline + `codimRep` corollary both
  typecheck with `[IsAlgClosed k]` REMOVED. Dropped correctly from the additive headline; carried-but-
  droppable on the `codimRep_*` corollaries — defensible (the geometric reading's consumer needs it to get
  irreducible⟹prime via the dictionary), not a hidden citation.
- **Hygiene:** axiom-clean (`propext, Classical.choice, Quot.sound`) on all 11 headlines; no
  `sorry`/`native_decide`/`axiom`; no `DLNFibre.DLN` import; whole library `scripts/sorries` = 0.

Minor hardening suggestions (non-blocking):
1. *(non-vacuity §2.1)* `IsZariskiClosed`/`IsZariskiIrreducible` have no in-file inhabitation `example`.
   Both are inhabited at `univ` (probed; `IsZariskiIrreducible univ` typechecks, `IsZariskiClosed univ`
   reduces to `Set.univ = ⊤`). A one-line `example` per predicate would close §2.1 cleanly.
2. *(precision §1.3)* The `[IsAlgClosed k]` on the `codimRep_*` corollaries is provably unused by their
   proofs. Defensible as a co-located geometric-reading hypothesis, but it is the one decorative-looking
   hypothesis; either keep with the existing docstring note or drop and let the consumer carry it.

Decorrelated Codex artefact: `codex/hardener-taste-{prompt,answer}.md`.
