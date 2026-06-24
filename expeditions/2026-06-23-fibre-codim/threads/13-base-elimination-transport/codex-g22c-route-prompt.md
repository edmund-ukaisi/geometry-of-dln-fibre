# Lean 4 / Mathlib v4.29 — architecture review for the FINAL localized base-ring transport (G2-2c)

I am a Lean formaliser. I need the cleanest, lowest-friction architecture for the final ~80–100 LoC
of a localized base-ring presentation. The heavy infra is ALL LANDED, sorry-free, axiom-clean. I want
a sanity check on the ROUTE before I grind, especially the localization/graph-ideal interplay.

## Objects (all LANDED unless marked NEW)
- `k` : a field. `IsAlgClosed k`, `CharZero k` available.
- `A_eng = MvPolynomial (RepCoord (dStratum q p)) k`  -- the engine coordinate ring (a poly ring over k).
- `detΔ : A_eng`  (= `detPivotPoly q p r hp hq`)  -- the pivot minor.
- `A_loc = Localization.Away detΔ`.  (algebra over A_eng)
- `Iad = (sigmaIdeal (dStratum q p) r).map (algebraMap A_eng A_loc)`  -- the localized base ideal.
  LANDED: `Iad.height = C` (= `(p-r)*(q-r)`), `Iad` is prime (localization of a prime, disjoint from powers of detΔ).
- `blockAlgEquiv : A_eng ≃ₐ[k] MvPolynomial B22block (MvPolynomial SchurVar k)` (LANDED),
  with `blockAlgEquiv detΔ = C (detSchurS)` (LANDED, `detSchurS : MvPolynomial SchurVar k`).
  `#B22block = C`, `#SchurVar = δ`.
- `Sd = Localization.Away detSchurS`  -- localization of `MvPolynomial SchurVar k` at detSchurS.
- LANDED engine: `height_graphIdeal_eq (c : σ → MvPolynomial τ k) : (graphIdeal c).height = Nat.card σ`
  for σ τ finite, over `MvPolynomial σ (MvPolynomial τ k)`. (`graphIdeal c = span (range fun i ↦ X i - C (c i))`.)
- LANDED: `graphIdeal_isPrime [IsDomain R] (c : ι → R) : (graphIdeal c).IsPrime`.
- LANDED: `graphIdealQuotientEquiv (c : ι → R) : (MvPolynomial ι R ⧸ graphIdeal c) ≃ₐ[R] R`.
- LANDED: `J ⊆ Iad` seed — every (r+1)-minor of the generic product is in `sigmaIdeal`
  (`det_submatrix_multPoly_mem_sigmaIdeal`).
- Mathlib v4.29: `IsLocalization.height_map_of_disjoint`, `MvPolynomial.isLocalization`
  (`MvPolynomial σ S` is the localization of `MvPolynomial σ R` at `M.map C` when S = loc of R at M),
  `Ideal.height_strict_mono_of_is_prime`, `height_map_algEquiv` (alg-equiv preserves height).

## The TARGET
`A_loc / Iad ≅ₐ[k] Sd`  (Sd regular poly-localization of dim δ), J internal.
The honest hard direction is `Iad ⊆ J` (injectivity of `Sd → A_loc/Iad`); I must EARN it, not assume.

## The chosen route (a): height-squeeze
1. Build a prime ideal `J ⊆ A_loc` (graph ideal of the forced B22 = B21 Δ⁻¹ B12 value, transported).
2. `height J = C`.
3. `J ⊆ Iad` (from the minor seed).
4. `Iad = J` by `height_strict_mono_of_is_prime`: J ⊆ Iad, both prime, height J = height Iad = C ⟹ no strict ⟹ equal.
5. `A_loc/Iad = A_loc/J ≅ Sd` via `graphIdealQuotientEquiv` transported.

## MY KEY WORRY — the localization/graph-ideal mismatch for step 2
`height_graphIdeal_eq` is stated over a POLYNOMIAL ring `MvPolynomial σ (MvPolynomial τ k)`.
But `A_loc` (≅ MvPolynomial B22block Sd via localized blockAlgEquiv) has coefficient ring `Sd`,
which is a LOCALIZATION of `MvPolynomial SchurVar k`, NOT a polynomial ring `MvPolynomial τ k`.
So `height_graphIdeal_eq` does NOT directly apply over `A_loc`.

QUESTION 1: What is the cleanest way to get `height J = C` over `A_loc`?
Two candidate sub-routes:
  (2a) Compute `height J_unloc = C` over the UN-localized `A_eng` (where the reindex gives
       `MvPolynomial σ (MvPolynomial τ k)`, so `height_graphIdeal_eq` applies via the translation
       automorphism to the coordinate ideal), then transport to `A_loc` via
       `IsLocalization.height_map_of_disjoint` (J_unloc disjoint from powers of detΔ).
       BUT: is `J_unloc` (the un-localized forced-B22 graph ideal) even well-defined? The forced value
       B22 = B21 adj(Δ) B12 / detΔ involves detΔ⁻¹, which doesn't exist in A_eng. So the un-localized
       graph ideal isn't literally a graph ideal over A_eng.
  (2b) Localize the LANDED `height_graphIdeal_eq` result directly: over `MvPolynomial B22block Sd`
       (= localization of `MvPolynomial B22block (MvPolynomial SchurVar k)` at `C detSchurS`),
       does `height (graphIdeal (forced : B22block → Sd)) = #B22block` follow from the un-localized
       `height (graphIdeal (forced0 : B22block → MvPolynomial SchurVar k)) = #B22block`
       (where forced0 = B21 adj(Δ) B12, NUMERATOR only, no division) via height_map_of_disjoint?
       i.e. is `graphIdeal (forced_loc)` = `(graphIdeal forced0).map (loc map)`? This needs the forced
       value over Sd to be the IMAGE of forced0 — but forced_loc = forced0 / detSchurS ≠ image of forced0.
       So `X_b - C(forced_loc b)` ≠ image of `X_b - C(forced0 b)`. Mismatch again.

Which sub-route is correct, and how do I handle the detΔ⁻¹ in the forced value cleanly? Is there a
slicker formulation where J is the graph ideal over `Sd` directly (forced : B22block → Sd, with the
genuine forced value B21 adj(Δ) B12 * detSchurS⁻¹ ∈ Sd), and `height_graphIdeal_eq` is replaced by a
"graph ideal over ANY domain that is a localization of a poly ring" height fact? Does the catenary
argument behind `height_graphIdeal_eq` survive replacing `MvPolynomial τ k` by `Sd`?

QUESTION 2: Actually — do I even need `height J = C` via the graph ideal, OR is there a shortcut?
Since `A_loc/Iad ≅ Sd` is the TARGET and `Sd` has dim δ, and `A_loc` has dim... hmm. Alternative:
Could I get the equiv `A_loc/Iad ≅ Sd` MORE directly? E.g. localize blockAlgEquiv to
`A_loc ≅ MvPolynomial B22block Sd`, then the forced-B22 graph ideal `J' ⊆ MvPolynomial B22block Sd`
has quotient `Sd` by `graphIdealQuotientEquiv` and height `#B22block` by some graph-ideal-height-over-Sd
fact, then squeeze `Iad' = J'` where `Iad'` is the image of Iad. Is the graph-ideal-height-over-Sd
the genuine remaining gap, and is it provable by the SAME catenary route (Sd is Noetherian, a domain,
`ringKrullDim Sd = δ` since localization of dim-δ poly ring at a nonzero element... wait, does
localization preserve Krull dim here? Localization.Away can DROP dimension)?

Give me the cleanest correct route for step 2, flag any dimension-of-localization trap, and tell me
which of (2a)/(2b)/(Q2-direct) is lowest friction at v4.29. Be concrete about the forced value's
detΔ⁻¹.
