# Lean 4 + Mathlib v4.29 encoding strategy: localized determinantal base presentation

You are an independent second model advising on the CONCRETE Lean 4 encoding of a formalisation,
in Mathlib v4.29. I have a GO on the mathematics (generator-free Schur-graph-ideal route, verified).
I need the cleanest Lean architecture — which ring is source/target, how to build the comorphism,
how to get the iso — that MINIMIZES proof friction. Be concrete with Mathlib lemma names. Flag
friction points. Propose the architecture you would actually write.

## The objects (all confirmed to typecheck in Lean already)

- Field `k`, `[Field k] [IsAlgClosed k] [CharZero k]`. Fix `r b c : ℕ` (with `b = p−r`, `c = q−r`).
  Set `p = r + b`, `q = r + c`.
- **Engine ring** `A_eng := MvPolynomial (RepCoord ![q,p]) k`, where `RepCoord ![q,p] =
  Σ _ : Fin 1, Fin p × Fin q` — i.e. `pq` variables, one per entry of a `p×q` matrix (the entry
  `(i,j)` of the single matrix `M`). The determinantal base is `Σ̄^r = productRankLocusLE ![q,p] r`
  (matrices of rank ≤ r), and its vanishing ideal `I := vanishingIdeal k (canonicalCoord ![q,p] ''
  Σ̄^r) : Ideal A_eng` is PRIME (landed: `isPrime_vanishingIdeal_productRankLocusLE_stratum`) of
  height `C = b*c` (landed: Brick A `codimRepCanonical_productRankLocusLE_eq_cCodim`).
- **Free Schur ring** `S := MvPolynomial (SchurVar r b c) k`, where `SchurVar r b c =
  (Fin r × Fin r) ⊕ (Fin r × Fin c) ⊕ (Fin b × Fin r)` — `r² + rc + br = δ` variables for the free
  blocks `Δ, B12, B21`. `det Δ_S` (`Δ_S i j = X (inl (i,j))`) is a nonzero element of `S`.
- The top-left `r×r` minor `det Δ` of `M`, as a polynomial `dΔ ∈ A_eng`, is `det` of the submatrix
  `(i,j) ↦ X ⟨0,(castLE i, castLE j)⟩` for `i,j : Fin r` (the top-left block of the `p×q` entry
  variables). I have G2-1's MATRIX-level fact `rank (fromBlocks Δ B12 B21 B22) = r ⟺ B22 =
  B21 Δ⁻¹ B12` (on `det Δ ≠ 0`) and the point-bijection `pivotRankChartEquiv`.

## The target (GO'd by the controller)

> `R_base` localized at `det Δ`  ≅ₐ[k]  the free Schur localization `S` localized at `det Δ_S`,

where `R_base = A_eng ⧸ I`. The intermediate is the **Schur graph ideal** `J`: in the localization
`(A_eng)_{dΔ}`, `J = (the localized images of the polynomials `dΔ·B22_{ab} − (B21·adj(Δ)·B12)_{ab}`)`.
The proof: `J ⊆ I_loc` (because `dΔ·g_ab` vanishes on all of `Σ̄^r` — on the chart by G2-1, on
`V(dΔ)` trivially — so `dΔ·g_ab ∈ I`, then `g_ab ∈ I_loc`); then `J = I_loc` by height comparison
(both prime of height `C`; `Ideal.height_strict_mono_of_is_prime`); finally `(A_eng)_{dΔ} / I_loc ≅
S_{dΔ_S}` because modding by `J` eliminates the `B22` block, leaving the free `Δ,B12,B21` localized.

## Specific encoding questions — be concrete

1. **Direction of the comorphism + which ring carries the localization.** Two options:
   (A) Build an algebra map `φ : S → (A_eng)_{dΔ}` sending free generators to the entry-variables of
       the corresponding blocks, prove `φ` factors through `S_{dΔ_S} → (A_eng)_{dΔ}` (sends `dΔ_S` to
       a unit), show it lands in / induces the iso to `R_base,loc`.
   (B) Build `ψ : A_eng → S_{dΔ_S}` sending each entry-variable to its block generator and the `B22`
       entries to the Schur expression `B21·adj(Δ)·B12 / dΔ_S`, show `I ⊆ ker ψ_loc`, get the induced
       `R_base,loc → S_{dΔ_S}`, and prove it's the inverse of (A).
   Which direction is LESS friction in Lean? My instinct: (B) gives surjectivity for free
   (`MvPolynomial.aeval` is surjective onto generators) so `Ideal.quotientKerAlgEquivOfSurjective`
   applies, but then I must identify `ker ψ_loc` with `I_loc` — is that the same height-comparison?
   And (A) needs me to prove `φ` surjective which is harder. Recommend one and say why.

2. **The Schur expression `B21·adj(Δ)·B12 / dΔ`.** In Mathlib v4.29, to write the `B22`-image under
   `ψ`, I'd use `Matrix.adjugate` (`adj Δ`) so the entries are polynomials and the division is just
   `* (IsLocalization.Away.invSelf dΔ_S)`. Is `Matrix.adjugate` + `Matrix.mul_adjugate`
   (`Δ * adj Δ = det Δ • 1`) the right toolkit, avoiding `Δ⁻¹` (`Matrix.inv`, which needs `det` a
   unit and is messier in a polynomial ring)? Confirm the cleanest way to state "the `(a,b)` entry of
   `B21 adj(Δ) B12` over `dΔ`" as an element of `S_{dΔ_S}`.

3. **`dΔ·g_ab ∈ I` via the engine's `vanishingIdeal`.** `I = vanishingIdeal (canonicalCoord '' Σ̄^r)`,
   so membership is `∀ A ∈ Σ̄^r, eval (canonicalCoord A) (dΔ·g_ab) = 0` (`mem_vanishingIdeal_iff`).
   For `A` with `det Δ(A) ≠ 0`: rank ≤ r AND det Δ ≠ 0 forces rank = r (top-left r×r minor nonzero
   ⟹ rank ≥ r), so G2-1's `rank = r ⟺ Schur` gives `g_ab(A)=0`. For `det Δ(A) = 0`: `dΔ(A)=0` so the
   product is `0`. Is this the cleanest case split, and does the "rank ≤ r ∧ det Δ ≠ 0 ⟹ rank = r"
   step have clean Mathlib support (`Matrix.rank` vs nonzero minor — is there `r ≤ rank` from a
   nonzero `r×r` minor)? Name the lemma if it exists.

4. **Localized-ideal height transport.** To compare heights of `J` and `I_loc` in `(A_eng)_{dΔ}`:
   `IsLocalization.height_comap` gives `(P.comap (algebraMap A_eng (A_eng)_dΔ)).height = P.height`.
   What is the cleanest way to get `height (I_loc) = height I = C` (the localization preserves the
   height of `I` since `dΔ ∉ I`, `I` prime), and `height J = C` (from the explicit `S_dΔ ≅ A_eng_dΔ/J`
   being a δ-dim domain via the poly bridge: `height J = pq − δ = C`)? Is there an
   `IsLocalization.height_map`/`primeHeight` of a localized prime not meeting the monoid? Name it.

5. **Is the FULL AlgEquiv worth it, or should the headline be the IDEAL EQUALITY `I_loc = J`?**
   The downstream chain (G2-4) consumes "R_base,loc is a free polynomial localization" for height
   transport `height(m_E) = δ`. Would stating the headline as the ideal equality `I_loc = J` (plus a
   corollary `R_base,loc ≅ S_{dΔ_S}`) be MORE robust / less friction than leading with the AlgEquiv?
   Or does the AlgEquiv carry strictly more and compose better?

## What I need back
A recommended concrete architecture: the source/target rings, the ONE comorphism to build and its
direction, the Mathlib lemmas for each of (2),(3),(4), and a verdict on (5). Plus the single biggest
friction risk in v4.29 and how to dodge it. Be specific and adversarial about where this will fight me.
