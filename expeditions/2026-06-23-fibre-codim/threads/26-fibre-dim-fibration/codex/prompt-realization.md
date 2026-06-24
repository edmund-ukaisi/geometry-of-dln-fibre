# Codex consult — cleanest Lean realization of the generic-fibre-dimension count (Lean 4 / Mathlib v4.29)

## Context (a formalisation in an affine-algebraic-geometry engine, no schemes)

I am formalising, in Lean 4 + Mathlib v4.29, the fibre-codimension of the multiplication map of deep
linear networks. The "engine" is entirely affine: varieties are subsets `Z ⊆ (σ → k)` (`k` an
algebraically closed field), codimension is `Ideal.height (vanishingIdeal Z)` in `MvPolynomial σ k`,
and dimension is `varietyDim Z := (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal Z)).unbotD 0`.
There are NO schemes, NO morphisms of schemes — only ideals, heights, ring Krull dims, and trdeg.

Concretely, for a dimension vector `d : Fin (N+1) → ℕ`:
- `Rep_d` = tuples of matrices `(A_1,…,A_N)`, `A_i : Mat_{d_{i+1} × d_i}`. Coordinates `RepCoord d`,
  `card = Σ_i d_{i+1} d_i`.
- `mult d A = A_N ⋯ A_1 : Mat_{d_N × d_0}`.
- `fibre d B = {A | mult d A = B}`.
- `Σ̄^r = productRankLocusLE d r = {A | rank(mult d A) ≤ r}`.
- `Mat^{≤r} = productRankLocusLE ![n,m] r` (the `N=1` rank-≤r determinantal variety in the TARGET).

## What is already LANDED (sorry-free, axiom-clean) — the engine handles

1. `codimRepCanonical Z = Ideal.height (vanishingIdeal (canonicalCoord '' Z))` (definition). Radical-
   insensitive: `= height (fibreGenIdeal d B)` for the fibre (H1).
2. **Reducible-friendly codim.** `Ideal.height I = ⨅ over I.minimalPrimes, primeHeight` — so
   `codimRepCanonical` of a REDUCIBLE locus is the MINIMUM over its irreducible components' heights.
   (`SigmaCodim` exploits exactly this: `codimRepCanonical Σ̄^r = ⨅_M codimRepCanonical(orbitClosure_M)`.)
3. `codimRepCanonical Σ̄^r = C := cCodim d r` (`SigmaCodim`, general r). Via the catenary bridge ⟹
   `varietyDim Σ̄^r = card − C` (but Σ̄^r is also reducible — see Q below).
4. `varietyDim (Mat^{≤r}) = δ := r(n+m−r)` (`DeterminantalStratumDim`, `[IsAlgClosed][CharZero]`,
   r≤n, r≤m). The `Mat^{≤r}` vanishing ideal IS prime here (single determinantal variety, irreducible).
5. **Catenary closer (PRIMALITY-GATED):** `codimRepCanonical Z = card − varietyDim Z` requires
   `vanishingIdeal (canonicalCoord '' Z)` to be PRIME (irreducible Z). [`NullstellensatzCodim`]
6. **Affine-domain equidimensionality (NO flatness):** for `A = MvPolynomial(Fin n) k ⧸ I` (I prime, so
   A a f.g. domain) and a prime `p` of A: `height p + ringKrullDim(A ⧸ p) = ringKrullDim A`.
   [`AffineDomainDimension.affine_domain_height_add_ringKrullDim_quotient_eq`]
7. **`ringKrullDim = trdeg`** for an f.g. domain quotient `MvPolynomial(Fin n) k ⧸ p`:
   `(ringKrullDim (R ⧸ p)).unbotD 0 = (trdeg k (R ⧸ p)).toNat`. [`AffineNoetherRank`] Plus
   `trdeg_eq_of_integral_injective` (integral injective `k[Fin s] →ₐ B` ⟹ `trdeg k B = s`).
8. **Comorphism of mult:** `multComap d : MvPolynomial(Fin d_N × Fin d_0) k →ₐ[k] MvPolynomial(RepCoord d) k`
   sending target-entry variable `X(r,c) ↦ multPoly d r c` (the generic product entry). `eval`-compatible.

## The certified math (the FIBRATION dimension count)

`mult|_{Σ̄^r} : Σ̄^r ↠ Mat^{≤r}` is dominant; `E = diag(I_r,0)` is a generic (rank-exactly-r) point of
`Mat^{≤r}`. Generic-fibre-dimension ⟹ `dim(fibre over E) = dim Σ̄^r − dim Mat^{≤r} = (card − C) − δ`.
Hence `codimRepCanonical(fibre E) = C + δ`. The fibre is REDUCIBLE; the equality is the TOP-component
dim. Hypothesis `r ≤ min_i d_i`. Certified pen-and-paper (Singular Krull dim, 13 cases incl N=3;
sympy Jacobian). NO flatness, NO scheme trivialization (that route walled earlier — circularity in a
deep flat iso `e`).

## THE QUESTION — the cleanest LEAN realization, given NO scheme morphisms

The thread's stated target is the GLOBAL `varietyDim(fibre E) = card − C − δ`, then the LANDED catenary
closer (5). But closer (5) needs PRIMALITY, and the fibre is REDUCIBLE. So the literal route is blocked.
Two candidate realizations:

**Route A (global varietyDim).** Prove `varietyDim(fibre) = card−C−δ` as the MAX over components, then
need a REDUCIBLE-friendly catenary closer `codimRepCanonical Z = card − varietyDim Z` (min-height =
card − max-dim). Does such a closer follow cheaply from (5) + (2) per-component + (6)? Or must I prove
"every component has dim ≤ card−C−δ AND one attains it"? The dominant-map fibration argument is usually
phrased schematically (`dim total = dim base + dim generic fibre`) — but I have NO scheme morphism, only
the ring map `multComap` (closed point B is NOT generic; `multComap` is NOT flat).

**Route B (per-component height, mirroring SigmaCodim).** `codimRepCanonical(fibre E) = ⨅ over min primes
P of fibreGenIdeal, primeHeight P`. Prove (b1) every P has `height P ≥ C+δ`, (b2) one P attains `C+δ`.
Then `⨅ = C+δ` directly — NO global varietyDim, NO primality of the whole fibre.

**Sub-questions:**
1. WITHOUT a scheme-morphism `dim total = dim base + dim fibre` theorem and WITHOUT flatness, how do I
   realize the fibration dimension count in this affine ideal/height/trdeg engine? The honest content of
   "dim fibre over E = dim Σ̄^r − dim Mat^{≤r}": is there a clean trdeg-additivity statement
   `trdeg(O(top comp of Σ̄^r)) = trdeg(O(Mat^{≤r})) + trdeg_{Frac}(generic fibre)` I can build from
   handle (7) + the injective `O(Mat^{≤r}) ↪ O(top comp)` (dominant ⟹ injective on coordinate rings)?
   Mathlib v4.29: is there `Algebra.trdeg`-additivity in a tower `k → A → B` with B a domain f.g. over A?
   (We have `trdeg_add_eq k A B` — tower additivity of trdeg — used in handle (7). Can that carry the
   fibration count if I localize at the generic point / pass to fraction fields?)
2. Is Route A's reducible-friendly catenary closer derivable, or is Route B (per-component height,
   no global varietyDim) strictly cleaner given the SigmaCodim precedent (handle 2,3)? Note SigmaCodim
   NEVER computes a global varietyDim — it goes straight to `⨅ over minimal primes`.
3. The generic fibre of a dominant map of irreducible varieties has dim = dim(source comp) − dim(target).
   In the affine ring language: the top component `W ⊆ Σ̄^r` (a maximal orbit closure, irreducible,
   `O(W) = MvPolynomial ⧸ p_W`), the restricted ring map `O(Mat^{≤r}) → O(W)` (injective: dominant),
   and the fibre over the maximal ideal `m_E`. Generic-fibre-dim = `dim O(W) − dim O(base)`. Can I get
   this from handle (6) applied to a prime of `O(W)` lying over `m_E`, PLUS the fact that `m_E` has
   `height = dim O(base) = δ` (since `Mat^{≤r}` irreducible, `m_E` maximal, handle in AffineDomainDimension
   `height_eq_ringKrullDim_of_isMaximal`)? I.e.: pick `P` a minimal prime of `m_E · O(W)` (the fibre
   component); `height P = height(m_E in base) + height(P relative to m_E·O(W)) = δ + 0`? But that
   additivity (going-down for `O(base) → O(W)`) needs FLATNESS or going-down — which fails globally.
   IS THERE A WAY without flatness? (The certified math says generic flatness is FREE — but Mathlib
   v4.29 generic-flatness?) OR: avoid the relative-height entirely and use trdeg-additivity (sub-Q1)?
4. Given the reducibility scope (the equality is the TOP component), what is the MINIMAL set of facts
   about `E`/the top component I actually need? Can I sidestep IDENTIFYING the top component by proving
   the two-sided bound directly: `codimRepCanonical(fibre E) ≤ C+δ` (exhibit ONE component of height
   ≤ C+δ — the dominant-map image / a generic point) AND `≥ C+δ` (every component, lower-semicontinuity
   /Krull's height theorem: fibre cut by δ+? equations… but the generators are d_N·d_0 ≫ δ)? Which
   direction is the hard one and what is the cleanest lever for it in this engine?

Please give: (a) which route (A global-varietyDim vs B per-component-height) is cleaner in THIS affine
engine and why; (b) the precise trdeg/height-additivity statement that carries the fibration count
WITHOUT a scheme morphism and WITHOUT global flatness, and whether it is buildable from handles (6)(7)
at v4.29; (c) the decomposition into 3–6 sub-lemmas with the hard rung named; (d) any Mathlib v4.29
trdeg/dimension lemma I should check exists before building (exact names). Be concrete and skeptical —
flag any step that secretly needs flatness or the walled scheme iso.
