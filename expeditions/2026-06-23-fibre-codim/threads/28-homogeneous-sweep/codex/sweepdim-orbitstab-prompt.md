# Codex consult (xhigh) — does the homogeneous sweep `dim Σ^r = δ + dim F` reduce to an orbit-stabilizer dimension theorem, or does it need a general product/fibre-dim theorem absent from Mathlib v4.29?

You are a Lean 4 + Mathlib (v4.29 PIN) algebraic-geometry / formalisation strategist. The project
formalises Lehalleur–Rimányi 2024 (fibres of the multiplication map of deep linear networks). I need a
DECISIVE adjudication of ONE reachability question. Two prior reads DISAGREE; break the tie with
engine-grounded reasoning. Do NOT write long proofs — give the cleanest decomposition, name the exact
missing theorem(s) if any, and a rough module-count. Highest reasoning effort.

## The setup (exact-certified on 9 cases, treat as ground truth)

`d = (d_0,...,d_N)`, `N≥1`, alg-closed char-0 `k`. `Rep_d = ∏_i Mat_{d_i × d_{i-1}}` (affine space,
coordinate ring a polynomial ring `R = k[RepCoord d]`, `card = Nat.card (RepCoord d)`).
`mult : Rep_d → Mat_{d_N×d_0}`, `A ↦ A_N⋯A_1`. `r ≤ min_i d_i`. `E` = rank-`r` normal form `[[I_r,0],[0,0]]`,
`F = fibre d E = mult⁻¹(E)`. `δ = r(d_N+d_0−r) = dim Mat^{=r}` (exact-rank-r matrices, a smooth
locally-closed homogeneous variety). `C = cCodim d r` (landed combinatorial codim).
`Σ^r = mult⁻¹(Mat^{=r})`, `Σ̄^r = productRankLocusLE d r = mult⁻¹(Mat^{≤r})`.

`H = GL_{d_N} × GL_{d_0}` acts on `Rep_d` through the TWO END vertices only (engine's
`BaseChange.baseChange`, inner units = 1). `mult` is H-equivariant: `mult(P•A) = P_N·mult(A)·P_0⁻¹`.
`Mat^{=r} = H·E` is a SINGLE H-orbit. Hence `Σ^r = H·F` (the H-sweep of the single fibre F).

TARGET (Step B, the one new rung): `varietyDim Σ^r = δ + varietyDim F`.

## The engine's EXISTING dimension method (ALL landed, sorry-free, v4.29) — the crux

The engine proves a dimension ONLY ONE WAY. For the SINGLE `G_d = ∏GL_{d_i}`-orbit-closure
`Z_M = orbitRankLocus M` (closure of one orbit of one tuple M), the chain is:

1. `OrbitPullbackDim.varietyDim_eq_ringKrullDim_range_orbitPullback` [Infinite k]:
   `varietyDim Z_M = (ringKrullDim (orbitPullback M).range).unbotD 0`, where `orbitPullback M : R →ₐ[k]
   groupRing d` is the ALGEBRA-MAP PULLBACK of the orbit parametrisation map `μ_M : G_d → Rep_d`,
   `g ↦ g•M`. `groupRing d = O(G_d)` (a localization of a poly ring; a domain). Proof: vanishingIdeal
   of the orbit-rank-locus = ker μ_M^* (Abeasis–Del Fra + orbit↔kernel), then 1st iso theorem so
   `R⧸ker ≃ₐ (orbitPullback M).range`, then `ringKrullDim_eq_of_ringEquiv`.
2. `AffineNoetherRank.ringKrullDim_range_orbitPullback_unbotD_eq_trdeg_toNat` (char-free):
   `ringKrullDim((orbitPullback M).range) = trdeg_k((orbitPullback M).range)`. Proof: Noether
   normalisation rank `s` of `ker` gives integral injective `k[Fin s] ↪ R⧸ker`, forcing BOTH
   `ringKrullDim = s` AND `trdeg = s` (`trdeg_eq_of_integral_injective` via `trdeg_add_eq` tower).
3. `JacobianTrdeg`/`OrbitImageDim`/`VoigtDischarge`: bound `trdeg((orbitPullback M).range) ≤
   finrank(range δ⁰)` (δ⁰ = orbit-tangent / deformation differential) via a char-0 differential
   criterion (`DiffIndepCriterion`, formal smoothness of the fraction field). The Voigt discharge
   SQUEEZES this to an EQUALITY `varietyDim Z_M = finrank(range δ⁰) = dim G_d − dim Stab_{G_d}(M)`.

So the engine's reusable dimension lemma is: **`varietyDim(closure of a SINGLE orbit) = trdeg of the
range of the orbit-parametrisation pullback = (orbit-tangent-space dim) = dim G − dim Stab`** — an
orbit-stabilizer dimension count, realised algebraically as trdeg-of-a-pullback-image, NOT a flatness
or generic-fibre-dim argument. There is NO general "dim total = dim base + dim fibre" theorem, NO
`trdeg(A⊗_k B) = trdeg A + trdeg B`, NO base-change dimension-invariance lemma in the engine, and (per
a Mathlib grep) none of those in Mathlib v4.29 either.

## The DECISIVE question

`Σ^r = H·F` is the sweep of a SINGLE fibre F (itself a reducible variety, a union of `G_d`-orbits) by
the group H. It is NOT a single G-orbit (F is not a point; the H-orbits in Σ^r are the H-translates of
F's points, but Σ^r is a union of MANY orbits parametrised by F). The action map `α : H × F → Σ^r`,
`(P, x) ↦ P•x`, is surjective with fibres = `Stab_H(E)`-cosets ⟺ `dim Σ^r = dim H + dim F − dim
Stab_H(E) = δ + dim F` (since `dim H − dim Stab_H(E) = dim(H·E) = dim Mat^{=r} = δ`).

**Q1 (the crux).** Does the engine's orbit-stabilizer dimension machinery (chain 1–3 above) extend to
this RELATIVE / SWEEP situation `Σ^r = H·F` WITHOUT a new general product-dim / base-change-invariance /
generic-fibre-dim theorem? Specifically:
  (a) Can `Σ^r = H·F` be presented as the closure of a SINGLE orbit of SOME group acting on SOME space,
      so that the engine's single-orbit chain applies verbatim (e.g. `H × F`-as-domain, or the action
      groupoid)? Or is it irreducibly a "family of orbits" (F is positive-dimensional, so `H·F` is not
      one orbit) for which chain 1–3 gives nothing?
  (b) The engine computes `trdeg(range of orbit-pullback)`. For the sweep, the analogous object is the
      pullback of `α : H × F → Σ^r`, i.e. `α^* : R → O(H × F) = O(H) ⊗_k O(F)`. To get `dim Σ^r =
      trdeg(α^*.range)` and then `= dim H + dim F − dim Stab`, what EXACTLY is needed? Is
      `trdeg(α^*.range) = δ + trdeg(O(F))` derivable from the engine's `trdeg_add_eq` tower /
      Noether-rank machinery, or does it require `trdeg(O(H)⊗O(F)) = trdeg O(H) + trdeg O(F)`
      (product/tensor trdeg, ABSENT)?
  (c) Is the cleanest honest route actually to DROP the orbit-stabilizer framing and instead use the
      catenary/height machinery the engine ALSO has (prime catenary `height I + ringKrullDim(R⧸I) =
      card`; affine-domain nested equidim `affine_domain_height_add_ringKrullDim_quotient_eq_fintype`)?
      i.e. compute `codim_{Σ̄^r} F` (the height of F's ideal in the coordinate ring of Σ̄^r) `= δ`
      directly as "the generic fibre of mult|_{Σ̄^r} over the δ-dim'l homogeneous base Mat^{≤r}", then
      `codim_{Rep} F = codim_{Σ̄^r} F + codim_{Rep} Σ̄^r = δ + C` by composing heights. Does HOMOGENEITY
      of the base (all fibres over Mat^{=r} literally H-isomorphic) let you get the relative codim = δ
      WITHOUT a general Chevalley upper-semicontinuity / generic-flatness theorem (both ABSENT)?

**Q2.** If a general theorem IS unavoidable, name the SMALLEST one precisely and estimate its
from-scratch module cost at the v4.29 pin: candidates are
  - product/tensor trdeg `trdeg_k(A ⊗_k B) = trdeg A + trdeg B` for f.g. domains;
  - `ringKrullDim(A ⊗_k B) = ringKrullDim A + ringKrullDim B` (f.g. `k`-algebras over a field);
  - base-change dimension-invariance (dim preserved under the H-translation — note the engine ALREADY
    has linear-coordinate height-invariance via `RingEquiv.height_comap` for a SINGLE base change P,
    `codimRepCanonical_fibre_baseChange`; does the SWEEP need more than a 1-parameter family of these?);
  - a relative/equivariant orbit-dim theorem (the action map α has uniform Stab-coset fibres BY
    HOMOGENEITY — is the uniform-fibre-dim ⟹ total-dim = base+fibre derivable, or is that itself the
    missing generic-fibre-dim theorem?);
  - the Step-C closure/density `vanishingIdeal Σ^r = vanishingIdeal Σ̄^r` (i.e. `Σ̄^r = closure Σ^r`).
  Which is genuinely needed, and which (if any) is small enough that the residual should be BUILT rather
  than carried as a named Cited hypothesis?

**Q3 (the verdict).** Give a one-paragraph VERDICT: is Step B (a) REACHABLE from the engine's existing
orbit-stabilizer / catenary machinery with only small/zero new general theorems (give the precise lemma
chain + rough module cost), or (b) MATHLIB-ABSENT — it requires a genuinely new general
product-dim/base-change/generic-fibre-dim theorem (name it + rough cost to build, or whether it should be
the NAMED Cited residual of the headline). Be decisive. State the single biggest risk of formalising a
subtly-WRONG statement (e.g. an off-by-`dim Stab` error, or a false `dim Σ^r = δ + dim F` when F is
reducible / when Σ^r has components of differing dimension).
