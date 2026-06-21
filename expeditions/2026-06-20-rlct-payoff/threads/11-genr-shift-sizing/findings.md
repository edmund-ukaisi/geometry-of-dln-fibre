# Thread 11 — general-`r` bundle-shift sizing (pen-and-paper, Codex-convergent)

## Verdict

**The bundle shift `codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)` (Lemma 4.6, `B` of rank `r`) is
NOT zero-cited-provable at Mathlib v4.29. CITE Lemma 4.6 — the shift NAMED in the carried statement.**
Same posture as the Aoyagi rlct value: a published geometric fact whose proof needs a
fibre-dimension / locally-trivial-bundle theorem Mathlib does not have, and which the landed
route-c (voigt L2b★) does *not* supply for this map.

But the general-`r` payoff splits into **two bricks of different status**, and only one is the wall:

| Brick | Statement | Status | Why |
|---|---|---|---|
| **A** (orbit-closure) | `codim Σ̄^r = cCodim d r` | **PROVE zero-cited** | the *same* landed orbit-closure machinery that proved `r=0`, run at general `r`; `Σ̄^r` is GL_d-stable and a finite union of orbit closures (`sigmaIdeal d r = sInf orbitIdeals`, **general in `r`**). No fibre-dim wall. |
| **B** (bundle shift) | `codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)` | **CITE Lemma 4.6** | hits the fibre-dim wall: `mult⁻¹(B)` (for `B≠0`) is *not* GL_d-stable, *not* an orbit closure, *not* a single inner-group orbit; the proof is a locally-trivial-bundle dimension count Mathlib lacks. |

Honest general-`r` headline: **PROVE Brick A + CITE Brick B**. Naming a single
`codim mult⁻¹(B) = C + shift` theorem as "proved" would be the overclaim CLAUDE.md warns against;
the proved part is `codim Σ̄^r = C`, the cited part is the `+ shift` to the fibre.

## The four routes, sized (decorrelated Codex converged on all four)

Decisive Mathlib gaps (re-confirmed by grep at the v4.29 pin, not assumed): **no** fibre-dimension
theorem (`dim total = dim base + dim fibre` over a flat/smooth/dominant/locally-trivial map); **no**
algebraic-group quotient `G/H` scheme or `dim orbit = dim G − dim Stab`; **no** `dim` of a Zariski
locally-trivial bundle; **no** general `trdeg ↔ ringKrullDim` bridge in the shipped library.
`Chevalley.lean` gives *constructibility* of an image, not its *dimension*.

### Route 1 — Direct fibre-codim via the landed `codimRep`/`Ideal.height` machinery — **BLOCKED**
The landed `codimRepCanonical (orbitRankLocus M) = orbitLinearCodim M` (the Voigt discharge) computes
the codim of a **single GL_d orbit closure** (a determinantal rank locus, GL_d-stable). The `r=0`
payoff worked *because* `fibre d 0 = Σ̄^0` is itself a finite union of such orbit closures.

For `B ≠ 0` this structure is **gone**: `mult(P•A) = P_N·mult(A)·P_0⁻¹`, so the full GL_d action moves
`mult⁻¹(B)` to a *different* fibre — not GL_d-stable, hence not a union of orbit closures. I checked the
next-best hope (single *inner*-group `G_in = ∏_{0<i<N} GL_{d_i}` orbit?): on `(2,2,2)`, `r=1`, the
inner-`GL_2` stabiliser of the fibre point `A₁=A₂=[[1,0],[0,0]]` is 1-dimensional, so its inner orbit is
`≤ 3`-dim while the fibre is **4**-dim — the fibre is strictly larger than any single inner orbit. The
landed machinery does not apply. **Missing theorem to unblock:** `codim(fibre over a point of a smooth
homogeneous base) = codim(total rank locus) + dim(base)` — i.e. the bundle theorem itself.

### Route 2 — Homogeneous-fibration (`Σ^r = ⊔_{rk B'=r} mult⁻¹(B')`, single `G_out`-orbit base) — **HITS THE SAME WALL**
The math is right: `Mat^{rk=r}_{d_N,d_0}` is one `G_out = GL_{d_N}×GL_{d_0}` orbit of dim `r(d_0+d_N−r)`,
all fibres are `G_out`-translates hence isomorphic, so `dim Σ^r = dim(fibre) + dim(base)`. But the
homogeneity does **not** dodge the wall. The step "all fibres isomorphic ⟹ dim of the union = fibre +
base" *is* the fibre-dimension / local-triviality theorem (one needs local sections of
`G_out → Mat^{rk=r}` and `G_out`-equivariant trivialisation — the paper's own proof). Mathlib has
neither the orbit-dimension (`dim G − dim Stab`) nor the bundle-dimension additivity, and the
determinantal-stratum dimension `r(d_0+d_N−r)` is itself not a ready theorem (provable via pivot charts,
but that is its own multi-module build). **Size if forced from scratch: ~7–10 modules.** Hardest
sub-lemma: `codimRepCanonical`/`varietyDim` additivity for a finite Zariski-locally-trivial affine bundle.

### Route 3 — Route-c-style dodge (trdeg / Jacobian-rank of `mult⁻¹(B)` directly) — **SECRETLY RE-HIDES THE WALL**
Most tempting (the landed `JacobianTrdeg.genericDifferentialRank` + the `trdeg ≤ rank` criterion are
stated **generally** for any `k`-domain `B` and family `f`, so reusable). The fibre differential at `A`
is `d(mult)_A(ΔA) = Σ_i A_N⋯A_{i+1}·ΔA_i·A_{i−1}⋯A_1`. Two pieces are missing, one is the wall in disguise:
- **(parametrisation)** Route-c for `Z_M` rode on the *orbit pullback* `μ_M : G → Z_M` — a surjective
  parametrisation whose image ring is the coordinate ring. `mult⁻¹(B)` has **no analogous surjective
  parametrisation** in the landed stack; build it from scratch.
- **(the wall)** The Jacobian rank at a smooth point gives only the *local* Zariski-tangent dimension.
  Pinning the **variety** dimension — the lower bound `dim mult⁻¹(B) ≤ dim Σ^r − r(d_0+d_N−r)` for
  *every* component (equidimensionality) — is exactly the bundle/fibre-dimension statement again. The
  derivative alone cannot supply it.

Confirmed the local-vs-global gap empirically: on `(2,2,2)`, `r=1`, the smooth-point Jacobian rank is 4
(generic codim 4 ✓), but at the special point `A₁=A₂=[[1,0],[0,0]]` the rank **drops to 3** — the fibre
*is* singular off a smooth locus, so a single-point Jacobian does not certify the dimension; you need the
global equidimensionality the bundle gives. **Size from scratch: ~10+ modules**, hardest sub-lemma the
global height lower bound for `Ideal.span {entries(mult − B)}`.

### Route 4 — CITE Lemma 4.6 as a named interface — **the honest move (~80–150 LoC, 1 small DLN module)**
A small carried structure field, *separate* from `RlctInterface` (different source: LR Lemma 4.6, a
geometric bundle statement; vs Aoyagi, an analytic rlct statement). Hardest part is not mathematical —
the `ℕ∞.toNat` finite-codim arithmetic after rewriting by the cited shift and the (proved) Brick-A
`codim Σ̄^r = cCodim d r`.

## Precise Lean-targetable statements

### D3-general, Brick A (PROVE — landed machinery, general in `r`)

The `r=0` theorem `codimRepCanonical_fibre_zero_eq_cCodim` used `fibre d 0 = Σ̄^0`. The general-`r`
analogue is *about `Σ̄^r` itself* (not the fibre — the fibre needs Brick B):

    -- D3-general, Brick A — PROVABLE zero-cited (Voigt + sigmaIdeal general in r + cCodim_rankShift)
    theorem codimRepCanonical_productRankLocusLE_eq_cCodim
        [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
        (hr : ∀ k', r ≤ d k') (h : (kostantPartitions d r).Nonempty) :
        ((codimRepCanonical (productRankLocusLE (k := k) d r)).toNat : ℤ) = cCodim d r h

Route (mirrors the landed `r=0` chain, all bricks general in `r`): `codimRepCanonical Σ̄^r = height
(sigmaIdeal d r)` (the `_eq_height_sigmaIdeal` argument, for `Σ̄^r` not just `fibre 0`) `= ⨅` orbit-codim
over corner-`≤r` orbits (`minimalPrimes_sigmaIdeal` is **general in `r`** — `Core.SigmaComponents`) `=
cCodim d r` (lower bound via `gabrielPartition`/corner-`r` realiser, upper bound via `realizerD`; both
general in `r`, used in thread 06/07 for `cCodim_rankShift`, `cCodim_d222_one`). **No fibre-dim wall** —
`Σ̄^r` is GL_d-stable.

### D3-general, Brick B (CITE Lemma 4.6 — the shift NAMED)

    -- D3-general, Brick B — CITED interface (LR Lemma 4.6, the locally-trivial-bundle shift)
    structure BundleShiftInterface (d : Fin (N + 1) → ℕ)
        (K : Type v) [Field K] [IsAlgClosed K] [CharZero K] (ι : ℝ →+* K) where
      /-- **Cited (Lehalleur–Rimányi Lemma 4.6 = `lem:rank_vs_fibers`).** For `B` of rank `r ≤ min d`,
      `mult⁻¹(B)` is a locally-trivial bundle over the orbit `Mat^{rk=r}` of dimension `r(d_0+d_N−r)`,
      so its codim is that of `Σ̄^r` shifted by the base dimension. Assumed geometric content, not proved
      here (needs a fibre-dimension theorem absent from Mathlib v4.29). -/
      cited_bundle_shift_lemma46 :
        ∀ (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ),
          B.rank = r → (∀ k', r ≤ d k') →
          codimRepCanonical (fibre (k := K) d (B.map ι))
            = codimRepCanonical (productRankLocusLE (k := K) d r)
              + (r * (d 0 + d (Fin.last N) - r) : ℕ∞)

Naming/scoping guards (each kills an overclaim, matching the `RlctInterface` discipline):
- **Separate structure** from `RlctInterface` — different citation (Lemma 4.6 vs Aoyagi Thm 1), so the
  two Cited dependencies are independently visible in any consumer's type.
- The carried field is **`cited_…_lemma46`** (citation + scope in the name); it carries *only* the codim
  shift (it stops before the rlct, so the rlct transport stays in `RlctInterface`).
- Codim is over the alg-closed char-0 `K` (the `C`-computation scope; `C` field-unambiguous per
  `rmk:real_points`); `B.rank` is read over ℝ and equals `(B.map ι).rank` since a ring embedding
  preserves matrix rank — keep `B.rank = r` (the ℝ rank) to match `RlctInterface.cited_aoyagi_dln`'s
  signature exactly (it already gates on `B.rank = r`, `r ≤ univ.inf' d`).
- The shift `r*(d 0 + d (Fin.last N) − r)` is a `ℕ`-subtraction inside `ℕ∞`; `r ≤ min d ≤ d_0, d_N` so
  `d_0 + d_N − r` is the honest integer (no truncation), with the `r ≤ d k'` guard in scope.

### R2-general (consumes both bricks; same `RlctInterface`, no new Aoyagi citation)

`RlctInterface.cited_aoyagi_dln` is **already general in `r`** (it carries `rlct(lossDLN d B) = ½·codim
mult⁻¹(B.map ι)` for any `B` of rank `r ≤ min d` — the `r=0` payoff merely instantiated `B=0`). So
R2-general is pure transport, gated only on the two D3 bricks:

    -- R2-general — the payoff, via BOTH the Cited Aoyagi rlct AND the Cited Lemma-4.6 shift
    theorem rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi
        (I : RlctInterface d K ι) (J : BundleShiftInterface d K ι)
        {B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ} {r : ℕ}
        (hB : B.rank = r) (hr : ∀ k', r ≤ d k') (h : (kostantPartitions d r).Nonempty) :
        I.rlct (lossDLN d B)
          = (((cCodim d r h).toNat : ℝ) + (r * (d 0 + d (Fin.last N) - r) : ℝ)) / 2

Proof skeleton: `rw [I.cited_aoyagi_dln B r hB …]` (→ `½·codim mult⁻¹(B.map ι)`); `rw
[J.cited_bundle_shift_lemma46 B r hB hr]` (→ `½·(codim Σ̄^r + shift)`); `rw
[codimRepCanonical_productRankLocusLE_eq_cCodim …]` (Brick A, → `½·(cCodim d r + shift)`); finish with
`ℕ∞.toNat`/cast arithmetic (the `(x+y).toNat = x.toNat + y.toNat` split needs both summands finite —
`codim Σ̄^r` finite from Brick A, shift finite as a `ℕ` literal). **Name = content:** both `I` and `J`
explicit in the type (both Cited dependencies visible); `via_aoyagi` names the rlct source; the `+ shift`
is visibly the Lemma-4.6 contribution, *not* claimed as proved geometry.

## Numerical certificate of the shift (exact, independent — Jacobian-rank, not the formula)

Three instances, each verifying `codim mult⁻¹(B)` *directly* via the rank of the fibre Jacobian
`d(mult)_A` at a generic (smooth) fibre point — never substituting the shift formula, so non-circular:

| `d` | `r` | `dim Rep` | `codim Σ̄^r` (landed) | shift `r(d_0+d_N−r)` | predicted fibre codim | direct Jacobian codim | rlct = codim/2 |
|---|---|---|---|---|---|---|---|
| (2,2,2) | 1 | 8 | 1 (`cCodim_d222_one`) | `1·(2+2−1)=3` | 4 | **4** ✓ | 2 |
| (2,2,2) | 2 = min d | 8 | 0 (`Σ̄²=Rep`) | `2·(2+2−2)=4` | 4 | **4** ✓ (over `B=I` and `B=[[1,2],[3,7]]`) | 2 |
| (2,2,1) | 1 = min d | 6 | 0 (`Σ̄¹=Rep`) | `1·(2+1−1)=2` | 2 | **2** ✓ (asymmetric `d_0≠d_N`) | — |

The brief's `(2,2,2)` `r=1` instance is confirmed: codim Σ̄^1 = 1, shift = 3, fibre codim = 4, rlct = 2.
The `r=2` corner case is `Cor 4.7` (fibre over a full-rank `B` is smooth, dim 4). The asymmetric
`(2,2,1)` instance independently confirms the `d_0+d_N` (not `2·something`) form of the shift.

Observation worth recording: at the *special* fibre point `A₁=A₂=[[1,0],[0,0]]` of the `(2,2,2)` `r=1`
fibre the Jacobian rank drops to **3** (not 4) — the fibre is singular there. This is *why* route 3
(single-point Jacobian) cannot certify the variety dimension on its own: the generic codim (4) needs the
global equidimensionality the bundle structure provides, which is the wall.

## Whether it hits the fibre-dim wall

**Yes — and precisely at one step.** Bricks D2 (loss zero-set, landed) and Brick A (`codim Σ̄^r = C`,
provable) are wall-free orbit-closure / combinatorial facts. The wall is *only* the passage `Σ̄^r ⤳
mult⁻¹(B)`, i.e. the bundle shift. Every route that tries to prove that passage zero-cited (1 direct, 2
homogeneous-fibration, 3 route-c-for-the-fibre) re-encounters the same missing Mathlib theorem — a
fibre-dimension / locally-trivial-bundle dimension count — either openly (routes 1, 2) or hidden as the
global lower bound (route 3). The landed voigt route-c does **not** transfer: it is hard-wired to the
GL_d orbit map `μ_M` whose differential is the quiver deformation `δ⁰`; `mult⁻¹(B)` has no such orbit
parametrisation.

## Close

- **Firmest result:** CITE Lemma 4.6 for the bundle shift (named `cited_bundle_shift_lemma46`, a carried
  field separate from Aoyagi); PROVE the orbit-closure brick `codim Σ̄^r = cCodim d r` zero-cited (landed
  machinery, general in `r`). Shift verified exactly on three instances by direct Jacobian rank. Exact
  scope: the proved part is `codim Σ̄^r = C`; the `+ r(d_0+d_N−r)` is Cited.
- **Most likely thing to break it:** if a future Mathlib (or in-repo) port lands a determinantal-stratum
  dimension + a finite-Zariski-locally-trivial-bundle codim-additivity lemma, route 2 becomes a
  zero-cited prove (≈7–10 modules) and the citation could be retired. Also watch the `ℕ∞.toNat` split in
  R2-general — it needs both summands finite (fine here, but the only fiddly part).
- **Next step to settle the open part:** hand the formaliser Brick A
  (`codimRepCanonical_productRankLocusLE_eq_cCodim`) as a tide — the *one* genuinely-provable general-`r`
  brick, and it unblocks R2-general the moment the (cheap) `BundleShiftInterface` is declared. Brick B
  stays Cited unless/until the bundle-dimension port is scoped as its own sub-expedition.

Codex artefacts: `threads/11-genr-shift-sizing/codex/shift-route-{prompt,answer}.md` (decorrelated; the
tentative CITE verdict was withheld from the prompt — Codex converged on CITE-lemma-4.6 independently and
caught the route-3 hidden-lower-bound point).
