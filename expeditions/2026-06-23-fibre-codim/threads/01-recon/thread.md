# thread 01 — recon  (explore / scout)

**Type:** explore (scout) — map terrain, scope viability. **No formalisation**; deliver a reachability
verdict that gates whether the controller launches a tide or roadmaps the gap.

**Goal:** decide whether LR **Lemma 4.6** (the fibre-codim bundle-shift) is *whole-in-reach* in our
engine — and if so, the cleanest proof route + a rung-ladder; if not, a sharp obstruction + the precise
missing theory.

## What to read / map
1. **LR Lemma 4.6** (`paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/…/main.tex` ≈ 844–858)
   + Cor 4.4 + Lemma 4.5 (≈ 816–833): the precise statement and LR's proof (the locally-trivial bundle
   of `mult⁻¹(B)` over the rank-`r` matrix variety `Mat^{rk=r}`).
2. **The ASSUMED target:** `lean/DLNFibre/DLN/RlctPayoffGeneral.lean` —
   `BundleShiftInterface.cited_bundle_shift` (the exact statement to discharge) + how
   `rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi` consumes it.
3. **The `r=0` landed template:** `lean/DLNFibre/DLN/RlctPayoff.lean` (`codim mult⁻¹(0) = C`,
   `fibre_zero_eq_productRankLocusLE_zero`).
4. **The AG dimension library** (`voigt-discharge`): `Core/VoigtDischarge`, `OrbitVariety`,
   `OrbitImageDim`, `OrbitDifferential*`, `AffineNoetherRank`, `JacobianTrdeg`, `SigmaCodim`,
   `RankLocusClosed` — what dimension machinery exists (variety dimension, `Ideal.height` codim,
   `dim 𝒪 = dim G − dim Aut`, image dimension) and what's reusable for a fibre-dimension count.
5. **The "fibre-dimension wall" (thread 11):** grep the repo (`expeditions/`, `lean/CLAUDE.md`, Lean
   docstrings) for "thread 11" / "fibre.dimension" to learn what was tried and why it stuck.
6. **Mathlib v4.29 coverage:** `rg` over `/home/ubuntu/workspace/geometry-of-dln-fibre/.lake/packages/mathlib/Mathlib/`
   (the MAIN checkout's *built* Mathlib — this worktree's `.lake` may still be building) for: fibre
   dimension of a morphism, Chevalley, upper-semicontinuity of fibre dimension, fibration/bundle
   dimension, `AlgebraicGeometry` dimension lemmas, `Order.height`/`Ideal.height` API.

## Output (append to this thread.md — the verdict)
(a) the precise unconditional Lean target (the interface to discharge);
(b) the cleanest proof route **in our engine** (bundle structure + dimension additivity);
(c) the missing pieces to build from scratch, and whether the `voigt-discharge` library reaches them;
(d) **REACHABILITY VERDICT** — *whole-in-reach* (→ a concrete rung-ladder: intermediate lemmas in
   order) **or** *genuine blocker* (→ the precise missing theory + a roadmap entry);
(e) a **decorrelated `local-codex-consult`** (frame-in / answer-out): "in Lean 4 + Mathlib v4.29
   affine-variety terms, what does it take to prove `dim` of a locally-trivial fibre bundle =
   `dim base + dim fibre`?" — report Codex's answer verbatim + your assessment.

## Scope
Recon only — **no Lean proofs**, read-only. `decide +kernel` not `native_decide` (n/a here). Don't
touch other worktrees or any stash. In-repo memory only (decline any `~/.claude` memory prompt).

---

# RECON REPORT (2026-06-23, scout)

**REACHABILITY VERDICT: GENUINE BLOCKER.** LR Lemma 4.6 (the fibre-codim bundle-shift) is **not
whole-in-reach** in our engine at the Mathlib v4.29 pin. The geometric content of the shift rests on
a **dimension theorem for finite-type morphisms** (`dim total = dim base + fibre dim`) that Mathlib
does not have and that the engine's landed AG library does not supply for *this* map. Sizing the
from-scratch build: **~8–15 focused modules** (decorrelated Codex this thread; prior thread-11 Codex
gave 7–10 for the homogeneous-fibration route). The honest move stands: **keep the cited interface
`BundleShiftInterface.cited_bundle_shift`**, and **roadmap** the missing AG as its own sub-expedition.
This confirms (does not merely echo) the thread-11 verdict — re-derived against the now-richer
`voigt-discharge` engine, with the precise reason the engine does *not* transfer recorded below.

This is the **last assumed step** under the LR `rlct = C/2 + shift` payoff besides the genuinely-cited
Aoyagi/Watanabe analytic bound; the verdict is that it should *remain* assumed, named, and roadmapped.

## (a) The precise unconditional Lean target

The interface field to discharge (in `lean/DLNFibre/DLN/RlctPayoffGeneral.lean`,
`structure BundleShiftInterface`), restated as a free-standing theorem:

```lean
-- TARGET (currently the carried hypothesis `cited_bundle_shift`):
theorem bundle_shift
    {N : ℕ} (d : Fin (N + 1) → ℕ)
    {K : Type v} [Field K] [IsAlgClosed K] [CharZero K] (ι : ℝ →+* K)
    (B : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ) (r : ℕ)
    (hN : 0 < N) (hB : B.rank = r) (hr : ∀ k', r ≤ d k') :
    codimRepCanonical (fibre (k := K) d (B.map ι))
      = codimRepCanonical (productRankLocusLE (k := K) d r)
        + ((r * (d 0 + d (Fin.last N) - r) : ℕ) : ℕ∞)
```

`codimRepCanonical Z := Ideal.height (vanishingIdeal (canonicalCoord d '' Z))` — the genuine height of
the vanishing ideal of `Z`'s Zariski closure (`Core.OrbitCodim`), so the statement correctly handles a
*reducible* `Z` (height = min codim over minimal primes). It discharges the consumer
`rlct_lossDLN_eq_half_cCodim_add_shift_via_aoyagi` (the `RlctPayoffGeneral` payoff), which is otherwise
pure `ℕ∞.toNat` transport (already landed against `J.cited_bundle_shift`).

**Paper provenance (read at source).** The shift is LR's `lem:rank_vs_fibers` (main.tex:844–858), stated
for the *exact-rank* locus `Σ^r`: `codim mult⁻¹(B) = codim Σ^r + r(d_0+d_N−r)`. The interface's
*closed*-locus form folds in `codim Σ̄^r = codim Σ^r` (`cor:irred_comp` + `lem:rank_0`, main.tex:816–833
— Zariski closure preserves codim; landed in `Core.SigmaCodim` as `codim Σ̄^r = cCodim d r`). Note the
brief's "Lemma 4.6" is `lem:rank_vs_fibers`; "Cor 4.4 + Lemma 4.5" are `cor:irred_comp` + `lem:rank_0`.
LR's own proof is **not** a from-scratch fibre-dimension count: it is `G_out`-equivariant homogeneity —
`Mat^{rk=r}` is ONE `G_out = GL_{d_N}×GL_{d_0}` orbit, `mult` is `G_out`-equivariant via `π_out`, local
sections of the submersion `G_out → Mat^{rk=r}` give `G_out`-equivariant local trivialisations. The
dimension additivity is then the standard "locally-trivial bundle ⟹ dim total = dim base + dim fibre".

## (b) The cleanest proof route in our engine (and why each step is the wall)

The engine's *one* genuine lever for converting a dimension count to a codimension is the catenary
complement `Core.NullstellensatzCodim`:

> `codimRep coord Z = Nat.card (RepCoord d) − varietyDim (coord '' Z)`  **for IRREDUCIBLE `Z`**
> (`codimRepCanonical_eq_card_sub_varietyDim`, needs `(vanishingIdeal …).IsPrime`),

with `varietyDim Z := (ringKrullDim (MvPolynomial σ k ⧸ vanishingIdeal Z)).unbotD 0`. Through it the
shift `codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)` is **equivalent** to the dimension additivity

> `varietyDim Σ^r = varietyDim mult⁻¹(B) + r(d_0+d_N−r)`     (≡ `dim base + dim fibre`, base `= Mat^{rk=r}`)

So the cleanest *engine-native* route is:
1. **Determinantal-stratum base dimension** `dim Mat^{rk=r}_{d_N,d_0} = r(d_0+d_N−r)` (verified
   numerically below: 2×2 rank-1 gives 3). `Mat^{rk=r}` is one `G_out`-orbit; the engine computes an
   orbit's dimension via its orbit-map image (the trdeg / generic-Jacobian-rank route,
   `Core.OrbitImageDim`/`JacobianTrdeg`), but **only for the `GL_d`-orbit map `μ_M` whose differential
   is the quiver deformation `δ⁰`** — there is no `G_out`-on-`Mat` orbit-map or its differential in the
   engine. New build.
2. **The bundle additivity** `varietyDim Σ^r = dim Mat^{rk=r} + varietyDim mult⁻¹(B)` — the locally-
   trivial-bundle / fibre-dimension theorem. This is the wall (see (c)).
3. **The per-component / irreducibility bookkeeping.** The complement bridge needs *primality*
   (irreducible `Z`); `Σ^r` and `mult⁻¹(B)` are **reducible** (the whole `θ`-component story — `θ` top
   components). For `Σ̄^r` the engine dodges this via the `min`-over-orbit-closures route
   (`sigmaIdeal = sInf orbitIdeals`, `minimalPrimes_sigmaIdeal_eq`, `Core.SigmaComponents`/`SigmaCodim`);
   `mult⁻¹(B)` has **no** such orbit-closure decomposition (it is not `GL_d`-stable), so the dodge does
   not transfer and one must run the complement per-component on objects whose `varietyDim` we have no
   handle on.

**Why the landed `r=0` template (`DLN.RlctPayoff`) does not generalise.** The `r=0` proof works because
`mult⁻¹(0) = Σ̄^0 = productRankLocusLE d 0` is a finite union of `GL_d`-orbit closures (det. rank loci),
so the *entire* landed stack applies (Voigt per-orbit codim + the realizer minimum). For `B ≠ 0`,
`mult(P•A) = P_N · mult(A) · P_0⁻¹`, so `GL_d` moves `mult⁻¹(B)` to a *different* fibre: it is **not
`GL_d`-stable, not a union of orbit-rank-loci, not a single inner-`G_in` orbit** (thread 11 checked:
on `(2,2,2)`,`r=1` the inner-`GL_2` orbit of the fibre point `A₁=A₂=diag(1,0)` is ≤ 3-dim while the
fibre is 4-dim). Every landed codim tool keys off the orbit-rank-locus structure that `mult⁻¹(B)` lacks.

## (c) Missing pieces, and whether `voigt-discharge` reaches them

| Piece needed by route (b) | In the engine / Mathlib v4.29? |
|---|---|
| `codimRep = card − varietyDim` for irreducible `Z` | **HAVE** (`NullstellensatzCodim`, via Mathlib `height_add_ringKrullDim_quotient_eq`). |
| `ringKrullDim (MvPolynomial ι R) = ringKrullDim R + card ι` (trivial-bundle dim) | **HAVE** in Mathlib (`MvPolynomial.ringKrullDim_of_isNoetherianRing`). Applies only to a *global* polynomial-ring trivialisation. |
| Orbit dimension via orbit-map image (trdeg/Jacobian) | **HAVE for the `GL_d` orbit map `μ_M`** (`OrbitImageDim`, `JacobianTrdeg`, `OrbitPullbackDim`). **NOT** for the `G_out`-on-`Mat` orbit map (no such map/differential built). |
| `dim Mat^{rk=r} = r(d_0+d_N−r)` (determinantal-stratum dim) | **MISSING.** No determinantal-stratum dimension; buildable via the orbit-image route applied to a NEW `G_out`-orbit map (its own module(s)). |
| **`dim total = dim base + dim fibre`** for a flat / smooth / dominant / locally-trivial finite-type morphism | **MISSING — the wall.** No Chevalley *dimension*-of-image (only constructibility, and even that not at v4.29), no fibre-dimension upper/lower semicontinuity, no `dim G − dim Stab`, no Zariski-locally-trivial-bundle dim additivity. |
| Affine-variety local triviality as first-class data (open cover `Uᵢ`, `f⁻¹Uᵢ ≃ Uᵢ × F`); dimension local on an open cover; nonempty open ⊆ irreducible has same dim; `dim(U × F)=dim U + dim F` | **MISSING for the `varietyDim` wrapper** (Codex this thread). Localization-height cousins exist but are not the affine-variety statements. |
| Per-component irreducibility handling for the *reducible* fibre | **No engine handle** — the `min`-over-orbit-closures dodge (`SigmaComponents`) is `GL_d`-stable-only and does not transfer to `mult⁻¹(B)`. |

**The single hardest missing piece** (Codex this thread, sharpening thread 11): a **dimension theorem
for finite-type morphisms**, ideally the ring form
`flat finite-type φ : A → B + constant fibre ringKrullDim d ⟹ ringKrullDim B = ringKrullDim A + d`,
or the classical generic-fibre-dimension + equidimensionality/upper-semicontinuity package. Mathlib
v4.29 has `Flat`, the smooth/standard-smooth `relativeDimension` API, polynomial-ring Krull lemmas — but
**not** the theorem linking `SmoothOfRelativeDimension d` / flatness to `ringKrullDim` of total space and
fibres. The `voigt-discharge` library does **not** reach it: route-c there is hard-wired to the `GL_d`
orbit map `μ_M` (image = the orbit-closure coordinate ring, differential = `δ⁰`); `mult⁻¹(B)` has no
analogous surjective polynomial parametrisation in the landed stack, and the Jacobian-rank route gives
only the *local* tangent dimension at a smooth point — not the *global* equidimensionality lower bound,
which IS the bundle theorem in disguise (confirmed numerically: the fibre is singular off a smooth
locus, below).

**No global-trivialisation escape for this bundle.** Codex flags that IF `k[X] ≃ₐ k[Y][t₁..tᵣ]` (global
trivialisation) one could finish via `MvPolynomial.ringKrullDim_of_isNoetherianRing`. But LR's bundle
`mult: Σ^r → Mat^{rk=r}` is only *locally* trivial — the structure map `G_out → Mat^{rk=r}` is a
`G_out^B`-torsor that is not globally trivial — so there is no global polynomial-ring trivialisation to
exploit. The escape does not apply.

## (d) VERDICT → roadmap entry

**GENUINE BLOCKER.** Do not launch a tide to discharge `cited_bundle_shift` now. The geometric content
is one published, true fact whose proof needs an AG dimension-theory-of-morphisms layer (~8–15 modules)
that is neither in Mathlib v4.29 nor in the engine, and the engine's route-c does not transfer.

**Roadmap entry (the precise missing theory, in build order if a future sub-expedition takes it on):**
1. **`Core` morphism-dimension layer (the wall).** The ring-form finite-type morphism dimension theorem
   `ringKrullDim B = ringKrullDim A + d` for a flat finite-type `φ : A → B` with constant fibre Krull
   dim `d` (Codex's `ringKrullDim_eq_base_add_fibreDim_of_flat_finiteType`), OR the geometric package:
   affine-variety local triviality + dimension-local-on-open-cover + `dim(U×F)=dim U+dim F` +
   nonempty-open-of-irreducible-has-equal-dim. (Largest piece; ~5–8 modules.)
2. **`G_out`-on-`Mat` orbit + determinantal-stratum dimension** `dim Mat^{rk=r} = r(d_0+d_N−r)`, via a
   new `G_out` orbit map and the existing orbit-image trdeg route. (~2–3 modules.)
3. **The equivariant trivialisation of `mult: Σ^r → Mat^{rk=r}`** (`G_out`-equivariance of `mult` via
   `π_out` is cheap; local sections of `G_out → Mat^{rk=r}`). (~1–2 modules.)
4. **Reducibility / per-component bookkeeping** for `mult⁻¹(B)` and `Σ^r`, and assembly into the
   `codimRepCanonical` shift. (~1–2 modules.)
Retire the citation only when layer 1 lands. Until then, `BundleShiftInterface.cited_bundle_shift`
is the correct, named, scoped (`0 < N`) posture — analogous to the Aoyagi rlct citation.

**Numerical certificate (re-derived this thread, independent of thread 11's record, sympy/numpy).**
The shift math is correct — the verdict is about Lean reachability, not the theorem's truth:
- `(2,2,2)`, `r=1`: generic fibre Jacobian rank (= codim at a smooth point) `= 4 = codim Σ̄^1 (1) +
  shift (1·(2+2−1)=3)`; fibre dim `= 8−4 = 4`. ✓
- `dim Mat^{rk=1}` (2×2) `= 3 = r(d_0+d_N−r) = 1·3` (rank of the `(u,v)↦uv^T` Jacobian). ✓
- **Equidimensionality is the wall**: at the special fibre point `A₁=A₂=diag(1,0)` the Jacobian rank
  DROPS to 3 (the fibre is singular there) — so a single-point Jacobian cannot certify the variety
  dimension; the generic codim 4 needs the global equidimensionality the bundle supplies. This is
  exactly why route-3 (Jacobian) and any local argument fail.

## (e) Decorrelated local-codex-consult (xhigh, gpt-5.x; frame-in/answer-out)

Prompt (`codex/bundle-dim-prompt.md`) framed the affine-variety setting + the engine's `varietyDim` /
catenary-complement / trdeg machinery and asked, decorrelated (my verdict withheld): what it takes to
prove `dim X = dim Y + dim fibre` for a homogeneous-base locally-trivial bundle in Lean 4 + Mathlib
v4.29; whether a shorter commutative-algebra route exists; and the single hardest missing piece + module
budget. Codex was authenticated (`openai-aisi`), ran ~4 min with Mathlib-doc web searches, exit 0.
Full answer verbatim in `codex/bundle-dim-answer.md`. Key verbatim points:

> "the clean general statement is not realistically reachable in Mathlib v4.29 without building
> substantial dimension theory for morphisms. The group/homogeneous-base story is not the main blocker;
> the blocker is turning 'finite type family with constant fibre' into a `ringKrullDim` equality."

> "The shortest viable route is not 'formalize locally trivial bundles'; it is a commutative-algebra
> theorem of the following shape: … `A irreducible/equidimensional/catenary`, `B flat over A`, `all
> fibres have ringKrullDim d` ⊢ `ringKrullDim B = ringKrullDim A + d`. … But it does not appear to have
> the needed theorem: flat finite type morphism + constant fibre dimension ⇒ dim total = dim base +
> fibre dimension."

> "A global trivialisation helps only in special cases. If you can prove `k[X] ≃ₐ[k] k[Y][t₁,...,tᵣ]`
> then `MvPolynomial.ringKrullDim_of_isNoetherianRing` basically gives the result." [Does not apply
> here — the bundle is only locally trivial; the `G_out`-torsor base map is not globally trivial.]

> "I would budget this as a substantial development, not a lemma or two: roughly 8-15 focused modules if
> you stay affine/ring-theoretic, more if you route through schemes. … the pragmatic route is to avoid
> proving the general homogeneous-bundle theorem unless it becomes central."

**My assessment of Codex's answer.** Convergent and decorrelated-confirming. It independently identifies
the same wall (a finite-type-morphism dimension theorem absent from v4.29) and *sharpens* thread 11 by
re-locating the obstruction: not the orbit/homogeneous-base step (cheap) but the
`dim total = dim base + dim fibre` ring-theoretic core. The 8–15 module budget is consistent with
(slightly above) thread 11's 7–10 for route 2, the difference being Codex here counts the per-component
irreducibility / fibre-ring identification bricks the engine's `GL_d`-only dodge does not cover. I cross-
checked the one escape it raised (global trivialisation) against LR's actual proof and confirmed it does
not apply (locally-trivial only). I did **not** find any engine asset that closes the gap; the verdict
stands as GENUINE BLOCKER → cite + roadmap.

## Close (reflection)

- **Most likely to advance the expedition:** the *recon verdict itself* — it correctly gates the
  controller AWAY from a doomed ~10-module tide and toward (i) banking the cited interface as-is, and
  (ii) a crisp roadmap entry for the morphism-dimension AG layer. The expedition's value here is the
  honest "stop, this is a from-scratch AG build," not a forced green.
- **Most likely to break:** the *budget*, not the verdict. If a future Mathlib lands the flat finite-type
  fibre-dimension theorem (layer 1), the build collapses to layers 2–4 (~4–6 modules) and the citation
  becomes retireable; watch Mathlib's `RingTheory.KrullDimension` / `AlgebraicGeometry.Morphisms`
  growth. The verdict (blocker *now*) is robust; the *cost* is the volatile number.
- **Next computation that would clarify:** before any layer-1 grind, prototype the determinantal-stratum
  dimension `dim Mat^{rk=r} = r(d_0+d_N−r)` (layer 2) as a *standalone* `Core` lemma via the existing
  orbit-image trdeg route on a new `G_out` orbit map — it is the one genuinely-in-reach geometric brick,
  is independently useful, and its difficulty is a faithful thermometer for whether layer 1 is worth
  opening. If even layer 2 fights the engine's `GL_d`-hard-wiring, the citation should stay untouched.
