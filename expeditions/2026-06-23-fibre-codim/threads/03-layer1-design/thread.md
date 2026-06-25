# thread 03 — layer1-design  (explore / scout, DESIGN recon)

**Type:** explore (scout), design recon — **no Lean proofs**. Produce a construction plan + rung-ladder
that lets the controller open the layer-1 tide(s) with a plan, not cold.

**Goal:** the cleanest **construction** of layer 1 — the finite-type-morphism dimension theorem
`dim(total) = dim(base) + dim(fibre)` for `mult⁻¹(B) → Mat^{rk=r}` (the bundle-shift's load-bearing
content) — in our engine at Mathlib v4.29, with a concrete **rung-ladder** and per-rung risk. The
reachability recon (thread 01) gave the build *order*; this gives layer 1's *internal* ladder.

## What to read / map
1. **Thread 01 recon** (`…/threads/01-recon/thread.md`) — the layer-1 framing, the HAVE/MISSING table,
   why the catenary (used by the thermometer) does NOT give the morphism shift.
2. **The target** — `DLN.RlctPayoffGeneral.BundleShiftInterface.cited_bundle_shift`
   (`codim mult⁻¹(B) = codim Σ̄^r + r(d_0+d_N−r)`), and the thermometer
   `Core.DeterminantalStratumDim` (the base `Mat^{rk=r}` dimension is now LANDED — `r(n+m−r)`).
3. **Landed AG dimension machinery** (the reusable substrate): `Core.NullstellensatzCodim`
   (`codimRep + varietyDim = card`, primality-gated), `Core.SigmaCodim`, `Core.VoigtDischarge`,
   `Core.OrbitImageDim` / `JacobianTrdeg` / `OrbitPullbackDim` / `OrbitVariety` / `OrbitDifferential*`
   (the orbit-map image-dimension route — generic Jacobian rank / trdeg), `Core.AffineNoetherRank`.
4. **The paper's Lemma 4.6 proof** (`paper-sources/…/main.tex` ≈ 844–858): the `G_out`-equivariant
   *local* trivialisation of `mult : Σ^r → Mat^{rk=r}` (local sections of the submersion
   `G_out → Mat^{rk=r}`). Note: only *locally* trivial — a global `k[X] ≃ k[Y][t]` does NOT apply
   (Codex flagged this in thread 01).
5. **Prior attempts** — `expeditions/2026-06-20-rlct-payoff/threads/11-genr-shift-sizing/findings.md`
   (thread 11's fibre-dimension-wall analysis).

## Mathlib v4.29 survey (the decisive part)
`rg` over `lean/.lake/packages/mathlib/Mathlib/` (the symlinked built copy resolves) for what's available
toward a morphism dimension theorem:
- `RingHom.Flat` / `Module.Flat` / `Algebra.Flat`; flat + finite-type fibre-dimension lemmas;
- `Algebra.relativeDimension`, standard-smooth `relativeDimension`, `IsStandardSmoothOfRelativeDimension`;
- `ringKrullDim` additivity: `ringKrullDim_quotient`, `MvPolynomial.ringKrullDim`, polynomial/tensor dim;
- Chevalley / constructible-image dimension; upper-semicontinuity of fibre dimension; `Order.height`;
- `Algebra.FormallySmooth` / `Smooth`, localisation dimension, `dimension` of a fibre product.
For each promising lemma: state exactly what it gives and what hypothesis it demands of *our* map.

## Output (append to this thread.md — the design)
(a) the **minimal target** morphism-dim statement sufficient for the bundle shift (do we need full
    `dim total = dim base + dim fibre`, or a narrower codim equality?);
(b) the **construction route** (candidates: flatness ⇒ fibre-dim additivity; local-trivialisation ⇒
    cover + glue; the catenary on the total/base/fibre vanishing ideals; an orbit-map route via a NEW
    `G` acting on the total space) — pick the cleanest, say why the others lose;
(c) a **RUNG-LADDER**: the ordered intermediate lemmas, each tagged LANDED / Mathlib-available /
    NEW-BUILD, with a per-rung difficulty + risk note and rough module count;
(d) the **wall-within-the-wall**: the single riskiest rung (most likely to be infeasible at v4.29),
    and a fallback if it is;
(e) a **decorrelated `local-codex-consult`** (frame-in / answer-out): "cleanest Lean 4 + Mathlib v4.29
    route to `dim(total) = dim(base) + dim(fibre)` for a dominant finite-type morphism of affine
    varieties that is a Zariski-*locally*-trivial fibre bundle" — report verbatim + assessment;
(f) a **go / re-scope recommendation**: is layer 1 a feasible multi-tide build (≈ how many rungs /
    modules), and where does the residual risk concentrate? Be honest if it should be re-roadmapped.

## Scope
Recon only — no Lean proofs, read-only (except this thread.md). Don't touch other worktrees / stashes.
In-repo memory only (decline `~/.claude` prompts). LR route — independent of the live aoyagi-full.

## Notes / progress
(appended during work)

---

# DESIGN REPORT (2026-06-23, scout — layer-1 construction plan + rung-ladder)

**Headline.** Layer 1 is **GO, in a reframed and substantially de-risked form.** The recon's "wall"
was the *general* finite-type-morphism dimension theorem `dim total = dim base + fibre` — that remains
out of reach. But that theorem is **not what we need.** Two of the three dimensions are *already
landed* (`dim total Σ^r = card − cCodim`, and `dim base Mat^{rk=r} = r(d_0+d_N−r)`, the thermometer),
so the only unknown is `dim fibre`, and the engine **already carries the exact commutative-algebra
lever** to extract it: the going-down height-additivity lemma, applied via flatness. The recon and the
synthesis materially *understated the landed substrate* (three engine files — `AffineDomainDimension`,
`FlatQuasiFiniteHeight`, `PolynomialDimension` — that already use this machinery were not surfaced).
The minimal target collapses from a ~8–15-module general bundle theory to a **~5–8-module
fixed-fibre flat-height-squeeze**, and the residual risk moves off Mathlib's AG gap and onto a
single, project-specific algebraic-geometry fact: **flatness of `mult` on a rank-`r` chart**.

This **confirms the operator's commit** to build layer 1 and *narrows* its scope. Codex (xhigh,
decorrelated, exit 0) converged on the identical reframe independently.

---

## (a) The minimal target sufficient for the bundle shift

**We do NOT need the full `dim total = dim base + dim fibre` morphism theorem.** We need only the
**fibre dimension**, and we get it by a *squeeze* on the two already-known dimensions plus a
height-additivity step.

The unconditional Lean target (the field to discharge) is unchanged — it is the `codimRepCanonical`
shift in `BundleShiftInterface.cited_bundle_shift`:

```lean
codimRepCanonical (fibre d (B.map ι))
  = codimRepCanonical (productRankLocusLE d r) + (r * (d 0 + d (last N) - r) : ℕ)
```

Through the landed catenary complement `codimRepCanonical Z = card − varietyDim Z` (primality-gated,
`NullstellensatzCodim`), this is **equivalent** to the dimension identity

> `varietyDim (fibre d B) = varietyDim Σ^r − r(d_0+d_N−r)`     (LR's *subtractive* form, main.tex:858)

with `card` and `varietyDim Σ^r` cancelling on both sides. Re-expressed as a *sum* (the form the
height lever produces),

> `varietyDim Σ^r = varietyDim Mat^{rk=r} + varietyDim (fibre d B)`,     `(★)`

with `varietyDim Σ^r` and `varietyDim Mat^{rk=r} = r(d_0+d_N−r)` BOTH already landed
(`SigmaCodim`+`NullstellensatzCodim`; `DeterminantalStratumDim`). **So the minimal new content is the
single equation `(★)` solved for `varietyDim(fibre)` — i.e. a fibre-dimension extraction, not a
two-sided morphism theorem.** Numerically certified on `(2,2,2),r=1`: `dim Σ^1 (7) = dim base (3) +
dim fibre (4)`, and `codim fibre = 4 = codim Σ̄^1 (1) + 3` (sympy this thread, matches recon).

**Caveat (reducibility, carried with the claim).** `Σ^r` and `fibre d B` are *reducible* (the θ-story).
The catenary complement `codimRepCanonical = card − varietyDim` is **primality-gated**; for the
reducible case the engine reads codim as `height = min over minimal primes` (`OrbitCodim`). So `(★)`
must hold **per top-dimensional component** (`= max-dimension component`), which LR gets *for free*
from local triviality (the bundle puts the irreducible components of `Σ^r` and of `fibre` in bijection,
preserving dimension up to the constant shift). This is rung L1-5 below and is the one genuinely
fiddly bookkeeping rung — but it rides on machinery the engine already has for `Σ̄^r` (`SigmaComponents`).

## (b) The construction route — flat-height-squeeze (route i′), and why the others lose

**Chosen route: the fixed-fibre flat-height squeeze (Codex's "i′").** For the rank-`r` chart, let
`A` = coordinate ring of the base `Mat^{rk=r}` (or a principal-open chart of it), `B` = coordinate
ring of the corresponding total chart of `Σ^r`, and `p`/`P` the primes of base-point `B₀ ∈ Mat^{rk=r}`
and a chosen point of the fibre. The engine **already** has the load-bearing lemma in usable form:

> **`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`** (Mathlib v4.29, `@[stacks 00ON]`,
> verified present): for `[IsNoetherianRing S] [Algebra.HasGoingDown R S]`, `P` lying over `p`,
> `P.height = p.height + (P.map (mk (p.map (algebraMap R S)))).height`
> — the second summand is the height of `P` **in the fibre ring `S ⧸ pS`**.

and **`Algebra.HasGoingDown.of_flat`** (`Module.Flat R S → HasGoingDown`, instance, verified). The
engine already *uses this exact pattern* twice: `FlatQuasiFiniteHeight.Ideal.height_eq_under_of_flat_quasiFiniteAt`
(fibre height 0 ⟹ heights equal) and `PolynomialDimension.height_eq_height_under_add_height_map_quotient`
(the `A → A[X]` tower). Our case is the *positive-fibre-dim* instance of the same lemma: the fibre
ring `S ⧸ pS` is the coordinate ring of `fibre d B`, whose `height` (at a closed point, `= dim`, by
the landed `AffineDomainDimension.height_eq_ringKrullDim_of_isMaximal`) is exactly the missing
`varietyDim(fibre)`. Re-reading `(★)` through this lemma at a closed point of the total chart:

> `dim Σ^r  (=height of the closed point)  =  dim Mat^{rk=r}  +  dim(fibre)`

— the height-additivity lemma **is** `(★)`, once flatness gives going-down. **This is the whole route.**

**Why the others lose:**
- **Local-trivialisation cover + glue (recon candidate 2).** Geometrically faithful to LR's proof but
  Lean-expensive: needs affine-open-cover infrastructure for the `varietyDim` wrapper (absent),
  `dim(U × F) = dim U + dim F` (absent), and gluing dimension across the cover. The flat-height route
  *uses* local triviality only to get **flatness** (a local-on-base property), then never touches the
  cover again — height-additivity is a single ring-map statement. **Strictly cheaper.** (Codex
  concurs: "geometrically natural, Lean-expensive.")
- **Global `k[X] ≃ k[Y][t]` (recon's noted escape).** Does NOT apply — the `G_out^B`-torsor base map
  is not globally trivial; only locally. Correctly ruled out in recon. Not revisited.
- **Catenary on the three vanishing ideals (recon candidate 3).** The landed catenary complement
  controls a *single* variety's `height + dim = card`; it does **not** by itself relate base/total/fibre
  ideals *under a morphism*. It is the right tool for the *output* bridge (turning the dim identity into
  the codim shift) but not for *producing* `(★)`. (Codex: "not enough.") — it is rung L1-6, downstream.
- **New `G` acting on the total space (recon candidate 4).** `dim total Σ^r` is already known, so an
  orbit-image recomputation of it produces no new information; to get the *fibre* dim this way one would
  still need a quotient/fibre theorem — i.e. it does not avoid the height step. Dead as a shortcut.
  (A *direct* orbit computation of the fixed fibre `mult⁻¹(B)` as a `G_in`-variety is a different,
  highly project-specific route — recon thread-11 already found the inner-`GL` orbit is *strictly
  smaller* than the fibre on `(2,2,2),r=1` (3-dim orbit vs 4-dim fibre), so the fibre is **not** a
  single inner orbit. Confirmed dead.)

## (c) RUNG-LADDER (ordered; tag / difficulty / risk / ~modules)

The build assumes the **rank-`r` chart reduction**: `Mat^{rk=r}` is a single `G_out`-orbit, so it
suffices to work over a principal-open affine chart `U ∋ B₀` of the determinantal base where the
torsor `G_out → Mat^{rk=r}` has a section (LR's local trivialisation). On `U`, `mult` restricts to a
finite-type map of affine domains. The ladder produces `(★)` per-component then bridges to codim.

| # | Rung | Tag | Diff | Risk | ~mod |
|---|------|-----|------|------|------|
| **L1-0** | **Flatness of `mult` on the rank-`r` chart** (`Module.Flat A B` for the restricted coord-ring map). | **NEW-BUILD** | **HIGH** | **THE WALL-WITHIN** | 1–2 |
| L1-1 | Going-down + height-additivity instantiated for our `A → B` (`of_flat`, then `height_eq_height_add_of_liesOver_of_hasGoingDown`). | Mathlib-avail + LANDED pattern | LOW | low — lemma verified present, engine uses it twice | 0–1 |
| L1-2 | Fibre coordinate-ring identification: `B ⧸ pS ≅` coordinate ring of `fibre d B` (the scheme-theoretic fibre = the set-theoretic fibre, reduced). | NEW-BUILD | MED | med — needs the fibre ideal = `pS` up to radical; char-0 + reducedness | 1 |
| L1-3 | `dim base = r(d_0+d_N−r)` on the chart (= the LANDED thermometer, transported to the chart via "nonempty principal open of irreducible has equal dim"). | **LANDED** (+ chart transport) | LOW | low | 0–1 |
| L1-4 | Height = dim at a closed point, both sides (LANDED `AffineDomainDimension.height_eq_ringKrullDim_of_isMaximal`); assemble `(★)` from L1-1+L1-2+L1-3. | **LANDED** | LOW | low — the engine equidim theorem is exactly this | 0 |
| L1-5 | Per-component / top-dimensional bookkeeping: lift `(★)` from the chosen component to `codimRepCanonical = min-over-components` for the *reducible* `Σ^r` and `fibre`. | NEW-BUILD (engine has the `Σ̄^r` analogue) | MED-HIGH | med-high — the bijection-of-components needs care; engine's `SigmaComponents` dodge is `GL_d`-stable-only | 1–2 |
| L1-6 | Output bridge: turn `(★)` into the `codimRepCanonical` shift via the catenary complement (LANDED `NullstellensatzCodim` + `SigmaCodim` value `codim Σ̄^r = cCodim`). | **LANDED** | LOW | low | 0–1 |
| **Total** | | | | | **~5–8** |

LANDED-leaning rungs (L1-3, L1-4, L1-6) are reuse/transport of existing engine theorems; the genuine
new build is **L1-0 (flatness)** and **L1-5 (reducibility)**, with **L1-2 (fibre-ring id)** a moderate
glue rung. This matches Codex's "~5–8 if the domain/component story is clean; ~8–10 if reducible
assembly is painful."

## (d) The wall-within-the-wall + fallback

**Riskiest rung: L1-0 — flatness of `mult` restricted to a rank-`r` chart (`Module.Flat A B`).**
Everything downstream is either landed or a verified-present Mathlib lemma; the *only* genuinely
uncertain new geometric input is that the restricted multiplication map is flat. It is **true**
(LR's local triviality ⟹ the restricted map is a trivial product on the chart ⟹ free ⟹ flat), but
proving `Module.Flat` in Lean for our concrete coordinate-ring map is the one step with no landed
template and no off-the-shelf Mathlib closer. Two sub-risks:
  - *Algebraising the local trivialisation.* The cleanest path is to exhibit the chart-restricted
    total coord ring as `A ⊗ (fibre ring)` (free over `A`) — but that re-imports the product structure
    the route was meant to avoid. The lighter path: flatness is *local on the base*, and on the chart
    `mult` is a base-change of the (trivial) `G_out`-torsor section, so flatness descends — but Mathlib
    v4.29's flat-descent / flat-local-on-base API may not be in the convenient form.
  - *Quasi-finiteness is NOT available here* (the fibre is positive-dimensional), so the
    `FlatQuasiFiniteHeight` shortcut (fibre height 0) does **not** apply directly — we need the
    *full* `height_eq_height_add` with a *nonzero* second summand. (That lemma is the general one and is
    present; only the engine's *specialisation* to height-0 fibres is what doesn't transfer.)

**Fallback if L1-0 (flatness) proves infeasible at v4.29:** drop to the **two-inequality sandwich**.
  - **Lower bound** `dim Σ^r ≥ dim base + dim fibre` is cheap and flatness-free: `HasGoingDown` (from
    flat) gives it via `exists_ltSeries_of_hasGoingDown`, but even *without* flatness, going-UP
    (`exists_ltSeries_comap_last_of_isIntegral`, LANDED in `IntegralDimension`) + a section gives a
    chain lift. The lower bound is structurally easy.
  - **Upper bound** `dim Σ^r ≤ dim base + dim fibre` is the genuinely hard half (fibre-dimension
    upper-semicontinuity / no-jumping). If flatness can't be had, this is where a *narrow*,
    project-specific argument is needed — possibly via the explicit `G_out`-action transitivity on the
    base making all fibres isomorphic (equidimensional by homogeneity), which is *exactly* the
    information local triviality encodes. **Second fallback:** keep the cited interface for the general
    case and discharge only `N` small / `r ≤ 1` (the witness range) as a non-vacuity demonstration,
    roadmapping full generality. (This would be a partial, honestly-scoped landing — better than the
    current fully-cited interface, weaker than full discharge.)

## (e) Decorrelated local-codex-consult (xhigh, gpt-5.x; frame-in / answer-out)

Prompt (`codex/layer1-route-prompt.md`) framed the affine-variety setting, the landed `varietyDim` /
catenary stack, the four candidate routes, and the **already-known two-of-three-dimensions** fact, and
asked — decorrelated, my own verdict withheld — for the cleanest v4.29 route, the two inequalities, the
single hardest missing piece, whether a narrower target suffices, and a module budget. Codex was
authenticated, ran ~3 min with Mathlib-doc lookups, exit 0. Full answer in `codex/layer1-route-answer.md`.
Verbatim key points:

> "the cleanest route is **not** the full bundle theorem. It is a narrowed version of (i): flatness +
> known `dim total` + known `dim base` + affine-domain equidimensionality ⟹ fixed closed fibre has the
> forced dimension."

> "Mathlib v4.29 has the useful pieces: flat algebras give going-down, `exists_ltSeries_of_hasGoingDown`
> exists, and `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` is already listed in the height
> theorem API. Chevalley is constructibility/open-map, not fibre dimension."

> "the fact that `dim total` and `dim base` are already pinned changes the route substantially. You
> should target the fixed-fibre height squeeze, not a general bundle theorem. … This avoids product
> dimension `dim(U × F)` and avoids upper semicontinuity."

> "Residual risk is **not** Mathlib's going-down/height API. The risk is the project geometry:
> algebraising the local trivialisation, proving the right localized map is flat, and making reducible
> components line up with the already-known `cCodim` value. … ~5–8 focused modules … The full bundle
> theorem should be roadmapped; the narrowed height-squeeze is the buildable route."

**My assessment of Codex's answer.** Strongly convergent and decorrelated-confirming — Codex landed
on the *same* reframe I built into the survey (genuine unknown = `dim fibre` only) and named the same
lever (`height_eq_height_add_of_liesOver_of_hasGoingDown`) and the same wall (flatness of the localised
map). I independently **verified** both lemma citations are real at our pin (the height-additivity
lemma at `KrullsHeightTheorem.lean:446`; `HasGoingDown.of_flat` instance present), and — going beyond
Codex — found that the engine *already uses this exact pattern* in two landed files
(`FlatQuasiFiniteHeight`, `PolynomialDimension`) plus carries the affine-domain equidimensionality
theorem (`AffineDomainDimension`). Codex's one slight over-optimism: it lists `dim(A/p)=dim B − dim A`
"via catenarity/equidimensionality of `B`" as if free, but for the *reducible* total space that is
rung L1-5 and is non-trivial — I weight L1-5 higher than Codex's prose implies. Net: Codex sharpened
and confirmed; no engine asset I found contradicts the GO verdict.

## (f) GO / re-scope recommendation

**GO — build layer 1 as the narrowed fixed-fibre flat-height squeeze (~5–8 modules).** The recon's
"genuine blocker" verdict was correct *for the theorem it scoped* (the general morphism dimension
theorem) but the operator's commit + this design show that theorem is **not the minimal target**. The
reframe (only `dim fibre` is unknown; the engine already carries the height-additivity lever) makes
this a feasible multi-tide build, materially smaller than the recon's ~8–15.

**Residual risk concentrates on exactly two rungs:**
1. **L1-0 (flatness of the localised `mult`)** — the wall-within. Recommend the **first tide opens
   here as a standalone de-risking rung** (mirror the thermometer's role): if flatness lands cleanly,
   the rest is largely transport; if it fights v4.29's flat-local-on-base API, fall to the
   two-inequality sandwich (upper bound = homogeneity/equidimensionality) before committing further.
2. **L1-5 (reducibility bookkeeping)** — the engine's `SigmaComponents` dodge is `GL_d`-stable-only
   and does not transfer to the non-`GL_d`-stable `fibre d B`; the bijection-of-components must come
   from the bundle structure. Buildable, but the fiddliest assembly.

**Nothing should be re-roadmapped to "blocked."** The honest posture upgrade vs the recon: the recon
said "keep cited + roadmap as ~8–15-module general AG"; this design says "build it now as a
~5–8-module squeeze, with L1-0 as the gating first rung." If L1-0 is infeasible, the *partial* fallback
(discharge `r ≤ 1` / witness range, roadmap generality) still strictly improves on the fully-cited
interface.

**Tide sequencing recommendation (for the controller):**
- **Tide A (gating):** L1-0 flatness as a standalone `Core` lemma. Thermometer-style — its difficulty
  decides whether the full squeeze proceeds or the sandwich fallback opens.
- **Tide B:** L1-1 → L1-4 (the squeeze assembly; mostly landed-transport).
- **Tide C:** L1-5 → L1-6 (reducibility + output bridge), retiring `cited_bundle_shift`.

## Close (reflection)

- **Most likely to advance the expedition:** the **reframe in (a)** — that we need only `dim fibre`,
  not the general morphism theorem, because two of three dimensions are landed. It converts the
  recon's blocker into a tractable squeeze and re-uses the height-additivity lever the engine already
  carries. This is the load-bearing finding; it should reset the controller's scope from the recon's.
- **Most likely to break:** **L1-0 (flatness of the localised `mult`)** — the one rung with no landed
  template and a Mathlib-v4.29 flat-local-on-base API of uncertain convenience. The whole GO rests on
  it; hence the recommendation to gate the build on it. If it breaks, the upper-bound half of the
  sandwich (fibre-dim semicontinuity) is the genuine residual hard problem.
- **Next computation that would clarify:** before opening Tide A, prototype L1-0 as an `example` block
  pinning the precise Mathlib v4.29 flatness API surface — does `Algebra.Flat` / `Module.Flat` descend
  along the chart base-change in a usable form, or does the engine need a `Flat`-local-on-an-open-cover
  brick first? That single API-availability check is the faithful thermometer for whether the squeeze
  is a clean ~5-module build or a ~8-module one. (Companion check: confirm the scheme-theoretic fibre
  `B ⧸ pS` is *reduced* in char 0 so L1-2's coordinate-ring identification holds without a radical.)
