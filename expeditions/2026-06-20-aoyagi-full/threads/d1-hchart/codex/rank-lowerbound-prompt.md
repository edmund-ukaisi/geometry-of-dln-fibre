# Lean tactic-design: the cleanest route to `nReg ≤ finrank (range Dg(v))`

Lean 4 + Mathlib v4.29. I have a `LinearMap` and need a clean, factored proof of a rank lower bound.
Want the cleanest INTERMEDIATE-LEMMA decomposition + the Mathlib API names, before I grind. No need
for full Lean code — the lemma chain + key Mathlib lemma names is ideal.

## The object (already built, sorry-free)
`jointDiffL2 H v : Params H →ₗ[ℝ] Matrix (Fin (H 0)) (Fin (H 2)) ℝ`,
`δ ↦ δ⁰ * (v¹) + (v⁰) * δ¹` where `δ⁰ = layer0 δ : Mat (H 0)(H 1)`, `δ¹ = layer1 δ : Mat (H 1)(H 2)`,
`v⁰ = layer0 v`, `v¹ = layer1 v`. (So `Dg(v)[δ] = δ⁰ A² + A¹ δ¹` with `A¹ = v⁰`, `A² = v¹`.)
`Params H = ∀ s : Fin 2, Mat (Fin (H s.castSucc))(Fin (H s.succ)) ℝ` — finite-dim ℝ.

## The target (the open sorry)
`r * (H 0 + H 2 - r) ≤ finrank ℝ (LinearMap.range (jointDiffL2 H v))`
given `prod H v = B` (i.e. `A¹ A² = B`) and `B.rank = r`. Call `nReg = r(H0 + H2 − r)`.

## Math facts (machine-verified, decorrelated)
- `dim (range Dg(v)) = H0·b + a·H2 − a·b` where `a = rank A¹`, `b = rank A²` (the image is
  `{δ⁰A² + A¹δ¹}`).
- `rank A¹ ≥ r`, `rank A² ≥ r` (since `rank (A¹A²) = r`), and `dim range = H0·b+a·H2−a·b ≥ nReg`
  always (slack `= (b−r)(H0−...) ...≥ 0`, tight iff `a=b=r`).
- So I only need the LOWER bound `≥ nReg`, NOT the exact dimension. I want to AVOID needing the
  exact-rank values `a`, `b` and the intersection-dim `{δ⁰A²}∩{A¹δ¹} = A¹·Mat·A²` (dim `a·b`) — those
  are the 3 absent/hard Mathlib facts.

## The candidate routes — which is cleanest in Mathlib v4.29?

ROUTE A (explicit independent family). Exhibit `nReg` explicit elements of `range Dg(v)` that are
linearly independent, then `Submodule.finrank_mono` (span ⊆ range) + `finrank_span_eq_card` (or
`LinearIndependent.card ... ≤ finrank`). Question: at GENERAL `v` (ranks `a,b` possibly `> r`), is
there a CLEAN uniform explicit family of size `nReg`, or does the family depend on the pivot pattern
of `A¹,A²` (forcing a case split)? If I take the SUBMATRIX route — pick column space `C = col(B)`
(dim r) and row space — can I write `nReg` independent images `δ⁰A² + A¹δ¹` purely from `B`'s rank-r
factorization without touching `a,b`?

ROUTE B (two-subspace sum lower bound, avoid intersection). `range ⊇ U + W` where
`U = {A¹ δ¹ : δ¹} = A¹ · Mat_{H1×H2}` (left-mul image, `δ⁰=0`) and `W = {δ⁰ A² : δ⁰} = Mat · A²`
(right-mul image, `δ¹=0`). `dim U = rank(A¹)·H2 ≥ r·H2`, `dim W = H0·rank(A²) ≥ H0·r`. But
`dim(U+W) = dim U + dim W − dim(U∩W)` needs the intersection — the thing I want to avoid. Is there a
way to lower-bound `dim(U+W) ≥ nReg` WITHOUT the intersection dim? (e.g. exhibit `U' ⊆ U`, `W' ⊆ W`
with `U' ∩ W' = 0` and `dim U' + dim W' = nReg` — a DIRECT sum of sub-pieces, sidestepping the full
intersection). What's the natural `U', W'`? My guess: split using `col(B)` (dim r): take
`W' = {δ⁰ A² : col(δ⁰A²) ⊆ col(B)}`... this is getting complicated. Is there a slicker split?

ROUTE C (factor B and reduce to deepest). Since `B = A¹A²` rank r, factor `B = P Q` with
`P : Mat (H0)(r)`, `Q : Mat (r)(H2)` full-rank-r. The "deepest" sub-differential `{δ⁰ Q + P δ¹}`
(`δ⁰ : Mat(H0)(r)`, `δ¹ : Mat(r)(H2)`) has image dimension EXACTLY `nReg` (the classic rank-variety
tangent space, `a=b=r` case), and is independent (P,Q full rank). Is `{δ⁰ Q + P δ¹} ⊆ range Dg(v)`?
This needs `δ⁰ Q` and `P δ¹` expressible as `δ̃⁰ A² + A¹ δ̃¹` — i.e. `Q = (something)A²` and
`P = A¹(something)`, which holds iff `row(Q) ⊆ row(A²)` and `col(P) ⊆ col(A¹)`. Since `B = PQ = A¹A²`
and rank r, `col(P) = col(B) ⊆ col(A¹)` ✓ and `row(Q) = row(B) ⊆ row(A²)` ✓. So `P = A¹ S`,
`Q = T A²` for some `S : Mat(H1)(r)`, `T : Mat(r)(H1)`. Then `δ⁰ Q + P δ¹ = δ⁰(T A²) + (A¹ S)δ¹
= (δ⁰ T) A² + A¹ (S δ¹) ∈ range Dg(v)`. So the deepest nReg-dim independent space EMBEDS in
range Dg(v) via the maps `δ⁰ ↦ δ⁰ T` (right-mul) and `δ¹ ↦ S δ¹` (left-mul). This looks like the
CLEANEST route: reduce to the EXACTLY-rank-r deepest tangent space, which is independent and has the
right dimension, and embed it. Confirm this is correct and identify the Mathlib lemmas for:
(i) `col(B) ⊆ col(A¹)` and `row(B) ⊆ row(A²)` from `B = A¹A²`;
(ii) the factorization `B = PQ` rank-r (Mathlib `Matrix.rank` → exists full-rank factorization?);
(iii) `P = A¹ S` from `col(P) ⊆ col(A¹)` (column-space containment ⟹ right-factor);
(iv) the deepest tangent space `{δ⁰ Q + P δ¹}` has `finrank = nReg` and how its independence is
     stated (is there a Mathlib determinantal-variety tangent lemma, or do I build the explicit
     nReg-basis `{P e_i ⊗ ... }`?).

## QUESTIONS
Q1. Is ROUTE C correct and the cleanest? Or does ROUTE A (explicit family) end up simpler in Lean
    because it avoids subspace-sum/embedding machinery? Be concrete about Mathlib v4.29 friction.
Q2. For the chosen route, what's the exact intermediate-lemma chain + the Mathlib lemma names
    (`Matrix.rank`, `Submodule.finrank_mono`, `LinearMap.finrank_range_...`, column-space/`Matrix.range`
    API, full-rank factorization, etc.)? Flag any that DON'T exist in v4.29 (so I build them).
Q3. The deepest tangent space `{δ⁰ Q + P δ¹}` independence + `finrank = nReg`: is there a slick
    Mathlib path, or is the honest cost an explicit `nReg`-element basis (e.g.
    `{P·(eᵢⱼ) : ...} ∪ {(eₖₗ)·Q : ...}` with the overlap removed)? Give the explicit basis if that's
    the real cost.
Q4. Biggest Lean-friction risk in the chosen route + where to put the 3-attempt watch.

Be adversarial and concrete. I want the lemma chain I can build, not a hand-wave.
