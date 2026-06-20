# lessons.md — Aoyagi-Full (append-only methodological learnings)

Seeded from the diagnostic of `expedition/aoyagi-rlct` (the prior, assumed-bad attempt) and the
pen-and-paper rounds that preceded this expedition. Directed-suspicion fuel for `priorities.md`.

## 2026-06-20 — seed lessons (from the diagnostic)

- **Treadmill failure mode (the thing to not repeat).** The prior expedition put ~55% of recent commits
  and +8.7K lines into reconciling a *printed Case-2 typo* with no stated target theorem, so accretion
  had no stop condition; open sub-items grew 7→25+ in a day. Guardrail: the goal skeleton with named
  `sorry`s is the contract; every unit closes a named sorry; sorry-count trends down.

- **The "awkward middle" — where to draw the Cited line.** Proving the blow-up *combinatorics* while
  citing the *extraction* strands the resolution *geometry* in between (neither proved nor cited), and
  that gap is what the bookkeeping was silently assuming. Cite the **extraction** (S2); **prove the
  construction** (R1, real charts). Never an abstract exponent-bookkeeping engine disconnected from the
  geometry.

- **Aoyagi's printed Case-2 vector is λ-safe; the "prefix-minimum correction" is NOT.** The printed
  `t^{(i)}=M^{(i+1)}` telescopes to `M^{(S)}M^{(S+1)}` (a two-width product ≥ 2λ) — always safe. The
  prefix-minimum "fix" the prior expedition built can violate admissibility and produce sub-2λ (even
  negative) values. So: do not reproduce the corrected-vector machinery; the Case-2 vectors never bind
  (proven). If we ever touch the printed vector, the printed reading is the geometrically valid one.

- **Definition 3 (relevant-set selection) may be ill-defined on unbalanced widths.** A finder returned
  no set for `[4,2,1,3]`. Mitigation: define `aoyagiλ` via the always-well-defined minimisation; prove
  the printed Theorem-2 expression equal where Def 3 applies; pin the exact Def-3 regime.

- **Clean closed form beats the printed one for formalisation.** `2λ_core = ½(Σqᵢ²−Σmₖ²)` (q = balanced
  ℓ-split of P) keeps terms small and sidesteps Def 3 in the core. Internal target; prove printed = clean.

- **Page images are necessary when a step depends on `M^{(s)}` vs `M(S)`** — plaintext PDF extraction
  collapses these notations. Record the source-imaged formula before accepting any transition data.
  (Carried from the prior expedition's own lessons; verified relevant.)

- **Build-time anti-pattern: one giant file.** A 13.7K-line module recompiles wholesale on any edit.
  Many small modules + a build-once Foundations layer + background builds.

## 2026-06-20 — statement-fidelity audits must be per-rung and adversarial

The Rung-0c audit (broad: defs, S2-minimality, θ-seam, hygiene) PASSED but MISSED two statement bugs in
the skeleton rungs — caught only by a later controller precision-read of the full `Skeleton.lean`:
- `block_elimination` (L1) was **vacuous**: `∃ invertible P,Q, (P·B·Q).rank = r` is trivially true
  (rank invariant under invertible mult). A non-X=X statement can still be vacuous — "rank preserved"
  reads like content but is a triviality. **Audit test:** for each rung, ask "could this be discharged by
  identity witnesses / an invariant that holds for ALL inputs?".
- `product_reduction` (L2) **over-claimed**: `rlctAt = aoyagiLambda` `∀ wstar ∈ optimalSet` — but the local
  RLCT varies over the fibre (min at the deepest point; that's why D1 exists), so it's false at milder
  points. **Audit test:** for each `∀`-over-a-set conclusion, ask "true on ALL admitted inputs, or only at
  special points?". Tell-tale: if the rung makes a sibling rung (D1) redundant, it's over-claiming.
Takeaway: a green build + a broad audit is necessary, not sufficient; statement-fidelity needs a sharp,
per-rung, adversarial pass (vacuity + over/under-claim + name=content) — now standard for skeleton audits.

## 2026-06-20 — the "deepest point" of a fibre: prefer a CONSTRUCTED point over a ∀-predicate

For the DLN fibre {∏A = B} (rank B = r), the local RLCT is minimized at the "deepest" point. Pinning the
identification (pp + decorrelated Codex, exact-algebra):
- **per-partial-product rank-r is WRONG** (too weak): a layer can be high-rank while the partial products
  stay rank r, giving a milder singularity. Counterexamples both r=0 ((2,2,2): (A¹=0,A² inv)→rlct 2≠3/2)
  and r>0 ((3,3,3) r=1: A¹=diag(1,0,0),A²=diag(1,Q)→9/2≠4).
- **per-layer rank-exactly-r is SUFFICIENT** (⟹ all-partial-rank-r by submultiplicativity; rlct constant
  over it = a single GL gauge orbit) **but NOT EXHAUSTIVE** — the full set attaining λ is larger (residual
  core in the closure of an Aoyagi-minimizing nested-rank stratum; multiple orbits attain λ).
- ⇒ **a ∀-predicate form (even per-layer) under-describes the attaining set.** Use a SINGLE CONSTRUCTED
  `deepestPoint` (block-normal rank-r chain, residual core = 0): D1 `⨅ = rlctAt(deepestPoint)` (Thm-2
  monotonicity), L2 `rlctAt(deepestPoint) = aoyagiLambda`. Lowest proof surface, zero over-claim, no
  gauge/orbit lemma needed. General lesson: when a "the special point(s)" set is subtle/non-unique, key the
  statement to ONE constructed witness, not a ∀-over-the-set predicate.
