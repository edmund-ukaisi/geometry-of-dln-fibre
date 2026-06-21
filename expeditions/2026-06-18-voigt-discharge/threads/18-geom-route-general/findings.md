# Thread 18 — general-M L3/L2 route decision (pen-and-paper, 2026-06-19)

## DECISION: HYBRID — homogeneity (Route B) for L3 + uniform local Jacobian for L2. (Codex convergent.)

### Route A (general explicit chart): SUB-LIBRARY — REJECTED
The (2,2,2) chart (thread 17, one pivot, Gröbner graph-ideal=closure-ideal) does NOT scale. General hardest step:
`localized graph ideal = localized closure ideal` for an arbitrary bar-list — pivot SET is `L`-dependent (bar-
incidence poset), residuals need explicit Laurent cofactor identities per orbit type, no Gröbner in Lean. **This
is the SAME matrix-Schubert / Abeasis–Del Fra lace combinatorics the paper only cites (= the L6 content).**
Kill-condition FIRED: no `L`-uniform Laurent formula. The general chart re-imports L6's sub-library. AVOID.
(Its payoff bricks are clean — `FormallySmooth (MvPolynomial)` + `Away` preserves + `iff_of_equiv` — so the risk
is 100% the `AlgEquiv` construction.)

### Route B (homogeneity): BOUNDED for L3 — CHOSEN
`IsSmoothAt k m` UNFOLDS to `FormallySmooth k (Localization.AtPrime m)`. `A = 𝒪(Z_M)` is FiniteType/FinitePresentation/k.
- **(i) a smooth closed point exists — the ONE Spec detour (bounded).** No ring-side generic smoothness at v4.29
  (`Algebra.smoothLocus` has only `isOpen`/`eq_univ_iff`). Use scheme-side `Scheme.Hom.dense_smoothLocus_of_perfectField`
  (Morphisms/Smooth.lean): model `Spec A`, `genericPoint ∈ smoothLocus` → transport to a CLOSED `k`-point
  (`jacobsonSpace`/`pointEquivClosedPoint`/`nonempty_inter_closedPoints`) → `StructureSheaf.stalkIso`
  (`AtPrime ≃ₐ stalk`) back to ring-side. CAUTION: openness gives generalization-stability, NOT specialization —
  (i) yields a smooth closed point *somewhere*; (iii) moves it to `M`. (`Group/Smooth.lean` runs this same stack.)
- **(ii) smoothLocus G-stable — bounded, ring-side.** Each `P:G(k)` ⟹ `k`-algebra automorphism `α_P` of `A`,
  `α_P(m_{P•M})=m_M`; `FormallySmooth.iff_of_equiv` transfers smoothness. (Build: a few aeval-automorphism + `comap`
  on `vanishingIdeal` lemmas; no absent brick.)
- **(iii) transitivity — DONE** (`rankPattern_eq_iff_orbit`, `Core.Orbit`).
- **(iv) open-orbit membership — one bounded lemma:** the witnessed smooth closed point lies in the open orbit
  `O_M` (smooth-set open+dense ∩ open-orbit open+dense in irreducible `Z_M` ⟹ nonempty), so transitivity applies.
  (`A` = closure ring; `M` in the open orbit; `AtPrime m_M` decided by the open orbit.)

### L2 (tangent = range δ⁰): ABSENT-brick in BOTH routes — the de-risk-first step
Mathlib has NO group-action-orbit-tangent API (`rg`: 0 hits); "orbit-map differential = δ⁰" and "image = tangent"
are MARKDOWN-only. So L2 is from-scratch either way. The hybrid makes it the NARROW UNIFORM
`m_M/m_M² ≃ ker(Jacobian of the ideal generators at M) = range δ⁰` (L-uniform — the orbit-map linearisation),
NOT a per-orbit chart `AlgEquiv`. **Most-likely-to-break:** the general CA bridge `m_p/m_p² ≃ ker(J_I)` for
`V(I)⊆kⁿ` at a `k`-point (Mathlib has `Ideal.Cotangent`, `KaehlerDifferential.kerCotangentToTensor`, but not a
packaged "Zariski tangent = Jacobian kernel"). **De-risk first** (thread 17 already has `ker(J_M)=range δ⁰` on (2,2,2)).

## Updated remaining plan (HYBRID)
- **L2a (next, de-risk):** general CA bridge `cotangent m_p/m_p² ≃ ker(Jacobian)` for `V(I)` at a `k`-rational point.
- **L2b:** `ker(J_M) = range δ⁰` for our orbit (orbit-map linearisation; (2,2,2) done).
- **L3:** homogeneity (i)+(ii)+(iii)+(iv) ⟹ `IsSmoothAt k m_M`.
- **L6:** `orbitRankLocus = Ō_M` (the box-move degeneration sub-library, 3–4 modules, paper-cited) — still needed.
- **L1:** `vanishingIdeal(Z_M)` prime (from L6 + O_M irreducible, thread 16).
- **L4-assembly + L7.**
Per-route hardest: A = orbit-cell combinatorics (sub-library, rejected); B = the L2 cotangent↔Jacobian bridge (shared).
Codex: convergent on HYBRID; sharpened — L2 absent-brick is shared by both routes (not B-specific).

Codex artefacts: `threads/18-geom-route-general/codex/route-{prompt,answer}.md`.
