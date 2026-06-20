# Thread 38 — A6 (L4-assembly + L7) design: discharge `hVoigt` (pen-and-paper, 2026-06-20)

The Lean-targetable design for the **final assembly** of the AG half: the REVERSE inequality
`finrank(range δ⁰) ≤ varietyDim Z_M`, the squeeze with A4 to equality, and the L7 arithmetic that
discharges

    hVoigt : codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M.

NO Lean written here (design only). Decorrelated Codex consult (xhigh): `codex/reverse-ineq-{prompt,answer}.md`.

---

## HEADLINE DECISIONS

1. **ROUTE = INTRINSIC. A5 / §WRINKLE is NOT needed — and is in fact UNSOUND as a route.**
   The reverse inequality is built by a directional-derivative pairing against `vanishingIdeal Z_M`
   DIRECTLY (no minors, no radical). The MINORS+WRINKLE route (feed `g = rankMinorSet M` to L2a) is
   not just heavier — it reintroduces a real hole: `span(rankMinorSet M)` equals `vanishingIdeal Z_M`
   only up to RADICAL, and **radical-equality + smoothness of the reduced quotient does NOT force the
   same cotangent**. Counterexample (Codex, decorrelated, convergent with my prior): `J = m²`,
   `rad J = m`; the reduced quotient `R/m` is a (smooth) point but `m_J/m_J²` for `R/J` is huge. So the
   A5 "local ideals agree at the smooth point" sub-lemma would have to prove a genuinely non-trivial
   fact (`span(minors)` is radical at M, i.e. the determinantal scheme is reduced at M) that the
   intrinsic route never needs. **DROP A5. DROP L2a from the A6 chain.** (L2a stays landed/reusable
   elsewhere, but it is the WRONG tool for the intrinsic tangent of the reduced orbit closure.)

2. **The reverse inequality is CHAR-FREE.** `[CharZero k]` enters `hVoigt` ONLY through A4's forward
   inequality (separability of the orbit map in the trdeg ≤ generic-Jacobian-rank step). The reverse
   `range δ⁰ ⊆ T_M Z_M` ("orbit tangent ⊆ Zariski tangent") is a first-order dual-number calculation,
   characteristic-free. A6's reverse module carries only `[IsAlgClosed k]` (inherited from L1/M3/L3).

3. **Two load-bearing arithmetic/transport gaps surfaced that are NOT route-specific** (both routes,
   and indeed any route through M3, hit them) — see §GAPS. Neither is hard, but they are real new
   sub-lemmas, not free rewrites:
   - **κ/k base-ring bridge:** M3 gives `finrank κ(m_M) (CotangentSpace) = ringKrullDim`, the
     intrinsic collapse gives `finrank k (CotangentSpace) = finrank k (m_M.Cotangent)`. Need
     `finrank k X = finrank κ(m_M) X` for `X = CotangentSpace(AtPrime m_M)` (κ(m_M) ≃ k, rational pt).
   - **L4d reindex:** L4d is stated over `MvPolynomial (Fin n) k ⧸ I`; our ring is over the `Fintype`
     index `RepCoord d`. A `renameEquiv`/`Fintype.equivFin` + localization-transport wrapper is owed
     (heavier than L0's height+dim reindex because the maximal ideal + localization transport too).

---

## THE REVERSE INEQUALITY — lemma chain (INTRINSIC)

Target: `finrank k (LinearMap.range (deformationδ M M)) ≤ varietyDim (canonicalCoord d '' orbitRankLocus M)`.

Notation: `R = MvPolynomial (RepCoord d) k`; `I = orbitIdeal M = vanishingIdeal (orbitSet M)` (PRIME,
landed); `A = orbitRing M = R ⧸ I`; `m_M = normalFormIdeal M` (maximal, κ(m_M)=k, landed);
`δ⁰ = deformationδ M M : C⁰ → C¹`; `a_M = canonicalCoord d M : RepCoord d → k` (the k-point).

### Step R1 — the directional-derivative functional (a `k`-derivation `R → k` per tangent vector)
For `v : C¹` (i.e. `v : RepCoord d → k` after `canonicalCoord`-flattening of an edge map) define
`Dv : R →ₗ[k] k`, `Dv f := MvPolynomial.eval a_M (∑ x, v x • pderiv x f)`. This is the L2a `jacobian`
row construction (`jacobian_apply`), reusable verbatim; it is a `k`-derivation `R → k` along the
`k`-algebra structure `aeval a_M : R → k` (Leibniz: `Dv(fg) = f(M)·Dv(g) + g(M)·Dv(f)`). Build via
`MvPolynomial.mkDerivation k v` post-composed with `eval a_M`, or directly as the linear map.
- *Mathlib bricks:* `MvPolynomial.pderiv`, `MvPolynomial.mkDerivation`, `Derivation`. (fact)
- *char-free, no smoothness.*

### Step R2 (HARDEST ★) — `Dv (I) = 0` for `v = δ⁰ φ` (orbit directions kill the orbit ideal at 1st order)
For every `f ∈ I = vanishingIdeal(orbitSet M)` and every `φ : C⁰`, `D_{δ⁰ φ} f = 0`. This is the
first-order orbit-tangent inclusion `range δ⁰ ⊆ T_M Z_M`. Two candidate discharges:

- **(R2-dual-number, Codex's route):** evaluate the defining identity `orbitPullback M f = 0`
  (= `f ∈ ker μ_M^*`, landed `vanishingIdeal_range_orbitMap_eq_ker`) at the dual-number group element
  `P_v = 1 + ε φ` over `k[ε]/(ε²)`; the ε-coefficient of `f((1+εφ)•M)` is exactly `D_{δ⁰ φ} f`, and it
  is `0`. Needs a `k[ε]/(ε²)` base-change of the orbit pullback + the identity `d/dε[(1+εφ)•M] = δ⁰ φ`
  (= the `dμ_e = δ⁰` certificate, thread 36 §2). This is the DUAL of A4.3's differential identity —
  shared math, opposite direction.
- **(R2-direct, likely cleaner in Lean):** the curve `c(t) := canonicalCoord((1+tφ)•M) : RepCoord d →
  Polynomial k` (or `→ k[t]`); `f` vanishes on the orbit ⟹ `f(c(t)) = 0` as a polynomial in `t` (for
  the Zariski-dense subset `t` with `1+tφ ∈ G_d`, hence identically since `k` infinite —
  `MvPolynomial.funext`/`Polynomial` is a domain); take the `t`-derivative at `0`: `eval` of the
  formal derivative of `f(c(t))` at `t=0` is `D_{δ⁰φ} f`. The orbit-pullback evaluation API
  (`evalGroupRing_orbitPullback`, landed) + the chain rule for `pderiv` along `c`. `dc/dt|_0 = δ⁰ φ`
  is `deformationδ_apply` computed on `(1+tφ)`.

  **Recommendation:** prototype R2-direct first (avoids standing up a `DualNumber`/`k[ε]` algebra and
  its base change of `orbitPullback`); fall back to R2-dual-number if the `Polynomial`-curve chain-rule
  is messier. EITHER reuses the landed `dμ_e = δ⁰` content. **This single step is the only genuinely
  new content of the reverse inequality; everything else is bookkeeping.**
- *Kill-condition:* if `D_{δ⁰φ} f ≠ 0` for some `f ∈ I` — would refute `range δ⁰ ⊆ T_M Z_M`. Cannot
  happen (orbit ⊆ Z_M, so orbit-tangent ⊆ Zariski-tangent); the risk is purely the Lean realization of
  the chain rule, not the math.

### Step R3 — descend `Dv` to `A`, restrict to `m_M`, factor through `m_M.Cotangent`
With R2, `Dv` (for `v = δ⁰ φ`) descends to `Ā_v : A →ₗ[k] k` (kills `I`). Restrict to `m_M ⊆ A` and
factor through `m_M/m_M²` via `Ideal.Cotangent.lift` (signature confirmed in Mathlib:
`Cotangent.lift (f : I →ₗ[R] M) (hf : ∀ x y : I, f (x*y) = 0)`; the `hf` is Leibniz + `f(M)=g(M)=0` for
`f,g ∈ m_M`). Result: `cot_v : m_M.Cotangent →ₗ[k] k` = an element of `Module.Dual k (m_M.Cotangent)`.
- *Mathlib bricks:* `Ideal.Quotient.lift`/`liftₐ` (descend to A), `Submodule.subtype`/restrict to m_M,
  `Ideal.Cotangent.lift`, `Ideal.toCotangent`. (fact)

### Step R4 — assemble the k-linear map `Φ : range δ⁰ → Module.Dual k (m_M.Cotangent)` and inject
`Φ (δ⁰ φ) := cot_{δ⁰φ}` is well-defined on `range δ⁰` (the construction depends only on the vector
`v = δ⁰ φ ∈ C¹`, not on the lift `φ` — `Dv` is a function of `v`). `Φ` is k-linear in `v`.
**Injective:** if `Φ v = 0` then `Dv` kills `m_M.Cotangent`, in particular the cotangent classes of the
coordinate functions `X_x − a_x` (which lie in `m_M`); but `Dv (X_x − a_x) = v_x` (the directional
derivative of a coordinate is the corresponding component), so `v_x = 0` for all `x`, i.e. `v = 0`.
- *Mathlib bricks:* `LinearMap.ker_eq_bot`, the coordinate-class computation (cf. L2a's
  `hPsi_i`/`jacobianTranspose_apply`). (inference: injectivity is straightforward; no nondegeneracy of
  a full pairing needed, only that `Φ` separates `range δ⁰`.)

### Step R5 — finrank ≤ via the dual
`finrank k (range δ⁰) ≤ finrank k (Module.Dual k (m_M.Cotangent)) = finrank k (m_M.Cotangent)`.
- *Mathlib bricks:* `LinearMap.finrank_le_finrank_of_injective` (needs `Module.Finite k
  (m_M.Cotangent)` — holds: `m_M.Cotangent` is finite-dim, it equals the finrank via R6),
  `Module.Dual.dual_finrank_eq` (both confirmed at the pin). (fact)

### Step R6 — chain the landed bricks to `varietyDim`
`finrank k (m_M.Cotangent)
   =[L2a intrinsic collapse `finrank_cotangentSpace_localization_eq_cotangent`] finrank k (CotangentSpace(AtPrime m_M))
   =[κ/k BRIDGE, §GAPS] finrank κ(m_M) (CotangentSpace(AtPrime m_M))
   =[M3 `finrank_cotangentSpace_eq_of_isSmoothAt`, needs A3 smooth + the dim feed] ringKrullDim(AtPrime m_M)
   =[L4d `ringKrullDim_localizationAtPrime_isMaximal_eq`, needs reindex §GAPS] ringKrullDim A
   = varietyDim Z_M`   (def of `varietyDim`, `unbotD`).

Composing R1–R6: `finrank(range δ⁰) ≤ varietyDim Z_M`. ∎ (the reverse inequality).

**Why this avoids the WRINKLE entirely:** every cotangent object above is the cotangent of `A = R/I`
at `m_M` — the *reduced* orbit closure, never a determinantal-thickening. The minors never appear.

---

## THE SQUEEZE → EQUALITY

- **(≥)** A4 (LANDED, conditional on `DiffIndepCriterion` + `hA43`):
  `varietyDim_orbitRankLocus_le_finrank_range_deformationδ` :
  `varietyDim Z_M ≤ finrank(range δ⁰)`.
- **(≤)** A6 reverse (above): `finrank(range δ⁰) ≤ varietyDim Z_M`.
- ⟹ `varietyDim Z_M = finrank(range δ⁰)` (`le_antisymm`).
  As `ℕ∞`: both sides finite (`finrank` coerced; `varietyDim` is `unbotD 0` of a finite dim), use the
  `ℕ`-level equality and coerce, OR keep in `ℕ∞`.

A6's equality is conditional on A4's two named obligations (W4 is discharging them); A6 consumes A4's
headline as a hypothesis/lemma — when A4 lands unconditionally, the equality is unconditional. **Build
A6 to consume `varietyDim_orbitRankLocus_le_finrank_range_deformationδ` (whatever its final hyp list),
so A6 needs no edits when A4 closes.**

---

## L7 — final arithmetic (ADDITIVE, no `ENat.toNat`)

Target: `codimRep (canonicalCoord d) (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)` (the `hVoigt`
shape; `hVoigt`'s RHS is `(orbitLinearCodim M : ℕ∞)`).

Let `r := finrank k (range δ⁰)`, `c1 := finrank k (cochain1 d d)`, `card := Nat.card (RepCoord d)`.

Available additive identities (all landed or §GAPS):
- L0: `codimRep _ (orbitRankLocus M) + varietyDim Z_M = card`   [`codimRep_add_varietyDim_eq_card`,
  needs `(vanishingIdeal Z_M).IsPrime` = L1 landed].
- squeeze: `varietyDim Z_M = r`.
- rank-nullity: `orbitLinearCodim M + r = c1`   [from `orbitLinearCodim` def `= c1 − r` and
  `finrank_quotient_add_finrank`; cf. `orbitLinearCodim_eq_finrank_deformationExt1`].
- **ambient identity (§GAPS, new tiny lemma):** `card = c1`   (both `= ∑_i d(i+1)·d(i)`).

Assembly (cancel the finite `r`, lossless):
```
codimRep _ (orbitRankLocus M)
  =[L0 additive]  card − varietyDim Z_M           -- via the additive form, then ℕ∞-subtract OR cancel
  =[squeeze]      card − r
  =[card = c1]    c1 − r
  =[def]          orbitLinearCodim M.
```
**Cleanest Lean shape (Codex-recommended, avoids `ENat.toNat` lossiness):** prove the `ℕ∞` equality
`codimRep _ (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)` by showing
`codimRep _ (orbitRankLocus M) + (r : ℕ∞) = (orbitLinearCodim M : ℕ∞) + (r : ℕ∞)` and cancelling
`(r : ℕ∞)` (finite ⟹ `AddLECancellable`, cf. `NullstellensatzCodim`'s `ENat.addLECancellable_of_ne_top`).
- LHS + r = `card` (L0 additive, since `varietyDim = r`).
- RHS + r = `(orbitLinearCodim M + r : ℕ∞)` = `(c1 : ℕ∞)` = `(card : ℕ∞)` (ambient identity, cast).
- ⟹ equal. ∎

This is exactly the additive/cancellation discipline `NullstellensatzCodim` already uses; no `toNat`,
no `WithBot ℕ∞` round-trip past the `varietyDim`/`unbotD` already inside L0.

---

## §GAPS — the non-route-specific new sub-lemmas (build these; small)

1. **`card_repCoord_eq_finrank_cochain1`** : `Nat.card (RepCoord d) = finrank k (cochain1 d d)`.
   - `RepCoord d = Σ i:Fin N, Fin(d i.succ) × Fin(d i.castSucc)`; `Nat.card` reduces via
     `Nat.card_sigma`/`Fintype.card_sigma`, `Fintype.card_prod`, `Fintype.card_fin` to
     `∑_i d(i.succ)·d(i.castSucc)`. `finrank_cochain1` (landed) = the same sum. ~10 lines. (fact)
   - *kill:* index-order mismatch (`succ`/`castSucc` vs the sum's order) — cosmetic, `Finset.sum`
     reorder.

2. **`finrank_base_change_residue_eq`** (κ/k bridge) : for the local ring `T = AtPrime m_M` with
   residue field κ = `ResidueField T` and the `k`-structure, `finrank k (CotangentSpace T) =
   finrank κ (CotangentSpace T)`. Since `CotangentSpace T` is a κ-module and κ ≃ₐ[k] k
   (`residueFieldNormalFormEquiv` composed with the `AtPrime`→`A/m` residue identification), the
   k-finrank equals the κ-finrank (scalars along an iso).
   - Cleanest: a general lemma "`κ ≃ₐ[k] k` (k-algebra iso of fields) ⟹ for a κ-module V,
     `finrank k V = finrank κ V`" via `finrank` multiplicativity in a tower
     (`finrank k V = finrank k κ · finrank κ V`, `finrank k κ = 1`), or transport along the scalar
     iso. ~15–30 lines. (inference: standard, but a real obligation — currently ABSENT, grep-confirmed
     no `finrank k … = finrank ResidueField …` bridge in Core.)
   - *trap (Codex + verified):* M3 is `finrank (ResidueField (AtPrime m_M))`, the intrinsic collapse and
     the pairing are `finrank k`. DO NOT silently identify them — discharge the bridge. κ(m_M)=k is a
     k-algebra iso of fields, so `finrank k κ = 1`, and the bridge holds; but it must be stated.

3. **`l4d_reindex`** : apply L4d to `A = orbitRing M = MvPolynomial (RepCoord d) k ⧸ I`.
   L4d is over `MvPolynomial (Fin n) k`. Wrap with `Fintype.equivFin (RepCoord d)` +
   `MvPolynomial.renameEquiv` + `Ideal.quotientEquivAlg` (transport `I`) + a localization-at-prime
   transport for the image of `m_M`, then `ringKrullDim_eq_of_ringEquiv`. ~30–50 lines (heavier than
   L0's reindex: must carry the maximal ideal + its localization, not just height+dim). (inference)
   - *alternative:* state a `Fintype`-indexed L4d once (mirroring `NullstellensatzCodim`'s
     `height_add_ringKrullDim_quotient_eq_card`) and reuse — preferable if A4 also needs it.

---

## A6 BUILD PLAN (module decomposition)

Two modules (reverse-inequality + assembly), plus the three small §GAPS lemmas homed sensibly.

- **Module A6.1 `Core/OrbitTangentCotangent.lean`** — the reverse inequality.
  Contents: R1 (`Dv` directional-derivative functional, reuse L2a `jacobian` shape) · R2★
  (`Dv (I) = 0` for `v = δ⁰φ`, via R2-direct curve or R2-dual-number — the only new content) · R3
  (`Cotangent.lift` factorization) · R4 (`Φ : range δ⁰ → Dual k (m_M.Cotangent)` + injectivity) · R5
  (`finrank_le` + `dual_finrank_eq`) · R6 chain (intrinsic collapse + κ/k bridge §GAPS-2 + M3 + L4d
  §GAPS-3). Headline: `finrank_range_deformationδ_le_varietyDim` :
  `finrank k (range δ⁰) ≤ varietyDim (canonicalCoord d '' orbitRankLocus M)`. `[IsAlgClosed k]` only.
  Homes §GAPS-2 (κ/k bridge) and §GAPS-3 (L4d reindex) if not already lifted into the landed files.

- **Module A6.2 `Core/VoigtDischarge.lean`** (or extend `OrbitCodim`) — the squeeze + L7.
  Contents: `card_repCoord_eq_finrank_cochain1` (§GAPS-1) · the squeeze `varietyDim = finrank(range δ⁰)`
  (le_antisymm of A4 + A6.1) · the L7 additive/cancellation assembly. Headline:
  `voigt_codimRep_eq_orbitLinearCodim` (= `hVoigt` instantiated) :
  `codimRep (canonicalCoord d) (orbitRankLocus M) = (orbitLinearCodim M : ℕ∞)`, hypotheses
  `[IsAlgClosed k] [CharZero k]` + A4's residual obligations (until A4 lands unconditional).
  THEN discharge `hVoigt` in `codimRepCanonical_orbitRankLocus_eq_multSum` ⟹ make
  `codimRepCanonical_orbitRankLocus_eq_multSum` UNCONDITIONAL (the expedition's deliverable).

**Module count:** 2 substantive (A6.1 reverse, A6.2 assembly) + 3 small §GAPS lemmas (home in A6.1 or
the relevant landed file).

**Single hardest sub-lemma:** R2★ `D_{δ⁰φ} f = 0 for f ∈ I` (the first-order orbit-tangent inclusion).
Everything else is landed-brick bookkeeping. It is the dual of A4.3 and reuses the same `dμ_e = δ⁰`
certificate — so it should ride on A4.3's infrastructure once that lands (coordinate the curve/
dual-number plumbing with the A4 tide to avoid duplicating `dμ_e = δ⁰`).

**Kill-conditions:**
- R2★: the math cannot fail (orbit ⊆ Z_M ⟹ orbit-tangent ⊆ Zariski-tangent); risk is the Lean
  chain-rule realization. If R2-direct's `Polynomial`-curve chain rule is messy AND R2-dual-number's
  `k[ε]` base change of `orbitPullback` is messy, scope R2★ as the single residual (everything else
  closes around it).
- §GAPS-2 (κ/k bridge): if `finrank k = finrank κ` transport is not a clean tower step at the pin,
  it inflates — de-risk by checking `Module.finrank_mul_finrank`/`finrank` tower API early.
- §GAPS-3 (L4d reindex): if the localization-at-prime transport across `renameEquiv` is heavy, prefer
  stating a `Fintype`-indexed L4d (one-time, shared with A4).

---

## HYPOTHESIS LEDGER (what `hVoigt`'s discharge ends up needing)

- `[IsAlgClosed k]` — L0 (Nullstellensatz), L1 (primeness), M3 (perfect residue field), L3 (smooth pt),
  κ(m_M)=k (rational point ⟹ residue field k). The reverse inequality, the squeeze, L7 all inherit it.
- `[CharZero k]` — **A4 forward inequality ONLY** (separability/`DiffIndepCriterion`). The reverse
  inequality (A6.1) is char-free; L7 arithmetic is char-free. So `[CharZero k]` is added to the
  `hVoigt`-discharging theorem **because of A4**, confirming thread-29/30's §SCOPE. Add `[CharZero k]`
  to the L7 headline + (per OrbitCodim docstring) note the geometric reading's honest scope is char 0.
  The `(C,θ)` engine, `orbitLinearCodim`, L6, and the conditional-on-`hVoigt`
  `codimRep…_eq_multSum` stay char-free; only the *unconditional* discharge needs char 0.
- `m_M` maximal — landed (`orbitPointIdeal_isMaximal`). κ(m_M)=k — landed
  (`residueFieldNormalFormEquiv`). `A` a domain — landed (L1 primeness). `IsSmoothAt k m_M` — landed
  (A3 `isSmoothAt_normalFormIdeal`). `(vanishingIdeal Z_M).IsPrime` — landed (L1
  `isPrime_vanishingIdeal_orbitRankLocus`).
- A4's residual: `DiffIndepCriterion k (groupRing d)` + `hA43` (W4 discharging). A6 consumes A4's
  headline; conditional until A4 closes.

---

## CODEX CONVERGENCE / DIVERGENCE

- **Convergent (load-bearing):** INTRINSIC over MINORS+WRINKLE; A5 NOT needed; the WRINKLE is
  *dangerous* (radical-equality ⊄ same cotangent, `J=m²` counterexample) — this independently confirmed
  and SHARPENED my prior (I expected "intrinsic avoids A5"; Codex showed the minors route is not merely
  heavier but unsound as stated). The pairing via `Ideal.Cotangent.lift` + injection into the dual;
  injectivity easy (test on coordinate classes); L7 additive not `ENat.toNat`.
- **Codex's independent contributions:** (1) the explicit `J=m²` unsoundness of the WRINKLE; (2) the
  dual-number `1+εφ` discharge of R2★ as an alternative to the curve route; (3) flagged the **κ/k
  base-ring bridge** (M3 over κ, pairing over k) as a real obligation I had under-weighted — promoted
  to §GAPS-2; (4) flagged the **L4d reindex** (Fin n vs Fintype) as heavier than L0's because of the
  maximal-ideal/localization transport — §GAPS-3.
- **Divergence / my refinement of Codex:** Codex leaned on the dual-number route for R2★; I rate the
  **R2-direct `Polynomial`-curve** route at least as clean in Lean (avoids standing up `k[ε]/(ε²)` and
  base-changing `orbitPullback`), reusing the landed `evalGroupRing_orbitPullback` + `dμ_e = δ⁰`. Both
  are sound; prototype R2-direct first. Codex did not surface §GAPS-1 (`card = finrank C¹`) as a named
  lemma — I add it (small but real).

## Artefacts
`codex/reverse-ineq-prompt.md`, `codex/reverse-ineq-answer.md`.
