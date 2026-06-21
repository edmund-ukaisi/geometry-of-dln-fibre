# Thread 29 — geometry/smoothness assembly ladder for `hVoigt` (pen-and-paper, 2026-06-19)

The dependency-resolved, Lean-targetable build plan for the SECOND half of the `hVoigt` discharge —
the geometry/smoothness cluster — INDEPENDENT of the L6 degeneration work. Target:

    codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M           [= hVoigt]

with `codimRep coord Z := Ideal.height (vanishingIdeal (coord '' Z))` and `orbitLinearCodim M =
finrank C¹ − finrank(range δ⁰) = finrank Ext¹(M,M)` (PROVED, `OrbitLinearCodim`).

## HEADLINE FINDINGS

1. **L2b entanglement RESOLVED — there is no standalone `ker Jac = range δ⁰` to prove.** The chain
   delivers `finrank(ker Jac at M) = dim Z_M` from landed bricks (M3+L2a+L4d) the moment L3 supplies
   smoothness. The residual is one inequality, `finrank(range δ⁰) ≥ dim O_M` (the orbit-map
   submersion / `dim O_M = dim G − dim Stab`), combined with the easy `range δ⁰ ⊆ ker Jac`. That
   inequality is the **single irreducible hard nugget** of the whole second half (Codex convergent,
   with a char-`p` witness — see §SCOPE). Everything else is bookkeeping over landed bricks.

2. **NEW SCOPE GUARD (the load-bearing discovery): the geometry route silently needs char-0 /
   separability.** Codex's decorrelated witness: `𝔾ₐ` acting on `𝔸¹` by `t·x = x + tᵖ` has a single
   dense smooth orbit but `d(t↦tᵖ)₀ = 0`, so `range dμ ⊊ T_O`. "Open dense transitive orbit + smooth
   closure" does **not** force `range δ⁰ = T_M Z_M`. The equality `finrank(range δ⁰) = dim O_M` is
   **false in char p without separability**. So `hVoigt` is a theorem about **`[CharZero k]`** (or
   separable orbit map); this hypothesis is currently ABSENT from `OrbitCodim.lean` and must be added
   to the `hVoigt`-discharging theorem. The `(C,θ)` engine and `orbitLinearCodim` are char-free; only
   the *geometric* reading `orbitLinearCodim = codim Ō` needs char-0. (Kill-condition for any
   "char-free geometric codim" claim: the Frobenius example.)

3. **L3 homogeneity sizing: 5–7 modules; the Mathlib group-smoothness precedent is NOT directly
   reusable** (`smooth_of_grpObj_of_isAlgClosed` is group-scheme-specific via `GrpObj.mulRight`; our
   `Z_M` is an external-action homogeneous space, not a group). Its *parts* are reusable
   (`dense_smoothLocus_of_perfectField`, `nonempty_inter_closedPoints`, `pointEquivClosedPoint`,
   `Scheme.Hom.preimage_smoothLocus_eq`, `FormallySmooth.of_equiv`). Most-likely-to-break: the
   smooth-closed-point-lies-in-the-open-orbit step (needs O_M **open** in Z_M, i.e. locally closed —
   not just dense; thread-18's openness caution is well-placed).

---

## THE BUILD-ORDER DAG

Notation: each node = `[Lk] name : statement`, then `hyp / consumes / sizing / kill`. `[LANDED]`
nodes are sorry-free already (grepped, §LANDED). `★` = the hard nugget.

```
                    L6 (ideal eq, SEPARATE LADDER — assumed delivered)
                      │   vanishingIdeal Z_M = vanishingIdeal O_M
                      ▼
   L1[LANDED] ──► L1' ──────────────────────────────────────────┐
   O_M irred       Z_M vanishingIdeal prime                       │
                      │                                           │
        ┌─────────────┼───────────────┐                          │
        ▼             ▼               ▼                           ▼
   L0[LANDED]   L4d[LANDED]      L3 (smooth)                   L2b★ residual
   height+dim   dim AtPrime       │  IsSmoothAt k m_M            finrank(range δ⁰)
   = card       = dim Z_M         ▼     (needs char-0)           = dim Z_M
        │             │      M3[LANDED] (smooth⟹regular)            │
        │             │           │  finrank cotangent = dim         │
        │             │           ▼                                  │
        │             │      L2a[LANDED] (cotangent = ker Jac)       │
        │             │           │                                  │
        └─────────────┴───────────┴──────────────────────────────────┘
                                  ▼
                          L7  final assembly  ⟹  hVoigt
```

### L1' — `(vanishingIdeal Z_M).IsPrime`  (one module, trivial given L6)
- **Statement:** `(MvPolynomial.vanishingIdeal k (canonicalCoord d '' (orbit-closure set))).IsPrime`,
  equivalently at the orbitRankLocus once L6 identifies the sets.
- **Hyp:** `[IsAlgClosed k]`; L6 ideal equality `vanishingIdeal Z_M = vanishingIdeal O_M`.
- **Consumes:** `isPrime_vanishingIdeal_orbitSet` (L1, LANDED) + the L6 ideal equality (rewrite).
- **Sizing:** ~5 lines (`rw [L6]; exact isPrime_vanishingIdeal_orbitSet M`). One-module sizing
  confirmed: the primeness is ALREADY proved for `orbitSet`; L1' is the transport across L6's
  set/ideal equality. **No new content.**
- **Kill:** if L6 delivers only `closure O_M = orbitRankLocus` as SETS but not the vanishing-ideal
  equality, add `vanishingIdeal` of equal sets are equal (one `congrArg`). Non-issue.

### L0 — catenary bridge  [LANDED, `NullstellensatzCodim.height_vanishingIdeal_add_varietyDim_eq_card`]
- **Statement:** prime `vanishingIdeal Z` ⟹ `height(vanishingIdeal Z) + varietyDim Z = Nat.card(RepCoord)`.
- **Consumes (downstream):** L1'. **Used in L7** to turn `height` into `card − varietyDim`.
- **Sizing:** done. **Kill:** none (landed, non-vacuity witness in-file).

### L4d — equidimensionality at a closed point  [LANDED, `AffineDomainDimension.ringKrullDim_localizationAtPrime_isMaximal_eq`]
- **Statement:** `A = R/I` finite-type DOMAIN over a field, `m` maximal ⟹
  `ringKrullDim(Localization.AtPrime m) = ringKrullDim A`.
- **Hyp consumed in L7:** `A = R / vanishingIdeal Z_M` is a domain (= L1' primeness) and `m_M` maximal.
- **Sizing:** done. This is the brick that converts `varietyDim Z_M = ringKrullDim(R/van)` into
  `ringKrullDim(AtPrime m_M)`. **Confirms `varietyDim Z_M = dim(AtPrime m_M)` is NOT a separate
  lemma — it is L4d applied at `m_M`.** **Kill:** none.

### L3 — `IsSmoothAt k m_M`  (homogeneity; 5–7 modules; needs char-0/perfect downstream not here)
`IsSmoothAt k m_M` UNFOLDS to `Algebra.FormallySmooth k (Localization.AtPrime m_M)` (Mathlib abbrev,
confirmed). Sub-ladder (thread-18 (i)–(iv), re-sized against the Mathlib precedent):

- **L3.0 (the G-action as ring automorphisms) — ring-side, ~1 module.**
  Each `P : BaseChangeGroup d` gives a `k`-algebra automorphism `α_P : R ≃ₐ[k] R` of
  `MvPolynomial (RepCoord d) k` (the linear coordinate change dual to `A ↦ P•A`), with
  `comap α_P (vanishingIdeal O_M) = vanishingIdeal O_M` (orbit is G-stable) and `α_P(m_{P•M}) = m_M`
  at the point ideals. Descends to `A ≃ₐ[k] A` and localizes to `AtPrime m_{P•M} ≃ₐ[k] AtPrime m_M`.
  - *consumes:* `baseChange` action (LANDED, `BaseChange`), `vanishingIdeal`/`comap` lemmas.
  - *sizing:* a few aeval-automorphism + comap-on-vanishingIdeal lemmas. Bounded, no absent brick.
- **L3.1 (G-stability of smoothness) — ~1 module.** `FormallySmooth.of_equiv` (Mathlib, KNOWN)
  + L3.0: `IsSmoothAt k m_{P•M} ↔ IsSmoothAt k m_M`. The smooth locus is G-stable.
- **L3.2 (a smooth closed point exists) — the Spec detour, ~2 modules, HARDEST.**
  No ring-side generic-smoothness at v4.29 (`Algebra.smoothLocus` has only `isOpen`/`eq_univ_iff`).
  Scheme-side: model `Spec A`, `Scheme.Hom.dense_smoothLocus_of_perfectField` (KNOWN) ⟹ dense smooth
  locus; `f.dense_smoothLocus_of_perfectField.nonempty` ∩ `nonempty_inter_closedPoints` ⟹ a CLOSED
  smooth `k`-point; `StructureSheaf.stalkIso` / `IsLocalRing` stalk ≃ `AtPrime` transports back to
  ring-side `IsSmoothAt`. **This is the precedent `smooth_of_grpObj_of_isAlgClosed`'s opening moves
  (lines 44–47), reusable as a TEMPLATE but not as a lemma.** Needs `[PerfectField k]` (from
  `[IsAlgClosed k]`) + `A` finite-type/reduced.
- **L3.3 (the smooth point is in the OPEN orbit) — ~1 module, MOST-LIKELY-TO-BREAK.**
  `O_M` open in `Z_M` (locally closed orbit — needs the orbit-is-open-in-its-closure fact, a
  standard but non-trivial consequence of `O_M` constructible + G-homogeneous; thread-18 flagged this
  caution and it is CORRECT — openness is NOT free from density). Then: smooth locus dense-open ∩
  O_M dense-open in irreducible (L1') `Z_M`, Jacobson ⟹ the intersection has a closed point ⟹ alg-closed
  ⟹ a `k`-point of O_M that is smooth. Transitivity (L3.1 + `rankPattern_eq_iff_orbit`, LANDED) moves
  smoothness from there to `m_M`.
  - *kill:* if O_M is NOT shown open in Z_M, the witnessed smooth closed point might sit on the
    boundary `Z_M ∖ O_M`, and transitivity does not apply. **Must prove `IsOpen` (in subspace
    topology of Z_M), not just `Dense`.** This is the one place to de-risk first.
- **L3.4 (assemble):** `IsSmoothAt k m_M` instance. ~1 module.
- **Sizing total:** 5–7 focused modules. Hardest single sub-lemma:
  `exists_closed_smooth_point_mem_openOrbit` (packages L3.2+L3.3: generic smoothness, Jacobson
  closed-point extraction, open-orbit membership, k-point dictionary). Codex convergent on the count.

### M3 — smooth ⟹ regular, cotangent = local dim  [LANDED, `SmoothPointRegular.finrank_cotangentSpace_eq_of_isSmoothAt`]
- **Statement:** `A` finite-type over `[IsAlgClosed k]`, `m` maximal, `[IsSmoothAt k m]`,
  `ringKrullDim(AtPrime m) = n` ⟹ `finrank κ(m)(CotangentSpace(AtPrime m)) = n`.
- **Consumes:** L3 (the `IsSmoothAt` instance) + L4d (the `n = dim Z_M`).
- **Sizing:** done. **Kill:** none (landed).

### L2a — Zariski cotangent = ker Jacobian  [LANDED, `CotangentJacobian.finrank_cotangentSpace_eq_finrank_ker_jacobian`]
- **Statement:** `R = MvPolynomial σ k`, generators `g : Fin m → R`, `k`-RATIONAL point `a` of `V(I)`
  (`eval a (g i)=0`), `maxIdealAt = ker(aug)`, residue field `κ = k` ⟹
  `finrank k (CotangentSpace(AtPrime maxIdealAt)) = finrank k (ker (jacobian g a))`.
- **Consumes (in L7):** the explicit minor-polynomial generators of the rank locus,
  `g = rankMinorSet M` (`RankLocusClosed`, LANDED). **WRINKLE (see §WRINKLE):** `rankMinorSet`
  generates an ideal whose `zeroLocus` is the rank locus; for L2a one needs `maxIdealAt` over
  `span(range g)` and `κ = k` — which IS the point ideal at `M` since `M` is a `k`-rational point.
  But the *cotangent* L2a computes is of `AtPrime (maxIdealAt over span g)`, NOT necessarily of
  `AtPrime (vanishingIdeal Z_M)` unless `span g` and `vanishingIdeal Z_M` have the same localization
  at `m_M` (same Zariski tangent). This is resolved by §WRINKLE.
- **Sizing:** done as a general lemma; the work is in FEEDING it (§WRINKLE).
- **Kill:** if the minor generators do not generate the right ideal locally, the Jacobian kernel is
  the tangent of the WRONG scheme. Guarded by §WRINKLE.

### L2b★ — `finrank(range δ⁰) = dim Z_M`  (THE HARD NUGGET; 2–4 modules + the submersion bridge)
This is the only genuinely new geometric content of the second half. Resolution of the entanglement:

- **`dμ_M = δ⁰` (the guard).** The orbit-map differential at the identity equals the deformation
  coboundary `deformationδ M M`, `φ ↦ (φ_{i+1} M_i − M_i φ_i)_i`. NOT a minor-pderiv Jacobian — it is
  the Lie-algebra-action linearization. (One lemma: differentiate `P ↦ P•M` at `P = 1`.)
- **Easy inclusion `range δ⁰ ⊆ ker Jac`** (`O_M ⊆ Z_M` ⟹ orbit tangent ⊆ Zariski tangent). Gives
  `finrank(range δ⁰) ≤ finrank(ker Jac) = dim Z_M`.
- **Hard reverse `finrank(range δ⁰) ≥ dim O_M`** = the orbit-map submersion. Cleanest route (Codex
  convergent, route A): the stabilizer is `Stab(M) = Aut(M) = (End M)ˣ`, and `End M = ker δ⁰ =
  Hom(M,M)` (LANDED objects). So `Stab(M)` is the principal open `D(∏ det) ⊂ Hom(M,M)` — affine,
  smooth, `dim Stab = finrank Hom(M,M)`. Then `dim O_M = dim G − dim Stab` (FIBRE DIMENSION) and
  `dim G = finrank C⁰` (G smooth), giving `dim O_M = finrank C⁰ − finrank Hom(M,M) = finrank(range δ⁰)`
  by rank-nullity (`deformationδ.finrank_range_add_finrank_ker`, LANDED).
- **The MISSING brick:** `dim O_M = dim G − dim Stab(M)`. Mathlib v4.29 has NO fibre-dimension
  theorem and NO `G/Stab` quotient (grepped, confirmed absent). This is the irreducible piece.
  - *NEEDS:* `[CharZero k]` (or separable orbit map) — the Frobenius example (§SCOPE) shows it is
    false otherwise.
  - *sizing:* this is the dominant cost of the second half. Either (i) build a minimal fibre-dimension
    bridge for the specific map `μ_M : G → O_M` (generic-fibre-dim = `dim G − dim O_M`, all fibres =
    `Stab`-cosets), or (ii) build `O_M ≅ G/Stab` and transport dimension. Both are multi-module.
    **Recommend de-risking by first proving the stabilizer description `(End M)ˣ = D(det)` (cheap,
    LANDED objects) and isolating the fibre-dimension bridge as the one new AG theorem.**
- **Kill:** the Frobenius example (`𝔾ₐ ↷ 𝔸¹`, `t·x = x+tᵖ`) — if anyone tries to prove the reverse
  inequality WITHOUT char-0/separability, this refutes it. State the char-0 hypothesis explicitly.

### L7 — final assembly  ⟹ `hVoigt`  (1 module)
- **Statement:** `[IsAlgClosed k] [CharZero k]` (the latter NEW — see §SCOPE), `M` a tuple, given L6
  ideal equality, prove `codimRep (canonicalCoord d) (orbitRankLocus M) = orbitLinearCodim M`.
- **The exact composition (all `ℕ∞`, then cast):**
  ```
  codimRep _ (orbitRankLocus M)
    = height (vanishingIdeal Z_M)                          [def of codimRep + L6 sets ⟹ same ideal]
    = Nat.card(RepCoord) − varietyDim Z_M                  [L0, via L1' primeness]
    = Nat.card(RepCoord) − ringKrullDim(AtPrime m_M)       [L4d: varietyDim = dim(AtPrime), L1' domain, m_M max]
    = Nat.card(RepCoord) − finrank κ(m_M)(cotangent)       [M3, needs L3 smoothness; κ(m_M)=k rational]
    = Nat.card(RepCoord) − finrank(ker Jac)                [L2a, via §WRINKLE feeding rankMinorSet]
    = finrank C¹ − finrank(range δ⁰)                       [L2b★: finrank(ker Jac)=dim Z_M=finrank(range δ⁰);
                                                             Nat.card(RepCoord)=finrank C¹ (easy, finrank_cochain1)]
    = orbitLinearCodim M                                   [def, OrbitLinearCodim]
  ```
- **What each step NEEDS (the hypothesis ledger):**
  - `[IsAlgClosed k]`: L0 (Nullstellensatz), M3 (perfect residue field), L3.2 (perfect field).
  - `[CharZero k]`: **L2b★ only** (separability of the orbit map). NEW; absent today.
  - `κ(m_M) = k` (M rational): L2a (rational point augmentation), M3 (residue field). `m_M = ker(eval_M)`
    is the point ideal of the `k`-rational tuple `M` — rational by construction.
  - `m_M` maximal: L4d, M3, L2a. (Point ideal of a `k`-point over alg-closed `k` is maximal — Nullstellensatz.)
  - `A = R/vanishingIdeal Z_M` a domain: L4d. = L1' primeness.
  - L6 BEFORE L7 (and before L1'): the ideal equality is the hinge; without it `Z_M`'s ring is not
    pinned. (L6 is the OTHER half, assumed.)
- **Sizing:** ~1 module of rewrites once L0/L1'/L4d/M3/L2a/L2b/L3 are in place. The `ℕ∞` subtraction
  is lossless here (`varietyDim ≤ card`), use the additive forms (`height + dim = card`) to avoid
  `ℕ∞` truncation, exactly as `NullstellensatzCodim` already does.

---

## §WRINKLE — feeding L2a: which generators, and the local-ideal match

L2a computes `ker Jac` for `g = ` any generating family of `span(range g)`, returning the cotangent of
`AtPrime (maxIdealAt over span g)`. The geometry needs the cotangent of `AtPrime (m_M over
vanishingIdeal Z_M)`. Two sub-facts close the gap:

1. **`rankMinorSet M` cuts out `Z_M` set-theoretically** (`RankLocusClosed.image_orbitRankLocus_eq_zeroLocus`,
   LANDED): `zeroLocus(span(rankMinorSet)) = canonicalCoord '' orbitRankLocus M`.
2. **At the smooth `k`-point `m_M`, the Zariski tangent only sees the radical / local ideal.** Since
   `vanishingIdeal Z_M = radical(span(rankMinorSet))` (Nullstellensatz, `[IsAlgClosed k]`) and
   `Z_M` is smooth (reduced) at `m_M` (L3), the localizations `span(rankMinorSet)·A_{m_M}` and
   `vanishingIdeal Z_M ·A_{m_M}` agree ⟹ same cotangent / same `ker Jac`. **This is a real sub-lemma
   (~1 module), NOT free.** Alternatively: prove L2a directly against generators of `vanishingIdeal
   Z_M` if L6 hands a generating family — but L6 hands an *ideal equality*, not generators, so the
   minor route is the concrete one.
- *kill:* if the minors generate a non-radical ideal whose tangent at `m_M` strictly exceeds the
  reduced tangent (a non-reduced/embedded-component pathology at `m_M`), `ker Jac` overcounts.
  Guarded by smoothness ⟹ reduced at `m_M` (L3). De-risk: verify on `(2,2,2)` (thread 17 has the
  chart; check `span(minors)` and `vanishingIdeal` localize equally at `M`).

---

## §SCOPE — the char-0 / separability hypothesis (NEW, load-bearing)

The `(C,θ)` engine, `orbitLinearCodim`, `deformationExt1`, and the Euler/indicator formulas are all
**char-free**. The *geometric* identification `orbitLinearCodim M = codim Ō_M` (= `hVoigt`) is NOT
char-free: it needs the orbit map `μ_M` to be **separable** (equivalently `dim O_M = finrank(range
δ⁰)`), which fails in char `p`.

- **Witness (Codex, decorrelated):** `𝔾ₐ` acts on `𝔸¹` by `t·x = x + tᵖ`. The orbit of `0` is all of
  `𝔸¹` (transitive, smooth, dense), but `d(t↦tᵖ)₀ = 0`, so `range dμ = 0 ⊊ T₀𝔸¹`. Hence
  `finrank(range δ⁰) = 0 ≠ 1 = dim O`. The geometric codim formula breaks.
- **Consequence for the Lean target:** `hVoigt`-discharging theorem must carry `[CharZero k]` (or a
  separability hypothesis). `OrbitCodim.lean` currently states `hVoigt` with only `[Field k]` on the
  type and `[IsAlgClosed k]` arriving via the discharge; **`[CharZero k]` must be added** to the
  L7/L2b theorems. This is fine for the DLN application (the paper works over `ℝ`/`ℂ`, char 0) and for
  the RLCT payoff. Flag to the controller: the geometric headline's honest scope is char 0.
- **This does NOT touch** `codimRep_orbitRankLocus_eq_multSum` as a *conditional-on-hVoigt* statement
  (it's char-free given `hVoigt`); it only constrains *when `hVoigt` is provable*.

---

## §LANDED (grep-confirmed, sorry-free in `Core/`)

| Brick | Lemma | File |
|---|---|---|
| L0 | `height_vanishingIdeal_add_varietyDim_eq_card`, `varietyDim`, `codimRep_eq_card_sub_varietyDim` | `NullstellensatzCodim.lean` |
| L1 | `isPrime_vanishingIdeal_orbitSet`, `isZariskiIrreducible_orbitSet` | `OrbitVariety.lean` |
| L4d | `ringKrullDim_localizationAtPrime_isMaximal_eq`, `height_eq_ringKrullDim_of_isMaximal` | `AffineDomainDimension.lean` |
| M2 | `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` | `SmoothLocalRelativeDimension.lean` |
| M3 | `smooth_point_isRegularLocalRing`, `finrank_cotangentSpace_eq_of_isSmoothAt` | `SmoothPointRegular.lean` |
| L2a | `finrank_cotangentSpace_eq_finrank_ker_jacobian`, `jacobian`, `maxIdealAt`, `aug` | `CotangentJacobian.lean` |
| rank-locus gens | `rankMinorSet`, `minorPoly`, `image_orbitRankLocus_eq_zeroLocus`, `isZariskiClosed_orbitRankLocus`, `orbitSet_subset_orbitRankLocus` | `RankLocusClosed.lean` |
| δ⁰ / Hom / Ext¹ | `deformationδ`, `Hom = ker δ⁰`, `finrank_range_add_finrank_ker`, `orbitLinearCodim`, `euler_identity` | `DeformationExt.lean`, `OrbitLinearCodim.lean` |
| G-action | `baseChange`, `smul_eq_baseChange`, `rankPattern_eq_iff_orbit`, `baseChange_normalForm` | `BaseChange.lean`, `Orbit.lean` |
| orbit map / pullback | `orbitMap`, `orbitPullback`, `vanishingIdeal_range_orbitMap_eq_ker`, `groupRing` (domain) | `OrbitVariety.lean` |

Mathlib (KNOWN): `FormallySmooth.of_equiv`; `Scheme.Hom.dense_smoothLocus_of_perfectField`;
`nonempty_inter_closedPoints`; `pointEquivClosedPoint`; `Scheme.Hom.preimage_smoothLocus_eq`;
`StructureSheaf.stalkIso`; `IsSmoothAt p := FormallySmooth k (AtPrime p)` (abbrev).
Mathlib (ABSENT at v4.29, grep-confirmed): fibre-dimension theorem; `G/Stab` scheme quotient;
ring-side generic smoothness; Cartier "group over perfect field smooth" (and false without reduced).

---

## §BUILD ORDER (the controller's plan)

Critical path runs through L2b★ (orbit-dimension) and L3 (smoothness); these are independent of each
other and both depend only on L1' + L6.

1. **De-risk L2b★ first** (highest residual risk): prove the stabilizer description `Stab(M) =
   (End M)ˣ = D(det) ⊂ Hom(M,M)` (cheap, LANDED objects) + `dμ_M = δ⁰` + the easy inclusion. Then
   isolate the fibre-dimension bridge `dim O_M = dim G − dim Stab` as the ONE new AG theorem to size
   properly (under `[CharZero k]`). If that bridge inflates, the whole second half inflates — find out now.
2. **De-risk L3.3** (O_M open in Z_M) in parallel — the second-highest risk. Prove `IsOpen` (subspace),
   not `Dense`.
3. **L3 sub-ladder** (L3.0→L3.4), reusing the `smooth_of_grpObj` template.
4. **§WRINKLE** local-ideal match (feeds L2a).
5. **L1'** (trivial, after L6).
6. **L7** assembly (rewrites) — gated on all above + `[CharZero k]` added.

Per-node hardest: L2b★ fibre-dimension bridge (new AG, char-0); L3 the open-orbit-smooth-point lemma.
Single biggest threat to the whole second half: the absence of a Mathlib fibre-dimension theorem
makes L2b★'s reverse inequality a multi-module build, OR forces importing the orbit-as-G/Stab
machinery. **This is the thing most likely to break the second-half timeline** — recommend the
controller scope L2b★ as its own sub-expedition if step 1's de-risk shows the fibre-dimension bridge
is not a 1–2 module job.

## Codex convergence/divergence
- **Convergent:** route A (Jacobian + explicit stabilizer) is cleanest; the precedent is template-only;
  the Spec detour for L3.2 is necessary at v4.29; L3.3 (open-orbit membership) is most-likely-to-break;
  the hard nugget is the orbit-dimension / submersion, not stabilizer-smoothness.
- **Codex's load-bearing contributions (independent of my prior):** (1) the char-`p` Frobenius witness
  proving the reverse inequality is IRREDUCIBLE and the route needs char-0/separability — this surfaced
  the §SCOPE guard I had not pinned; (2) the clean `Stab(M) = (End M)ˣ = D(det) ⊂ Hom(M,M)` description
  giving `dim Stab = finrank Hom` cheaply, isolating the residual to the fibre-dimension bridge alone;
  (3) confirming the "collapse into one" (deriving cotangent = coker δ⁰ᵀ directly) does NOT remove the
  hard theorem — it is the same separability content dualized.
- **Divergence:** Codex's first-pass framing ("L2b standalone vs chain-delivered") leaned toward
  "prove `finrank(range δ⁰) = varietyDim Z_M` directly and skip the Jacobian stack." On the focused
  follow-up Codex agreed route A (keep the landed Jacobian stack, add only the orbit-dimension bridge)
  is cleanest — i.e. the Jacobian stack is NOT optional waste; it converts "dim O_M" into "dim Z_M via
  the smooth-point local ring" using ONLY landed bricks, leaving the single fibre-dimension bridge as
  the new content. The two consults converge on this once the orbit-dimension nugget is isolated.

Artefacts: `codex/ladder-{prompt,answer}.md`, `codex/nugget-{prompt,answer}.md`.
