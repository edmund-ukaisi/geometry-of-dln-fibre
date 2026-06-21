# Thread 02 — sizing-math-stratification (pen-and-paper)

**Seat.** Design-space math sizing for the `rlct-payoff` expedition: pin the four precise statements
(`Σ^r`, the stratification, components ⟹ θ, the `(C/2, θ)` payoff + the Cited boundary), size each
phase honestly, verify the `(2,2,2)` r=0 instance, decorrelate against Codex.

**Source of truth.** Paper `paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex`
§4 (`sec:mult`, lines 739-873), §3 hierarchy (`sec:hierarchy` 706-724), §8 RLCT (`sec:RLCT`
1782-1937); digest `docs/expositions/paper-digest/high-level-overview.md`. LANDED Lean bricks
`Core.Setup`, `Core.OrbitClosure`, `Core.OrbitCodim`, `Core.VoigtDischarge`, `Core.CThetaGeometric`,
`Core.CTheta`. Codex (xhigh, decorrelated) `codex/stratification-rlct-{prompt,answer}.md`.

---

## HEADLINE VERDICTS (read this first)

1. **`Σ^r`, `Σ^{≤r}`, `mult`, `fibre` are ALREADY LANDED as Lean `Set` objects** in `Core.Setup`
   (`productRankLocus`, `productRankLocusLE`, `mult`, `fibre`). Phase **G1 and D1 are mostly done**:
   the variety-as-a-set definitions exist and are non-vacuous. What is missing is the *bridge* to the
   orbit world and the topology.

2. **`r = 0` (zero-product) is the load-bearing case** — paper Lemmas 4.5 (`lem:rank_0`) + 4.6
   (`lem:rank_vs_fibers`) reduce general `r` and the fibre `mult⁻¹(B)` to `Σ^0_{d-r}`. The
   *combinatorial* rank-shift `cCodim/numTop d r = cCodim/numTop (d-r) 0` is **already proved**
   (`Core.CTheta.cCodim_rankShift`, `numTop_rankShift`). The geometric rank-shift (Lemma 4.5/4.6 as a
   variety statement) is NOT built; it is needed only to transport the *geometric component picture*
   from `r=0` to general `r`/fibres, not for `(C, θ)` themselves.

3. **Components = MAXIMAL orbit closures** (entrywise rank-pattern order), not minimal. Verified
   exactly on the two paper-worked examples `(2,2,2)` and `(2,3,2)`. The paper's Cor 4.4
   (`cor:irred_comp`) source line reads "minimal elements of `R^{≤r}`" — this is a **transcription
   hazard to resolve in the tide**; the math under the closure theorem (`O_s ⊆ Ō_r ⟺ s ≤ r`
   entrywise, paper Thm 3.8) is unambiguously *maximal*. Both worked examples decide it.

4. **The brief's premise `m = θ` (rlc-multiplicity = component count) is FALSE per the paper.** Paper
   §8 Remark (after `thm:aoyagi-rlct`, line 1934): "there is no simple relationship between
   `rlcm(K^DLN_B)` and the number `k` of irreducible components of `mult⁻¹(B)`." The RLCT payoff is a
   **codimension** statement `rlct = C/2`; `θ` enters as the count of top-dim components of the
   *geometry* (`Σ^r`/fibre), **not** as the rlc-multiplicity. Codex independently reached the same
   conclusion. **This must reshape the brief's closing criterion** (see Phase R below).

5. **Feasibility of the geometric phases is GOOD**; the hard piece is **G2** (the stratification) and
   the **G3** topology glue (Mathlib has the `irreducibleComponents` API). **Phase R (rlct) is a Cited
   interface**, small in Lean *if* scoped as `rlct = C/2`-against-an-interface; the rlct *definition*
   itself (archimedean zeta / resolution of singularities) is **absent from Mathlib** and a from-scratch
   build would be a multi-month analytic sub-library — DO NOT build it; interface it.

---

## STATEMENT 1 — `Σ^r`, precisely

**Paper definition** (Def in `sec:mult`, lines 751-760):

> `Σ^r_d := { A ∈ Rep_d | rk(mult A) = r }`,  `Σ̄^r_d := { A ∈ Rep_d | rk(mult A) ≥ r }`.

Note the source uses `≥ r` for `Σ̄`; the digest footnote `[^rank-closure]` flags that the
component/codimension statements use the **`≤ r`** convention (`Σ̄^r = {rk(mult) ≤ r}`), which is the
genuine Zariski closure of `Σ^r` (Cor 4.4(a)). **Use `≤ r`** — this is what `Core.Setup`'s
`productRankLocusLE` already encodes, and it is the closure that has the components.

`mult : Rep_d → Mat_{d_N,d_0}`, `(A_1,…,A_N) ↦ A_N ⋯ A_1` (line 741-743). `Rep_d = ∏_{i=1}^N
Mat_{d_i,d_{i-1}}`. `mult⁻¹(B) = { A | mult A = B }` (the fibre).

**LANDED in Lean** (`Core.Setup`, all honest `Set (Tuple d)` for fixed `d`, `[CommRing k]`):
- `Tuple d := ∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) k`  (`= Rep_d`)
- `mult d A := multPrefix d A (Fin.last N)`  (the ordered product, `mult_eq_submult` bridges to the
  sub-product machinery — `Core.Submult.mult_eq_submult`)
- `productRankLocus d r := { A | (mult d A).rank = r }`  (`= Σ^r`)
- `productRankLocusLE d r := { A | (mult d A).rank ≤ r }`  (`= Σ̄^r`)
- `fibre d B := { A | mult d A = B }`  (`= mult⁻¹(B)`), with `fibre_eq_preimage : fibre d B =
  mult d ⁻¹' {B}`.
- Non-vacuity witness in-file (`(2,2,2)` over ℤ).

**Which `Σ^r` the build targets.** Build everything on **`r = 0`** (`Σ^0 = {mult A = 0}`, the
zero-product locus), then transport to general `r` and the fibre by the rank-shift. Justification:
- `(C, θ)` for `Σ^r` and for `Σ̄^r` coincide (`codim Σ^r = codim Σ̄^r`, paper line 920 + Cor 4.4(a)),
  and reduce to `Σ^0_{d-r}` by Lemma 4.5 (`lem:rank_0`).
- The **combinatorial** rank-shift is already proved (`cCodim_rankShift`/`numTop_rankShift`), so the
  `(C, θ)` *numbers* transport for free. Only the *geometric* component bijection (Lemma 4.5's
  `Σ^0_{d-r} ↪ Σ̄^r_d`) and the fibre bundle (Lemma 4.6, `k = ℂ`, locally-trivial) are unbuilt; they
  are needed for the *geometric* component count of the fibre, not for `(C, θ)`.

**Lean-targetable core link** (the one new lemma G1 needs, the rest is landed):
the corner rank-pattern entry IS the product rank.

    rankPattern d A 0 (Fin.last N) (Fin.zero_le _) = (mult d A).rank

Proof: `rankPattern d A 0 (last) = (submult d A 0 (last)).rank` (def) `= (mult d A).rank` by
`Core.Submult.mult_eq_submult`. (One-liner; `Submult.rankPattern` is `(submult …).rank`.)

---

## STATEMENT 2 — the stratification `Σ^r = ⋃ Ō_M` (the hard structural piece, G2)

**Indexing set.** `Ō_M = orbitRankLocus M` for Kostant partitions / rank patterns `M`. Write
`m_{0N}` for the corner multiplicity, `r_{0N}` for the corner rank-pattern entry; these are equal to
the product rank (Statement 1).

**Exact statements** (paper lines 787-802; Cor 4.4):

    Σ^r_d  = ⋃_{M : m_{0N} = r}  O_M          (disjoint union of orbits — the exact stratum)
    Σ̄^r_d = ⋃_{M : m_{0N} ≤ r}  Ō_M          (closure; finite union of irreducible closed orbit closures)

with `R^{≤r}_d = { r ∈ R^orb_d | r_{0N} ≤ r }`, `M^{≤r}_d = { m ∈ M^+_d | m_{0N} ≤ r }`.

**Proof sketch** (two inclusions, both elementary given the LANDED bricks):
- *`Σ̄^r ⊆ ⋃_{m_{0N}≤r} Ō_M`*: every `A ∈ Rep_d` lies in some orbit `O_S` (Gabriel, finitely many
  orbits — LANDED `Core.Gabriel`/`OrbitKostant`); `A ∈ Σ̄^r ⟺ rk(mult A) ≤ r ⟺ s_{0N} ≤ r`
  (Statement 1) ⟹ `M = S` has corner `≤ r` and `A ∈ O_S ⊆ Ō_S`.
- *`⋃_{m_{0N}≤r} Ō_M ⊆ Σ̄^r`*: `Ō_M = {A | ∀ i≤j, r_{ij}(A) ≤ r_{ij}(M)}` (the determinantal rank
  locus, LANDED `Core.OrbitCodim.orbitRankLocus` + the equality `Ō_M = orbitRankLocus M`,
  `Core.OrbitClosure.image_orbitRankLocus_eq_repClosure_orbitSet`). For `A ∈ Ō_M`,
  `rk(mult A) = r_{0N}(A) ≤ r_{0N}(M) = m_{0N} ≤ r`, so `A ∈ Σ̄^r`.

The *exact-stratum* version `Σ^r = ⋃_{m_{0N}=r} O_M` is the same with `=`; `Σ^r` is locally closed
(it is `Σ̄^r ∖ Σ̄^{r-1}`).

**Lean-targetable form.** As an equality of `Set (Tuple d)`:

    productRankLocusLE d r = ⋃ (M ∈ {M | corner(M) ≤ r}), orbitRankLocus M

Most cleanly: index the union by `Fin`-arrays / the realizers of corner-`≤ r` Kostant partitions
(`Core.CThetaGeometric.listOfPartition` already realises a partition as an interval list, and
`intervalDirectSum` builds the module). The RHS is a *finite* union (Gabriel finiteness) of
irreducible closeds (`isPrime_vanishingIdeal_orbitRankLocus` ⟹ irreducible).

**Honest difficulty.** The hard half is the **first inclusion**, which needs "every tuple lies in
*some* orbit indexed by its rank pattern" — i.e. the surjectivity of the rank-pattern → Kostant
classification at the *set* level over the working field. `Core.Gabriel`/`OrbitKostant` give the
orbit ↔ Kostant bijection; the missing glue is packaging "`A ∈ O_{S(A)}` where `S(A)` is `A`'s rank
pattern" as a clean membership lemma. This is bookkeeping over LANDED facts, not new mathematics.
**Estimate: 1 module, ~300-500 lines.** Suspicion: index-wrangling between `productRankLocusLE`
(indexed by `mult`-rank) and `orbitRankLocus` (indexed by the full rank pattern) is the time sink.

---

## STATEMENT 3 — components = maximal `Ō_M`; θ = numTop (G3 + θ1/θ2)

**The component characterisation** (the maximal-vs-minimal point, SETTLED):

> The irreducible components of `Σ̄^r_d` are exactly the `Ō_M` with `M` **maximal** (in the entrywise
> rank-pattern order) among `{ M : m_{0N} ≤ r }`. The top-dimensional ones are the **min-codim** `Ō_M`
> among them; their count is `θ`.

**Why maximal** (closure theorem, paper Thm 3.8 `O_s ⊆ Ō_r ⟺ s ≤ r`, LANDED): a finite union of
irreducible closeds `⋃ Ō_M` has as its irreducible components the *maximal* members under inclusion
(an `Ō_S` that sits inside another `Ō_R` is not a component). Inclusion `Ō_S ⊆ Ō_R ⟺ S ≤ R`
entrywise ⟹ components = maximal rank patterns.

**The min-codim ⟹ component lemma** (load-bearing, paper Thm 5.5 proof line 920; Codex-confirmed):

> If `Ō_S ⊊ Ō_R` are orbit closures, then `codim Ō_R < codim Ō_S` (proper inclusion of irreducibles
> strictly drops codim). Hence a corner-`≤r` orbit of **minimal codimension** among all corner-`≤r`
> orbits cannot be properly contained in another corner-`≤r` orbit closure, so it is **maximal**,
> i.e. a component.

**Consequence — `θ = numTop`** (the count needs no full component enumeration):

> `numTop d r` (= # of min-codim Kostant partitions over **all** corner-`r` orbits, what
> `Core.CTheta.numTop` computes) **equals** the number of top-dimensional (= min-codim) irreducible
> components of `Σ^r`. Because the min-codim orbits are automatically components (above lemma), the
> min-over-all-orbits count and the min-over-components count coincide.

This is the brick that makes the Lean `numTop` an honest `θ`: the component-count direction is
purchased by the "min-codim ⟹ maximal" lemma, *without* enumerating which non-minimal orbits are
components. `cCodim` similarly = geometric codim of `Σ^r` because the components carry the min codim,
and `cCodim_eq_inf_geomCodim` (LANDED) already gives `cCodim` = min over orbits of the **geometric**
orbit-closure codim.

**Lean-targetable forms.**

    -- G3a: components are among the orbit closures
    ∀ Z ∈ irreducibleComponents Σ̄^r, ∃ M, corner(M) ≤ r ∧ Z = orbitRankLocus M
    -- G3b: a min-codim orbit closure is a component
    (codim Ō_M minimal among corner-≤r) → orbitRankLocus M ∈ irreducibleComponents Σ̄^r
    -- θ2: the count
    (irreducibleComponents Σ̄^r |>.filter topDimensional).card = numTop d r

**Mathlib coverage (CHECKED, present at the v4.29 pin).**
`Mathlib/Topology/Irreducible.lean`:
- `irreducibleComponents X := {s | Maximal IsIrreducible s}` — the maximal-irreducible definition.
- `irreducibleComponents_eq_maximals_closed` — = maximal among closed-irreducible.
- `mem_of_subset_sUnion_irreducibleComponents` — a component contained in a finite union of
  irreducible closeds is `⊆` one of them. **This is exactly G3a.**
- `exists_mem_irreducibleComponents_subset_of_isIrreducible`, `irreducibleComponent_mem_…`.
So G3a/G3b are buildable on existing Mathlib API; the work is plugging the orbit closures
(irreducible + closed, LANDED) into these and discharging the codim-strict-monotone step (needs
`codim` reflecting proper inclusion — the geometric `codimRep` is `Ideal.height`; the strict-drop is
the analogue of `dim` monotone-strict on irreducibles, which `Core.AffineDomainDimension`/dim theory
should supply or be a short extension).

---

## STATEMENT 4 — the `(C/2, θ)` payoff and the Cited boundary (Phase D + R)

**The loss** (paper line 162, 1877): `K^DLN_B(A) = ‖mult(A) − B‖²₂ = Tr((mult A − B)ᵀ(mult A − B))`,
a real-analytic (in fact polynomial) function on `Rep_d` (real form). `K^DLN_B ≥ 0` and
`(K^DLN_B)⁻¹(0) = mult⁻¹(B) = fibre d B` (LANDED `fibre`).

**The rlct (paper Def `defn:rlct`, line 1787):** `rlct(F) = sup{ s | |F|^{-s} loc. integrable }`.
The **general inequality** (paper `eqn:rlct_upper_bound_glob`, line 1833): for real-analytic
`F`, when attained, `rlct(F) ∈ (0, codim(F⁻¹(0)) / 2]`.

**The DLN equality (paper `thm:aoyagi-rlct`, line 1889):** `rlct(K^DLN_B) = codim(mult⁻¹(B)) / 2`.

**THE CITED BOUNDARY — precisely.** Three layers, do not conflate:
- **CITED (analytic).** The general bound `rlct(F) ≤ codim(F⁻¹(0))/2` (Atiyah/Bernstein resolution
  of singularities) AND the *equality* `rlct(K^DLN_B) = codim(mult⁻¹(B))/2`. The equality is **proved
  by comparison with Aoyagi [aoyagi] Theorem 1** (paper proof line 1898-1931): Aoyagi computed
  `rlct(K^DLN_B)` directly; the paper matches Aoyagi's value to its own codim formula. So the
  load-bearing CITED input is: **`rlct(K^DLN_B) = (Aoyagi's explicit value)`**, which the paper then
  *recognises* as `codim(mult⁻¹(B))/2`. The codim → rlct identification is NOT proved geometrically
  here — it is Aoyagi's analytic theorem.
- **OURS (geometric, the new content, target zero-cited).** `codim(mult⁻¹(B))` itself: via the fibre
  bundle (Lemma 4.6) `codim mult⁻¹(B) = codim Σ^r + r(d_0+d_N−r)`, and `codim Σ^r = C = cCodim d r`
  (LANDED per-orbit, plus the G2/G3 aggregate). This is the half this expedition builds.
- **The rlct *definition itself*.** Mathlib has **no** rlct / archimedean-zeta / SLT scaffolding
  (searched: no `rlct`, no Watanabe, no log-canonical-threshold; the complex `lct` is also absent).
  Building it from scratch = real-analytic resolution of singularities + meromorphic continuation of
  `∫|F|^s` = a multi-month analytic sub-library. **SCOPE VERDICT: interface it, do not build it.**

**Cleanest Lean-targetable payoff** (interface form):

    -- interface bundling Aoyagi's cited theorem, with rlct as an opaque/axiomatised object
    structure RlctInterface where
      rlct : (Rep_d → ℝ) → ℝ
      aoyagi : ∀ B, rk B = r → rlct (K^DLN_B) = (codim (fibre d B) : ℝ) / 2   -- CITED
    -- the payoff = plug the GEOMETRIC codim (ours) into the interface:
    theorem rlct_payoff (I : RlctInterface) (B) (hB : rk B = r) :
        I.rlct (K^DLN_B) = (cCodim d r h + r*(d_0+d_N−r)) / 2          -- C/2, with C from the engine

Name discipline (`precision.md`, the recurring trap): the theorem name must say
`rlct_eq_half_codim_via_aoyagi` or carry the `Cited` tag — NOT a bare `rlct_…` that hides the
analytic interface.

**θ in the payoff — CORRECTED.** `θ = numTop` is the count of **top-dimensional irreducible
components of the fibre / `Σ^r`** (a geometric multiplicity), delivered by Statement 3. It is **NOT**
`rlcm(K^DLN_B)` (the rlc-multiplicity). Paper line 1934 (explicit): "no simple relationship between
`rlcm` and the number of irreducible components." The paper's `rlcm` formula is
`rlcm = m²·{S̃/m}(1−{S̃/m})` (`thm:aoyagi-rlct`), a different quantity. **Recommendation:** the
expedition should deliver `θ = #top-dim components` as the geometric multiplicity (honest, ours), and
state the rlct payoff as the codimension equality `rlct = C/2` (Cited). The brief's framing
"`rlct = (C/2, θ)` with `m = θ`" conflates the geometric `θ` with the analytic `rlcm`; **the
`m = θ` half is not a paper result and should be dropped or re-stated as the SLT free-energy reading,
which the paper does not claim.** (Watanabe's free energy `F_n ≈ nL₀ + λ log n − (m−1) log log n`
uses `λ = rlct` and `m = rlcm`; substituting `m = θ` there is unsupported.)

---

## THE `(2,2,2)`, r=0 INSTANCE — exact verification

`Rep_{(2,2,2)} = Mat_{2,2} × Mat_{2,2}` (pairs `(A, B)`), `Σ^0 = {(A,B) | BA = 0}`. Six corner-0
Kostant partitions; `codimForm` values `{4, 3, 5, 4, 5, 8}` (matches Lean `Core.CTheta`
docstring exactly). By `(r_{01}, r_{12}) = (rk A, rk B)`:

| `(rkA, rkB)` | Kostant `m` (nonzero) | codim | maximal? | geometric meaning |
|---|---|---|---|---|
| `(2,0)` | `m_{01}=2, m_{22}=2` | 4 | **yes** -> component | `B = 0` |
| `(1,1)` | `m_{00}=m_{01}=m_{12}=m_{22}=1` | **3** | **yes** -> component | `det A=det B=0, BA=0` (top-dim) |
| `(0,2)` | `m_{00}=2, m_{12}=2` | 4 | **yes** -> component | `A = 0` |
| `(1,0)` | `m_{00}=m_{01}=m_{11}=1, m_{22}=2` | 5 | no (⊂ `(2,0)`,`(1,1)`) | — |
| `(0,1)` | `m_{00}=2, m_{11}=m_{12}=m_{22}=1` | 5 | no (⊂ `(1,1)`,`(0,2)`) | — |
| `(0,0)` | `m_{00}=m_{11}=m_{22}=2` | 8 | no (⊂ all) | the origin-type orbit |

- **3 components**, codims `{4, 3, 4}` — matches paper Ex 4.3 (`(A=0)` c4, `(B=0)` c4,
  `(detA=detB=0,BA=0)` c3) **exactly**.
- **C = 3** (min codim among components = the `(1,1)` orbit). **θ = 1** (unique min-codim component).
- **Cross-check with Lean** `Core.CTheta`: `cCodim_d222_zero = 3` ✓, `numTop_d222_zero = 1` ✓ (both
  `decide +kernel`, axiom-clean). The Lean docstring (CTheta.lean:438) correctly flags that the
  *geometric* "Σ⁰ has one top-dim component" reading is OPEN pending the G2/G3 build — this expedition
  closes it.
- **Second example `(2,3,2)`** (`A:k²→k³, B:k³→k²`, `BA=0`): maximal-closure gives **2 components**,
  both codim 4 (`(rkA,rkB) = (2,1)` and `(1,2)`), so `C=4, θ=2` — matches paper Ex line 776 exactly.

Both examples are **decisive** that components = MAXIMAL orbit closures (not minimal), settling the
Cor 4.4 transcription ambiguity.

---

## PER-PHASE SIZING (honest, with hardest sub-lemma)

Convention: a "module" is one `DLNFibre/<Core|DLN>/…/File.lean`, one theorem family. LOC are rough.

### Phase G — `Σ^r` geometry
| step | what | status / size | hardest sub-lemma |
|---|---|---|---|
| **G1** `Σ^r`-as-variety | `productRankLocus`/`LE`, `mult`, `fibre` + corner = product rank | **LANDED** (`Core.Setup`) + 1 link lemma `rankPattern_corner_eq_mult_rank` (~10 lines) | trivial (the link is `mult_eq_submult`) |
| **G2** `Σ̄^r = ⋃ Ō_M` | the stratification (set equality) | **1 module, ~300-500 LOC** | "`A ∈ O_{rankPattern A}`" — package the LANDED Gabriel/Kostant bijection as a membership lemma; index-wrangling `mult`-rank ↔ full rank pattern |
| **G3** components = maximal `Ō_M` | irreducibleComponents glue | **1 module, ~250-400 LOC** | codim strictly drops under proper irreducible inclusion (extends dim theory); plugging `Ō_M` (irred+closed, LANDED) into `mem_of_subset_sUnion_irreducibleComponents` |

Phase G is **not** a sub-library: it consumes the LANDED engine and Mathlib's `irreducibleComponents`.
**~2 modules of new content + 1 trivial link.**

### Phase θ — component count
| step | what | size | hardest |
|---|---|---|---|
| **θ1** top-dim = min-codim | min-codim ⟹ component lemma | folds into G3 (~80 LOC) | the strict-codim-drop (shared with G3) |
| **θ2** `numTop = θ` | `(components.filter topdim).card = numTop d r` | **~150-250 LOC** | the bijection min-codim-orbits ↔ top-dim-components; `cCodim_eq_inf_geomCodim` (LANDED) supplies the codim side |

Phase θ **consumes** `Core.VoigtDischarge` + `Core.CThetaGeometric` (both LANDED). Not a sub-library.
**~1 module + a lemma in G3.**

### Phase D — DLN application
| step | what | size | hardest |
|---|---|---|---|
| **D1** `Rep_d`/`mult`/fibres | **LANDED** (`Core.Setup`) | 0 (re-export into `DLN`) | — |
| **D2** square-Frobenius loss | `K^DLN_B := ‖mult A − B‖²`, `≥ 0`, zero-set `= fibre` | **~100-200 LOC** | Frobenius norm² as `Tr(MᵀM)` over ℝ; `(K=0) ↔ (mult=B)` is `sq_eq_zero`/`norm` API |
| **D3** loss geometry = `Σ^r` | `(K^DLN_B)⁻¹(0) = mult⁻¹(B)` and its components = those of `Σ^r` (Lemma 4.6 bijection) | **~200-400 LOC** | the *geometric* Lemma 4.6 (fibre ↔ `Σ^r` bundle, `k=ℂ`) — the component bijection; OR scope to the codim identity only (smaller) |

Phase D is `DLN`-side, **~2 modules**. D3's full bundle statement (locally-trivial over `Mat^{rk=r}`,
paper `lem:rank_vs_fibers`, `k=ℂ`) is the genuinely-harder geometric piece; **scoping D3 to the
codimension identity `codim mult⁻¹(B) = codim Σ^r + r(d_0+d_N−r)` avoids the bundle and suffices for
the payoff.** Recommend the scoped version first.

### Phase R — the RLCT payoff
| step | what | size | verdict |
|---|---|---|---|
| **R1** rlct definition/interface | the SLT machinery | **DO NOT BUILD from scratch** (multi-month analytic sub-library: real-analytic resolution + ∫\|F\|^s continuation; absent from Mathlib) | **interface/axiomatise the rlct + Aoyagi's theorem** (Cited) |
| **R2** `rlct = C/2` | plug geometric `C` into the interface | **~50-150 LOC** | name discipline (must not hide the Cited interface); the arithmetic `C/2` |

**Phase R as a buildable Lean target is SMALL** *only* under the interface scoping. The from-scratch
rlct is a **genuine sub-library** and a **scope-surprise to surface** if zero-cited rlct is demanded.
**Recommended close: `rlct_eq_half_codim` against a `Cited`-tagged `RlctInterface`** carrying Aoyagi.

### Aggregate
- **New geometric content (G2+G3+θ2+D2+D3-scoped): ~5 modules, ~1.3-2k LOC.** Clearly in scope,
  consumes the LANDED engine. The `(2,2,2)`/`(2,3,2)` examples are ready acceptance tests.
- **Cited interface (R): small**; the rlct *definition* is out of scope (interface it).
- **No phase except R1 is a sub-library.** R1 is, and should be **interfaced not built**.

---

## KILL-CONDITIONS / what would break this

1. **Maximal-vs-minimal.** Kill if a third worked example (e.g. `(2,4,2)`, paper says *irreducible*,
   codim 4 — one component) fails under maximal-closure. *`(2,4,2)` should give a single maximal orbit
   ⟹ irreducible; consistent.* Run it in the tide as a third acceptance test.
2. **min-codim ⟹ component lemma.** Kill if proper irreducible inclusion does *not* strictly drop the
   geometric `codimRep` (e.g. if `Ideal.height` is not strictly monotone on the relevant chain). Needs
   the dim theory's strict monotonicity — verify it exists in `Core.AffineDomainDimension` before G3.
3. **`Σ^r` exact vs `Σ̄^r`.** `Σ^r` (exact rank) is locally closed, not closed; its *components* are
   the components of `Σ̄^r` intersected with `Σ^r` (Codex's "dense open pieces"). Build the component
   statement on the **closed** `Σ̄^r` (= `productRankLocusLE`) — the paper does (Cor 4.4). Kill if a
   component of `Σ̄^r` is trapped in `Σ̄^{r-1}` (would not meet `Σ^r`); the rank-raising density fact
   rules this out for `r ≤ min d` (paper `lem:sigma_non_empty`).
4. **θ = rlcm confusion.** Already killed: paper line 1934 explicitly denies it. Do not state it.

---

## CODEX DECORRELATION (convergence / divergence)

Decorrelated consult (xhigh, hypothesis withheld), `codex/stratification-rlct-answer.md`:
- **CONVERGES** on: components = **maximal** orbit closures (not minimal); the min-codim ⟹ component
  lemma (strict-codim-drop under proper inclusion) as the load-bearing step; `numTop = θ`; the
  stratification both inclusions; the Cited boundary (Aoyagi supplies the *analytic* rlct value, ours
  is the codim); and **`rlcm ≠ θ`** in general (Q2b).
- **DIVERGENCE (minor, noted):** Codex frames components of the *exact* stratum `Σ^r` as "dense open
  pieces `Ō_M ∩ Σ^r` with `M` maximal among `m_{0N}=r`", flagging the rank-raising/density fact as the
  subtle point — this is the `Σ^r`-vs-`Σ̄^r` distinction in kill-condition 3. The paper sidesteps it
  by stating components for the *closed* `Σ̄^r`; build there. No mathematical conflict.
- **No code pasted** (consult was a math read). The diagnosis (maximal, min-codim⟹component, rlcm≠θ)
  is the load-bearing takeaway and matches the independent exact computation.

---

## ROADMAP HANDED TO THE FORMALISER (Lean-targetable ladder)

    LANDED (dev): Setup (Σ^r,Σ̄^r,mult,fibre) · OrbitClosure (Ō_M=orbitRankLocus, irred/prime, Thm 3.8)
                  · VoigtDischarge (per-orbit codim) · CThetaGeometric (cCodim=inf geom codim) · CTheta (numTop)
                           │
     G1  rankPattern_corner_eq_mult_rank            (~10 LOC; mult_eq_submult)
           │
     G2  productRankLocusLE d r = ⋃_{corner≤r} orbitRankLocus M       (1 module; the structural piece)
           │
     G3  irreducibleComponents (productRankLocusLE d r) = maximal orbitRankLocus M  (1 module; Mathlib API ready)
           │   └─ θ1  min-codim Ō_M ⟹ component         (strict-codim-drop)
           │
     θ2  (components.filter topdim).card = numTop d r   (consumes cCodim_eq_inf_geomCodim)
           │
     D2  K^DLN_B (loss), (K^DLN_B)⁻¹(0) = fibre d B     (DLN; ~100-200 LOC)
     D3  codim mult⁻¹(B) = codim Σ^r + r(d_0+d_N−r)     (DLN; scoped — no bundle)
           │
     R1  RlctInterface  { rlct ; aoyagi : rlct K^DLN_B = codim(fibre)/2 }   (CITED interface, axiomatised)
     R2  rlct_eq_half_codim_via_aoyagi : rlct K^DLN_B = (C + r(d_0+d_N−r))/2  (~50-150 LOC; plug geom C)

**Build order:** G1 → G2 → G3/θ1 → θ2 (this is the new geometric payoff and the strongest deliverable)
→ D2 → D3-scoped → R-interface. Surface to the operator only if a zero-cited rlct *definition* is
demanded (that is the sub-library scope-surprise).
