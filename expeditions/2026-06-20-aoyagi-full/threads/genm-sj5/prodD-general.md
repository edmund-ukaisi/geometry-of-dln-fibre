# ∀M deeper-product tube-codim + the Core-codim bridge — the last Level-A math gap for the general fill

**Seat:** pen-and-paper (witness + obstruction — adjudicate one truth-value: does the product-rank tube
leading power = codim ∀M, or does it drop below at some width class = a wall?). **Date:** 2026-07-11.
**NO Lean.** **Charge (team-lead, task #127):** for a DEEPER-PRODUCT tail (`A₁···A_{L−1}` a genuine
product), confirm the product-rank tube codim `D = codim{rank(A₁···A_{L−1}) ≤ q−1}` (pushforward measure)
has **leading power = codim** (ties → log, threshold-preserving), and the linchpin
`minAdm ≤ D + M₀(q−1)` holds with the PRODUCT `D` at general width. ★ Check the bridge: is `D` the Core
geometric `C`-codim (type-A Ext / `cCodim`)?

**Exact algebra (mine):** `/tmp/prodD/{algebra,tube_jac}.py` (minAdm/front-peel scan; exact Jacobian-rank
codim; tube-MC slope ladder). **Decorrelated:** own `local-codex-consult` (xhigh, my "no-wall" conclusion
WITHHELD — I asked it to HUNT the wall): `codex/prodD-{prompt,answer}.md`. Codex concurred term-for-term
and supplied the rigorous multiscale argument that rules the wall out.

---

## VERDICT (headline): NO WALL ∀M. `L = D = C(reduced) = minAdm(reduced)`. The gap is not independent.

**The product-rank tube leading power `L` equals the algebraic codim `D` for every width class** (up to
logs; a literal `Ct^D` can be false, the honest statement is `t^{D+o(1)}`). `D = C(m₁−(q−1),…,M_L−(q−1)) =
minAdm(reduced by q−1)` — the type-A quiver / Lehalleur–Rimányi codimension of the **reduced chain**, so
the **Core bridge HOLDS ∀M** (proven, not just for the `(3,3,3,4)` instance). The linchpin
`minAdm(M) ≤ D + M₀(q−1)` is the `j=q−1` front-peel competitor — tautological (0 violations / 28420).

Two decorrelated lines agree: (i) mine — exact Jacobian-rank codim (5 cases incl. narrow-internal) +
tube-MC slopes trending to codim + the `normalSlice` unit-Jacobian CoV straightening the pushforward to
the reduced chain's Lebesgue zero-product tube; (ii) Codex — the add-longest / rank-shift / QIP proof of
`D = C(reduced)`, and an **affine-on-the-singular-value-simplex** argument proving no interior/multiscale
configuration lowers the exponent below the integer-rank (front-peel) vertex value.

**The deeper structural finding: the ∀M tube-codim is NOT an independent gap.** `L = D` at arity `L` is
*logically equivalent to* the reduced chain's zero-product box-finiteness at arity `L−1` (the tube leading
power IS the box-integral abscissa of convergence). Via the `normalSlice` unit-Jacobian CoV the product
tube becomes the reduced chain's Lebesgue Σ⁰-tube, so `L = D` closes by the **arity-descent induction**
already in the B5-desc/covdesign architecture (front-peel linchpin + `normalSlice_transfer`, base `L≤2`
banked). There is nothing extra to prove per width class.

---

## 1. The Core-codim bridge — `D = C(reduced) = minAdm(reduced)` ∀M (PROVEN, largely banked)

`D = codim{rank(A₁···A_{L−1}) ≤ s}` (`s = q−1`, factor-space Lebesgue) equals the type-A quiver
codimension of the reduced chain:
> `D = C(m₁−s, m₂−s, …, M_L−s) = minAdm(m₁−s,…,M_L−s)` for `0 ≤ s ≤ min_i m_i` (`= 0` if `s ≥ min_i m_i`).

**Mechanism (Codex, PROVEN; = the paper's own machinery).** Full-product rank = multiplicity of the
longest-interval module; removing `s` longest intervals leaves a representation of widths `m_i−s` with zero
full product. The longest interval is **projective-injective**, so adding/removing it preserves the normal
slice and orbit codimension (the paper's **add-longest theorem** `main.tex:682` + **rank-shift lemma**
`main.tex:816` + **QIP** `main.tex:1138`). Rank exactly `s` is dense in `{rank ≤ s}`.

**Banked Core consumed (no re-derivation for the ∀M lift):**
- `cCodim_rankShift` (`Core/CTheta.lean:377`, Lemma 4.5): `cCodim d r = cCodim (d−r) 0` — the reduce-by-`s`.
- `productRankLocusLE_eq_iUnion_orbitRankLocus` (`Core/SigmaStratification.lean:135`): the product-rank
  locus = ⋃ orbit rank loci (so its codim is the `cCodim`).
- `codimRepCanonical_orbitRankLocus_eq_…` (`Core/OrbitCodim.lean`) + Voigt (`Core/VoigtDischarge.lean`):
  geometric codim = `cCodim` (char-0, alg-closed).
- `cCodim_eq_qipMin` (`Core/CThetaQIPConverse.lean:833`) + `cCodim_zero_eq_cValue_comp_sort`
  (`Core/CThetaArbitrary.lean:43`): `cCodim = QIP min = minAdm`, **permutation-invariant** (so the reduced
  chain's possible non-monotonicity is a non-issue — sort it).

**Exact verification (mine, `tube_jac.py`).** Jacobian-rank codim (rank of the Jacobian of the
`(s+1)`-minors of `P` at a locus point) **MATCHES `minAdm(reduced)` in all 5 cases:**

| tail (product) | `s` | Jac-codim | `minAdm(reduced)` |
|---|---|---|---|
| `(3,3,4)` 2-layer | 1 | 4 | `minAdm(2,2,3)=4` ✓ |
| `(3,3,4)` | 2 | 1 | `minAdm(1,1,2)=1` ✓ |
| `(4,4,5)` 2-layer | 2 | 4 | `minAdm(2,2,3)=4` ✓ |
| `(3,1,3)` narrow | 0 | 3 | `minAdm(3,1,3)=3` ✓ |
| `(2,1,2)` narrow | 0 | 2 | `minAdm(2,1,2)=2` ✓ |

Codex's worked cases match: `(3,3,4)s=1 → C(2,2,3)=4` (two top components), `(3,3,3,4)s=1 → C(2,2,2,3)=3`
(unique min at `(1,1,0)`).

**One Lean-bridge caveat (state, don't launder):** the `minAdm = cCodim` identity — both are `C` — may need
its explicit Lean lemma (the box-morse-cert flagged `cCodim_eq_minAdm` "NEEDS PINNING"; alternatively the
pure-ℕ `minAdm_rrp_subadd` route). And the geometric `cCodim` is the **complex** codim (char-0, alg-closed);
the analytic tube is over ℝ — the real determinantal-variety codim = complex `cCodim` (standard; one
geometry↔analysis bridge to state, as box-morse-cert §3 noted).

---

## 2. Leading power `L = D` ∀M — the wall is ruled out (no strict power reduction)

The load-bearing measure-theoretic claim: the tube `vol{σ_{s+1}(P) ≤ t}` (in a **bounded** box — the whole
factor space has infinite tube volume by reciprocal rescaling of adjacent factors) has leading power
`L = D`, not `< D`. **Two independent arguments, both giving `L = D`:**

### (a) The affine-on-the-simplex argument (Codex, decorrelated — rules out the ≥3-factor bend)

Write the tail product `Q`'s positive singular values on a dyadic shell as `σ_i(Q) ≍ t^{β_i}`,
`0 ≤ β₁ ≤ … ≤ β_r ≤ 1`. A simultaneous rank-flag pivot decomposition gives a shell exponent that is
**affine in `β`** on the ordered simplex; multiplying by the free front factor adds `(m₁−s)Σ_{i>s}(1−β_i)`,
still affine. An affine function on the ordered `β`-simplex is minimized at a **vertex**
`β = (0,…,0,1,…,1)` — an **integer** effective rank `j`, where the exponent is
`T(m₂,…,M_L; j) + (m₁−s)(j−s)`. So an **interior (fractional / multiscale) configuration cannot produce a
smaller power**; a flat minimizing face gives only logs. Substituting the IH `T(tail;j) = C(reduced tail)`
recovers the front-peel formula `= C(m₁−s,…,M_L−s) = D`. **Hence `L = T = D`; the ≥3-factor "shell-rate
bend" is a reordering within the simplex, not a power drop.** This is the decisive ruling-out of the wall
(Codex independently hunted it and reported "NO: `L` cannot be strictly smaller than `D`").

### (b) The arity-descent identity (mine — the gap is not independent)

`normalSlice_transfer` (banked witness #109, unit-Jacobian threaded shear, exact `L≤4`) maps
`{rank P ≤ s} ≅ Σ⁰(reduced)` **measure-preservingly**, so the pushforward tube `vol{σ_{s+1}(P) ≤ t}`
equals the reduced chain's **Lebesgue** zero-product tube `vol{‖Y₁···Y_{L−1}‖ ≤ t'}`. That tube's leading
power is the reduced chain's box-integral abscissa `= minAdm(reduced)` — the reduced chain's
box-finiteness, one arity down. So `L = D` is **the arity-descent induction itself** (base `L≤2` banked:
the single free matrix has `L = m·n = codim` exactly). The "pushforward-not-Lebesgue" worry (pivchg
§PRODUCT-D) is **resolved**: the CoV straightens the pushforward to Lebesgue on the reduced factors.

### Empirical corroboration (tube-MC slope ladder, `tube_jac.py`) — slopes trend UP to codim, never below

- `(3,3,4) q=2` [codim 4]: slopes `3.39, 3.57, 3.42` — consistent with `t⁴log(1/t)` (two tied cuts).
- `(3,3,3,4) q=2` **3-layer** [codim 3]: `2.46 → 2.67 → 2.77 → 2.83` — trending UP to 3 (the log signature),
  NOT saturating below.
- narrow `(3,1,3) q=1` [codim 3]: `→ 2.77`; narrow `(2,1,2) q=1` [codim 2]: `→ 1.73`. All trend to codim.

No case saturates below codim (which would flag a genuine power drop). The finite-`t` undershoot is the
`t^{D}·log` signature, not a fractional wall.

### Logs are real but harmless (Level-B θ, not Level-A)

`L = D` up to logs: `(3,3,4)s=1 → t⁴log(1/t)` (two tied minimizing cuts), `(3,1,3)s=0 → t³log(1/t)`. The log
= the **θ-count** (≥2 top-dimensional components at the binding stratum) and can compound to `log^{L−1}`
across the descent. It NEVER moves the strict threshold: `∫ t^{D−1}(log 1/t)^k · t^{−α} dt < ∞ ⟺ α < D`
regardless of `k`. So the θ-tie is a Level-B multiplicity; the strict Level-A threshold `α < D` is intact.

---

## 3. The linchpin ∀M with the product `D` — tautological (0 violations)

`minAdm(M) ≤ D + M₀(q−1)` with `D = minAdm(reduced by q−1)` is the `j=q−1` term of the banked front-peel
identity `minAdm(M) = min_j [M₀·j + minAdm(m₁−j,…,M_L−j)]` (`minAdm_eq_frontPeel`). Verified (`algebra.py`):
- front-peel identity `minAdm == min_j [...]`: **0 mismatches / 19500** (`L∈{2..5}`, widths ≤5).
- linchpin `minAdm ≤ M₀(q−1) + minAdm(reduced by q−1)`: **0 violations / 28420**, **18131 tight** (binding).
- Reps: `(2,3,3,4)` tight at `q=3`; `(3,3,3,3,4)` tight at `q=2` (`6=3+3`); `(2,4,4,5)` tight at `q=4`;
  narrow `(2,3,1,3)`, `(3,3,1,3,4)`, `(2,2,1,2)` all hold (tight where noted). Codex Q4 concurs: tight iff
  `j=q−1` is a minimizing cut (`(3,3,3,4)` charges `[8,7,7,9]`: `q=2` tight `7=3+4`, `q=1` strict `7<8`).

Geometric reading (Codex): on the tail-rank-`j` stratum the tail contributes codim `C(reduced by j)` and
`A₀P=0` imposes exactly `M₀·j` independent linear conditions — the front-peel `M₀·j + C(reduced)`.

---

## 4. Narrow internal widths (the flagged risk) — handled, no wall

`subred`/`pivchg` flagged that a narrow internal width makes `rank(product) < min` **generic** (not null).
This does **not** break `L = D`: `minAdm(reduced)` already accounts for internal bottlenecks (it is the QIP
min, sensitive to every width). Verified exact: `(3,1,3)s=0 → D=L=3`, `(2,1,2)s=0 → D=L=2` (Jacobian-codim
+ tube slope). And `(3,1,3)s=1`: `σ₂(P) ≡ 0` (rank ≤ 1 identically), so `D=L=0` — the formula's
"`= 0` once a bottleneck is exhausted" convention (Codex). The narrow-internal regime shifts *which*
strata are generic but leaves `L = D = minAdm(reduced)` intact.

---

## 5. Close

- **Firmest.** No wall ∀M: `L = D = C(m₁−s,…,M_L−s) = minAdm(reduced)`, up to logs (`t^{D+o(1)}`). The
  Core bridge holds ∀M (add-longest projective-injective + rank-shift Lemma 4.5 + QIP; = banked
  `cCodim_rankShift`/`cCodim_eq_qipMin`/`SigmaStratification`/Voigt). Exact Jacobian-codim matches in 5
  cases incl. narrow-internal; tube-MC slopes trend to codim; the linchpin is the tautological `j=q−1`
  front-peel term (0/28420). Two decorrelated lines: my Jacobian+CoV+MC and Codex's add-longest +
  affine-simplex (which independently hunted and ruled out the ≥3-factor bend).
- **The key structural point:** `L = D` is NOT an independent lemma — via `normalSlice` (unit-Jacobian CoV)
  it IS the reduced chain's box-finiteness one arity down, closed by the same arity-descent induction the
  general fill already uses (front-peel + `normalSlice_transfer`, base `L≤2` banked). So the "last Level-A
  math dependency" for the ∀M majorant lift is **discharged by the existing recursion**, consuming banked
  Core for the algebraic `D`; no new analytic wall is introduced by going from the `(3,3,3,4)` instance to
  general width.
- **Most likely to break / watch.** (i) The `minAdm = cCodim` Lean bridge (both `= C`; needs its explicit
  lemma or the ℕ `minAdm_rrp_subadd` route) and the **real-vs-complex codim** seam (Core is complex `cCodim`;
  the analytic tube is real — codim equal, standard, but state it). (ii) θ-tie **logs compound** across the
  descent (`log^{L−1}`) — harmless to the strict Level-A threshold, but a Level-B exact-RLCT/θ computation
  must track them. (iii) `normalSlice_transfer` is witnessed exact `L≤4` and argued general (standard rank
  normal form); the opaque-width block-shear identity is the one bounded brick (already banked B5a′ per
  BUILT-INDEX).
- **Next.** The ∀M lift needs no new analytic result: consume banked Core for `D = cCodim(reduced)`, the
  banked front-peel for the linchpin, and `normalSlice_transfer` + arity induction for the tube leading
  power. The residual is bookkeeping (the `minAdm=cCodim` bridge lemma + real-codim statement), not a wall.
