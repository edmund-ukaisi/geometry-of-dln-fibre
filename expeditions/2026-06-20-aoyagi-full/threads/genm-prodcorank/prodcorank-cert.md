# prodcorank — the native-vs-cite gate of the (□) endgame: is the DLN product-corank resolution natively buildable, or Aoyagi's wall?

**Seat:** pen-and-paper, aoyagi-full `genm-prodcorank` (OBSTRUCTION+WITNESS). **Date:** 2026-07-17.
**NO Lean edits, NO build.** Exact algebra (sympy Gröbner + exact-ℕ minAdm recursion + generic-Jacobian-rank
codim) + Aoyagi primary-source cross-check + decorrelated `local-codex-consult` (gpt-5.x xhigh, my verdict
WITHHELD): `codex/princ-{prompt,answer}.md`, `princ-run.log`. **Decorrelated from decstep + satred** (who
share the 5-round framing): I re-derived the product-corank codim, the balanced-component geometry, the
discriminator, and the principalization from scratch. My verdict CONVERGES with decstep round-5's flip and
SHARPENS it to a firm call. Scripts (reproducible): `codex/prodcorank2.py`, `codex/discriminator.py`,
`codex/verify_codex.py`.

The single truth-value asked: **is a NATIVE resolution of the DLN product-corank ideal (the joint incidence
Γ·S of the middle product) able to reach the RLCT c* non-circularly (option A, native-buildable-deep), OR is
it a genuine wall = the core of Aoyagi's product-corank resolution, whose native re-derivation is
research-grade (option B, cite)?**

---

## ★ VERDICT (firm): WALL → CITE (B).

**A native resolution reaching c* at the c≥2 (min-corank ≥ 2) product-corank atom is NOT factor-only
detail-at-scale. It is (the DLN specialisation of) Aoyagi's joint product-corank / Vandermonde-matrix-type
log-resolution theorem. Recommendation: CITE the product-corank finiteness at the min-corank-≥2 atom;
(□) is native ABOVE it.** Four independent lines converge:

1. **Principalization (Proved, exact).** Resolving the FIRST factor's rank strata alone does NOT
   principalize the product ideal — a smooth codim-`C_k` JOINT center (with an *alignment* coordinate)
   survives. Smallest failure `n=2, k=2`. The single-factor cover misses the RLCT-binding component.
2. **Non-submersiveness = the exact codim gap (Proved, exact).** The multiplication differential
   `dμ(dP,dZ) = dP·Z + P·dZ` has `coker(dμ) ≅ Hom(ker Z, coker P)` of dimension `a·c = ⌊k²/4⌋ = k² − C_k`
   on the balanced binding component. The naive first-factor codim `k²` falls to the true `C_k` by EXACTLY
   the non-submersiveness of matrix multiplication. No transverse (submersive) pullback exists there.
3. **Both split accountings are fictions on the balanced locus (Proved arithmetic + Argued).** The naive
   `m²` reaches c* but assumes the FALSE transversality; the product `C_m` (the true codim) UNDERSHOOTS c*
   but assumes the joint center SPLITS from an independent reduced chain — also false. Neither per-stratum
   codim paired with an independent reduced chain is a valid resolution ratio; only a genuine JOINT
   resolution gives the true discrepancies (which do land on c* — that is Aoyagi's content).
4. **Aoyagi primary source (Cited cross-check).** Aoyagi's own resolution of the product/Vandermonde-type
   `‖A·B‖²` is a *recursive blowup with branch-selection* (Entropy 2013, App. C, Step 1 (i)–(v), inductive
   over `s`). His general Theorem 5 gives only UPPER bounds on the RLCT; EXACT values are known only for
   `N=1` or small `H`, with the general exact value stated as *future research*. The direction the (□)
   endgame needs (box-finiteness ⟺ `rlct ≥ c*`, a LOWER bound on the RLCT) is Aoyagi's HARD direction (the
   exact resolution), not Watanabe's universal `rlct ≤ ½codim`. Native re-derivation = re-proving this.

The one honest INFERENCE (preserved from Codex, not promoted): a native proof "remains possible" — a single
uniform resolution indexed by ranks AND alignment/intersection data COULD cover all sizes. But that IS the
joint product-corank resolution theorem; it is not the bounded, factor-only, self-similar bookkeeping that
decstep rounds 2–4 hoped for. So (A) is not *impossible*; it is *research-grade native*, which for the
Proved-vs-Cited call is a CITE.

---

## 1. The design space and the load-bearing invariant

Object: the DLN square chain `(n,n,n,n)` (three free `n×n` factors), loss `f = ‖P·Z·W‖²` near 0; cited
`rlct(f) = c* = ½·minAdm(n,n,n,n)` (Aoyagi). The (□) endgame reduces, per outer peel, to a residual
`‖Γ·Q_b·(I−P_pivot)‖²` where `Γ` is a FREE `a×b` corank block but `Q_b` is a DEEPER matrix PRODUCT (nested
DLN factors), not a free matrix. The load-bearing invariant is the **codimension of the product-corank
(joint-incidence) locus of the middle product** and whether an explicit resolution reaches c*
NON-circularly (forbidden: "`rlct = ½codim` (Aoyagi) ⟹ no smaller-ratio divisor" — that is the very thing
to prove).

## 2. Product-corank codim: independently re-derived C_k = k² − ⌊k²/4⌋ (Proved, exact, two routes)

For the middle product `Y = P·Z` (two free `n×n` matrices), the corank-`k` locus `V_k = {rank(PZ) ≤ n−k}`
has MINIMAL codim `C_k = k² − ⌊k²/4⌋` (`C_1=1, C_2=3, C_3=7, C_4=12, C_5=19, …`), NOT the naive `k²`.

- **Route 1 (Schubert-component minimisation).** `rank(PZ) < n` FORCES a rank drop in a factor (invertible×
  invertible is invertible). The minimal component is not "one factor drops to corank `k`" (codim `k²`) but
  the **BALANCED** one: `rank(P)` drops by `a`, `rank(Z)` by `c`, AND `im(Z) ∩ ker(P)` has forced dim `e`
  (alignment). codim `= a² + c² + e(c−a+e)`, minimised at `a≈c≈e≈k/2`, giving `C_k`. Verified n=2..8, all k.
- **Route 2 (generic Jacobian rank).** At a smooth point of the balanced component (`n=4,k=2`: rank P=3,
  rank Z=3, `im Z ∩ ker P` = 1-dim), the normal-space map `(dP,dZ) ↦ U_coker^T(dP·Z+P·dZ)V_ker` has rank
  `3 = C_2`. Confirmed.

**Idea/mechanism (the fingerprint of the wall).** The codim deficit from naive `k²` is EXACTLY the
non-submersiveness of the multiplication map: `k² − C_k = ⌊k²/4⌋ = a·c = dim coker(dμ)` on the balanced
component (verified all k, and numerically `coker dim = 4` at `n=4,k=4`). The product-corank variety is
"bigger than transverse" by precisely the cokernel of `dμ` — this is why no submersive first-factor pullback
resolves it.

## 3. The discriminator: naive m² PASSES, product C_m UNDERSHOOTS (Proved, exact-ℕ, n=3..8)

Outer peel of `(n,n,n,n)`, stratified by deeper corank `m`, each stratum paired with reduced chain
`(n−m,n,n)`:

- **naive `m²`:** `T_m = m²/2 + ½·minAdm(n−m,n,n) ≥ c*` for every `m`; `min_m T_m = c*` (binding strata
  MARGINAL). Reaches c*.
- **product `C_m`:** `T_m = C_m/2 + ½·minAdm(n−m,n,n)` UNDERSHOOTS c* for all `n≥4` (e.g. `n=4,m=2`:
  `3/2 + 7/2 = 5 < 11/2 = c*`; the undershoot widens and spreads across strata as `n` grows — n=8 has 5
  undershooting strata).

The two give OPPOSITE verdicts. **This is not a numerical accident to be patched: it is the signature that
the SPLIT accounting (per-stratum codim ⊕ independent reduced chain) is invalid on the joint locus.** The
naive `m²` lands on c* because `m²` is the SUBMERSIVE (free-block) discrepancy — correct only where the
pullback is transverse, which is exactly where it is NOT (§2). The product `C_m` uses the true codim but
still assumes the joint center detaches from the reduced chain. Both are fictions on the balanced component;
the real resolution's discrepancies require joint computation (Codex Q4, independently).

## 4. Principalization: the single-factor cover leaves a smooth JOINT center (Proved, exact — Gröbner)

The decisive geometric fact, verified independently (not pasted): near a balanced point of the `n=2,k=2`
product-corank locus, with `W` invertible, coordinate changes bring `P ~ diag(1,x)`,
`Z ~ [[y+bc, b],[c, 1]]`, so

    I(P·Z·W) = I(P·Z) = (x, y, b)   [sympy Gröbner: each product entry ∈ (x,y,b) and conversely].

Here `x=0` = P's rank-drop divisor, `y=0` = Z's rank-drop divisor, `b` = the **alignment** coordinate.
`(x,y,b)` is a SMOOTH codim-3 (`=C_2`) complete intersection. Blowing up the individual factor-rank loci
(the Cartier divisors `x=0`, `y=0`) is a local isomorphism / does nothing to make `(x,y,b)` principal — the
alignment coordinate `b` is genuinely new data. **A joint center survives after any finite sequence of
single-factor blow-ups.** (`n=1` is the monomial `pzw`, already principal, so `n=2,k=2` is the minimal
failure.)

- **Self-similar but NOT factor-closed (Proved for factor-only; Argued for uniformity).** The residual is
  NOT a strictly-smaller instance of the SAME factor-rank recursion (the alignment coord is new). A uniform
  resolution would need charts indexed by ranks AND alignment/intersection data — rectangular
  block-composition ideals and joint centers. That is a new construction, not iterated single-factor
  bookkeeping.

## 5. Why the finiteness direction is the hard one (Argued — the domination asymmetry)

Box-finiteness `∫_box f^{−c'} < ∞` for `c' < c*` is `rlct(f) ≥ c*` — a LOWER bound on the RLCT. By Aoyagi's
Lemma 1(1) (`Σg² ≤ Σf² ⟹ λ(g) ≤ λ(f)`), dropping squares LOWER-bounds `λ(f)`; to certify `λ(f) ≥ c*` one
needs a sub-loss `g` with `λ(g) ≥ c*` KNOWN — but any such `g` capturing the binding singularity IS the
product-corank loss itself (circular). Native "dominate-and-bound" tools (Aoyagi's Thm 2/Thm 5, via Lemma
1) yield UPPER bounds on `λ` — the WRONG direction for the endgame. The finiteness/lower-bound direction
genuinely needs the explicit resolution with all divisor ratios `≥ c*`, i.e. the joint product-corank
resolution. This matches the banked lesson (`rlct-runway-target`: "singular-locus lower bound; smooth locus
only gives an upper bound").

## 6. Aoyagi primary-source cross-check (Cited)

`paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/entropy-15-03714.pdf`
(Aoyagi, *Entropy* 2013):
- The product/Vandermonde-type singularity is `I = ⟨elements of A·B⟩` (Def. 3), `B` built from products of
  the `b`-variables — exactly the nested-product structure of the DLN middle product.
- The resolution (App. C, Step 1, claims (i)–(v)) is a **recursive blowup with branch-selection** `k(s) ∈
  {1,…,N}`, inductive over `s = 1..H`, with a nontrivial Jacobian exponent `d_i = (N−1)Q Σ(count−1)` and
  coordinate changes via Theorem 2 (deepest singular point) + Theorem 3 (add variables).
- Theorem 5 gives only `λ ≤ min{bound1,bound2,bound3}` (UPPER bounds). EXACT values: only `N=1` [24] or
  small `H` [14]. General exact value = "our future research aim" (Conclusion).
- Remark 1 (real-field example: `λ` differs from the complex case) shows the REAL RLCT here is genuinely
  subtler than the complex log-canonical threshold — native re-derivation cannot borrow the complex answer.

**So even Aoyagi's general method yields bounds, not the exact product-corank RLCT.** Establishing that the
DLN recursion's resolution has all discrepancies giving `≥ c*` is exactly the exact-value theorem — the
research-grade content the destination already cites (`RlctInterface.cited_aoyagi_dln`).

## 7. The minimal cited interface + (□) is native ABOVE it (the deliverable)

**Cited (minimal interface).** The product-corank finiteness at the **min-corank-≥2 atom**: for `c' <` the
shifted threshold, `∫_box ‖Γ·Q_b·(I−P_pivot)‖^{−2c'} < ∞` where `min(a,b) ≥ 2` and `Q_b` is the deeper
product — equivalently, the joint-composition-ideal log-resolution `min_E A_E/(2N_E) = ½·minAdm` for the
rectangular dimension vectors of the recursion. This is decstep §4 option (b)'s `innerCorankDescent_lt_top at
min(a,b)≥2`, now firmly adjudicated as the cited boundary. **It is a modest extension of the existing cite,
not a new dependency class:** it is logically WEAKER than (a corollary of) the already-cited
`rlct = ½·codim` equality. Two honest packagings:
- **B1 (no new axiom):** keep `cited_aoyagi_dln`; the min-corank-≥2 atom is discharged by the cited equality,
  not natively re-derived.
- **B2 (sharper, replaceable):** a narrower `cited_aoyagi_product_corank` interface (the joint-resolution
  finiteness above), isolating exactly the research step one level below `rlct = ½codim`.

**Native ABOVE it (per decstep/satred structure; Proved-by-prior-threads where marked):**
- the outer `(S,J)` / decorated peel recursion (`RouteMSJDecoratedPeelStep`) — native reduction to reduced
  chains;
- the Schur-weld (`chartInner_schurWeld_eq`), C-integration (`gammaAtom_aniso_shifted_eq`), pivot-Gram
  disposal (`qbox`/Wishart) — native banked bricks (carry the PIVOT Gram, never the corank Gram — the "atom
  trap");
- the exact-ℕ arithmetic (`minAdm` recursion, `peelCharge`, `A_r`/stratum budget, `min = minAdm`) — airtight;
- the min-corank-≤1 cases (scalar/row corank blocks, no joint incidence — decstep §1, native at n=3) and the
  two non-square wings (tall `b=0` full-column-rank Wishart recursion; wide `a=0` full-row-rank) — native.

Only the min-corank-≥2 product-corank joint-principalization (the balanced-component resolution, §2–§4) is
cited.

## 8. Levels kept apart

- **Quiver/orbit** — untouched; `minAdm`/`redChain`/`peelCharge` consumed as exact-ℕ.
- **Codim (C,θ)** — `C_k = k²−⌊k²/4⌋`, the balanced-component codim, the `m²`-vs-`C_m` discriminator, the
  `a·c = ⌊k²/4⌋` coker identity are exact facts of the varieties (sympy/Gröbner/Jacobian-rank verified).
- **RLCT cap** — the box-finiteness `rlct ≥ c*` at the atom is the CITED step (§5–§7); NOT re-derived here.
  The Aoyagi equality is invoked only as the cited interface, never smuggled into a native argument (the
  circularity guard is the whole point).

## Close

- **Firmest result.** WALL → CITE (B). The DLN product-corank resolution reaching c* at min-corank ≥ 2 is
  not native detail-at-scale: iterated single-factor blow-ups do not principalize the joint ideal (a smooth
  codim-`C_k` alignment center survives, Gröbner-verified at `n=2,k=2`); the multiplication map is
  non-submersive there with `coker dim = a·c = ⌊k²/4⌋ = k²−C_k` (exact); both split accountings (`m²`,
  `C_m`) are fictions on the balanced locus; and the required joint resolution is (the DLN specialisation of)
  Aoyagi's recursive-blowup theorem, whose exact form is research-grade (Aoyagi's own general method gives
  only bounds). The finiteness direction the endgame needs is Aoyagi's hard direction, not Watanabe's easy
  bound. Four decorrelated lines converge (my exact algebra, the Aoyagi source, the domination asymmetry,
  Codex xhigh `WALL-REQUIRES-JOINT-RESOLUTION`).
- **Most likely to break this call.** (i) The one INFERENCE — that a uniform joint resolution "could" exist
  (Codex Q3); if some special DLN structure collapsed the branch-selection into pure bookkeeping, (A) could
  become buildable. But the alignment coordinate is genuinely new data at each depth and the real-field
  subtlety (Aoyagi Remark 1) blocks borrowing the complex answer — so this is unlikely, and even then it is
  a research build, not detail-at-scale. (ii) If a formaliser ships a peel with single-factor
  radial/pivot-Gram blow-ups claiming to close min-corank ≥ 2, it will NOT (the joint center `(x,y,b)`
  survives — do not ship it). (iii) I have not hard-proved the NON-existence of a native resolution (that is
  not the claim); I have proved single-factor covers fail and the joint step = Aoyagi's theorem.
- **Next.** (a) If (B) accepted: pin the minimal `cited_aoyagi_product_corank` interface (B2) at the exact
  rectangular widths of the recursion, or fold into `cited_aoyagi_dln` (B1); then commission the native
  (□) build ABOVE it (§7). (b) If a native attempt is still wanted, the ONE research obligation is the
  uniform joint-composition-ideal log-resolution `min_E A_E/(2N_E) = ½·minAdm` with SNC support and no
  smaller-ratio divisor — a multi-tide monument, not a peel; scope it as its own expedition, not an endgame
  atom.

Files (absolute):
- `…/threads/genm-prodcorank/prodcorank-cert.md` (this cert)
- `…/threads/genm-prodcorank/codex/princ-{prompt,answer}.md`, `princ-run.log` (decorrelated,
  `WALL-REQUIRES-JOINT-RESOLUTION`)
- `…/threads/genm-prodcorank/codex/{prodcorank2,discriminator,verify_codex}.py` (exact, reproducible):
  product-corank codim `C_k` two routes; the `m²`-vs-`C_m` discriminator n=3..8; the `n=2` residual ideal
  `I(PZ)=(x,y,b)` (sympy Gröbner); the `a·c = ⌊k²/4⌋ = k²−C_k` coker identity + numerical `coker dim` at
  `n=4,k=4`.
- Aoyagi source: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/entropy-15-03714.pdf`
  (recursive blowup App. C; bounds-only Theorem 5; exact values only N=1/small-H; real-field Remark 1).
