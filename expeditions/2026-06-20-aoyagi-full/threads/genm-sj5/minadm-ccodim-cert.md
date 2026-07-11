# minAdm = cCodim Lean bridge — scoping cert (the last bookkeeping brick)

**Seat:** pen-and-paper (scoping + witness). **Date:** 2026-07-11. **NO Lean.** **Charge (team-lead):**
scope the Lean-buildable `minAdm = cCodim` bridge — is it a clean lemma, via which route; the real-vs-complex
codim seam; consume #127's Core-codim work. Output the recipe (name banked Core pieces) OR the precise gap.

**Exact algebra (mine):** `/tmp/prodD/qip.py` (minAdm=qipMin monotone; perm-invariance; the `T↔e` map).
**Consumed (banked Core):** `cCodim_eq_qipMin` (monotone, `CThetaQIPConverse:833`),
`cCodim_zero_eq_cValue_comp_sort` (perm-invariance, `CThetaArbitrary:43`), `cCodim_rankShift`
(`CTheta:377`); (DLN side) `minAdm` = QIP-inf over `Adm`/`Mval` (`RouteMLayerSplit:51`),
`minAdm_eq_frontPeel` (#117), `minAdmRec_eq_minAdm`. **Decorrelated:** own `local-codex-consult` (xhigh,
conclusion withheld — asked whether the bridge is a clean identity AND whether it is even needed):
`codex/minadm-{prompt,answer}.md`. Codex gave the exact `T↔e` bijection + the ℕ perm-invariance + the
real-vs-complex verdict + confirmed the critical-path scoping. Adopted.

---

## VERDICT (headline): the bridge `minAdm(M) = cCodim(M,0)` is TRUE and banked-ADJACENT (two new ℕ lemmas + two banked Core theorems). It is NOT on the (□)-finiteness critical path — the tube is minAdm-SELF-SUFFICIENT (#127) — so discharging (□) mints the unconditional payoff WITHOUT it. The bridge is required to CALL `minAdm` the paper's geometric `C` (the Aoyagi ↔ Lehalleur–Rimányi unification) and for the cited `rlct ≤ ½·C` upper bound. It sidesteps the real-vs-complex seam on the (□) path.

Verified numerically: `minAdm(M) = qipMin(M)` for **all weakly-increasing `M`** (0 mismatches, `L≤4`,
widths ≤4; the 124 mismatches are all NON-monotone, where L-R's QIP gives junk incl. negatives), and
`minAdm` is **permutation-invariant** (3000/3000). So `minAdm = cCodim(·,0)`, via a clean route, both are
`C`.

---

## 1. Is the bridge on the (□) critical path? NO — minAdm is self-sufficient (Q4)

The (□) discharge is stated and banked entirely in `minAdm` terms: `(□) = RouteMBoxThresholdFinite M`
(`∫ < ⊤ for c' < ½·minAdm M`); the tube side is banked in `minAdm` (`minAdm_eq_frontPeel` #117,
`minAdm_rrp_subadd`, `minAdmRec_eq_minAdm`); and **`minAdm` appears NOWHERE in `Core/`** (grep-confirmed) —
the analytic tube never touches the geometric `cCodim`. My #127 established the tube leading power
`D = minAdm(reduced)` ANALYTICALLY (the arity-descent induction: the reduced chain's own box-finiteness
threshold, via the unit-Jacobian normalSlice CoV), NOT geometrically. So the (□) discharge → the payoff
(`aoyagi_learning_coefficient = aoyagiLambda`, `Skeleton:1685`; the `_gen` reduction is Stage-1-banked,
conditional on `(□)` in minAdm terms) needs **no** `minAdm=cCodim` bridge.

Codex Q4 concurs, verbatim: *"minAdm is self-sufficient for the analytic finiteness leg. The geometric
cCodim bridge is optional analytically, but required to call that integer the paper's C, and useful for
sharpness via the universal codim upper bound."* (Two cautions it flags, both handled: finiteness ≠ full
tube asymptotic — the matching `rlct ≤ ½·codim` is the Cited Watanabe half; and the layer-cake
`∫‖prod‖^{−2c} ⟺ ∫r^{−2c−1}V(r)dr` uses the PRODUCT sublevel volume `V`, NOT a Euclidean distance tube, so
no bi-Lipschitz distance-transfer is needed — `minAdm`-native.)

**So the bridge is the paper's headline unification (`Aoyagi's minAdm = L-R's C`), a valuable connection to
the (C,θ) engine + permutation-invariance, but not a (□) blocker.** The tube-D "consumes cCodim" framing is
better read as "consumes `minAdm(reduced)`" — the two are equal (below), but the analytic route uses the ℕ
`minAdm` directly.

---

## 2. The bridge route (if built) — two new ℕ lemmas + two banked Core theorems

`minAdm(M) = minAdm(M↑) = qipMin(M↑) = cCodim(M↑,0) = cCodim(M,0)` where `M↑` = the weakly-increasing sort.

### (a) `minAdm(M) = qipMin(M)` for weakly-increasing `M` — NEW, via a direct `T↔e` bijection (Q1, PROVEN)

The Aoyagi layer-peel profile `T` (weakly-decreasing, `T_{−1}:=M_0`, `T_{L−1}=0` = the terminal
zero-product) and the L-R QIP variable `e` (zero-based `e_0,…,e_{L−1}`, `Σe_i = M_0`) correspond by
> `e_i = T_{i−1} − T_i` (`0≤i<L`); inverse `T_i = M_0 − Σ_{k≤i}e_k = Σ_{k>i}e_k`.

With `E_i = Σ_{k≤i}e_k = M_0 − T_i`, both objectives collapse to the SAME sum:
`Mval(M,T) = Σ_i e_i(E_i + M_{i+1} − M_0) = G(M,e)` — **pointwise** under the bijection. Hence
`minAdm = qipMin` for weakly-increasing `M`. (Indexing note Codex flagged: the `G = Σ_{j≤i}e_i(e_j + M_{j+1}−M_j)`
form I used is the ZERO-based-`e` convention — consistent with my numerics; the paper's one-based `e` shifts
`M_{j+1}−M_j → M_j−M_{j−1}`.) For NON-monotone `M` the inverse `T` can violate `T_i ≤ M_{i+1}`, so
`qipMin(M) ≤ minAdm(M)` (the formal QIP minimises over a larger set, hence the negatives) — matching the
numerics; the paper applies the QIP only after sorting. **This is the one genuinely-new combinatorial lemma.**

### (b) `minAdm` permutation-invariance — NEW, a pure ℕ argument (Q2, PROVEN; no geometry, no circularity)

The layer-peel is `minAdm(a,m_1,…,m_L) = K_{m_1}⋯K_{m_{L−1}}B_{m_L}(a)`,
`(K_b f)(a) = min_{0≤t≤min(a,b)}[(a−t)(b−t)+f(t)]`, `B_c(a)=ac`. The three-width base
`H(a,b,c) = K_b B_c(a) = min_t[(a−t)(b−t)+ct]` has the closed form (complete-the-square, Codex)
> `H(a,b,c) = xy − ⌊max(0, x+y−z)²/4⌋` (`x≤y≤z` the sorted triple) — **symmetric in all three**.

Hence `K_b K_c = K_c K_b` (`(K_bK_cf)(a) = min_s[f(s)+H(a−s,b−s,c−s)]`, symmetric), `K_bB_c=K_cB_b`, and
the leading two widths swap directly (`(a−t)(b−t)` symmetric). Adjacent transpositions ⟹ full
`minAdm(M)=minAdm(σM)`. **This is the second new ℕ lemma.** Route (a) [prove minAdm perm-inv directly] is
the operator proof — geometry-free, so **no circularity**; route (b) [go through `cCodim` perm-inv] is not
genuinely different (its first step already needs minAdm perm-inv). Use the direct ℕ argument.

### (c) The banked Core closers

`qipMin(M↑) = cCodim(M↑,0)` — banked `cCodim_eq_qipMin` (monotone `M↑`). `cCodim(M↑,0) = cCodim(M,0)` —
banked `cCodim_zero_eq_cValue_comp_sort` (cCodim perm-invariance). So the chain closes:
`minAdm(M) = cCodim(M,0)`.

**New Lean pieces to build:** (i) `minAdm_eq_qipMin` (monotone; the `T↔e` bijection + `Mval=G` pointwise —
a `Finset.inf'` congruence over the bijection); (ii) `minAdm_perm_invariant` (the `K_b`-commute ℕ argument;
the `H` closed form is the crux). Both combinatorial ℕ, no analysis, no geometry. **Banked-consumed:**
`cCodim_eq_qipMin`, `cCodim_zero_eq_cValue_comp_sort`. Optionally `cCodim_rankShift` if the bridge is stated
at general rank `r` (`cCodim(M,r) = cCodim(M−r,0)`, then `= minAdm(M−r)`).

---

## 3. The real-vs-complex codim seam (Q3) — standard for THESE loci; arises only on the geometric route

`cCodim(M,0)` is the COMPLEX codim (char-0, alg-closed, Voigt). The analytic tube is real. **What must be
shown:** `codim_ℝ X_ℝ = cCodim(M,0)` for the real zero-product / rank locus. This holds for the type-A loci
(Codex Q3, PROVEN; = the paper's base-field theorem + real-points remark, `main.tex:605`, `main.tex:860`):
every realizable rank pattern has a 0-1 partial-permutation REAL representative; its real orbit is a smooth
real manifold of real dim = the complex orbit's algebraic dim, Zariski-dense in its orbit closure; the
product-rank locus is a finite union of such closures. So every top-dim complex component has a top-dim
smooth REAL stratum ⟹ `codim_ℝ = cCodim`. The semialgebraic tube theorem then gives
`vol{dist ≤ t} = Θ(t^C)` near a top-dim real stratum (the origin — the locus is conical).

**The general principle is FALSE** (`x²+y²=0`: complex dim 1, real locus `{0}`), but the failure does NOT
occur here (real top-dim strata exist). **Two cautions:** (i) a localization missing all top-dim strata can
raise the local exponent — need a regular compact localization meeting a top-dim stratum (the origin
works); (ii) the Euclidean DISTANCE tube ≠ the product sublevel set `{‖A_L⋯A_1‖≤t}` automatically —
transferring needs local bi-Lipschitz control.

**But this seam arises ONLY on the geometric route** (identifying the tube-D with `cCodim`). The
`minAdm`-native route (#127, §1) uses the PRODUCT sublevel volume `V(r)` directly (layer-cake
`∫‖prod‖^{−2c} ⟺ ∫r^{−2c−1}V(r)dr`), whose exponent is `minAdm(reduced)` by the arity induction — no real
codim, no distance tube, no complexification. **So the (□) discharge sidesteps the real-vs-complex seam
entirely.** The seam is a concern only if one wants the geometric `C`-statement, and there it is standard
(base-field theorem).

---

## 4. Close

- **Firmest.** `minAdm(M) = cCodim(M,0)` is TRUE (verified: `minAdm=qipMin` monotone, 0 mismatches;
  `minAdm` perm-invariant, 3000/3000) and banked-adjacent: two new ℕ lemmas — `minAdm_eq_qipMin`
  (monotone, the `T↔e` bijection `e_i=T_{i−1}−T_i`, `Mval=G` pointwise) and `minAdm_perm_invariant` (the
  `K_b`-commute ℕ argument via the symmetric `H(a,b,c)=xy−⌊max(0,x+y−z)²/4⌋`) — plus banked
  `cCodim_eq_qipMin` + `cCodim_zero_eq_cValue_comp_sort`. Both new pieces are combinatorial ℕ, no analysis.
- **The scoping verdict (the load-bearing point).** The bridge is **NOT on the (□)-finiteness critical
  path** — the tube is `minAdm`-self-sufficient (#127 arity induction + banked #117), and the (□)→payoff
  reduction is Stage-1-banked in `minAdm` terms (`aoyagi_learning_coefficient = aoyagiLambda`). Discharging
  (□) mints the unconditional payoff without it. The bridge is required to (a) CALL `minAdm` the paper's
  geometric `C` (the Aoyagi↔L-R unification, the connection to the (C,θ) engine / permutation-invariance of
  `C`), and (b) obtain the Cited `rlct ≤ ½·C` upper-bound half. Recommend building it AS a clean
  standalone `Core↔DLN` bridge (the 2 ℕ lemmas), decoupled from the (□) build.
- **Most likely to break / watch.** (i) The QIP indexing (zero- vs one-based `e`; state `minAdm_eq_qipMin`
  against the EXACT `Gqip` def `CThetaQIP:56` — my numerics used the zero-based form matching it). (ii) The
  real-vs-complex seam is standard for these loci but is a genuine geometry↔analysis statement (base-field
  theorem) IF the geometric route is taken; the `minAdm`-native route avoids it. (iii) The Euclidean-tube ≠
  product-sublevel caution (only if one routes through the distance tube — not needed).
- **Next.** Build the 2 ℕ lemmas (`minAdm_eq_qipMin` monotone via `T↔e`; `minAdm_perm_invariant` via
  `K_b`-commute) as the `minAdm ↔ cCodim` bridge, consuming `cCodim_eq_qipMin` + `cCodim_zero_eq_cValue_comp_sort`.
  It is off the (□) critical path — schedule it for the geometric `C`-statement / the `rlct ≤ ½·C` half, not
  as a (□) blocker. The (□) discharge (g(Q): cell_1 + corank-q #131 + cover/sum) mints the unconditional
  `aoyagi_learning_coefficient` in `minAdm` terms directly.
