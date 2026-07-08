# genm-r1subgenwall — CERTIFICATE: the R1-UPPER sub-generic wall is CONFIRMED (dissolution fails)

**Seat:** pen-and-paper, dissolve-or-confirm (WITNESS a dissolution; if none, CONFIRM the scoped no-go).
**Wall:** R1-UPPER, `sjJointResolution` (`RouteMSJResolution.lean:797/803`, the SOLE R1-UPPER sorry) at
the sub-generic (product-rank-deficient) strata, `L ≥ 3`. **Branch:** `genm-inj-injon` worktree
(read-only on Lean). **Method:** exact integer arithmetic over the *proven* `minAdm` layer-peel; exact
matrix-variate RLCT (singular-value Jacobian + symbolic transverse Hessian, sympy); ground-truth
`#print axioms`; decorrelated `local-codex-consult` (xhigh, neutral). No Lean edits.

**Scripts (reproduce):** `subgen_probe.py` (layer-peel / front-peel charge on (3,3,3,4) + battery,
`minAdm` via the proven recursion), `gram_threshold.py` (Gram-coupling threshold + the binding-cut
budget arithmetic), the sympy transverse-Hessian one-liner (§C). Codex artefacts in `codex/`.

---

## HEADLINE (controller-facing)

**Verdict: WALL CONFIRMED — escalate. `SchurRecStep` is CLOSED (not the gap).** The dissolution
attempt FAILS on all three candidate angles, each for a concrete exact-algebra reason, and — decisively —
the sub-generic obstruction is pinned to an **exact borderline (zero-budget) integrability threshold**:
at the binding cut of the smallest genuine case `(3,3,3,4)`, the front-boundary peel's Gram coupling
`det(Q_b Q_bᵀ)^{−a/2}` sits **exactly at its own integrability threshold** (`a/2 = 1 = (M₂−b+1)/2`)
while the post-peel residual exponent **exactly saturates** the reduced-chain threshold (`3/2 = 3/2`).
Both saturate **simultaneously** — zero slack. This is the precise opposite of the D1 `dgeflat`
dissolution (there the Gauss–Newton residual had core degree `≥ 3`, i.e. strict slack; here the
transverse degree is exactly `2` = Morse = zero slack, so the dgeflat-style structural argument
provably does not transfer). Closing the step therefore requires resolving the determinantal ideal of
the matrix **product** `A₁′·A₂···A_{N−1}` jointly with the reduced-chain integrand — the paper's
`addlongest` normal-slice iso (Thm ~line 688), equivalently UPDATE-690's "joint principalisation of
`det(Q_b Q_bᵀ)` for the matrix product at corank ≥ 2", which Mathlib lacks. Operator decision (A build /
B cite) stands.

---

## PART 1 — `SchurRecStep` is CLOSED (r1layerpeel's #70 correction confirmed with ground truth)

`#print axioms schurRecStep_p` (run in-worktree against the built olean):

    'DLNFibre.DLN.RLCT.schurRecStep_p' depends on axioms: [propext, Classical.choice, Quot.sound]

clean-three, sorry-free. `schurRecStep_p (p) : SchurRecStep p (schurLambdaP p)` (`RouteMSchurRecStepP.lean:50`)
is proved by two closed branches — cap-B `schurCoreP_directMorse` (`r ≥ 3`, no recursion) and cap-A
`schurCoreP_capA` (the carve, `RouteMSchurCapACarveP.lean`, 0 sorries) — riding `core_schurGen_lt_top`
(WellFounded on corank `r`), so it holds **∀p AND ∀corank r**. Both dependency files have 0 `sorry`.
The `schurRecStep4_stub` (`RouteMSchurGeneral.lean:143`) is a DEAD vestige: its ilean `usages` list is
empty — consumed by nobody. **r1transfer's #70 read ("corank-3 in flight, higher open") was stale**; it
read the stub and missed `RouteMSchurRecStepP`. The corank induction did NOT wall. `SchurRecStep` is NOT
the R1-UPPER gap. **Confirmed: SchurRecStep closed: YES.**

---

## PART 2 — the sub-generic wall: DISSOLUTION FAILS (the load-bearing adjudication)

### 2.0 The exact object

`sjJointResolution` needs (`RouteMSJResolution.lean:797`): for `c' < ½·minAdm M`, `1 ≤ t ≤ min(M₀,M₁)`,
the per-`(t,ρ,κ)`-chart integral is finite:

    gammaPeelIntegral M t ρ κ c' = ∫_{A′∈box(tailChain M)} ∫_{A₀∈box ∩ pivotChart ρ κ}
                                     frobSq(A₀ · prod(tailChain M) A′)^{−c'}  < ⊤.

On the chart the `t×t` pivot of `A₀` is a unit; the banked EXACT `frobSq_schur_block_split` + the MP
shear `D ↦ Γ` rewrite the integrand as `(‖A·Q̃_p‖² + ‖C·Q̃_p + Γ·Q_b‖²)^{−c'}`, `Γ` free `(M₀−t)×(M₁−t)`,
`Q_b` = the `(M₁−t)` non-pivot rows of `P = A₁·(A₂···A_{N−1})` — a matrix **product**, hence
product-rank-deficient on a proper subvariety of the deeper matrices. Integrating out `Γ` (Gram CoV
`Γ ↦ Γ·Q_b`) produces the Jacobian prefactor `det(Q_b Q_bᵀ)^{−(M₀−t)/2}` and shifts the exponent by
`(M₀−t)·s′/2`, `s′ = rank Q_b`. The OUTER integral over the deeper matrices of that prefactor times the
reduced-chain residual is the standing L≥3 wall (`RouteMSJResolution.lean:795`).

### 2.1 The three dissolution angles all FAIL

**(i) Concrete pivot-chart cover of the product.** Covering `{rank Q_b = q}` by pivot charts of the
product and Schur-decomposing the product itself localizes the `det(Q_b Q_bᵀ)^{−a/2}` blow-up to chart
interiors, but the divergence lives at the chart **boundary** (the deeper rank-drop locus). Each chart
integral is still the same borderline determinantal integral (§2.2). Covering relocates, does not
dissolve. — FAILS.

**(ii) Gauss–Newton / self-similar-frobSq (the dgeflat-style angle).** The coupling factor is
`det(Q_b Q_bᵀ)^{−a/2}` — an **anisotropic determinantal** integrand that vanishes on the entire
rank-drop locus. The IH covers only `frobSq(prod)^{−c'}` (isotropic). `det⁺` is not `frobSq`, so the
shifted chain does **not** arise "for free" from the concrete algebra — it is a genuinely different
(determinantal) integrand outside the IH's reach. And the transverse vanishing order is exactly `2`
(Morse; §2.3), so there is no degree-`≥3` slack for a structural split to bite on. This is the exact
**opposite** of the D1 `dgeflat` dissolution (`K = ‖resid‖²`, `resid = 0` at optimum ⟹ core degree `≥ 3`
⟹ strict slack ⟹ Morse split had nothing to bite on). — FAILS (and the failure is structural, not
incidental).

**(iii) Domination (higher-codim ⟹ implied).** The sub-generic strata are **binding**, not dominated:
r1rankcharge's tightness (closure `minAdmRank = minAdm` breaks if the charge is shrunk by 1) already
shows zero combinatorial slack, and the exact budget arithmetic (§2.2) shows the analytic budget
saturates with **zero margin**. The binding top component of `minAdm` is frequently realized at a
sub-generic tail rank (r1substratum: `(4,4,2)`@q=1, `(5,4,3,2)`@q=0). Higher-codim strata blow the
integrand up at exactly the rate that cancels the codim gain — no domination margin. — FAILS.

### 2.2 The decisive exact computation — zero budget at the binding cut of `(3,3,3,4)`

`minAdm(3,3,3,4) = 7` (proven layer-peel recursion). Binding layer-peel cuts `t ∈ {1,2}` (both total 7).
Take `t = 1`: `a = M₀−t = 2`, `b = M₁−t = 2`; the generic tail-product rank feeding `Q_b` is
`min(b, rank A₂) = min(2,3) = 2 = b` (full on full measure). `Q_b = W·A₂`, `W` free `2×3` (two rows of
`A₁`), `A₂` `3×4`.

| quantity | value | meaning |
|---|---|---|
| `½·minAdm(3,3,3,4)` | `7/2` | the RLCT bound `c'` must clear |
| `Γ`-block Morse shift (generic, full-rank `Q_b`) | `a·b/2 = 2` | exponent removed peeling `Γ` |
| residual exponent as `c'→7/2⁻` | `c'−ab/2 → 3/2` | fed to the reduced chain |
| `½·minAdm(redChain 1 M) = ½·minAdm(1,3,4)` | `3/2` | reduced-chain threshold |
| Gram coupling exponent | `s = a/2 = 1` | power of `det(Q_b Q_bᵀ)` in the Jacobian |
| its own `W`-integrability threshold `(M₂−b+1)/2` | `1` | see §2.3 |

**Two simultaneous saturations, zero slack:**
- residual exponent `3/2` **=** reduced-chain threshold `3/2` (front-boundary peel exactly hits the
  reduced budget — no room left);
- coupling exponent `a/2 = 1` **=** its own integrability threshold `1` (the `det(Q_b Q_bᵀ)^{−1}`
  factor is exactly borderline — no room left).

So at `c' → 7/2⁻` there is **zero budget** for the `det(Q_b Q_bᵀ)^{−a/2}` coupling AND that coupling is
itself at its threshold. The two borderline factors share the deeper variables and **cannot be bounded
independently** (Fubini-out `W` first ⟹ a borderline/log divergence). They must be principalised
**jointly** on a common resolution of the product's rank-drop locus — exactly the `addlongest`
normal-slice iso (= the shifted chain `(M₁−q,…,M_N−q)`, which is provably **not** any `redChain t M`:
its deeper widths are shifted `(2,3)`, whereas `redChain t M = (t,3,4)` keeps `M₂,M₃` unshifted). This
matches UPDATE-690's independently-derived "genuine-new brick" and r1upper-derisk §3's Gap R1U-∀L.

### 2.3 The Gram-coupling threshold (exact, two independent derivations — not MC)

For a FREE real `p×n` matrix `W` (`p ≤ n`), over a bounded box, `∫ det(W Wᵀ)^{−s} dW < ∞ ⟺ s < (n−p+1)/2`.
Derivation 1 (SVD Jacobian): one singular value `σ→0` on the codim-`(n−p+1)` locus `{rank = p−1}`,
measure `~ σ^{n−p} dσ`, integrand `~ σ^{−2s}` ⟹ converge iff `n−p−2s > −1`. Derivation 2 (symbolic,
`2×3`, exact): `det(W Wᵀ) = Σ minorᵢ²`; near a rank-1 base (`row₁=(1,0,0)`, `row₂=0`), perturbing `row₂`
by `ε(u,v,x)` gives `det = ε²(v²+x²)` — an isotropic quadratic in exactly the `2 = n−p+1` transverse
directions ⟹ `∫(v²+x²)^{−s}` over the 2-ball converges iff `2s < 2`, i.e. `s < 1`. For the case at hand
`p=2, n=3`: threshold `1`, coupling `a/2 = 1` — borderline. (Monte-Carlo over the box is NON-discriminating
here — the divergence is weak/log and the box does not concentrate at the locus; `gram_threshold.py`
records this. The exact algebra is authoritative.)

### 2.4 Why no peel order / route escapes

Any boundary peel of an `L ≥ 3` chain leaves a deeper matrix **product** (≥ 2 factors) whose rank drops
on a subvariety — the same coupling arises. The front-peel and the layer-peel's entangled `(‡)` recursion
produce the identical shifted chains (`(M₁..M_N)−q` vs `(M₂..M_N)−r`); the Fubini-`A₀`-first (FrontPeelStep)
route hits the identical anisotropic Gram (r1transfer). The pure/isotropic brick
(`matBox_corank_dominates_absZ_lt_top`) requires the block to appear as `frobSq Δ` (isotropic); matching
the faithful `Γ·Q_b` block to it requires the Gram CoV, which reintroduces `det(Q_b Q_bᵀ)^{−a/2}` even on
the full-measure generic stratum (there is no positive isotropic lower bound `‖CQ̃_p+ΓQ_b‖² ≥ ε‖Γ‖²` when
`Q_b` degenerates). So the det coupling — integrated over the deeper matrices near the product-rank-drop
locus — is unavoidable, and it is borderline at the binding cut. The obstruction is in the **generic-stratum
outer integral**, not confined to a measure-zero set.

### 2.5 Decorrelated Codex (xhigh, neutral prompt — conclusion withheld) — CORROBORATES

Codex was given the objects + the three candidate angles + the micro-example, with **no** steer toward
wall or dissolution. It independently reached the SAME verdict and — decisively — the SAME exact
computation: near `W = [[1,0,0],[u,x,y]]`, `det(W Wᵀ) = x²+y²`, threshold `α < 1`, and the coupling
`(M₀−t)/2 = 1` is "**exactly critical** … diverges logarithmically. … The budget `c' < 7/2` does not by
itself make this prefactor integrable." It rejected (i) ("repairable only by proving the normal-slice
content in coordinates"), (ii) ("false — the IH controls product-**zero** loci, not inverse Gram
determinants near nonzero rank-deficient products"), (iii) ("false — codim 2 vs vanishing order 2 ⟹
threshold 1 ⟹ no spare domination margin"). It also reconstructed the shifted chain concretely as the
Schur complement of the rank-one **product** chart (`W♯ A♯`, widths `(M₁−t−q, M₂−q, …, M_N−q)`), with
chart threshold `½·minAdm(1,2,3) = 1` — an independent derivation that the normal-slice content **is**
the shifted chain. Its epistemic caveat matches this cert's exactly: *"I would not claim no possible
proof exists outside this framework, but for the specific tools listed the missing ingredient is exactly
a product-rank normal-slice analysis, whether stated abstractly or encoded by explicit Schur pivot
charts."* — i.e. a "concrete" route IS a concrete encoding of `addlongest` (operator-option A), not an
avoidance. Artefact: `codex/subgen-answer.md`. I did not paste its code; I ran my own (§2.2–2.4) and its
threshold matches mine to the exact rational.

---

## PART 3 — the precise gap (for the operator escalation)

**Gap (the load-bearing analytic input `sjJointResolution` needs at L≥3):** a measure-preserving /
bounded-Jacobian reparametrization of the product-rank-deficiency locus
`{rank(A₁′·A₂···A_{N−1}) ≤ q}` that reduces

    ∫ det(Q_b Q_bᵀ)^{−(M₀−t)/2} · [reduced-chain integrand]^{−(c'−ab/2)} d(deeper matrices)

to a shifted-chain box integral `box(M₁−q, M₂−q, …, M_N−q)` covered by the IH — i.e. principalising the
determinantal ideal of the matrix product jointly with the reduced-chain integrand so the two borderline
factors become monomials with exponents summing to exactly the `minAdm` budget. This is the paper's
`addlongest` normal-slice iso (Thm ~line 688) = the "L-layer joint resolution" (Gap R1U-∀L) = UPDATE-690's
"joint principalisation of `det(Q_b Q_bᵀ)` for the product at corank ≥ 2". **Mathlib lacks it; the repo
has only the algebraic front-peel identity (`RouteMFrontPeelCharge.lean`), no analytic peel bound.**

**Convergence (five decorrelated lines, now including this exact-borderline probe):** r1transfer
(front-peel anisotropic Gram), r1substratum ("most likely to break" = the normal-slice iso), r1layerpeel
(stratum-blind undercounts, stratum-aware needs the shifted chain), the earlier sjcarrier9/UPDATE-690
recalibration (independent "genuine-new brick"), and this thread (exact zero-budget threshold). The
combinatorics are settled; the analytic obstruction is genuine.

**Operator decision unchanged:** (A) BUILD `addlongest` from scratch (a genuine new analytic/AG module —
the paper proves it, so it is *buildable*, but heavy and Mathlib-missing) OR (B) CITE `addlongest` for the
sub-generic upper bound (one more citation, parallel to the already-Cited Aoyagi `rlct = ½·codim`). The
L=2 headline is unaffected (no sub-generic strata at L=2).

---

## Firmest result / most likely to break it / next step

- **Firmest:** WALL CONFIRMED. `SchurRecStep` is clean-three sorry-free ∀p∀corank (ground-truth
  `#print axioms`). The sub-generic obstruction is an **exact borderline (zero-budget)** determinantal
  integral at the binding cut of `(3,3,3,4)`, verified by exact matrix-variate RLCT (SVD Jacobian +
  symbolic transverse Hessian). All three dissolution angles fail concretely; the dgeflat structural
  dissolution provably does not transfer (transverse degree exactly 2 = zero slack, vs dgeflat's ≥3).
- **Most likely to break it:** a *cleverer joint* change of variables (not Fubini-separating `Γ` from
  the deeper matrices) that realizes the budget concretely. But such a CoV, if it exists, **is** the
  joint resolution — a concrete realization of `addlongest`, not an avoidance of it. So even a "concrete
  dissolution" collapses to operator-option (A) "build `addlongest`", not to "no escalation". The
  distinction the escalation turns on (build vs cite) is unaffected.
- **Next step:** operator picks (A) build or (B) cite. If (A): the first milestone is the concrete
  `(3,3,3,4)` `q∈{1,2}` joint CoV realizing `det(Q_b Q_bᵀ)^{−a/2} · reduced` as the shifted-chain box —
  the decisive constructive probe (and the honest test of whether "build addlongest" is bounded labour
  or a deeper AG effort).
