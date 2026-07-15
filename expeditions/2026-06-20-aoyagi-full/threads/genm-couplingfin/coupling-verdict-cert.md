# A_cor-coupling of the head-split pivot — BOUNDED (the coupling is benign; the shell is load-bearing for the pivot)

**Seat:** pen-and-paper (design-space math, one truth-value, decorrelated), aoyagi-full Stage 2,
`genm-couplingfin`. **Date:** 2026-07-13. **NO Lean, NO git, NO build.** Exact algebra (rank/codimension
counts, singular-value structure of the linear pivot map, exact `minAdm`/QIP recursion) + a semi-analytic
sublevel-volume RLCT estimator (`/tmp/pivot_coupling2.py`, `/tmp/pivot_cases3.py`, `/tmp/pivot_deepz.py`,
`/tmp/bgtu_and_mech.py`, `/tmp/scope_sweep.py`; MC is a guide, the load-bearing exponents are the rank
counts). Decorrelated `local-codex-consult` (xhigh, my conclusion WITHHELD): `codex/coupling-{prompt,answer}.md`.

**Consumed / read (signatures, not re-derived):** `s1-spine-headsplit-cert.md` (Part A P-radial + §B.2b
`M₂>M₁` scope boundary); `codex/s1-Chle-angular-answer.md` (the `J`-threshold `uρ/2` at FIXED `Q`, gate
`minAdm(redChain u M) ≤ uρ`); `codex/s1-headsplit-answer.md` (Ky-Fan shell⊆G containment); `offsector-il-
design-cert.md` (two-brick + flag, Gram divisor `det(Q_bQ_bᵀ)^{−a/2}` corank charge); `final-assembly-
design-cert.md` (flag stratification, `C_j ≥ minAdm(M)`); `genm-sj5-recon/s0-reduced-core-fidelity-cert.md`
(the domination `freedSchurLoss ≥ w`, `w = frobSq([P|B₁₂]·A₂·A₃)`); `tobl3b-s1A-decomposition-review.md`
(the `hpiv` gate encoding + marginal-endpoint per-exponent note).

---

## ★ VERDICT — **BOUNDED.** The A_cor-coupling admits a uniform-in-`A_cor` reorganization; C < ⊤ per-exponent under `hpiv`.

The A_cor-coupled radial-peeled pivot `frobSq(P̂·Q_stack(A_cor))` **does** admit a uniform-in-`A_cor`
bound to the A_cor-free `decLoss` + the S3 `ab`-charge, and the domination closes with a **finite C(ε)**
for every `c'` strictly below `carrierThreshold(M)`, **provided the singular-shell restriction
`σ_min(Z_full) ≥ ε` is in force** (it is — the LHS is `shellSpineIntegrand`) and `hpiv` holds. There is
**no uncontrolled `A_cor→0` direction** and **no uncontrolled `z→deep` direction**. The sharp findings:

1. **`A_cor→0` is TRANSVERSE to the pivot — it is a pure S3 corank charge, not a pivot divergence.**
2. **The coupling's *only* delicacy is the joint corner `{P→singular} ∩ {Z_full rank-drop}`; the shell
   excludes exactly that corner.** Off-shell the coupled pivot threshold degrades `uρ/2 → 5/2` (anchor);
   on-shell it is uniformly `uρ/2`. **This makes the shell restriction load-bearing for the PIVOT** — a
   sharpening the `s1-Chle` consult missed (it fixed `Q` at generic full rank `ρ`, i.e. implicitly on-shell).
3. **Finite C rests on the pre-existing gate `hpiv: minAdm(redChain u M) ≤ u·tailMinWidth(M)`**, marginal at
   the anchor `(3,3,3)@u=2` (`6 = 6`, per-exponent), holding at every `M₂≤M₁` binding cut, failing exactly
   at `M₂>M₁` (the `s1-spine` B.2b scope boundary — a route scope limit, **not** a coupling wall).

Decorrelated Codex CONCURS on (1) and on the degradation-stratum being singular-`P`, and on the gate
`m>uρ` as the genuine obstruction; the one apparent divergence (whether `(3,3,4,4)` is bounded) traces to a
chart phrasing in my prompt and dissolves (below).

---

## 1. The object, precisely (what varies with `A_cor`)

At a binding cut `u`, `a=M₀−u`, `b=M₁−u`, `n=M_last`, `ρ := tailMinWidth(M) = min(M₁,…,M_last)`. The deep
product `Z_full = A'₀·Z_deep` (`M₁×n`), rows split into pivot `Q_p = z0·Z_deep` (`u×n`) and corank
`Q_b = A_cor·Z_deep` (`b×n`); `Q_stack = [Q_p;Q_b] = Z_full`. On `IsUnit P` the freed-corner peel leaves the
pivot energy (top `u` rows of the front `M₀×M₁` layer):

    w(P,B₁₂,A_cor) = frobSq([P|B₁₂]·Q_stack) = frobSq(P·Q_p + B₁₂·A_cor·Z_deep)     — DEPENDS on A_cor.

The RHS comparator replaces `w` by the A_cor-**free** `decLoss = commonDivisor(v)²·frobSq(Q_p)` (`v` = the
P-radial coordinate), and charges the corank `(A_cor,Γ)` by the S3 Gram divisor `det(Q_bQ_bᵀ)^{−a/2}`
(→ `½·ab`). The crux: `w` couples to `A_cor` through `B₁₂·A_cor·Z_deep`, so S3's fixed-scalar-`w` lemma
does not apply pointwise-in-`w`.

**Banked fact (s1-Chle, re-verified here):** for a FIXED generic `Q_stack` of maximal rank `ρ`, the map
`[P|B₁₂] ↦ [P|B₁₂]·Q_stack` is linear of rank `u·ρ`, so `∫_{[P|B₁₂]} w^{−c} = ` finite iff `c < uρ/2`
(semi-analytic, `/tmp/pivot_coupling2.py`: slope `3.000` at `(3,3,3)@u=2`, `ρ=3`).

## 2. `A_cor→0` is transverse — a separate corank charge, not a pivot divergence (EXACT; Codex CONCURS)

As `A_cor→0`, `Q_b = A_cor·Z_deep → 0` and `w → frobSq(P·Q_p) ≥ σ_min(P)²·frobSq(Q_p) > 0` (P invertible
on the chart, generic reduced-`z` ⟹ `frobSq(Q_p)>0`). So **`w` does not vanish as `A_cor→0`.** Hence the
pivot-zero locus `{w=0}` is **disjoint** from the corank-zero locus `{Q_b=0}` (at `Q_b=0`, `w=frobSq(P·Q_p)>0`).
The `A_cor→0` singularity is carried **entirely** by the S3 Gram divisor `det(Q_bQ_bᵀ)^{−a/2}` (charge
`½·ab`); the two singular loci never reinforce. [Codex Q3, decorrelated: `w→‖P z0‖²_F ≥ σ_min(z0)²‖P‖²_F>0`,
"`{w=0}` disjoint from `{Q_b=0}`; this direction creates only a separate corank charge, not pivot divergence".]

## 3. The coupling's only delicacy: the `{P→singular} ∩ {Z_full rank-drop}` corner — shell-excluded

**Off-shell (`A_cor` integrated freely, rank-drops included) the coupled pivot threshold DEGRADES below
`uρ/2`.** Semi-analytic RLCT of `∫_{[P|B₁₂],A_cor} w^{−c}` at `(3,3,3)@u=2`:

| domain | coupled-pivot RLCT `λ` |
|---|---|
| fixed generic `A_cor` | `3.000 = uρ/2` |
| `A_cor` FREE (no shell) | `2.500 = 5/2` (degraded) |
| `A_cor` on shell `σ_min(Z_full)≥ε` | `3.000 = uρ/2` (restored) |

**The degradation stratum is `{A_cor ∈ rowspace(Q_p)}` (⟺ `Z_full = A'₀·Z_deep` drops rank), and it consists
entirely of SINGULAR `P` (EXACT).** On `{A_cor ∈ rowspace(z0)}` (`τ:=` the transverse component `=0`), the
pivot-zero equation `P·Q_p = −B₁₂·A_cor·Z_deep` forces `P = −B₁₂·(A_cor·Z_deep)·Q_p⁺`, which has
`rank ≤ b < u` (a rank-`≤b` product), hence `det P = 0`. So `{w=0}` on `{τ=0}` never meets `{P invertible}`
away from `P→0`. The rank-`2` drop of `L` at the codim-`1` `{τ=0}` locus lowers the exponent from `uρ/2=3`
to `2 + ½ = 5/2` (`rank-4` part `→ 2`, plus the codim-`1` `τ` `→ ½`), matching the MC.

**The route's LHS is shell-restricted (`shellSpineIntegrand`, `σ_min(Z_full) ≥ ε`), which EXCLUDES exactly
this corner** (`{τ≈0}` ⟺ `Z_full` near rank-drop ⟺ off-shell / higher flag level `j≥1`). On the shell the
coupled pivot threshold is uniformly `uρ/2` — verified across every requested case (semi-analytic, on-shell):

| chain @ cut | `a,b` | `uρ/2` | on-shell `λ` | comparator `minAdm(redChain u M)/2` | `hpiv` |
|---|---|---|---|---|---|
| `(3,3,3)@u=2` (anchor, L=0) | `1,1` | `3` | **3.000** | `3` | `=` marginal |
| `(3,3,3,3)@u=2` (deep-z, L=1) | `1,1` | `3` | **3.000** | `2.5` | `<` margin |
| `(4,4,4)@u=2` (`b=u=2`) | `2,2` | `4` | **4.000** | `4` | `=` marginal |
| `(3,4,4)@u=2` (`b=2`) | `1,2` | `4` | **4.000** | `4` | `=` marginal |
| `(2,4,4)@u=1` (`b=3>u=1`) | `1,3` | `2` | **2.000** | `2` | `=` marginal |
| `(3,5,5)@u=2` (`b=3>u=2`) | `1,3` | `5` | **5.000** | `5` | `=` marginal |
| `(3,3,4,4)@u=2` (**WALL**) | `1,1` | `3` | **3.000** | `3.5` | `>` **FAILS** |

**This is the exact pin the brief asked for.** The `s1-Chle` consult found `uρ/2` treating `Q` at generic
full rank `ρ` — correct, but *only because that is the on-shell configuration*; it did not surface that the
shell is what keeps `A_cor` off the rank-drop corner. The shell restriction is **load-bearing for the
pivot**, not merely for the corank Loewner floor. [Codex independently: the stratum "consists entirely of
singular `P`"; it also notes `|det P|≥δ` removes the corner — an additional safety, §6.]

## 4. `z→deep` is absorbed by the shell (Ky-Fan) + the reduced-comparator IH

On the shell, the Ky-Fan containment (`s1-headsplit`: `Z_full∈S_j ⟹ σ_m(Z_deep) ≥ ε'`) forces `Z_deep` to
floor rank `m`, so neither `Q_p = z0·Z_deep` nor `Q_b = A_cor·Z_deep` degenerates from the deep tail. The
remaining `z→deep` degeneration is `z0` (the reduced comparator's own front variable) becoming
rank-deficient — charged by the **reduced comparator's** threshold (the v-radial monomial
`minAdm(redChain u M)/2` + the arity-`(L+1)` IH), **not** by the pivot. The L=1 deep-z anchor
`(3,3,3,3)@u=2` confirms the on-shell pivot threshold stays `uρ/2 = 3.0 > 2.5` (margin). No uncontrolled
`z→deep` direction.

## 5. Finite C rests on `hpiv`, marginal at the anchor (per-exponent)

After (2)–(4), the residual is the standard pivot-vs-comparator threshold match: the pivot's `P→0` radial
singularity (`uρ/2`) must be dominated by `decLoss`'s radial charge (`minAdm(redChain u M)/2`), i.e.

    hpiv:  minAdm(redChain u M) ≤ u·tailMinWidth(M).

Anchor `(3,3,3)@u=2`: `uρ = minAdm(2,3) = 6` — **equality**, marginal. `C(ε) < ⊤` for `c'` strictly below
`carrierThreshold(M)` (the reduced comparator at exponent strictly below its threshold); `C(ε)→∞` only AS
`c'→` the endpoint (log). This is per-exponent finiteness — exactly what the `(□)` needs (`c' <
carrierThreshold` strictly). The tide must **not** claim endpoint-uniform `C`. [Codex Q4: "when `m=uρ` and
the kernel is present, finiteness is assured only for strict `c<m/2`; endpoint/uniform constants require
pole-order information." — matches `s1A` review point 3.]

**Scope (WALL side), exact.** Sweep over all binding cuts (arity 3,4, widths 2–5): `hpiv` holds at 177/177
`M₂≤M₁` cuts and FAILS at 71 cuts — **every failure has `M₂>M₁`, zero failures with `M₂≤M₁`**
(`/tmp/scope_sweep.py`). So at a binding cut, `hpiv ⟸ M₂ ≤ M₁`, and every wall has `M₂ > M₁`. E.g.
`(3,3,4,4)@u=2`: `minAdm(2,4,4)=7 > uρ=6`; both binding cuts (`u=1,2`) fail. **This is the identical
boundary the `s1-spine` cert derived independently (B.2b: `L≥1 ∧ M₂>M₁`, shell-forced `m<a+b`)** — a route
scope limit, not a coupling wall. Those cuts need a finer `Z_deep`-stratification / the saturated branch.

## 6. Decorrelated Codex (my conclusion WITHHELD; prompt framed "argue whichever direction")

`codex/coupling-{prompt,answer}.md` (xhigh). **CONCURS** on the load-bearing structure, **decorrelated**:
- **Q3 [FACT]** `A_cor→0`: `w→‖P z0‖²>0`, `{w=0}` disjoint from `{Q_b=0}`, only a separate corank charge.
  (Identical to §2.)
- **Structure [FACT]** the degradation stratum "consists entirely of singular `P`" (identical to §3's
  `{τ=0} ⟹ det P=0`); rank-drop is a codim-`5`-in-`9` stratum with threshold `5/2` (identical exponent).
- **Q5 [INFERENCE]** the genuine wall is `m := minAdm(redChain u M) > uρ` — i.e. `¬hpiv` (identical to §5).
- **One apparent divergence, traced and dissolved:** Codex read my prompt's "`|det P|` bounded below" as
  `≥δ>0` and concluded the pivot kernel `{P=0}` misses that chart (`threshold +∞`), calling `(3,3,4,4)`
  bounded. But the route's chart is `outerDom = {det P ≠ 0}` with `P→0` **reachable** (the P-radial blow-up
  parametrizes `s = commonDivisor(v) → 0`); there the `uρ/2` singularity is operative and `(3,3,4,4)` walls.
  Codex's own condition (`m>uρ`) then gives the wall. (Even granting the `|det P|≥δ` chart, `(3,3,4,4)`
  still walls via the corank weight `m<a+b`, `s1-spine` B.2b.) The concurrence on the gate is decorrelated;
  the divergence is a chart artifact of my prompt, not a substantive disagreement. Codex's `|det P|≥δ`
  observation is a genuine *bonus*: the degradation corner is removed by `|det P|≥δ` as well as by the shell.

## The exact lemma the tide needs (BOUNDED form)

**`headSplit_pivotDom` (scope + shell-restricted, per-exponent):** for a binding cut `u` with `hpiv`
[`minAdm(redChain u M) ≤ u·tailMinWidth(M)`] and `c'` strictly below `carrierThreshold(M)`, there is
`C(ε) < ⊤` with — **on the singular shell `{σ_min(Z_full) ≥ ε}` (flag level `j=0` / the good set `G`)** —

    ∫_{[P|B₁₂]∈outerDom} frobSq([P|B₁₂]·Z_full)^{−(c'−½ab)} d[P|B₁₂]
        ≤ C(ε) · (v-radial decLoss comparator on redChain u M at exponent c'−½ab).

**Load-bearing hypotheses that must appear (do NOT drop):**
- the shell `σ_min(Z_full) ≥ ε` (§3 — without it the LHS threshold degrades `uρ/2 → <uρ/2` via the
  `{P-singular}∩{rank-drop}` corner; the corner is routed to flag levels `j≥1`);
- `hpiv` (§5 — the P→0 radial charge matching `decLoss`; equality at the anchor);
- per-exponent `C(ε)` only (§5 — no endpoint-uniform claim);
- the `M₂>M₁` scope carried as a hypothesis, or those cuts routed through a finer stratification (§5, =
  `s1-spine` B.2b).

The `A_cor→0` and `z→deep` directions require **no** extra hypothesis: the former is transverse (absorbed
into S3's `½·ab`), the latter is absorbed by the shell (Ky-Fan) + the reduced-comparator IH.

## Close

- **Firmest result.** The A_cor-coupling of the head-split pivot is **BOUNDED**: the uniform-in-`A_cor`
  reorganization exists and `C(ε)<⊤` per-exponent under `hpiv`. `A_cor→0` is transverse (a pure S3
  `½·ab` charge, `w` bounded below there); the coupling's sole delicacy — the joint
  `{P→singular}∩{Z_full rank-drop}` corner, where the pivot threshold degrades `uρ/2→5/2` — is excluded by
  the singular-shell restriction that the route already carries. **The shell is load-bearing for the pivot,
  not just the corank floor** (the pin beyond the `s1-Chle` consult, which fixed `Q` at generic rank).
  Decorrelated Codex concurs (transverse `A_cor→0`; singular-`P` degradation stratum; `m>uρ` gate).
- **Most likely to break it.** (i) The **marginal endpoint** at every equal-rate cut (`uρ = minAdm(redChain u M)`,
  incl. the anchor): `C(ε)→∞` as `c'→carrierThreshold`; sound only for strict `c'<` (the mountain works
  strictly below, so this is fine — but the tide must state per-exponent `C`, never endpoint-uniform).
  (ii) The **`M₂>M₁` scope boundary** (`hpiv` fails): a genuine route limit (= `s1-spine` B.2b), where the
  head-split at that cut does not close; carry the scope hypothesis or route via a finer stratification.
- **Next.** For the D-tide: thread the shell hypothesis into `headSplit_pivotDom` as load-bearing (it is
  the exclusion of the rank-drop corner), and consume `hpiv` as the gate; the `A_cor→0` corank charge is
  already banked (S3 `shell_corankOffSector_le_unif`). One optional pen-and-paper follow-on: pin the
  degraded-exponent formula on `{τ=0}` for general `(u,a,b,ρ)` (the anchor gives `uρ/2 − ½`) to double-check
  that flag levels `j≥1` charge the excluded corner at `C_j ≥ minAdm(M)` — the charge arithmetic is already
  verified (offsector §3, 3161 cuts, 0 undershoots), so this is confirmation, not a gap.
