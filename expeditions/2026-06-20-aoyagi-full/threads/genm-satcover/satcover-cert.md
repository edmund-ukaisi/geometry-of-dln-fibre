# The j=r saturated-shell coverage adjudication — VERDICT: **(b) — SD-7 is a SEPARATE mechanism, NOT subsumed by Brick D.** The claim under test is REFUTED.

**Seat:** pen-and-paper (OBSTRUCTION-primary / witness-fallback, decorrelated), aoyagi-full Stage 2,
`genm-satcover`. **Date:** 2026-07-15. **NO Lean, NO build.** Exact integer algebra (minAdm layer-peel
recursion, incidence codim `C_{ℓ,s}`, block dimensions at `ab=0`) + a decorrelated `local-codex-consult`
(xhigh, gpt-5.x, my conclusion WITHHELD, prompt framed "argue whichever way"):
`codex/satcover-{prompt,answer}.md`. Codex reached **(B)** INDEPENDENTLY and contributed three corrections
(all verified, folded in below).

**Cross-read (verified against, not paraphrased):** `genm-incidencepp/incidence-cert.md` §1/§3/§3b
(the object `G`, `C_{ℓ,s}`, the charts, the `a+b≤M₂` scope), `genm-bltj/mixdegen-cert.md` (b<j regime =
outcome (b) via subset-monotonicity, but SILENT on j=r), `genm-jreq/jreq-verdict.md` (the earlier
`(b)-NEEDS-ARITY-IH` adjudication), `genm-brickd-design/reconciliation-T1.md` (the descent `(∗_T1)`, shell
load-bearing for descent), the SD-7 Lean statement `deeperFlagSaturatedShell_reduce`
(`genm-sj5-jreqb:RouteMSJDecoratedStep.lean:315`), the Brick D statement `deeperFlag_shell_le`
(`genm-sj5-brickdfin:RouteMSJDeeperFlagCore.lean:752`), the good-connector dispatch
(`genm-sj5-good:RouteMSJGoodConnector.lean`), rescopefin's subset route
(`genm-sj5-rescopefin:RouteMSJShellSubset.lean`).

---

## ★ VERDICT — the coverage claim is FALSE. Outcome **(b)**.

> **Claim under test:** *"Brick D (`headSplit_domination`) covers the saturated shell `j=r` at `min(a,b)=0`
> with a valid descent, so SD-7 `deeperFlagSaturatedShell_reduce` is subsumed by Brick D — no separate
> mechanism needed."*

**REFUTED.** The claim conflates the **statement** (which does coincide at `ab=0`) with the **proof
mechanism** (which does not). Precisely:

1. **The DESCENT TARGET is shared and non-circular — that part of the claim is TRUE.** Both `deeperFlag_shell_le`
   (Brick D, `j<r`) and `deeperFlagSaturatedShell_reduce` (SD-7, `j=r`) bound the shell integrand by
   `C · (cornerComparator (redChain (t+j) M) k jc).integral(c' − peelCharge/2)` on the **shorter** chain
   `redChain (t+j) M` (one fewer layer). At `j=r`, `peelCharge = 0`, so the shift is `0` and the two RHS
   exponents coincide at `c'`. So SD-7's conclusion is literally the `ab=0` instance of `deeperFlag_shell_le`'s
   conclusion. This is a genuine arity-descent (closed by the lower-arity decorated IH `hIH`), **not** the
   circular subset route — so outcome **(c) is excluded** (see §4).

2. **"Subsumed by Brick D — no separate mechanism needed" is FALSE.** Brick D's proof is the **incidence
   resolution** (`deeperFlag_spineToCore → deeperFlag_shell_core_le`), whose load-bearing content is VACUOUS
   at `ab=0`: the corank-Gram divisor `det(Q_b Q_bᵀ)^{−a/2}` is **always a unit**, and one of the two blocks
   structurally vanishes (§3). The incidence blow-up is built to resolve the coupling between `row(Q_p)` and
   the corank block `row(Q_b)` and to absorb the pointwise `σ_min(Q_p)→0` blow-up against the corank-Gram —
   and **there is nothing there to resolve when a block is absent.** SD-7 must be proved by a **separate,
   simpler** mechanism (drop the empty corner, then a single direct pivot-radial blow-up onto the reduced
   product), exactly as the current `jreqb` architecture already encodes it (`hsat` is hypothesis-light,
   `hcvg`-dropped, "corank-trivial", pivotDom-independent). **SD-7 is a distinct brick.**

**Triple-confirmed:** exact block algebra (§3) + the exhaustive `minAdm`/`peelCharge`/`C_{ℓ,s}` sweep (§5)
+ decorrelated Codex (independent, no repo access — reached (B), sharpened the block analysis, caught three
of my mis-statements).

---

## 1. The setup (verified against the incidence-cert + the Lean statements)

At a binding cut `u = t★ + j`, `a = M₀ − u`, `b = M₁ − u`, `peelCharge M u = (M₀−u)(M₁−u) = a·b`. The
saturated shell is `j = r = min(M₀−t★, M₁−t★)`, i.e. `u = t★ + r = min(M₀, M₁)`.

The shell integrand `shellSpineIntegrand M u κ ε r ⟨j,_⟩ c'` must be shown `< ⊤` for `c' < T1 = ½·minAdm M`.
Three candidate mechanisms exist in the codebase:

- **(1) Brick D / incidence resolution** (`deeperFlag_shell_le`, strict shells `1 ≤ j < r`): the head-split
  object (incidence-cert §1)
  `G = ∫_z ∫_{Q_b} det(Q_bQ_bᵀ)^{−a/2} · [∫_{P,B,C} (‖[P|B]·hsQ‖² + ‖C·Q_p(I−Π_b)‖²)^{−q}]`, `q = c'−ab/2`,
  `Q_p = prod(redChain u M)·z` (`u×M₂`), `Q_b = A_cor` a free `b×M₂` corank block, `hsQ = (Q_p;Q_b)`,
  resolved along incidence strata `rank W = ℓ`, `W = Q_p·N`, `N` spanning `ker Q_b`. **Requires scope
  `a+b ≤ M₂`** (else the corank-Gram diverges — incidence-cert §Verdict-2) and bounds by the **shifted**
  comparator on `redChain u M`.
- **(2) Subset route** (rescopefin, `shellSpineIntegrand_le_layerBox`, j-agnostic): `shell ≤ routeMLayerBoxIntegral M`
  (the level-`M` box). Finite iff the level-`M` box is finite — banked at the 3-width leaf, **circular for
  `L ≥ 1`** (rescopefin's own caveat).
- **(3) SD-7** (`deeperFlagSaturatedShell_reduce`, `j = r`): the degenerate-corner reduction to the **UNSHIFTED**
  comparator on `redChain u M`; pivotDom-independent, uses **none** of `hpiv/hcvg/hrange`.

---

## 2. The load-bearing arithmetic at j=r (Deliverable: exact algebra)

**(F1) `j = r ⟹ min(a,b) = 0`, `peelCharge = 0`, `ab = 0`.** `u = min(M₀,M₁)` ⟹ `a = (M₀−M₁)₊`,
`b = (M₁−M₀)₊`, so `a·b = 0` and `peelCharge M u = ab = 0`. **At least one of `a,b` is 0; BOTH when
`M₀ = M₁`** (Codex correction — I had mis-said "exactly one"; the sweep has 1093/2925 cases with `a=b=0`).
Sweep: 0 exceptions in 2925 saturated cuts (arities 3–5, widths 1–6).

**(F2) `peelCharge = 0 ⟹ minAdm M ≤ minAdm(redChain u M)`** (the reduced threshold `≥ T1`). This is the
`t = u` candidate of the `minAdm` layer-peel recursion, directly (no sweep needed — Codex correction):
`minAdm M ≤ (M₀−u)(M₁−u) + minAdm(redChain u M) = ab + minAdm(R) = minAdm(R)` at `ab=0`
(banked `minAdm_le_peelCharge_add_redChain`). Hence `c' < ½·minAdm M ≤ ½·minAdm(redChain u M) =
carrierThreshold(redChain u M)`, exactly the threshold `hIH` needs. Sweep: 0 exceptions.

**(F3) The incidence exponent identity survives, but is a red herring at `j=r`.** `C_{ℓ,s} = (M₀−s)(M₁−s)+sM₂−ab`
(the `ℓ`-independent identity, incidence-cert §3; 0 sweep failures). At `ab=0` this is
`(M₀−s)(M₁−s)+sM₂` — the SINGLE-peel codim, whose min over feasible `s` equals `minAdm M` only at the
3-width leaf. For deeper chains the relevant threshold is `½·minAdm(redChain u M)` (the comparator's, from
F2), NOT the single-peel `C_{ℓ,s}` min. (My first sweep's "F3 fail" was this off-target comparison, not a
real gap.)

**(F4) `hcvg` — the codebase's coverage hyp — is NOT guaranteed at `j=r`, but this is moot.** The PURE
incidence scope `a+b ≤ M₂` in fact **holds at every genuine `j=r` cut** (`r ≥ 1`): 0/2925 violations
(Codex correction — my earlier "631 fails" was the codebase's STRONGER `hcvg = min(M₁,M_last)−j`, not the
pure scope; e.g. `M=(2,1,2)` has `a+b=1 ≤ 2 = M₂`, satisfying the pure scope, and only fails the stronger
coverage bound). The stronger `hcvg` fails at 631/2925 `j=r` cuts — but **the good connector's `hsat`
(and `hstrict`) branches are both `hcvg`-DROPPED** (`RouteMSJGoodConnector.lean:341,348`), so neither
branch requires it. Net: `hcvg` is not a discriminator; the discriminator is the block-vanishing (§3).

---

## 3. The decisive block algebra — why the incidence mechanism is vacuous at `ab=0` (KEY SUB-QUESTION)

> *At `min(a,b)=0` does the incidence chart retain BOTH blocks (pivot `Q_p`, corank `Q_b`), or does one
> vanish, and does that make the incidence blow-up content-free?*

**The corank-Gram divisor `det(Q_bQ_bᵀ)^{−a/2}` is ALWAYS a unit at `ab=0`** (the decisive fact):

| case | `Q_b` (`b×M₂`) | `det(Q_bQ_bᵀ)^{−a/2}` | transverse Schur (`a` C-rows) | incidence `W = Q_p·N` |
|---|---|---|---|---|
| `b=0` (`M₁≤M₀`) | **empty** (0 rows) | `det(∅) = 1` | present, but `Π_b=0` so `= ‖C·Q_p‖²` (no projection) | `N = I_{M₂}` ⟹ **`W = Q_p`** |
| `a=0` (`M₀≤M₁`) | present (`b` rows) | `det^{0} = 1` (unit) | **empty** (0 C-rows) | `W = Q_p·N` may be nontrivial |
| `M₀=M₁` | empty | `1` | empty | `W = Q_p` |

**What the incidence resolution is FOR (incidence-cert §3–§4), and why it has nothing to do here:**
- The resolution's HARD, non-trivial content is the **coupled corank-Gram**: `sup_{Q_b} det(Q_bQ_bᵀ)^{−a/2}=∞`,
  so it must ride inside the shrinking incidence tube, and its integrability is *exactly* the scope
  `a+b ≤ M₂` (Wishart smallest-SV `∫τ^{n−b−a}dτ`). **At `ab=0` this divisor is a unit** — the entire coupled
  corank-Gram apparatus, and the scope it needs, is ABSENT.
- The transverse-Schur term `‖C·Q_p(I−Π_b)‖²` monomialises the **incidence** `W = Q_p·N` (the meeting of
  `row Q_p` with `row Q_b`). At `b=0` there is no `Q_b` to be transverse to (`Π_b=0`, `W = Q_p`); at `a=0`
  there are no C-rows, so the term is absent. **The incidence-specific coordinate is gone.**

**Codex's sharpening (preserved, [FACT]): the residual `rank W = ℓ` blow-up is NOT always vacuous** — at
`b=0`, `W = Q_p`, so `rank Q_p = ℓ` can still drop; at `a=0`, `Q_b` remains. But **this residual is a plain
matrix-product / pivot-radial blow-up, not the incidence blow-up.** At `b=0` the object collapses to
`G = ∫_z ∫_{Y} (‖Y·Q_p‖²)^{−c'}`, `Y=(P;C)∈ℝ^{M₀×u}` — the front against the reduced product `Q_p`, with
**no** det-Gram, **no** corank coupling, **no** `σ_min(Q_p)→0`-vs-corank-Gram interplay. Resolving `rank Q_p`
here is precisely the banked **D-A `pivotBlock_radial_blowup`** that SD-7 uses directly — NOT
`deeperFlag_shell_core_le`.

**Conclusion of §3.** The incidence resolution's distinctive machinery (coupled corank-Gram + scope
`a+b≤M₂` + transverse-Schur incidence coordinate) is **content-free** at `ab=0`; what survives is the bare
pivot blow-up. So Brick D's PROOF does not "specialise validly" to `j=r` — it degenerates to a different,
simpler argument. That simpler argument is SD-7. This forces outcome **(b)**, and (with §4) not **(c)**.

---

## 4. Why NOT (c) (base-like / subset suffices) — the descent is genuinely needed for `L ≥ 1`

The subset route (rescopefin) bounds `shellSpineIntegrand ≤ routeMLayerBoxIntegral M` (the level-`M` box).
Finite iff `RouteMBoxThresholdFinite M`. **rescopefin's own caveat (next to the claim):** *"this subset
bound is CIRCULAR for the box-finiteness INDUCTION — it bounds a peel-component of the chain-`M` box by the
chain-`M` box itself … it does NOT supply the reduced-comparator domination the `L ≥ 1` recursion needs."*
Unconditional only at the 3-width leaf (`routeMBoxThresholdFinite_mnp`).

At `j=r`, `redChain u M` (arity `L+2`) is **not** the terminal object for `L ≥ 1` — it is a genuine
lower-arity chain still requiring `hIH`. So the shell object is NOT already the reduced/terminal object;
a descent is required. SD-7 supplies it (bound by the comparator on `redChain u M`, closed by `hIH`);
the circular subset route cannot. **Outcome (c) is false for `L ≥ 1`.** (At the leaf, `j=r` finiteness is
free via the base case — but that is the base case, not the recursion step.)

---

## 5. The exact SEPARATE reduction SD-7 needs (Deliverable: the arity-IH statement)

The statement is already pinned in `jreqb` and is **correct as stated** — it is a distinct brick, not a
Brick-D instance:

    theorem deeperFlagSaturatedShell_reduce (M) (t j) (κ) (hε) (c')
        (ht) (hj) (ht1) (hnd)
        (hc' : ((M₀−(t+j))·(M₁−(t+j)) : ℝ)/2 < c')
        (hjeq : j = min (M₀−t) (M₁−t)) :
      ∃ C : ℝ≥0∞, C < ⊤ ∧
        shellSpineIntegrand M (t+j) κ ε (min (M₀−t)(M₁−t)) ⟨j,_⟩ c'
          ≤ C * (cornerComparator (redChain (t+j) M) ![1] ![minAdm (redChain (t+j) M) − 1]).integral c'

with the UNSHIFTED exponent `c'` (`peelCharge = 0`), on the SHORTER chain `redChain (t+j) M`. **Uses NONE
of `hpiv/hcvg/hrange`.**

**Its proof (the residual analytic content — a small dedicated brick, NOT Brick D)** = jreq-verdict steps
3–4, re-confirmed here and by Codex:
1. **Drop the empty corner.** `min(a,b)=0` ⟹ corank energy `≡ 0` (`b=0`: no `Q_b`; `a=0`: `det^0=1`) and any
   surviving C-rows only ADD a nonneg term ⟹ `freedSchurLoss ≥ frobSq(P·Q̃_p)` (pivot only). The Γ-box
   collapses to weight `1` (`ab=0`).
2. **Direct pivot-radial blow-up.** Banked D-A `pivotBlock_radial_blowup` + det-1 clear factors the pivot
   energy to `commonDivisor²·frobSq(prod(redChain u M) z) = decLoss`; surviving rows integrate to a finite
   constant `C`.
3. `= C · (cornerComparator (redChain u M) ![1] ![minAdm−1]).integral c'`.

**The close** (`deeperFlagSaturatedShell_finite`, ALREADY sorry-free modulo SD-7 on `jreqb`): consume SD-7,
`cornerComparator_adm`, and `hIH` on `redChain u M`; the peel-charge arithmetic (F2) subordinates
`hcT : c' < ½·minAdm M` to the reduced threshold `hIH` needs. This is the arity-IH (`hIH` quantifies over
`M':Fin(L+1+1)→ℕ`; `redChain u M : Fin(L+1+1)→ℕ`). **Both Brick D and SD-7 use this same `hIH`; the
distinguishing content is the SEPARATE domination proof, not the IH.**

**Same lemma as Brick D?** No. Same descent TARGET and same IH; **genuinely separate domination proof**
(direct pivot blow-up vs incidence resolution). Codex: *"a genuinely separate endpoint/pivot reduction,
even if packaged under a common wrapper."*

---

## 6. Impact on the endgame (Deliverable: the knowing decision)

- **SD-7 `deeperFlagSaturatedShell_reduce` is NOT subsumed by Brick D — it needs its own (simpler) proof.**
  The endgame-map's ORPHAN #1 resolution "confirm the incidence Brick D discharges `j=r`" is **negative**:
  Brick D does not discharge `j=r`. The correct fill is the **direct empty-corner pivot reduction** (§5),
  a small dedicated brick (jreq steps 3–4). jreqbuild's original "= finfin S3 ∀j finiteness" fill was dead
  (finfin killed), and the replacement is NOT Brick D — it is this direct reduction. **Assign SD-7 its own
  owner** (or fold it into whatever lane owns the banked D-A `pivotBlock_radial_blowup` — it needs those
  lemmas to accept the degenerate widths `a=0`/`b=0`; if they were stated only for `min(a,b)>0`, SD-7 needs
  a tiny empty-corner variant — still NO new math).

- **The `(v)`-assembly `j=r` branch is a NON-ISSUE — it is never invoked at `j=r`.** The good connector
  (`RouteMSJGoodConnector.lean:504–509`) dispatches shells: `jf=0 → hsector`, `1 ≤ jf < r → hstrict` (Brick D),
  `jf = r → hsat` (SD-7). So the incidence `(v)` assembly (`incidenceCell_lintegral_le → headSplit_domination
  → deeperFlag_shell_le`) is **only ever consumed for `j < r`.** Recommendation: **add strict `hjr : j < min
  (M₀−t)(M₁−t)` to `headSplit_domination`/`deeperFlag_spineToCore`/`deeperFlag_shell_le`** (the jreq-verdict
  packaging directive; currently these are typed `j ≤ r` with no `hjr`). This lets the incidence proof assume
  `min(a,b) ≥ 1` throughout and never thread empty-block case-splits. Alternatively leave them `j ≤ r` and
  simply never invoke them at `j=r` — but the strict `hjr` documents the scope and removes a latent
  wrong-proof hazard at `@544`.

- **`bltj` (the `b<j` regime, `1 ≤ j < r`) is settled separately as outcome (b)** and is NOT the same as
  `j=r`: bltj closes via subset-monotonicity of the FULL incidence object (both blocks present, `min(a,b)≥1`);
  `j=r` closes via block-vanishing + direct pivot descent. Adjacent, distinct mechanisms.

---

## 7. Numerics / exact algebra (all load-bearing; `/tmp/satcover/*.py`, exact integer)

- `satcover_exact.py`: F1 (0/2925 fail), F2 (0/2925 fail), the `C_{ℓ,s}` identity (0 fail).
- `vanish.py`: at `j=r`, always one block vanishes — `both a=b=0`: 1093, `b=0 only`: 916, `a=0 only`: 916,
  `neither`: 0.
- `codex_check.py`: pure scope `a+b ≤ M₂` holds at all `j=r` (0/2925 fail); codebase `hcvg`+`hrange` fails
  631/2925 (stronger bound, dropped by both connector branches); `minAdm M ≤ minAdm(R)` from the `t=u`
  recursion candidate (spot-checked incl. `(4,4,4,4)`, `(5,3,2,6)`).

*(The Python is exact-integer computation, not MC; it enumerates the recursion and block dimensions.)*

## 8. Decorrelated Codex (conclusion WITHHELD; prompt "argue whichever way")

`codex/satcover-{prompt,answer}.md` (xhigh). Independent, reached **(B)** and CONTRIBUTED:
- **[FACT]** the det-Gram divisor is always a unit at `ab=0`, but the residual `rank W = ℓ` blow-up is not
  always vacuous — it is a matrix-product/pivot blow-up, not the incidence blow-up (sharpens §3; I had
  over-claimed "entire `W`-stratification content-free").
- **[CORRECTION]** "exactly one of `a,b` is zero" is wrong — both when `M₀=M₁` (verified, §2 F1).
- **[CORRECTION]** `M=(2,1,2)` does NOT violate `a+b≤M₂` (`1≤2`); only the stronger coverage bound (§2 F4).
- **[FACT]** `minAdm M ≤ minAdm(R)` is the `t=u` recursion candidate directly, no sweep needed (§2 F2).
- **[FACT]** the subset bound is circular for `L ≥ 1`; saturation does not identify the shell with the
  reduced object (§4).
- Its verdict-3 gives the SAME separate reduced-chain bound as §5, unshifted `c'`, "genuinely separate …
  even if packaged under a common wrapper."

---

## Close

- **Firmest result (OBSTRUCTION).** At `j=r` the peeled corner degenerates (`min(a,b)=0`, `peelCharge=0`);
  the corank-Gram divisor is a unit and one block vanishes, so the incidence resolution's load-bearing
  content is content-free. Brick D therefore does **not** cover `j=r`: the saturated shell needs a
  **separate**, simpler, pivotDom-independent reduction (SD-7 = drop empty corner + direct D-A pivot
  blow-up), a genuine arity-descent to `redChain u M` at the unshifted exponent `c'`, closed by the same
  lower-arity IH. **Outcome (b). The claim under test is refuted.** The current `jreqb` architecture
  (SD-7 separate, feeding a sorry-free-modulo-SD-7 close) is correct.
- **Most likely thing to break it.** (i) If the banked D-A lemmas (`pivotBlock_radial_blowup`,
  `frobSq_schur_split_inv`, `prod_headSplit`) are stated only for `min(a,b) > 0`, SD-7's fill needs a small
  empty-corner variant (NO new math, but a real Lean chore). (ii) A build that tries to reuse
  `deeperFlag_shell_core_le` at `j=r` (empty-block case-splits) — wrong way; it will thrash. (iii) If some
  `j=r` cut had `a+b > M₂` with `r ≥ 1` (it does not, 0/2925) SD-7 would still be fine (it does not use the
  scope) but Brick D's statement would additionally fail to type-apply.
- **Next construction/consult to settle the open part.** The coverage decision is settled. The residual is
  the Lean fill of SD-7: confirm the banked D-A lemmas accept `a=0`/`b=0` widths, or scope a tiny
  empty-corner peel. Recommend the strict-`hjr` packaging of `deeperFlag_shell_le`/`deeperFlag_spineToCore`
  (removes the `j=r` wrong-proof hazard at `@544`). Assign SD-7 an owner (it is currently ORPHAN #1).
