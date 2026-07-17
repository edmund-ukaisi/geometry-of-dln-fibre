# b0-wall-adjudication — is the b=0 (tall) / POWER-interior / d1-a≥u non-factoring regime a SECOND WALL in Lane 1?

**Seat:** pen-and-paper (witness + obstruction), `genm-d1design`, Lane 1. **Date:** 2026-07-17. **NO Lean.**
Controller-elevated to a soundness/completeness adjudication. Verified: exact-ℕ (`scripts/d1_{corners,power_strata,b0_reach}.py`,
`minAdmRec`) + a0rev's free-variable-separation criterion + TWO decorrelated `local-codex-consult` (xhigh,
conclusions withheld — `codex/power-{prompt,answer}.md`, `codex/wall-{prompt,answer}.md`). Consumes d1split
`redteam-cert.md`, a0rev's criterion (via controller), the socket.

---

## ★ VERDICT (LEAD) — NOT a second MATH wall; but plain hIH is INSUFFICIENT for the hard arms, AND the "carried-Gram nested-qbox recursion" is a DEAD ROUTE. The three hard arms UNIFY under the JOINT COUPLED source–tail incidence (FreeBilinear + finite box = the d1-a≥u atlas).

**a0rev's criterion (the discriminant):** the front–tail decoupling to plain `hIH` is valid **iff the Gram
weight left behind is the Gram of a FREE variable, separated from the tail by a genuine (surjective) CoV.**

- **a=0 wide BOUNDED (`M₂≤b`): CLEAN — plain hIH (PROVEN, a0rev + lane1shell landed).** `W=F·A₁` is a genuine
  CoV (F wide, full row rank ⟹ `A₁↦W` SURJECTIVE ⟹ `W` a free `M₀×M₂` variable), and `det(FFᵀ)` is the Gram of
  the FREE front `F` — a separated free-box qbox factor. Immune to the tail-coupled counterexample.
- **b=0 tall (ALL M₂), a=0 POWER interior (`0<s<M₀`), d=1 a≥u: FAIL the criterion (PROVEN).** The front sits
  BEFORE the tail product with NO free layer to CoV against surjectively (b=0/POWER: tall/injective front;
  d1-a≥u: corank couples to the deep product `Q̃ₚ`). Integrating the front leaves a Gram of a **tail PRODUCT**
  (`det(Q_pQ_pᵀ)^{−M₀/2}` for b=0; `det((C·Z_deep)(C·Z_deep)ᵀ)^{−r/2}` after the POWER Δ-blow-up, `codex/power`
  PROVEN). This is tail-coupled — the FORBIDDEN naked-Gram object (d1split ε-counter `M=(4,3,2)`). So these
  arms do **NOT** close on plain hIH. **No clean sub-regime for b=0** (`scripts/d1_b0_reach.py`: 0 leaf cells at
  arity ≥ 4; the "clean one-shot qbox" of waist-pin §5 is only the arity-3 leaf where `Q_p` is a single FREE layer).

## Q1 — does b=0 close on plain hIH, for which M₂? WITNESS + refutation

**Refuted for all b=0** (obstruction above). The only clean-plain-hIH regimes are **a=0 BOUNDED (`M₂≤b`)** and
**d=1 a<u** (drop-transverse leaf). lane1shell's conjectured "clean `M₂≤a` sub-regime" for b=0 does NOT exist as
plain hIH: integrating the tall front always yields the tail-coupled `det(Q_pQ_pᵀ)^{−M₀/2}` (`Q_p=prod(redChain
M₁ M)`); `M₂≤a` is only the convergence of the FIRST disposal qbox, not a plain-hIH factorization. (The
arity-3 leaf where `Q_p` is a single free layer IS a one-shot free-box qbox — but that is the leaf, not a general M₂ sub-regime.)

## Q2 — SECOND WALL? NOT a math wall; but the nested-qbox recursion WALLS (dead route), and the JOINT COUPLED incidence is required (native)

**The carried-Gram NESTED-QBOX RECURSION is a DEAD ROUTE (PROVEN, `codex/wall`).** Disposing the tail-coupled
Gram by integrating each reduced-chain free layer via a qbox (carrying the deeper Gram) requires **Fibonacci-type
inequalities** `r+k ≤ M₂`, `k+M₂ ≤ M₃`, `M₂+M₃ ≤ M₄`, … (`r=M₀−s`, `k=M₁−s`) that the `minAdm` charge recursion
does **NOT** supply. **Smallest failure `M=(2,2,1,2) @ s=1`** (`a=b=d=r=k=1`, binding, charge `rk=1`,
`minAdm(1,1,2)=1`, total `2=minAdm`): the first C-qbox is `(b,q,a)=(k,M₂,r)=(1,1,1)`, requiring `1<1` — FALSE,
log-diverges throughout the window `½<c'<1`. So the nested-qbox route is UNSOUND — **bake as a KILL-condition:
do NOT dispose the tail-coupled Gram by an iterated free-layer qbox recursion.**

**But it is NOT a math wall.** The same minimal cell `M=(2,2,1,2)` (which is `d=1`, `a=b=1`) CLOSES via the
**banked scalar FreeBilinear leaf** (`γ⊗z`, `freeBilinear_box_lt_top`/`sumSqND_box_lt_top`), keeping the
`(Δ,C,Z)` block JOINTLY on the FINITE box. Codex (decorrelated): *"Closing these cells requires a genuinely
coupled source–tail incidence mechanism — retaining the finite-domain cap / joint `(Δ,C,Z)` geometry, with the
scalar free-bilinear resolution at the minimal cell — not a carried-Gram qbox recursion."* This IS the d1-a≥u
**joint `[C|Γ]` atlas** (`d1-atom-spec.md §2`). So:

**The three hard arms (b=0, a=0-POWER-interior, d1-a≥u) UNIFY under ONE native mechanism — the JOINT COUPLED
source–tail incidence** (free front-block × tail product, resolved JOINTLY on the finite box, FreeBilinear at
the leaf), NOT plain hIH, NOT a nested-qbox recursion. Reachability DISSOLVES the "wall": it is native (banked
FreeBilinear + finite box + the min-over-strata charge, 0/5292 + cut-soundness 0/22932), reaching `½minAdm(M)`.
**Lane 1 stays fully NATIVE** (no new cite; no naked global Gram-decorated IH — that is FALSE). The genuinely-new
content is the GENERAL joint `(Δ,C,Z)` coupled resolution (generalizing the banked FreeBilinear leaf to
`min(a,b)=1` blocks over a product tail) — ARGUED-native (the minimal cell is banked; the general is the heart to build).

## Q3 — LOG + POWER interior ν_j

- **LOG (`M₂=b+1`, a=0):** the free-variable separation STILL holds (`W=F·A₁` free), but the free-front-Gram
  qbox is MARGINAL (`M₂<b+1` needed strict), so the clean factorization's `∫_F det(FFᵀ)^{−M₂/2}` factor is
  log-divergent. It does NOT fit a clean one-factor δ-fold; it needs the **coupled log-density δ-fold**
  (`ρ(W)≍log`, convert via `one_add_log_inv_le_rpow` to `τ^{−δ}`, absorb the `δ` in the loss headroom `Δ>0`,
  binding stratum `s<M₀`). EXPENSIVE-TRANSCRIPTION (standard δ-slack), but a COUPLED estimate, not the clean
  factorization. (Δ>0 needs the binding stratum interior — holds for LOG cells; to confirm at the build widths.)
- **POWER interior ν_j (`0<s<M₀`, `codex/power` PROVEN):** blow up the `Δ` block (the `r×k=(M₀−s)×(M₁−s)` block
  measuring the SOURCE rank drop `{rank F ≤ s}`), single exceptional divisor `z=‖Δ‖`, **exponent
  `ν_z=(M₀−s)(M₁−s)`** (the peelCharge, = codim`{rank F≤s}`, NOT codim`{rank W≤s}=(M₀−s)(M₂−s)`). Template
  `M=(2,3,3,·)@s=1`: `|det DΦ|=|x|^{−2}|z|`, `ν_z=2`. This gives the charge `(M₀−s)(M₁−s)` and the shift
  `c'↦c'−(M₀−s)(M₁−s)/2`, but leaves the residual `det((C·Z_deep)(C·Z_deep)ᵀ)^{−r/2}` → the JOINT COUPLED
  incidence (Q2), NOT a nested-qbox. So POWER interior = `Δ`-blow-up (banked-style CoV) + the joint coupled leaf.

## Kill-conditions (bake for the §2 / POWER formaliser)
1. **Do NOT dispose a tail-coupled product-Gram by an iterated free-layer qbox recursion** — it WALLS (Fibonacci
   qbox conditions fail, `M=(2,2,1,2)`). Use the JOINT COUPLED `(Δ,C,Z)` incidence (FreeBilinear leaf + finite box).
2. **Do NOT claim plain hIH for b=0 / POWER-interior / d1-a≥u** — they fail the free-variable-separation criterion.
   Plain hIH is only for a=0 BOUNDED + d1 a<u.
3. **Do NOT carry a naked global Gram-decorated IH** — FALSE (d1split ε-counter). The Gram is resolved LOCALLY
   by the joint coupled incidence, never carried globally.

## Close
- **Firmest.** NOT a second MATH wall: the hard arms are native, unified under the joint coupled source–tail
  incidence (FreeBilinear + finite box = the d1-a≥u atlas), reaching `½minAdm(M)`. But TWO routes are DEAD:
  plain hIH (fails free-variable separation) and the carried-Gram nested-qbox recursion (Fibonacci qbox
  conditions fail, PROVEN `M=(2,2,1,2)`). b=0 has NO clean plain-hIH sub-regime. The genuinely-new heart is the
  general joint `(Δ,C,Z)` coupled resolution (ARGUED-native; minimal cell banked FreeBilinear).
- **Most likely to break THIS.** The general joint coupled resolution reaching `½minAdm` for `min(a,b)≥... ` —
  wait, these arms are `min(a,b)≤1` (d≤1) by construction (d≥2 is cited); the joint block is a free `a×(u+1)` (d1)
  or the tall front (b=0), corank rank ≤1, so the FreeBilinear leaf applies. If some arm needed a `min≥2` free
  block the FreeBilinear leaf would not suffice — but d≤1 guarantees rank-≤1, so FreeBilinear is the right leaf.
  (Verify the general joint coupled resolution at the build.)
- **Next.** Build the JOINT COUPLED `(Δ,C,Z)` incidence resolution (the d1-a≥u atlas, generalized): POWER
  interior = Δ-blow-up (`ν_z=(M₀−s)(M₁−s)`) + the joint leaf; b=0 = the tall-front joint leaf; d1-a≥u = the
  `[C|Γ]` joint atlas. All FreeBilinear at the rank-≤1 leaf. Kill the nested-qbox recursion. LOG = coupled
  log-density δ-fold. Report to controller + lane1shell.

Files (absolute): `…/threads/genm-d1design/b0-wall-adjudication.md` (this); `codex/power-{prompt,answer}.md`
(POWER Δ-blow-up + residual Gram, NEW-BLOWUP), `codex/wall-{prompt,answer}.md` (nested-qbox WALLS, joint
coupled required); `scripts/d1_{corners,power_strata,b0_reach}.py`; d1split `redteam-cert.md`; `d1-atom-spec.md §2`.
