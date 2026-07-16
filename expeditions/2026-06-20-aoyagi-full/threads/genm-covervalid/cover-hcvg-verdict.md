# hole (d) cover (LEMMA C) — hcvg per-shell validity: VERDICT

**Seat:** pen-and-paper (obstruction+witness), aoyagi-full Stage 2, `genm-covervalid`. **Date:** 2026-07-13.
**NO Lean edits, NO build.** Exact ℕ arithmetic (truncated Nat-sub) over the CURRENT Lean defs
(`minAdm`/`minAdmRec` `RouteMLayerSplit`, `bindingCut = Nat.find (exists_binding_cut)` `RouteMSJAdm:112`,
`peelCharge` `RouteMSJDecoratedCharge:45`, `tailMinWidth` `RouteMSJDeeperFlagCore:458`, `deeperFlag_shell_le`
hyps `RouteMSJDeeperFlagCore:750`). Scripts: `scripts/covervalid_{scan,genuine,split,wide,final,achiever,B}.py`.
Decorrelated `local-codex-consult` (xhigh, my conclusion WITHHELD — prompt framed "adjudicate either
direction"): `codex/hcvg-{prompt,answer}.md`. Codex CONCURS on every point + supplies the off-sector proof.

Setup (from the brief + the real defs): `t★ = bindingCut M`, `r = min(M0−t★, M1−t★)`; shell `j∈[0,r]`,
`u = t★+j`, `a = M0−u`, `b = M1−u`, frame `m = min(M1,Mlast) − j`. Per `deeperFlag_shell_le`:
`hcvg : a+b ≤ m`, `hrange : m ≤ M2` (else the shell is empty). GENUINE shell = `a≥1 ∧ b≥1` (nonempty corank
block). GOOD chain = nondegenerate + `hpiv` (`minAdm(redChain u M) ≤ u·tailMinWidth M`) at every genuine
shell (the non-waist condition; the brief's `deepTailMin ≤ M1` gives the SAME failure counts).

---

## ★ VERDICT — the literal claim is FALSE; the cover is SOUND only under a shell-split. WITNESS at j=0.

**The literal question — "does hcvg hold for EVERY non-empty cover-shell `j∈[0,r]` in the good case?" — is
FALSE.** hcvg fails, but the failure is **confined ENTIRELY to the SECTOR shell `j=0`**; every off-sector
shell `1≤j≤r−1` is fine. Exact counts (my sweep, arity 3–5, matched by Codex's independent sweep):

| shell class | good-case genuine non-empty shells | hcvg FAIL |
|---|---:|---:|
| **sector `j=0`** | 1630 | **511 (≈31%)** |
| **off-sector `1≤j≤r−1`** | 466 | **0** |

Codex's independent sweep (widths 1..8, arity 3–5): j=0 fails **1120**, j≥1 fails **0**; every failing GOOD
chain has failure set exactly `{0}` (not scattered). **Both models agree: 100% of good-case hcvg failures
are at the sector `j=0`, zero off-sector.**

### WITNESS (sector j=0) — a principled infinite family, not a lucky hit
- **Smallest:** `M = (2,2,1)`. `t★=1` (plateau `{1,2}`, least achiever), genuine shell `j=0`: `a=b=1`,
  `m=min(2,1)=1`, `hrange 1≤M2=1 ✓`, `hpiv minAdm(1,1)=1 ≤ 1·min(2,2,1)=1 ✓` — GOOD — but `a+b=2 > 1=m`.
- **Canonical / principled:** the **balanced cube `(w,w,w)`, odd `w≥3`** (e.g. `(3,3,3)`, `(5,5,5)`).
  Least binding cut `t★=(w−1)/2`, so `a★+b★ = 2(w−t★) = w+1 = min(M1,Mlast)+1` — hcvg fails by EXACTLY 1.
  (Even `w`: `t★=w/2`, `a★+b★=w=min(M1,Mlast)`, hcvg holds — `(2,2,2)` is the boundary that works.)
- Mechanism: at `j=0` the shell frame `m = min(M1,Mlast)` (Ky-Fan floor on the full product `Z_full=A₀·Z_deep`)
  must absorb the full binding corner `a★+b★`, and the LEAST-achiever binding cut leaves `a★+b★ ≥ min(M1,Mlast)+1`.

### OBSTRUCTION (off-sector j≥1) — hcvg HOLDS in the good case, with an EXACT derivation
For nondegenerate `M`, any binding-cut achiever `t★`, and an off-sector genuine shell `j≥1` with `hpiv`:
let `D(x)=minAdm((x,)+M[2:])`, `w=tailMinWidth M`, `q=min(M1,Mlast)`.
1. **Binding minimality** `f(t★)≤f(u)` (`f(t)=(M0−t)(M1−t)+D(t)`, `u=t★+j`) ⟹ `D(u)−D(t★) ≥ j(a+b+j)`.
2. **Ray-concavity** of `D` (`u·D(t)≥t·D(u)` for `0<t<u`, `D(0)=0` — verified EXACT 0/11172,
   `/tmp/concav_check.py`) ⟹ `D(u)−D(t★) ≤ (j/u)·D(u)`.
3. **hpiv** `D(u) ≤ u·w` and `w ≤ q` ⟹ `D(u)−D(t★) ≤ j·w ≤ j·q`.
4. Combine: `j(a+b+j) ≤ j·q`, cancel `j≥1`: `a+b ≤ q−j = m`. **∎ = hcvg.**
At `j=0` step 1 degenerates to `0≤0` — no control over `a+b`. This is the sharp reason the failure is
exactly at `j=0`. (Derivation by Codex, decorrelated; its concavity lemma verified here.)

The off-sector M₂>M₁ divergent shells (`(4,3,5,5)`, `(3,3,4,4)`; `tobl3b-M2gtM1-scope-cert`) are excluded
from GOOD by `hpiv` — they are WAISTS (`good(hpiv)=False`), consistent with that cert routing them to the
separate needs-new-work / waist base case. So `hpiv` is exactly the gate that makes off-sector hcvg hold.

---

## What this means for hole (d)'s assembly (the soundness gate holed flagged)

**If hole (d) routes ALL shells `j∈[0,r]` through `deeperFlag_shell_le` (the brief's literal framing), it is
UNSOUND** — `hcvg` is unprovable at `j=0` for ~31% of good chains, incl. the balanced anchor `(3,3,3)`.

**The cover IS sound under the reformulation cert's DESIGNED 3-way split** (`tobl3b-reformulation-cert` §3,
line ~160: "`S_0` uses PSD-monotonicity outright (`uniformWenn_le`), `S_r` has p=0 freed corner weight ≡1";
off-sector bound stated for `1≤j≤r−1`):
- **`j=0` (sector `S_0`):** route via the LANDED `uniformWenn_le` / `sjSector` / `frontFirst` branch (the
  (a) top-stratum, task #120). **No `hcvg`.** The `a+b ≤ min(M1,Mlast)` Ky-Fan bound genuinely cannot carry
  the sector; the sector needs its own full-rank two-block argument (already landed for the good stratum).
- **`1≤j≤r−1` (off-sector):** `deeperFlag_shell_le`. `hcvg` holds unconditionally in the good case (proven
  above, 0/856+ exact).
- **`j=r` (saturated `S_r`, and any `a=0/b=0` degenerate shell):** the saturated leaf (p=0, weight ≡1). No `hcvg`.

**Do NOT rely on refinement (B) "use the greatest binding-cut achiever".** It makes hcvg hold at all
genuine shells (10786/10786) BUT collapses `r=0` for 10218/10972 good chains (charge-0 degenerate front
peel) — it VACATES the mountain (relocating the difficulty to a degenerate front peel), it does not solve
it. It is a useful diagnostic of WHY j=0 fails (least-achiever maximizes `a★+b★` on the minAdm plateau),
not a fix.

---

## ADDENDUM (2026-07-14) — the j=0 branch residual, resolved: sector over-runs the M2 frame by AT MOST 1

Controller residual: does the LANDED sector tool (`uniformWenn_le`/`sjSector`, #120) discharge the sector
`S_0` up to `c'<minAdm/2` for the balanced/hcvg-failing case, or does it silently carry `a+b ≤ min(M1,Mlast)`
(which would sink the j=0 branch too)? THREE exact findings (scripts `/tmp/covervalid_{Lge1,sectorframe,balanced,borderline}.py`; decorrelated Codex `codex/sector-{prompt,answer}.md`, conclusion withheld, CONCURS + proves the bound):

1. **The balanced-cube hcvg-failure is L=0-ONLY — it never reaches the cover.** The `DecoratedStepHyp` fill
   routes `L=0` (3-width) through the banked closed form `routeMBoxThresholdFinite_mnp`; only `L≥1` (≥4-width)
   uses the shell cover (endgame-lanes lines 10–11). Balanced `L≥1` cubes `(w,…,w)` ALL pass hcvg at the
   sector (binding cut lands at `a★+b★ ≤ w`; verified arity 4–6, w=2..7, 0 failures). So `(3,3,3)`/`(5,5,5)`
   are base cases, NOT cover witnesses — the balanced alarm does not reach the cover.

2. **`uniformWenn_le` carries `a+b ≤ M2`, NOT `a+b ≤ min(M1,Mlast)`.** Its finiteness is `Wenn(I_{M₂})<⊤`
   (`RouteMSJShellUniform:55` + `detGram_lintegral_box_lt_top`), i.e. `a < M₂−b+1 ⟺ a+b ≤ M₂` — the full
   M₂ (deep-row) frame, a DIFFERENT and strictly weaker condition than the Ky-Fan hcvg frame `min(M1,Mlast)`.
   For `L≥1` it covers the sector shells where `min(M1,Mlast) < a+b ≤ M₂` (the majority of hcvg-failures).

3. **THEOREM (Codex-proven, exact, all widths/arities): `a★+b★ ≤ M₂+1` always.** Let
   `G(x)=minAdm((x,M₂,…,Mlast))`. Reusing the minimizing first cut gives `G(x+1)−G(x) ≤ M₂`; binding
   optimality `f(t★)≤f(t★+1)` gives `a★b★ − (a★−1)(b★−1) = a★+b★−1 ≤ G(t★+1)−G(t★) ≤ M₂`, so
   `a★+b★ ≤ M₂+1`. Exact sweep (arity 4–6, widths 1..7): sector `a+b≥M₂+2` bucket is EMPTY (0/12111);
   the only shells failing BOTH frames are exactly `a+b = M₂+1` (the borderline `a = M₂−b+1`).

**Consequence — the j=0 branch does NOT sink; the sector's worst case is the KNOWN θ-interpolation
borderline `a = M₂−b+1`** (`shell_convergence.py`: "borderline bites ONLY at j=0, θ-interpolation"; the
vslice anchor `(3,3,3,4)` is an instance). At that borderline the DECOUPLED corank weight (uniformWenn OR
the Cat-I Gram-Schur det-Gram) diverges MARGINALLY (`a = M₂−b+1` is the exact boundary, not strict), so it
needs the COUPLED pivot×corank bound — the θ-interpolation / Cat-I good-stratum radial model (#113/#120,
`RouteMSJRadialInt.integrableOn_norm_rpow_neg_ball` is general-`n` and landed), governed by `hpiv`
(`c'−½ab < ½·u·tailMinWidth`, holds in the good case), NOT `hcvg`.

**Corrected j=0 routing (refines the 3-way split above):** the sector `S_0` is itself TWO sub-cases —
(i) `a+b ≤ M₂` (strict): `uniformWenn_le` (deep M₂-frame, no hcvg); (ii) `a+b = M₂+1` (borderline, ≤ +1
over-run, proven): the COUPLED θ-interpolation (Cat-I radial + pivot; vslice done, general-`n` radial
landed). **No `a+b ≥ M₂+2` case exists** (proven), so there is NO unbounded sector divergence and NO
`a+b ≤ min(M1,Mlast)` bound sinking the branch.

**Verdict on the residual: j=0 branch SOUND — no balanced sink, no unbounded scope gap.** The one honest
open piece is the GENERAL-M borderline θ-interpolation coupled bound (the step2 lane `pivotPeel_domination`,
D-A-radial + S3-corank, in progress; vslice instance + general radial engine landed) — bounded LABOUR, not
a wall, and NOT a hidden `a+b ≤ min` assumption. `uniformWenn_le` alone is NOT the full sector tool: it
discharges only the strict sub-case (i); the borderline (ii) needs the coupled bound.

---

## Close
- **Firmest result.** hcvg is FALSE at every non-empty cover-shell only at `j=0`; TRUE (with exact
  derivation) for `1≤j≤r−1` in the good case. Witness `(2,2,1)` / `(3,3,3)`; obstruction proven via
  binding-minimality + ray-concavity of `D` + `hpiv`. Decorrelated Codex concurs on verdict, split, witness,
  and supplies the off-sector proof.
- **Most likely to break the FIX.** That the landed `uniformWenn_le`/`sjSector` sector branch actually
  discharges `S_0` for ALL good chains (not just the vslice anchors) — that is the (a) top-stratum's own
  scope, outside this seat's question; the reviewer/controller should confirm it covers the general balanced
  sector (`(3,3,3)`-type, `a★+b★ = min(M1,Mlast)+1`) and is not itself silently assuming `a+b ≤ min(M1,Mlast)`.
- **Next.** Wire hole (d) as the explicit 3-way `Finset.sum` split (S₀ / 1≤j≤r−1 / Sᵣ), applying
  `deeperFlag_shell_le` ONLY on the off-sector middle. The `lintegral_le_sum_finCover` subadditivity is
  agnostic to how each summand is bounded, so the split is a routing choice in the assembly, not new analytic
  content.
