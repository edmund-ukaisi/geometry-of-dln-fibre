# Toric-ray Q_D certification + gap-(iii) quantitative sectors

**Seat:** pen-and-paper (decorrelated no-obstruction certification — genm-sj5-cover). **Date:** 2026-07-11.
**NO Lean.** **Charge (team-lead):** upgrade Q_D from UNPROVEN → CERTIFIED (or find the offending ray) via
toric-ray principalization of the rank-one angular chart ideal `(P·Q_tp, u(q₁+sq₂), uvq₂)` + the two binding
reduced charts, on `(3,3,3,4)` and `(4,4,4,4)`; emit the quantitative sectors + Jacobians for gap (iii).

**CORRECTION (2026-07-11, from `transversality-recursion.md` #144):** below I say the critical divisor is
"pivot-vanishing with the shared deeper product generic FULL-RANK" (§2, §4, §5). The literal full-rank form
is an OVER-CLAIM and is FALSE in general (reduced `(2,2,2)` has its top component at `rank Zdeep=1<2`). The
correct, width-general invariant is the WEAKER `rank_{gen,X}(Zdeep) ≥ a+b−1 ≥ b` on every top-dim component
(proven by `minAdm` binding-cut convexity) — exactly enough for the `b` corank rows to survive → `p=0`. The
`p=0` conclusion and the Q_D no-obstruction verdict here are UNCHANGED; only the geometric reason is
corrected. See `transversality-recursion.md`.

**Exact algebra (mine):** `/tmp/prodD/{toric_verify,verify_fast,corner75,audit75}.py` (the combined-ray formula
+ offending-ray + the corrected `v`-integral + the anchor transversality). **Decorrelated:** own xhigh
`local-codex-consult`, conclusion WITHHELD, told to compute the rays and hunt an offending one:
`codex/toricray-{prompt,answer}.md`. Codex produced the EXACT combined-ray formula (which I re-derived and
verified by hand) and the two oracle-compatible extremal models; I then SETTLED the decisive datum (`p=0` on
the critical divisor) geometrically, which Codex left open. (MC RLCT was attempted as a guide and DISCARDED —
the reference law puts `f` at `O(1)`, so the `f→0` tail is not sampled; not a certificate and not reliable.)

---

## ★ HEADLINE VERDICT — CERTIFIED no-obstruction for both anchors (Aoyagi-independent at top level)

**No toric ray of our front-peel resolution lies below `½minAdm` — for BOTH `(3,3,3,4)` and `(4,4,4,4)`.**
The certification is NOT automatic from the plain reduced RLCT oracle (Codex exhibited two oracle-compatible
models, one giving `7/2` and one giving `3/2`); it hinges on ONE precise, checkable geometric datum, which I
verified: **on the CRITICAL reduced divisor, the mixed corank direction `H₁ = |q₁+s q₂|` is a UNIT (`p=0`).**
This holds because the critical reduced divisor is the **pivot-block-vanishing locus with the shared deeper
product generic** — on which the corank rows are transverse (generic, nonzero). With `p=0`, Codex's exact
combined-ray formula gives every ray `≥ ½minAdm`, binding exactly at the coupled ray. **So there is NO
finiteness obstruction** (independently consistent with Aoyagi's `RLCT = ½minAdm`). Two build-critical
corrections fall out (§4): the load-bearing invariant the decorated IH must carry is `p=0` on critical
divisors (NOT `q=0`), and the residual decoration is `H₁^{−3}(H₁+H₂)^{−1}`, NOT `H₁^{−3}H₂^{−1}`.

---

## 1. Convention + the exact combined-ray formula (Codex, re-derived by me)

For `f = Σ g_i²` and measure `dμ = Π|x_k|^{ρ_k}dx`, `∫ f^{−c'}dμ < ∞ ⟺ c' < λ`,
`λ = min_E (ord_E Jac + 1)/ord_E f`, `ord_E f = 2·min_i ord_E g_i`. **CERTIFIED no-obstruction ⟺
`λ ≥ ½minAdm` ⟺ every ray ratio `(ord_E Jac+1)/ord_E f ≥ ½minAdm`.** (This is the RLCT of the LOSS; note the
factor 2 vs the ideal-lct — the controller's "`ord_E I/(ord_E Jac+1) ≥ ½minAdm`" phrasing was inverted, the
verdict is convention-independent.)

**Local model** (front peel, rank-one angular chart): `f = R² + u²(H₁² + v²H₂²)`, `H₁=|q₁+s q₂|`, `H₂=|q₂|`,
`R=|P Q_tp|`; `u` the Γ-block radial (`ρ_u = ab−1`), `v` the determinant-normal coordinate (`ρ_v=0`), the
reduced variables governing `(R,H₁,H₂)`. For a combined primitive ray `w=(x,y;η)` (`x=ν_w(u)`, `y=ν_w(v)`,
`η` a reduced ray with `r=ν_η(R)`, `p=ν_η(H₁)`, `q=ν_η(H₂)`, `K=ord_η(Jac_red)+1`, `d=ab`):

    ord_w(f) = 2·min(r, x+p, x+y+q),    ord_w(Jac)+1 = d·x + y + K,
    λ(w) = (d·x + y + K) / (2·min(r, x+p, x+y+q)).            [Codex; hand-verified — /tmp/prodD/toric_verify.py]

**The `u`- and `v`-integrals (verified exact):** `∫₀¹u^{d−1}(R²+u²H²)^{−c'}du ≍ R^{−2c'}` (`H≤R`) or
`R^{d−2c'}H^{−d}` (`R≤H, c'>d/2`); `∫₀¹(H₁²+v²H₂²)^{−2}dv ≍ H₁^{−3}(H₁+H₂)^{−1}` (`= H₁^{−4}` if `H₂≤H₁`,
`H₁^{−3}H₂^{−1}` if `H₁≤H₂`). [My earlier audit/prompt used `R^{4−2c'}H^{−4}` — correct for `a=b=2`; the
`R^{2ab−2c'}H^{−2ab}` in the toric prompt was a doubled typo, Codex corrected, immaterial to the anchors.]

## 2. The certification hinges on `p=0` — and `p=0` holds on the critical divisor (Q_D verdict)

**The oracle alone is INSUFFICIENT** (Codex, verified): the plain reduced RLCT gives only `K = C_red·r` on the
critical ray, saying nothing about `p,q`. Two oracle-compatible models (both plain-reduced-RLCT `3/2` for
anchor A):

| model | `(r,p,q,K)` | minimizing ray | `λ` |
|---|---|---|---|
| `R=z`, `H₁=H₂` units, `dμ=|z|²dz` (TRANSVERSE) | `(1,0,0,3)` | `(x,y,r)=(1,0,1)` | **`7/2`** |
| `R=H₁=H₂=z`, `dμ=|z|²dz` (CO-VANISHING) | pure reduced | `(0,0,1)` | `3/2` (obstruction) |

So a bare hunt cannot conclude; the DECISIVE datum is `p = ν_η(H₁)` on the critical divisor. **Scan of the
combined-ray formula (exact, `/tmp/prodD/toric_verify.py`):**

| datum | anchor A `(3,3,3,4)` min `λ` | verdict |
|---|---|---|
| `p=q=0` (transverse) | `7/2` at `(1,0,1)` | **CERTIFIED `≥7/2`** |
| `p=0, q=1` (only `H₂` vanishes) | `7/2` | **still CERTIFIED — `q` is HARMLESS** |
| `p=1, q=0` | `2` | OBSTRUCTION |
| `p=1, q=1` | `3/2` | OBSTRUCTION |

**Only `p` is load-bearing.** For `(4,4,4,4)`: both binding cuts certify with `p=0` — `t=2` (`d=4,C_red=7`)
→ `11/2`, `t=3` (`d=1,C_red=10`) → `11/2` (and `t=3` is robust even at `p=1`). So the binding constraint is
`p=0` on the `t=2` reduced critical divisor.

**`p=0` HOLDS (the geometric fact, verified for the anchor).** For `(3,3,3,4)`, redChain `(1,3,4)`: the
reduced product is the pivot row `A₁[0,:]∈ℝ³` times the shared deeper `Z (3×4)`. The critical locus
`{A₁[0,:]·Z = 0}` has main component `{A₁[0,:]=0}` with `Z` generic full-rank — **codim 3 = `minAdm(1,3,4)`**,
the RLCT-achieving divisor. On it the corank rows `q₁=A₁[1,:]·Z`, `q₂=A₁[2,:]·Z` (`A₁[1,:],A₁[2,:]` free, `Z`
full-rank) are **generic units** → `p=q=0` (`/tmp/prodD/toric_verify.py` C4: `|q₁|,|q₂|=O(1)` on the divisor).
The `Z`-rank-deficient strata (where the corank rows WOULD co-vanish, `p>0`) are strictly HIGHER codim →
non-critical (`K > C_red·r`), where the formula shows `p>0` is NOT an obstruction. **So the critical divisor is
pivot-vanishing/transverse, `p=0`, and every ray `≥ 7/2`: CERTIFIED no-obstruction, Aoyagi-independently.**

**Width-general:** the same structure recurses (at each peel the critical reduced divisor is the
current-pivot-block-vanishing locus with the shared deeper product generic → the current corank rows
transverse → `p=0`). Verified at the TOP reduced level for both anchors; the full recursion is the decorated
IH's obligation (§4). Independently, Aoyagi's `RLCT=½minAdm` FORCES `p=0` on all critical divisors (else the
formula yields `λ<½minAdm`, contradicting Aoyagi) — so no obstruction exists at any width; the value of this
cert is the STRUCTURAL reason (`p=0` transversality) and the exact spec it hands the build.

## 3. Q_D — final

**CERTIFIED no-obstruction for `(3,3,3,4)` and `(4,4,4,4)`:** no toric ray below `½minAdm`; the binding ray is
the coupled `(x,y,r)=(1,0,1)` at exactly `½minAdm`. Certified via the exact combined-ray formula + the
verified `p=0` transversality on the critical reduced divisor. NO offending ray. It is a construction/labour
gap (build the decorated resolution), NOT a finiteness obstruction. The only residual for a fully
width-general Aoyagi-INDEPENDENT certificate is the recursion of `p=0` to all levels — verified top-level,
and Aoyagi-implied throughout.

## 4. Two build-critical corrections (fold into the decorated-IH build)

1. **The decorated IH must carry the corank-row valuation `p = ν_η(H₁)` and maintain the invariant `p=0` on
   critical reduced divisors** — equivalently, the invariant "the corank block is transverse to the deeper
   pivot degeneration (the critical divisor is pivot-vanishing with the shared deeper product generic)."
   `q = ν_η(H₂)` need NOT be tracked for finiteness (`q` alone is harmless, §2). This is the PRECISE decoration
   (sharper than "carry `H^{−4}`" from the #141 audit): the load-bearing datum is `p`, and the target is `p=0`.
2. **Correct the residual decoration to `H₁^{−3}(H₁+H₂)^{−1}`** (the exact `v`-integral), NOT `H₁^{−3}H₂^{−1}`
   (used in the design/#141). The sloppy form BLOWS UP as `H₂→0` with `H₁` a unit (artificial divergence);
   the correct form → `H₁^{−4}` finite there. Requiring `3p+q=0` (sloppy) over-constrains; the correct form
   needs only `p=0`. (`/tmp/prodD/toric_verify.py` C3.)

## 5. Gap-(iii) quantitative sectors + blow-up coords + Jacobians (feeds the formaliser's finite-cover CoV)

For the `a×b` Γ-block (anchor `a=b=2`), on the rank-drop neighbourhood:

- **Front Γ-radial + angular + det-normal chart.** `Γ = u·M`, `M = [[1, s],[t, s t + v]]` (`u≥0` the radial
  `= ‖Γ‖`-scale; `s,t` bounded ANGULAR units; `v` the DETERMINANT-NORMAL coordinate, `det M = v`). Jacobian
  `|dΓ| = u^{ab−1} du ds dt dv = u³ du ds dt dv`. The loss pulls back to `f = R² + u²(H₁² + v²H₂²)` after a
  bounded row operation (`row₂ ↦ row₂ − t·row₁`), `H₁=|q₁+s q₂|`, `H₂=|q₂|`.
- **`v` is RETAINED as an exceptional coordinate near `{v=0}` (rank-1 Γ).** Do NOT invert `v` / do NOT
  Gaussian-eliminate through the singular `M` — that reintroduces the uncontrolled `|det M|^{−1} = v^{−1}`
  (the F2 seam). Keep `f = R² + u²(H₁² + v²H₂²)` with `v` a coordinate; the `{v=0}` branch is the rank-1
  sub-chart (= the `t=3` binding cut for `(4,4,4,4)`), certified at `½minAdm` (§2, C2).
- **Finite entrywise cover (reciprocal charts).** Cover `{Γ ≠ 0}` by the finitely many charts "entry `Γ_{ij}`
  is the largest" (each a bounded-box chart with the same `u³` Jacobian shape). This supplies the reciprocal
  chart the single `M`-form misses.
- **The coupling charts (both required).** The front radial `u₀` and the reduced radial `u₁` couple; cover the
  corner by `u₁ = u₀·τ` (`0≤τ≤1`, covers `{|u₁|≲|u₀|}`, Jacobian gains `du₁ = u₀ dτ`, i.e. `+1`) AND the
  reciprocal `u₀ = u₁·σ` (`0≤σ≤1`, covers `{|u₀|≲|u₁|}`). Both give the same threshold `½minAdm` (verified,
  `/tmp/prodD/corner75.py`); a single chart covers only half the corner.
- **Charges ADD on the coupled corner:** measure `∏|u_i|^{p_i}(∑u_i²U_i)^{−c'}` converges ⟺ `c' < ½Σ(p_i+1)`,
  `Σ(p_i+1)=Σ(block dims)=minAdm`; the units `U_i>0` bounded below on the generic chart (recurse where a unit
  vanishes — that is the deeper pivot-vanishing critical divisor, `p=0`).

---

## Firmest / most-likely-to-break / next

- **Firmest.** CERTIFIED no-obstruction for `(3,3,3,4)` and `(4,4,4,4)`: no ray `< ½minAdm` (exact combined-ray
  formula + `p=0` transversality on the critical divisor, both hand-verified). The load-bearing datum is
  `p=ν(H₁)=0`; `q` is harmless; the residual is `H₁^{−3}(H₁+H₂)^{−1}`.
- **Most likely to break.** A width where the critical reduced divisor is NOT pivot-vanishing-with-generic-Z
  but forces the corank block to co-vanish (`p>0`) — this would be a genuine obstruction (`λ<½minAdm`), and
  by Codex's formula it is EXACTLY detectable. It does not occur at the anchors' top level (verified) and is
  Aoyagi-excluded, but the Aoyagi-INDEPENDENT width-general proof is the recursion of `p=0` (the decorated
  IH's invariant). This is the precise thing the formaliser must maintain.
- **Next.** Hand the decorated-IH build (genm-sj5-descent) the invariant `p=0` (transversality) + the
  corrected residual `H₁^{−3}(H₁+H₂)^{−1}` + the gap-(iii) sectors (§5). If a fully width-general
  Aoyagi-independent certificate is wanted, the residual is the recursion of the `p=0` transversality lemma at
  each peel level (a clean geometric statement: current corank block transverse to the deeper pivot
  degeneration), which I can scope next.
