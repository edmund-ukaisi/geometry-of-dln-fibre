# Lane-2 witness battery — prodcorank discriminators as executable kill-conditions

**Seat:** pen-and-paper, aoyagi-full `genm-l2witness` (WITNESS). **Date:** 2026-07-17.
**NO Lean.** Exact algebra only (sympy Groebner over QQ + exact-integer DP + exact rational
arithmetic; the normal-map / coker ranks are computed with `sympy.Matrix.rank()` over QQ, NOT
float `numpy` ranks). Each script self-checks with `assert` and exits nonzero on any regression.

## What this battery is

The controller requires — before Lane 2's native-engine design pass — that the `genm-prodcorank`
discriminators (the four proved lines that established the **min-corank >= 2 wall**) be deposited as
**executable battery witnesses**: the kill-conditions the native resolution engine must satisfy,
as runnable exhibits, not prose. Source cert:
`../../genm-prodcorank/prodcorank-cert.md` (cross-read `../../genm-decstep/decstep-cert.md` §2-3
for the residual-class / binding-cut structure).

Each witness is runnable, checked in **with its captured output** (`*.out`), and carries a header
naming its discriminator, the engine kill-condition it guards, the exact instrument, and the
expected result.

## The three witnesses

| # | Script | Discriminator | Exact instrument |
|---|--------|---------------|------------------|
| W1 | `w1_joint_center_survival.py` | JOINT-CENTER SURVIVAL: single-factor resolution does NOT principalize the product ideal | sympy Groebner over QQ |
| W2 | `w2_codim_undershoot_family.py` | CODIM-UNDERSHOOT FAMILY: true codim `C_m = m^2 - floor(m^2/4)` vs naive `m^2`, gap `floor(m^2/4)` | exact-int min + sympy exact rank over QQ |
| W3 | `w3_tightness_at_binding_cell.py` | TIGHTNESS AT BINDING CELL: budget inequalities meet `c*` with EQUALITY at the binding cell | exact-int DP + `fractions.Fraction` |

Run all three (each prints `... PASS: True` and exits 0):

    python3 w1_joint_center_survival.py
    python3 w2_codim_undershoot_family.py
    python3 w3_tightness_at_binding_cell.py

## Witness -> engine kill-condition map

### W1 — JOINT-CENTER SURVIVAL  (guards: no single-factor closure of min-corank >= 2)

- **Exhibit.** At the minimal failure `n=2, k=2`, in the balanced chart
  `P = [[1,0],[0,x]]`, `Z = [[y+bc, b],[c,1]]`:
  - `I(P*Z) = (x, y, b)` (both containments, reduced Groebner bases).
  - the two single-factor rank divisors are `det P = x`, `det Z = y`.
  - **THE KILL:** the alignment coordinate `b` is **NOT** in `(det P, det Z) = (x, y)`
    (`b` reduces to `b != 0` mod the Groebner basis `[x, y]`). So `(x,y,b)` strictly contains the
    ideal cut out by the single-factor divisors — `b` is genuinely new data.
  - `(x,y,b)` is a smooth codim-3 (`= C_2`) complete intersection (Jacobian rank 3).
- **Engine kill-condition guarded.** The native engine MUST NOT claim to close the
  min-corank >= 2 product-corank atom by any finite sequence of **single-factor** (per-matrix
  rank-drop) blow-ups. If a peel ships single-factor radial / pivot-Gram blow-ups asserting
  min-corank >= 2 is principalized, W1 fires: the joint center `(x,y,b)` with its alignment
  coordinate `b` survives. min-corank >= 2 is the **cited** boundary, native ABOVE it.

### W2 — CODIM-UNDERSHOOT FAMILY  (guards: do not conflate `m^2` and `C_m` on the balanced locus)

- **Exhibit.** For headline `n=4..7` (robustness `n=2..8`) and each `m`:
  - true minimal codim of `{rank(P*Z) <= n-m}` `= C_m = m^2 - floor(m^2/4)`, minimiser
    `(a,c,e)` balanced;
  - undershoot gap `m^2 - C_m = floor(m^2/4) = a*c = dim coker(d mu)` (exact non-submersiveness);
  - **EXACT** (sympy over QQ) normal-map rank at an explicit rational `n=4,m=2` balanced point
    `= 3 = C_2` (not the transverse `4`); EXACT `coker(d mu)` dim at `n=4,m=4` `= 4 = 4^2 - C_4`.
- **Engine kill-condition guarded.** The engine must not conflate the two codim accountings on
  the balanced (min-corank >= 2) component: the FREE-block / submersive discrepancy is `m^2`
  (valid only where the pullback is transverse, i.e. min-corank <= 1); the VARIETY codim is
  `C_m < m^2`. Charging `m^2` as the discrepancy at a non-transverse cut, or using `C_m` as if the
  joint center split off a free reduced chain, is unsound. W2 exhibits the exact gap that
  separates them, member by member.

### W3 — TIGHTNESS AT BINDING CELL  (guards: every carried inequality is tight, no slack)

Per the **operator rule**: any inequality-shaped condition the engine will carry gets an
EQUALITY-AT-BINDING-CELL witness, not only a truth scan. W3 supplies the equality certificate
(exact `Fraction`) for every budget inequality the engine carries, plus the paired
strict-undershoot that marks the INVALID accounting.

- **(A) master peel budget** `minAdm(M) = min_t [peelCharge(M,t) + minAdm(redChain t M)]` —
  EQUALITY at the argmin (binding) cut(s), STRICT above off them. This is the tightness at every
  peel node. Binding cut `t*` and corank `m* = n - t*` reported per `n`.
- **(B) free-block outer peel** `T_m = 1/2 m^2 + 1/2 minAdm((n-m,n,n)) >= c*` — EQUALITY exactly at
  the binding corank `m*`, STRICT above off it. (This is (A)'s top peel with `m = n - t`; the
  native engine's budget.)
- **(C) balanced product-corank threshold** `T_k = 1/2 (C_k + n(n-k)) >= c*` — EQUALITY exactly at
  the binding stratum `k*`, STRICT above off it. This is decstep's `(C_k + n*r')/2` identity with
  `r' = n-k`; `min_k[C_k + n(n-k)] = minAdm(n,n,n,n)` exactly (reproduces decstep's reported
  `k* = 2,2,3,4,...`).
- **(D) GUARD — the invalid split.** Pairing the TRUE product codim `C_m` with an independent
  RECURSIVE reduced chain, `T_m = 1/2 C_m + 1/2 minAdm((n-m,n,n))`, **strictly UNDERSHOOTS** `c*`
  for every `n>=4` (deficits reported per stratum). The engine must NOT use this pairing — it is a
  fiction on the balanced locus (the joint center does not detach from the reduced chain).
- **Engine kill-condition guarded.** There is no slack at the binding cut: a peel that loses even
  `delta` of budget there breaks `c*`. Any accounting that undershoots (D) or that would make the
  binding-cell inequality strict is invalid.

## Reading the three together (the wall boundary)

- **W3 (tightness):** the budget inequality `>= c*` is exactly tight at the binding cell (equality,
  no slack). This tightness is what the native peel achieves at min-corank <= 1.
- **W2 (undershoot):** at min-corank >= 2 the variety codim `C_m` undershoots the naive `m^2` charge
  by `floor(m^2/4) = coker(d mu)`. So the `m^2` charge is not the true discrepancy there; the
  naive budget's tightness rests on a transversality that fails on the balanced component.
- **W1 (joint-center survival):** the reason — single-factor blow-ups leave a smooth codim-`C_k`
  joint center with an alignment coordinate `b` outside the single-factor divisor ideal. The engine
  cannot natively principalize at min-corank >= 2; it must cite (Aoyagi product-corank /
  joint-resolution finiteness).

## Levels kept apart

- **Quiver/orbit:** untouched; `minAdm` / `redChain` / `peelCharge` consumed as exact-integer DP.
- **Codim `(C, theta)`:** `C_m`, the gap `floor(m^2/4)`, the `a*c` coker identity, and all budget
  sums are exact facts of the varieties / the integer program (sympy / Groebner / exact-rank /
  Fraction verified).
- **RLCT cap:** these witnesses are at the codim / budget levels. They do NOT re-derive
  `rlct = 1/2 codim`; the min-corank >= 2 product-corank FINITENESS is the CITED step (Aoyagi). The
  witnesses mark WHERE the native accounting is valid vs where it must cite — they do not lift to
  the RLCT level.

## Decorrelated Codex sanity-check

`codex/battery-{prompt,answer}.md`, `battery-run.log` — an independent gpt-5.x (xhigh) recompute of
Q1 (product-corank codim), Q2 (the `n=2` joint ideal + single-factor membership), Q3 (the three
integer-program minima), with my conclusion WITHHELD. See `codex/README.md` for the outcome and how
it corroborates / diverges from the exhibits.

## Files

- `w1_joint_center_survival.py` + `w1_joint_center_survival.out`
- `w2_codim_undershoot_family.py` + `w2_codim_undershoot_family.out`
- `w3_tightness_at_binding_cell.py` + `w3_tightness_at_binding_cell.out`
- `index.md` (this file)
- `codex/battery-prompt.md`, `codex/battery-answer.md`, `codex/battery-run.log`, `codex/README.md`
