# Thread 02 — Direct (corner-pair) route: findings

> Homed by the controller from `probe-direct`'s report (pen-and-paper seat hit the harness `.md`-write
> block). Scratch enumerator + Codex prompt committed at `3643ba8`. Claims exact-arithmetic verified.

**VERDICT: OBSTRUCTED as a *shorter* route.** Both direct attack vectors collapse to the same hard
statement `cCodim d 0 = cCodim (sort d) 0`, and the only direct proof is a GLOBAL min-level swap map whose
best-case edit radius grows LINEARLY with `|d|` (exact-verified). That is ≥ the size of the LANDED
`CCodimZeroMono`/`CCodimZeroStrict` tides (~2500 LoC, same global-optimization shape) and is the open
direct-bijection form the authors lack. The q-series route (thread 03) is the better formalisation target.

## (1) Corner-pair → symmetric form: PARTIAL, no crack
Corner-pair rigidity confirmed for ALL d (306/306 pairs, incl. non-monotone — extends the strict-cert's
full-coverage 256521 off that restriction). But `(C,θ)(d) = ClosedForm(sort d)` exactly (117/117) only
gives the VALUE — the closed form is proven monotone-only, so applying it to non-monotone `d` still needs
`C(d) = C(sort d)`. Minimisers of permuted `d` are genuinely different lace configs; the QIP objective is
order-dependent (shifts `[1,3,2]→[-2,-1]` vs sorted `[-1,-2]`) and its symmetry is circular per the paper.

## (2) Min-level adjacent-swap map: OBSTRUCTED (load-bearing)
Vertex-relabel transport breaks intervals (cover `{0,1}` under `swap_1` → `{0,2}`, not an interval).
Best-case edit radius (min over all minimiser pairs — closest a map could stay): `d=[1,2,…,L]` swap col 0
→ radius `L−2`; LINEAR in `|d|`. So any `C(d)=C(swap d)` map is global, not local surgery. Decorrelated
Codex (high-effort, exceeded budget mid-trace) independently flagged the same trap; endpoint then
unresponsive — rested on exact algebra per role.

## (3) Size
Direct ≥ mono/strict pair (~2500 LoC, 4–6 files), NEW research. q-series PEEL ~6–8 files / 1.5–3wk,
published math (RWY 2018), clean L1 extraction. → **q-series.**

## CLEAN POSITIVE (landable bedrock regardless)
Order-reversal `[a,b]↦[N−b,N−a]` is a codimForm-PRESERVING Kostant bijection (441/441, 0 form changes) ⟹
`(C,θ)(d) = (C,θ)(reverse d)`, ~1 file zero-cited. Order-2 only — not perm-invariance.

## RESIDUAL GAP (the one thing that could overturn the verdict)
Did NOT prove non-existence of a non-surgical AGGREGATE monovariant for `C(d) ≤ C(sort d)` (an inequality
on the minimum itself, not on partitions). Found none and the QIP route is circular, but if anyone wants
to push the direct route, that aggregate-inequality search (not more local surgery) is the only move left.
