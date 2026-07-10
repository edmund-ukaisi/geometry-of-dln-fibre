# Fidelity card — Aoyagi Case-2 exponent: the printed divergence is IMMATERIAL to `(□)`

**Status:** PROVED (vslice pen-and-paper `threads/genm-vslice/case2-cert.md` + Codex xhigh decorrelated
concurrence, 2026-07-10). **Case-2 never binds `(□)`; coarse suffices; NO sharp Case-2 machinery is
needed.** This card is the honest, named account of the printed-paper Case-2 discrepancy — a framing
REVERSAL of the earlier "printed is wrong, prefix-min is the correction" read (which was itself a
misread; see "real pitfall" below).

## The finding
`minAdm(M) ≤ M(S)·M^{(S+1)} ≤ M^{(S)}·M^{(S+1)}` for all `S` (PROVED; the admissible prefix-min-pivot
branch has `Mval = M(S)·M^{(S+1)}`; cross-checked 0/35424 counterexamples, widths ≤ 6). Since both the
printed (actual-width, telescoping to `M^{(S)}M^{(S+1)}`) and the prefix-min forms are `≥ minAdm`,
**neither is "wrong" for finiteness** — Case-2 never binds the `⨅`, and it is SUBSUMED by the `minAdm`
accounting (`minAdmRec_eq_minAdm`). The de-risk `2λ ≤ M^{(i)}M^{(j)}` is confirmed exactly. Worked
binding chain where the divergence bites: `M=(2,4,4)`, `M(2)=2 < M^{(2)}=4`, printed `16` vs prefix-min
`8`, both `≥ minAdm=7` (binder is rank-1 `t=(1,0)`).

## Fidelity-card wording (drop-in, from case2-cert §6)
*"Aoyagi's Case-2 divisor exponent is stated with prefix-min block rows `(M(S)−J)(M^{(S+1)}−J)` (p.20)
and an actual-width pivot vector `t^{(i)}=M^{(i+1)}` whose terminal `Mval` telescopes to
`M^{(S)}M^{(S+1)}` (p.22); the two differ by `(M^{(S)}−M(S))(M^{(S+1)}−J)` where the prefix-min `M(S)`
collapses to the actual `M^{(S)}` under plaintext extraction. This is immaterial to our result: both
forms are `≥ minAdm` (PROVED), so Case-2 never binds and is subsumed by the `minAdm` accounting. We do
not reproduce the (unsound) prefix-min column-correction."*

## The REAL pitfall to AVOID (proven, matches lessons.md)
The prior expedition's buggy "prefix-min fix" mixed **prefix-min columns in `Mval`** with an
**actual-width pivot** → NEGATIVE exponents (e.g. `M=(2,5,4,7)`, `S=3` → `−2`). That mixed form is
internally inconsistent + was an `+8.7K`-line treadmill. **Do NOT reproduce it.** The
`(n_S−μ_S)(n_{S+1}−J)` "discrepancy" the captured pitfall note flagged is a HARMLESS overcount, not a
bug to fix.

## Caveat (scope)
This is about `(□)` / the RLCT VALUE `λ`, which needs only `≥ minAdm` (coarse). The θ / MULTIPLICITY
(tie-counting) side WOULD make the sharp Case-2 form load-bearing — but θ is the secondary deliverable
(the deferred analytic-multiplicity seam, `cards/theta-analytic-multiplicity-seam.md`) and `(□)` does
not need it. So: build coarse for `(□)`; the sharp Case-2 exponent is only ever a θ concern.
