# genm-vsastruct — DecoratedPeelStep instance cert (T4 well-posedness pre-build)

**Seat:** pen-and-paper (obstruction-adversarial). **Date:** 2026-07-11. **NO Lean.** **Scope:** ONE
decorated peel of the smallest genuine bottleneck(s); adjudicate T4 well-posedness before the formaliser
is commissioned. **Exact algebra:** `/tmp/dps_coupling.py` (coupling-Jacobian abscissa, MC-guided).
**Decorrelated:** `codex/dps-{prompt,answer}.md` (gpt-5.6, xhigh; my conclusion withheld — it CONFIRMED
every point term-for-term and supplied the Q3 counterexample + the exact scaling test). Reads:
`recon-map.md` (banked file:lines), `RouteMSJFreedPeel.lean:114`, `RouteMSJCorankPeel.lean:114`,
`RouteMSJDecoratedRec.lean:78`, `RouteMSJDecoratedCharge.lean`. Companion: `corank2-cert.md` (its
asymmetry finding is the same phenomenon, now located at the peel's shared rank-drop divisor).

---

## ONE-LINE VERDICT

**T4 is NOT well-posed as "regime A/B holds a.e. in A' + the PLAIN box IH closes it".** The banked corank
atom emits a PERSISTENT scalar coupling `det(Q_bQ_bᵀ)^{−a/2}` that is a GENUINE EXTRA weight — decisive
scaling test `Q_b = εR ⟹ det(Q_bQ_bᵀ)^{−a/2} = ε^{−ab}·(…) → ∞` while the reduced core stays fixed, so
the atom output is neither `=` nor `≤` the plain redChain-box integrand (my numeric: the coupling's own
integrability abscissa is `≈0.88 < 1 = a/2`, so `det^{−a/2}` is not even integrable ALONE). The plain box
IH of `DecoratedPeelStep` therefore CANNOT close the outer `∫_{A'}`; an **anisotropic carrier tracking the
shared rank-drop divisor** (a decorated/rank-stratified IH) is required — the genuinely-new "(S,J) double
induction". It is NOT a hard wall (the true integral is finite at 7/2, three ways), and it is buildable —
but as the decorated double-induction, NOT as a single peel onto the plain IH. **The soundness watch-point
(d) is the load-bearing crux: the det valuation and the reduced loss SHARE the deeper rank-drop divisor;
the correct resolution ADDS their Jacobian charges along it (→ 7/2), a scalar-independent split takes the
MIN (→ the RLCT-collapse caricature). And (Q3, NEW): the `c'=ab/2` log-borderline is NOT always interior —
it coincides with `½·minAdm` at `M=(4,4,2,2), t=2` — so the peel MUST use the binding (minimising) cut.**

---

## 0. The instance and the peel (verified against live code)

Take `M = (3,3,3,4)` (4 nodes, the vslice), binding cut `t = 1` (`minAdm = 7 = peelCharge + minAdm(redChain)`,
vslice-cert §6). Then `a = M₀−t = 2` (corank rows), `b = M₁−t = 2` (corank cols), `peelCharge = ab = 4`,
`p = a = 2`. The deep factor `Q = prod(tailChain M) A' = A₁·A₂` (`3×4`, a genuine PRODUCT); `Q_b` = its
`b=2` corank rows (`2×4`), `Q_p` = its `t=1` pivot row. The peel (banked
`gammaPeelIntegral_schurShearFree_eq`): `∫_{A'}∫_x∫_Γ (freedSchurLoss x Γ Q)^{−c'}`,
`freedSchurLoss = frobSq(P·Q̃ₚ) + frobSq(C·Q̃ₚ + Γ·Q_b)`, `Q̃ₚ = Q_p + P⁻¹B₁₂Q_b`. The banked atom
(`corankBlock_morsePeel`, `freedSchurLoss_inner_peel_lt_top`) integrates the inner `Γ` for `c' > ab/2`,
`Q_bQ_bᵀ` PosDef:

> `∫_Γ (freedSchurLoss)^{−c'} dΓ = det(Q_bQ_bᵀ)^{−a/2}·C(ab)·(w + ‖A·Q̃ₚ‖² + ‖C·Q̃ₚ(I−Π)‖²)^{−(c'−ab/2)}`,
> `w = frobSq(P·Q̃ₚ)`, `Π = Q_bᵀ(Q_bQ_bᵀ)⁻¹Q_b`.

The intended finish: this reduced integrand, over `A'`, lands on `redChain 1 M` at exponent `c'−ab/2 <
½·minAdm(redChain 1 M)`, closed by the PLAIN box IH. The soundness watch-point is the shared deep factor
`Q = A₁·A₂` and its rank-drop.

## 1. (a) hG/hpiv "producible a.e. in A'" — TRUE but necessary-not-sufficient

`hpiv` (`w = frobSq(P·Q̃ₚ) > 0`) fails on `{Q̃ₚ = 0}` (proper subvariety); `hG` (`Q_bQ_bᵀ` PosDef) fails
on `{rank Q_b < b}` (the deep-product rank-drop). Both hold for **a.e. A' (Lebesgue)** — the failure loci
are measure-zero. **But a.e. is NOT sufficient for the outer `∫_{A'}` to be finite** (Codex Q2, confirmed):
the atom output is UNBOUNDED near those null loci (`det(Q_bQ_bᵀ)^{−a/2} → ∞`), and "finite a.e. + unbounded
near a null set" is the `|u|^{−1}` non-integrability model. So the well-posedness content is NOT the a.e.
conditions — it is whether the outer integral of the (blowing-up) atom output converges. [FACT.]

## 2. (b)+(Q3) regime choice — well-defined, BUT the borderline is NOT always interior (correction)

Regime A (`c' > ab/2`, `corankBlock_morsePeel`) vs regime B (`c' ≤ ab/2`, `freedSchurLoss_inner_bounded`,
bounded via `hpiv`) is a well-defined dichotomy in `c'` (both branches banked). **CORRECTION (Codex Q3,
decorrelated counterexample):** `c'<½·minAdm(M)` does NOT in general force `c'` off the borderline
`c'=ab/2`. At `M=(4,4,2,2)`, cut `t=2`: `ab=(4−2)² = 4`, `minAdm(M)=4`, `minAdm(2,2,2)=3`, so
`ab/2 = 2 = ½·minAdm(M)` — the log-borderline **coincides with the final threshold**. The borderline is
strictly interior ONLY on the binding (minimising) cut, where `minAdm M = ab + minAdm(redChain)` with
`minAdm(redChain) ≥ 1` forces `minAdm M > ab`. **⟹ The peel MUST select the binding cut `u★`
(`exists_binding_cut`), not an arbitrary legal cut** — else the `c'=ab/2` log-hole sits exactly at the
claimed threshold. (For `(3,3,3,4)` the binding cut `t=1` has `ab/2 = 2 < 7/2` — interior — so the vslice
instance is safe; the correction is a width-general guard.) [FACT — Codex counterexample verified:
`minAdm(4,4,2,2)=4`, `minAdm(2,2,2)=3`.]

## 3. (c) the threshold shift — BANKED and tight at the binding cut

`carrierThreshold M − ½·peelCharge M u ≤ carrierThreshold(redChain u M)` is BANKED
(`carrierThreshold_shift`, cast of `minAdm_le_peelCharge_add_redChain`, exact `0/171`), and TIGHT at the
binding cut (`exists_binding_cut`: equality). So `c' < ½·minAdm(M) ⟹ c'−ab/2 < ½·minAdm(redChain u★ M)`,
STRICT. The reduced exponent lands strictly below the reduced threshold — the IH's strict inequality is
available. [FACT — banked; not a gap.] (For `(3,3,3,4)` t=1: `c'−2 < 3/2 = ½·minAdm(redChain)` for
`c'<7/2`.)

## 4. (Q1) THE COUPLING IS NOT ABSORBED — the det is a genuine extra weight

The reduced integrand carries `det(Q_bQ_bᵀ)^{−a/2}`, a PERSISTENT weight in `A'`. For the plain redChain
IH to close, this must be `≤` (or `=`) the plain redChain-box integrand. **It is not.** [FACT — Codex Q1,
decisive scaling test:] fix `Q̃ₚ = Z ≠ 0`, `B₁₂ = 0`, and scale the coupling `Q_b = εR` (`rank R = b`).
Then `Π` and the bracketed loss `(w + ‖A·Q̃ₚ‖² + ‖C·Q̃ₚ(I−Π)‖²)` are FIXED (they depend on `Z`, not the
scale of `Q_b`), while

> `det(Q_bQ_bᵀ)^{−a/2} = ε^{−ab}·det(RRᵀ)^{−a/2} → ∞`.

So the atom output → ∞ while the plain reduced-chain integrand stays fixed: **no uniform domination, no
equality.** The `det` is the `Γ ↦ Γ·Q_b` induced-volume Jacobian (`dΓ = det(Q_bQ_bᵀ)^{−a/2} dY`) — but it
REMAINS after the `Γ`-integration; when `q > b` (`q=4 > b=2` here) the map is a PROJECTION (image `Π`), not
a bijection onto `ℝ^{a×q}`, so the det is not cancelled by a reconstruction. The unit-Jacobian triangular
`Q_p ↦ Q̃ₚ` cannot cancel it either. **Numeric corroboration** (`dps_coupling.py`): the coupling's own
integrability abscissa over the `(A₁,A₂)` box is `≈ 0.88 < 1 = a/2` — `det(Q_bQ_bᵀ)^{−a/2}` is not even
integrable ALONE; its finiteness is inseparable from the reduced core's behaviour near `{rank Q_b < b}`.
**⟹ the plain box IH of `DecoratedPeelStep` cannot close the outer integral.** The minimal missing result
is the JOINT weighted finiteness `∫ det(Q_bQ_bᵀ)^{−a/2}·H(A',x)^{−(c'−ab/2)} dA' dx < ∞`, or an equivalent
rank-stratified / uniformly-truncated estimate — an ANISOTROPIC statement the scalar redChain IH does not
provide.

## 5. ★ (d) THE SOUNDNESS WATCH-POINT — charges ADD along the shared divisor, never MIN

`det(Q_bQ_bᵀ)^{−a/2}` (blows up on `{rank Q_b < b}`) and the reduced loss `H^{−(c'−ab/2)}` (its own deeper
rank-drop) **SHARE the same deeper rank-drop divisor** (the A₂-rank-drop, sub-locus of `{rank Q_b < b}`).
[FACT — Codex Q2, exact.] The correct resolution **ADDS their Jacobian valuation charges along that shared
divisor** — this is the coupled corner (`u₀²U₀ + u₁²U₁`, charges `3+2+1 = 6` add → `7/2`; corank2-cert §1,
vslice §5). **A scalar-independent split — treating the det valuation and the reduced loss as two
independent branches — replaces the coupled ADDITION by a MINIMUM**, giving the `z²(x²+y²)` RLCT-collapse
caricature (→ `3/2`, the undershoot). This is EXACTLY the "units `U₀,U₁` bounded below on the generic-A₂
chart" brick: it holds only when the A₂-rank-drop is split OFF to a higher-Mval (higher-codim) branch. If
the a.e.-framing silently lets A₂ degenerate INSIDE the cell (treating `{rank Q_b<b}` as "null, ignore"),
the shared-divisor charges are mis-split and the threshold collapses — textbook conceptual slop. **Dropping
the det entirely OVER-claims finiteness** (the other failure mode). So (d) requires an EXPLICIT stratified
handling: the A₂-rank-drop tube is resolved (not ignored) by adding its charge, via one of
  (i) a higher-rank-drop / higher-Mval stratum analysis (a deeper peel on the shared divisor),
  (ii) a strengthened anisotropic IH retaining the det/minor weight, or
  (iii) a uniformly-truncated atom whose estimate saturates as `Q_b` degenerates.
[FACT+INFERENCE — Codex Q2, matching corank2-cert §1 + vslice §5.]

## 6. VERDICT — T4 is BUILDABLE but NOT as "a.e. + plain IH"; the anisotropic carrier is required

**Well-posedness answer:** the atom's HYPOTHESES (`hG`/`hpiv`) ARE what the resolution supplies at a
generic `A'` (a.e.), so the atom is APPLICABLE a.e. — but the atom's OUTPUT (the scalar `det(Q_bQ_bᵀ)^{−a/2}`
coupling) is NOT what the plain box IH can absorb (§4), so `DecoratedPeelStep` as stated (single peel →
plain box IH of `redChain`) is **not provable by the banked atom alone.** The `DecoratedBoxThresholdFinite`
predicate + `SJDecoration` carrier already ANTICIPATE this — the decoration is the anisotropic carrier — but
the single-peel-to-**plain**-IH reduction (`decoratedPeelStep_imp_sjStepHyp` feeds the plain
`RouteMBoxThresholdFinite` IH) is the mismatch: a 4-node peel lands on a 3-node DECORATED (det-weighted)
integral, which the plain 3-node box IH does not cover. **The build must either (A) strengthen the
inductive predicate so the IH is the DECORATED finiteness (carry the accumulated det/minor weight through
the recursion — the honest "double induction"), or (B) prove the joint weighted finiteness (§4) as a
new anisotropic lemma discharging the shared-divisor charge-addition (§5).** This is the ~65–75%
genuinely-new content every prior pass flagged — confirmed, and now LOCATED precisely: the coupling
`det(Q_bQ_bᵀ)^{−a/2}` absorption via the shared rank-drop divisor, with charges ADDED (not min).

**Not a hard wall:** the true integral is finite at `7/2` (corank2-cert, three ways; vslice §5 corner). The
obstruction is that the CURRENT `DecoratedPeelStep` statement routes through the plain IH, which is too weak.

### Firmest / most-likely-to-break / next
- **Firmest.** (§4) `det(Q_bQ_bᵀ)^{−a/2}` is a genuine extra weight (scaling test `ε^{−ab}` + abscissa
  `0.88<1`), NOT absorbed by the plain IH; decorrelated-confirmed. (§3) the threshold shift is banked +
  tight. (§5) the shared-divisor charges must ADD; a scalar split gives the min-caricature collapse.
- **Most likely to break the build.** (d) the A₂-rank-drop split. The banked atom is a SCALAR-det weight;
  if the build applies it a.e. and hands the det to the plain IH, it either (i) can't close (§4) or (ii)
  silently mis-splits the shared divisor and RLCT-collapses (§5). The fix — an anisotropic/decorated IH —
  is the unbuilt double induction, not bounded labour on the banked atom. Secondary: (Q3) a non-binding
  cut re-opens the `c'=ab/2` log-hole (`(4,4,2,2)` witness) — the build MUST use `exists_binding_cut`.
- **Next (the minimal settling build).** Prove the JOINT weighted finiteness for ONE peel of `(3,3,3,4)`
  at `t=1`: `∫_{A'} det(Q_bQ_bᵀ)^{−1}·H^{−(c'−2)} dA' < ∞` for `c'<7/2`, with the A₂-rank-drop tube
  resolved by ADDING the shared-divisor charge (NOT the plain redChain box IH). If that closes, the
  anisotropic-IH architecture is validated and T4 is buildable as the decorated double induction; if the
  charge-addition cannot be realised without the full decoration carried through the IH, the
  `DecoratedPeelStep` STATEMENT itself needs strengthening (plain IH → decorated IH) before the formaliser
  is commissioned.
