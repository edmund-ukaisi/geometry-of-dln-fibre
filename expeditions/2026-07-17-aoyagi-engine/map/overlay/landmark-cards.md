# Overlay — landmark cards (cartographer, curated layer) — the A–E frame

*RE-ROOTED 2026-07-21 (re-root #1, tip 70a8ec6cf). One card per carried landmark (9, proposed in
`claims.yaml.proposed` — elder proposes / controller sets the field). The chart-era cards (8: mint,
hbox, engine-route, resolution-tree, coverage, ledger-bridge, theorem4, rr4) are ARCHIVED at
[[archive/landmark-cards-chart-era]]; their node-id dispositions are in [[naming]]. "True state"
verified against the live Lean tree, not the log.*

---

## 1. `aoyagi-summit` — the corollary/test (root; `stated`)

**What.** `rlctGlobal (lossDLN d 0) = cCodim/2` for monotone positive-width `d`, `0 < N` — the
value DERIVED via A∘B∘C∘D, NO Aoyagi cite invoked. Charter §0: a corollary and a test, NOT the
objective (steering by it produced the drift, twice).

**True status.** `aoyagi_learning_coefficient_via_engine` (`LearningCoefficient.lean:299`): proof
COMPOSED and kernel-checked; `#print axioms` (AxCheck:1358, informational) = clean-three
**+ sorryAx from exactly `exists_coreResolution`**. Flips clean-three the day object-b lands —
no wiring owed.

**Why a landmark.** The map's root; the kill-path (cites not invoked) is the destination's
definition of done made visible on every build.

## 2. `object-a` — ideal-RLCT invariance (PROVEN)

**What.** Aoyagi Lemma 1 at full generality, two-sided + weighted: germ-equal generated ideals
give equal `rlctAt`/`wrlctAt`. Category-NEW (Mathlib-absent); legalises every ideal-preserving
step; the missing half of every lower bound.

**True status.** Sorry-free, batch-gated (8 decls, [[banked-families]] § OBJECT A). Landed as
locked — the statement-lock discipline's first full test.

**Traps.** Measurability hypotheses are load-bearing (`hWmeas`; the C-delta `Measurable unit` is
the same class); `LocallyNullZeros` is the junk-0 guard — do not weaken.

## 3. `object-b` — the resolution atlas (THE frontier; `stated`, ONE sorry)

**What.** `∃ res : Resolution (coreGen d e) 0, AtlasRealizesExponents d res` — the coupled
corank≥2 ideal-route atlas: analytic `g`, two-sided dom-wide `⟨∏C⟩=⟨diag(b)⟩`, Jacobian
certificate, hcover BUILD. The charter's named mountain (§1.B: never scoped out).

**True status.** The library's ONE sorry (`LearningCoefficient.lean:287`). Combinatorial half
DISCHARGED (salvage adapter) — the residual is purely geometric and STRICTLY weaker than the
original leaf (rev-monument-adapter escalation). Ladder: leaf-2 LANDED → rung (B) d12 IN FLIGHT
(seat-d12) → 8-leaf skeleton queued; leaves 3–5 = the wall. Multi-tide monument (~5% single-tide,
mon-geo + decorrelated codex).

**Witnesses.** `g-coupled-binding-334` (coupling real), `g-delta-flatten` (flatten breaks),
thread-31 certificate (the MATH playbook; Lean pricing superseded), thread-33 shear pin
(g = shears ∘ blow-ups; unit ≡ 1 stands).

## 4. `object-c` — the guarded S2 boxed rule (PROVEN)

**What.** Monomial-ideal RLCT under `DivChain` + `Measurable unit`:
`wrlctAt = min (h+1)/(2k)`, DLN form `2·wrlctAt = min (h+1)`. Object C's genuine analytic pole.

**True status.** All 3 leaves sorry-free, batch-gated. GUARDED form — `not_divChain_coupled_example`
is the honest boundary; the charter's "full generality" residual rides B (name = content).

## 5. `object-d` — the codimension chain (PROVEN/banked)

**What.** `minAdm = cCodim = qipMin`, θ, permutation-invariance — the combinatorial read-off.

**True status.** Banked pre-phase (Core, axiom-clean) + dev's cite-free determinantal geometry +
the adapter's `qipMin_eq_minAdm`. Guards: `g-minadm-groundtruth`, `g-def3-broken` (Def-3 typo:
use the geometric `½·min Mval`).

## 6. `b-value-cov` — monument 1: the atlas CoV + value chain (PROVEN)

**What.** `rlctAt(∑Fᵢ²) = ⨅ charts` (InjOn-off-null area formula ∘ off-origin C ∘ compact
subcover) composing to `2·rlctAt = divisorMin = cCodim`.

**True status.** Clean-three, batch-gated; rev-cov-fidelity PASS. The value chain takes `res` +
min-attainment as HYPOTHESES — it never touches the existence monument, so it cannot be gamed by
a false atlas. Fidelity nuance (docstring, landed): the amplitude/prior φ is folded into
unit/hjac (`hunit_ne`), the standard SLT `φ(w*) > 0` setting.

## 7. `b-leaf2-blowup-atlas` — the universal origin blow-up (PROVEN; the shared atom)

**What.** `blowupResolution (hD : 2 ≤ D) : Resolution (coordFam D) 0` — max-pivot atlas,
universal Jacobian `(w i)^(D−1)`, exact argmax sector cover.

**True status.** Clean-three; every Chart field discharged. Universal-in-D dissolves the
opaque-width cast wall BY DESIGN (instantiates at `flatDim d`, no transport). The atom for BOTH
rung (B) and the monument's per-step geometry. D=2 cousins carry `…2` names ([[naming]]).

## 8. `corollary-reduction` — the reduction to the core (PROVEN)

**What.** `rlctGlobal (lossDLN d 0) = rlctAt (∑ coreGenᵢ²) 0`: linear m.p. flatten + Frobenius
identity + deepest-point/homogeneity transport.

**True status.** Clean-three, batch-gated (3 decls). Reusable spillover: `GlobalHomog.lean`
(network-generic global=local-at-0 for homogeneous losses). The `he_lin` guard on the monument is
REQUIRED there and correctly ABSENT here (elder-verified end-to-end).

## 9. `kill-cite` — delete `cited_aoyagi_lower_ax` (queued at close)

**What.** The charter §3 kill-target: the one in-library Aoyagi-value cite, to be PROVEN via
A+B+C and DELETED. `cited_watanabe_upper_ax` is a separate proof-target CANDIDATE (not
settled-external); `cited_local_zeta_pole` off-path.

**True status.** The summit already avoids it (kill-path asserted every build). Deletion waits on
object-b + a consumer audit (`AoyagiCited.lean:67`); a cite-free endpoint is the operator-confirmed
definition of done — any weakening is a DoD change (wait-for-explicit-go).
