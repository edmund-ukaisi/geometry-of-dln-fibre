# Candidate carried-invariant strengthenings (seat-L4D) — INPUT TO THE ELDER, not baked

**Why a strengthening is forced.** The carried conjunct-1 (`Deg1SupportedSlot` MonumentAtlas:544-549) has
an `∃c` whose coefficients are constrained by CONTINUITY ONLY — no factoring. Two defects follow, both in
this one object (`FoldStepInvAt` under-transcribes Aoyagi's induction hypothesis):
- **form TOO WEAK** (11th catch): the case11 boost split needs the b-chain (extra-block coefficients carry
  the reused divisor's exceptional); Codex (banked `boostready-beta-feasibility-answer.md`, xhigh)
  confirmed NO-NEEDS-INDUCTION — `hslot` does not force it; counterexample `F(u)=u_q` for `q ∈ extraBlock`
  satisfies `hslot` but survives `center→0`.
- **support TOO TIGHT** (10th catch): the descended support `blockCoords(S+1)` fails to contain the
  faithful recoord's out-of-cap column on WIDE branches (see `capescape-def-confirm.md`).

Both keep the statement ∀e HONEST by CARRYING the b-chain (a hypothesis discharged at L5's canonFlatten
base + preserved), NEITHER derives it from an arbitrary-e root (chainCompat_holds's fatal flaw). The
consumption end (BoostSplit + `deg1SupportedOn_boostForm`/`_of_boostSplit`, Case1Wire) is BANKED clean-three;
so the genuinely-new statements are the birth-INTRODUCTION + per-step PRESERVATION obligations.

## FRAME PIN (load-bearing — the same class that hid the cap-escape)
`foldResid d e p j u` — VERIFIED frame direction: `foldResid(step p …) u = foldResid(parent)(M(u))` with
`M` the step map (MonumentAtlas:451-457); `foldG = pathMap(stepMapList)` composes the EARLIEST (root-ward)
step OUTERMOST (`foldG_eq_pathMap` + `pathMap_append`, MonumentAtlas:391-399). So **`u` is the DEEPEST /
node-`p` chart frame, PRE the path's shears**; the composition applies the shears (`blockShear φ = u+φu`,
PathAtoms:63) on the way DOWN to `coreGen` (root frame).

Consequence for the vanishing locus: the reused divisor's Schur-reduced exceptional (empirical, pnp table
65eec01f9: on (2,2,2,2) `e₂ = u_(0,1,1) − u_(0,1,0)·u_(0,0,1)`) is what `coreGen` READS at the birth-corner
slot — i.e. it lives in the near-root frame, formed by the (outermost) birth shear applied to the running
coords. **In `foldResid`'s argument (node chart) frame it is a COMBINATION `e₂(u)`, NOT the raw slot
`u(birth-corner)`.** So a vanishing clause written as `u(cornerToFlat(divBirthCoord k)) = 0` names the
WRONG locus (that is the root-frame single-coordinate reading); the correct locus is the Schur exceptional
expressed in the running chart frame, `e₂(u) = 0`. **AMENDMENT (controller): the vanishing locus is the
SCHUR pivot in the running chart frame.** Consequence to flag for the elder: because the factor is the
combination `e₂(u)` (not a bare coordinate `u_pv`), `deg1SupportedOn_boostForm` as banked (coordinate
pivot `u pv`) may need its pivot-factor generalised to a continuous `e₂(u)`, OR the boost stated in the
frame where `e₂` is a coordinate — the elder should pin which frame the ruled invariant lives in.

## FORM V — value / vanishing (MINIMAL; recommended)
Strengthen `Deg1SupportedSlot`'s `∃c` with a per-divisor vanishing: for each active divisor `k : Fin
s.numDiv` and each support coord `i` with `col(i) ≥ s.divTilde k`,
  `∀ u, e₂ₖ(u) = 0 → c_i u = 0`,   where `e₂ₖ(u)` = divisor `k`'s Schur-reduced exceptional in the running
  chart frame (a continuous combination; on the birth-corner + its cross-term; per the FRAME PIN — NOT the
  raw `u(cornerToFlat(divBirthCoord k))`).
- YIELDS the case11 boost split: at a case11 node reusing `f` (`divTilde f = runLen`), `center =
  {pivot}∪{col<runLen}`; at `center→0`, `e₂_f = 0` ⟹ extra-block (`col≥runLen`) `c_i = 0` (Form V) ⟹ extra
  terms vanish; partial (`col<runLen`) `u_i=0` ⟹ partial vanish ⟹ `foldResid=0`. (Needs the boost center's
  "pivot→0" to force `e₂_f→0` — the frame reconciliation above.)
- **INTRODUCTION** (new): at `f`'s birth clear (case2/case12, `divTilde f = birthJ`), the δ=1 recoord /
  δ=0 blow-up makes the coefficients of `col ≥ birthJ` coords vanish at `e₂_f = 0`. Per-step lemma at the
  birth clear; rides the EARLIER descended clear (where the cap-escape also bites — the shape+field meet).
- **PRESERVATION** (new): an intervening step preserves the vanishing (`e₂_f` survives as a spectator /
  the running-frame combination transports). Per-step, four cases — LIGHTER than the exact weight.

## FORM S — structural / explicit b-product (= ChainNF, re-homed as CARRIED)
`c_i = chainWeight(s)(col i)·r_i`, `chainWeight(s)(idx) = ∏_{k: divTilde k ≤ idx} (divisor k's exceptional)`
(NON-STRICT ≤, the FIX-1 already applied), `r_i` ignoring the exceptionals.
- YIELDS the split via `bLedger` + `deg1SupportedOn_boostForm` (banked) AND the explicit `M_{s,k}` exponent
  ledger (feeds the Aoyagi exposition). STRONGER than Form V.
- Same FRAME question PER FACTOR: each `chainWeight` factor is a divisor's Schur exceptional (a combination
  in the running chart frame), not a raw birth-corner coordinate — the `chainWeight` def currently reads
  `u (cornerToFlat …)` (a raw slot); under the FRAME PIN it should read the running-frame Schur exceptional.
- **INTRODUCTION**: root `chainWeight ≡ 1` (`numDiv=0`); birth adds `f` at `col ≥ divTilde f`.
  **PRESERVATION**: the four-case ε-transport (cert §7). HEAVIER.

## Coupling + recommendation
- COUPLING: both forms' support `S` must be the CORRECTED (post-cap-escape) descended support —
  `blockCoords(S+1) ∪ {recoord escape coords}` (the (a)-WIDEN shape, consumer-safe per the scope
  interlock), or a re-derived cap — else the `∃c` decomposition itself fails at descended wide states.
  `#32` (cap-escape) and `#40` (invariant) are ONE joint; the field INTRO obligation rides the same
  earlier descended clear.
- `PerLayerDeg1From` SURVIVES unchanged (pnp empirical table) — no draft change on the degree conjunct.
- RECOMMENDATION: **Form V** — minimal unblock for the case11 boost split; vanishing preserves more
  robustly than the exact product, and it avoids the explicit weight bookkeeping. Form S only if the
  exposition wants the explicit `M_{s,k}` ledger from the same invariant. Whichever: CARRY it (a
  `FoldStepInvAt` field or a parallel invariant), discharge at L5's canonFlatten base — and pin the FRAME
  explicitly (the vanishing/factor is the Schur exceptional in the running chart frame, whose root-frame
  image is the single birth-corner slot). Operator directive (5746fd4a9): the ruling LEADS with worked.tex
  (her `M_{s,k}`, her `b`'s); these candidates are judged as TRANSCRIPTIONS of her induction hypothesis.
