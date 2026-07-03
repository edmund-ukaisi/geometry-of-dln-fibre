# genm-d1gates — the `hrank₂` front-loaded assessment (LEAF 2 NOT closed; core-geometry gate de-risked)

Charged to close LEAF 2 of the L=2 headline by discharging the 3 per-`v` gates of the two-peel
producer `d1ge_L2_rect_two_peel`, with the CORE-GEOMETRY gate `hrank₂` FRONT-LOADED. This card
reports the front-loaded assessment: **`hrank₂` is TRUE and TIGHT (no rank drop, no constant-rank
wall) — but discharging it in Lean is a genuine NEW-MODULE build, NOT bounded plumbing on the current
bank.** Per the binding discipline (do NOT launder, do NOT reduce-to-another-hypothesis; STOP and
report the precise obstruction), LEAF 2 (`HeadlineL2Assembly.lean:107`) is left correctly-stated;
nothing laundered. The math confound the assessment removes is real and durable.

## The gate `hrank₂` (the CORE geometry gate, front-loaded)

In `d1ge_L2_rect_two_peel` (`D1RectHDomProducer.lean`), for the first-peel bump-globalised residual
`q` (from `dln_hchart_residual_c2`):

    extraCountRect (H0-r) (H2-r) a b  ≤  rank( jacResid (fun t => q(0,t)) t0 )

`jacResid h t0` = the matrix of component-wise `fderiv`s of `h` at `t0` (`D1SecondPeelMinor.lean`).

## FINDING 1 — the MATH is TRUE and TIGHT; NO rank drop (decisive, decorrelated)

Numeric certificate (`hrank2_residual_rank_certificate.py`, this dir; reproducible, seeded):
`q =ᶠ (rawResidVec ∘ Ψsymm ∘ splitHomeo.symm ∘ (0,·))` near the basepoint, so
`jacResid (q(0,·)) t0 = [Dg(v) with the nReg selected er-rows zeroed] ∘ (DΦ(0))⁻¹ ∘ [complement
injection]`, where `Dg(v) = jointDiffL2 H v` (the loss-entry differential `δ ↦ δ0·v1 + v0·δ1`).
Computing this composite at ~860 constructed **middle-stratum** optimal `v` (`prod v = B`, `rank B =
r`, layer ranks `rank v0 = r+b`, `rank v1 = r+a`), `H` up to `(5,5,5)`, various `r`, INCLUDING
**adversarial random valid `nReg`-minor selections**:

    rank(jacResid (q(0,·)) t0) = extraCountRect (H0-r) (H2-r) a b   EXACTLY, ZERO fails, never drops.

So (i) the `≤` bound `hrank₂` HOLDS and is TIGHT; (ii) there is **NO constant-rank / stratification
DROP** — the residual Jacobian's rank is structurally `= extra` at every middle stratum. This is the
GOOD outcome the brief anticipated ("the finite-atlas peels the constant final-rank corner, so the
residual rank should be structurally ≥ extraCountRect"), and it REMOVES the live confound that a rank
drop at some stratum would be a genuine geometry wall (the #120/hRform failure mode). The extra count
matches the cross-paired `extraCountRect` with the middle-stratum layer-rank labeling
`(rank v0, rank v1) = (r+b, r+a)` (`a` = output/row-side rise, `b` = input/col-side rise; sympy-exact,
matches the `D1RectValueArith` cross-pairing).

The **abstract, network-free identity** underneath (the b2 brick, below) is likewise clean: for ANY
matrix `T` (rank ρ) and ANY invertible `nReg`-minor `(er,ec)`, the composite `[T with er-rows zeroed]
∘ (DΦ(0))⁻¹ ∘ [complement injection]` has rank EXACTLY `ρ − nReg` (0 fails / 400 random abstract
matrices). This is a genuinely PROVABLE, reusable linear-algebra fact.

## FINDING 2 — the OBSTRUCTION is formalisation-reachability, and it is genuine (verdict B)

Discharging `hrank₂` in Lean at a general `v` is NOT "a clean explicit minor you just build" on the
current bank. It needs THREE genuinely-new pieces (my read + decorrelated Codex xhigh, both verdict
**B — new-module wall, no RLCT-transfer shortcut**):

- **b1 — a NEW first-peel producer variant exposing `HasFDerivAt (q(0,·)) L t0`** with `L` the
  explicit composite. The IFT chart DOES have the inverse derivative internally
  (`exists_boundedUnit_chart_of_contDiffAt` proves `HasFDerivAt Ψsymm f'.symm 0`, `f'.symm =
  (chartFDerivEquiv)⁻¹`), and `HasFDerivAt chartΦ f' 0` is banked — but `dln_hchart_residual_c2`
  DISCARDS the derivative, outputting only `(q, t0, ContDiff, q(0,t0)=0, RLCT-transfer EQUATION)`. The
  RLCT-transfer is an integral/measure statement; **it cannot recover the composite Jacobian** (Codex's
  single load-bearing reason). So b1 must re-thread the germ `q ↔ rawResidVec` + `dΨsymm(0) = f'.symm`
  + `d(splitHomeo.symm∘(0,·))` through the chain rule to expose `L`. Substantial derivative plumbing;
  no `fderiv(rawResidVec)` / `jacResid(q(0,·))` identity is built anywhere in the repo.
- **b2 — a NEW network-free residual-rank linear-algebra module** proving `rank(L) = ρ − nReg` (the
  abstract identity above). Self-contained and provable (numerically certified clean), in the SPIRIT of
  the banked `nReg_le_finrank_range_jointDiffL2` (a gauge-injection rank bound) but at the RESIDUAL /
  complement-restricted level. NOT a restatement of any banked lemma (that one bounds `rank Dg`, not
  the residual composite). Comparable size (~100–200 LoC of dense linear algebra).
- **b3 — the `(a,b)` middle-stratum extraction** at a general `v` (`a = rank v1 − r` [output side],
  `b = rank v0 − r` [input side]) with the honest-subtraction constraints, needed even to STATE
  `extra = rank Dg(v) − nReg`. Bounded combinatorial/rank bookkeeping, but genuinely required and
  entangled with b2's statement.

`hInterface` (gate 2) and b3 are the bounded gates the brief expected to do "after `hrank₂` clears";
they DEPEND on b1+b2 landing first (the second-peel residual must be identified before R1 can be
instantiated at `M'`), so with `hrank₂` open they do not stand alone.

## What was NOT done, and why (discipline)

- LEAF 2 NOT closed. `HeadlineL2Assembly.lean:107` `sorry` stands (correctly-stated). No edit to it.
- `hrank₂` NOT laundered into a sorry, NOT reduced to yet another hypothesis. Three prior hands
  (`d1-secondpeel`, `genm-d1l2prod`, `genm-hdomprod`) kept it a named hypothesis for exactly this
  reason; this hand CONFIRMS the reason is real (formalisation-reachability, verdict B) and ADDS the
  decisive de-risking: the rank does NOT drop (the geometry does not wall), and the underlying identity
  is a clean provable rank fact. So the residual is now precisely scoped as b1+b2+b3, all three genuine
  new content, none a disguised chart-existence.
- The b2 abstract brick was assessed as provable-and-reachable but NOT built this hand: it is entangled
  with b3 (needs `extra = rank Dg − nReg` to state at the DLN site) and is a ~100–200 LoC dense
  linear-algebra module, i.e. a genuine build unit, not the bounded plumbing the "just do it" bar wants
  a leaf hand to complete inside one tide. Flagged as the highest-value next brick (see ROADMAP note).

## Build status

Base branch (`origin/genm-hdomprod`) builds green (`lake build DLNFibre.…D1RectHDomProducer` exit 0,
3011 jobs). This thread added no Lean; the sorry footprint is unchanged (the LEAF-2 sorry + the
pre-existing general-L skeleton walls). `hrank₂` remains a named hypothesis, not a sorry.

## Pointer for the next hand (the honest runway)

`hrank₂` is the sole remaining CORE-geometry content of LEAF 2 and is now DE-RISKED to a build task,
not an open truth-value: build **b1** (a `dln_hchart_residual_c2`-variant that additionally returns
`HasFDerivAt (q(0,·)) L t0` with `L = [Dg(v) sel-rows-zeroed] ∘ f'.symm ∘ [compl inj]`, via the germ
`q =ᶠ rawResidVec∘Ψsymm∘splitHomeo.symm` + the internal `hsymm_hfderiv`), then **b2** (the abstract
`rank(L) = rank T − nReg`), then **b3** (the `(a,b)` extraction) — after which `hInterface` + the
value close finish LEAF 2 on the validated two-peel chain. The numeric certificate here fixes the
target rank identity and the cross-pairing labeling, so b2 can be stated and checked against it.
