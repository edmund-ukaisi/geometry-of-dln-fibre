   Updating ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (HEAD)
    Updated ssh://git@github.com/AI-Safety-Institute/aisi-inspect-tools (fa7351f6ef4773f536ee4975c3251325eb9c44df)
OpenAI Codex v0.142.2
--------
workdir: /home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability
model: gpt-5.5
provider: openai-aisi
approval: untrusted
sandbox: read-only
reasoning effort: xhigh
reasoning summaries: none
session id: 019efdcb-95cf-7351-913e-6d04aab89e22
--------
user
<task>
Decorrelated design review of a Lean-proof DECOMPOSITION (not asking for a proof — asking whether my
sub-lemma breakdown is COMPLETE and correctly ordered, and which step is the real risk). Re-derive the
dependency structure independently; tell me what I've mis-scoped.
</task>

<setting>
Deep linear net, L layers (L≥2), widths H, target rank r. Deepest point = a rank-r block-normal chain.
A gauge chart `split : flat-params ≃ DeepestSplit = (reg) × (core × spec)`. There is a per-layer frame
family (P_s, Q_s) carrying the deepest layer to the block-normal corner (`P_s · deepestPoint_s · Q_s =
corM`, banked as `deepestPoint_frame_normal`).

GOAL (a single theorem body, `framedParams_split_eq_frame_raw`): produce constant endpoint frames
P0, QL (+ inverses) and a neighborhood U of the deepest point s.t. for w ∈ U, with blocks P00,P01,P10,P11
from the conjugated loss:
  (a) reindex(P0·(prod(paramsSymm w) − B)·QL) = fromBlocks (P00−1) P01 P10 P11      [hconj]
  (b) ∑(E_full(split w))² = ∑(P00−1)² + ∑P01² + ∑P10²   (Sreg)                       [reg-energy identity]
  (c) ∑(P10·P00⁻¹·P01)² ≤ t²·Sreg                                                    [leak bound]
  (d,e) core comparability: ∑(P11 − P10 P00⁻¹ P01)² ≍ deepestCoreF(coreAbsorb(split w))  [γ₁,γ₂]
where E_full(split w) = the reg blocks (packed by a bijection regResidualPack) of
reindex(prod(framedParamsPivot(split w))), and framedParamsPivot is the per-layer reconstruction
`framedLayer_s = corM + P_s·reindex(fromBlocks readX_s readY_s readZ_s T_s)·Q_s`.
</setting>

<banked_atoms_available>
1. reindex_fromBlocks_reads_eq_deviation: reindex(fromBlocks readX readY readZ readT)(deepestSplit w)
   = ((paramsEquivFlat).symm (w − wstar)) s   — ENTRY-WISE, THRESHOLD split on BOTH row & column sides.
2. deepestPoint_frame_normal: P_s · deepestPoint_s · Q_s = corM.
3. endpoint_telescoping: if C_s = P_s·A_s·Q_s and all INTERIOR interfaces collapse (Q_s=1 ∧ P_{s+1}=1
   for (s)+1<L), then prod C = P0 · prod A · QL, with P0 = P_first, QL = Q_last.
4. deepestPoint_frame_Qf_eq_one / _Pf_eq_one (boundary), deepestPoint_interior_frame_id (interior, L≥3).
5. exists_deepest_lastLayer_pivotFrame: ∃ J,Q: reindex(rThr, pivotThr J)(deepestPoint_last · Q) =
   fromBlocks 1 0 0 0, with the (2,2) block a unit.
6. core_comparability_squeeze: from P11 = leak + Rcore entrywise + ∑leak² ≤ t²∑E², get the two-sided
   ∑E²+‖Rcore‖² ≍ ∑E²+‖P11‖².
7. fullProduct_core_split: the Frobenius block split + P11 = (P10 P00⁻¹ P01) + (P11 − P10 P00⁻¹ P01).
8. regResidualPack: a bijection Fin nReg ≃ (the three reg block index types).
9. pivotThresholdSplit_symm_inl/inr: the pivot column-split inverse decode.
NOTE atom 1 (reindex_fromBlocks_reads_eq_deviation) uses rThresholdSplit on the COLUMN side; but
framedParamsPivot's LAST layer uses pivotThresholdSplit (pivotJSucc J) on the column side instead.
</banked_atoms_available>

<my_proposed_decomposition>
S1 (per-layer round-trip): framedParams(split w) s = P_s · (paramsSymm w)_s · Q_s.
   = framedLayer = corM + P_s·reindex(fromBlocks reads)·Q_s; corM = P_s·deepestPoint_s·Q_s (atom 2);
     reindex(fromBlocks reads) = (paramsSymm w − deepestPoint)_s (atom 1); so framedLayer =
     P_s·deepestPoint_s·Q_s + P_s·(paramsSymm w − deepestPoint)_s·Q_s = P_s·(paramsSymm w)_s·Q_s.
   NON-last layers only (last layer has the pivot column split — see S1').
S1' (last-layer pivot variant): the SAME identity but the column reindex is pivotThresholdSplit, so
   atom 1 must be re-proved with pivot column split. (THE FLAGGED RISK.)
S2 (telescope): prod(framedParams(split w)) = P0·prod(paramsSymm w)·QL (atom 3 + 4).
S3 (B-normalize): reindex(P0·B·QL) = fromBlocks 1 0 0 0 (atom 5), same J. So
   reindex(P0·(prod(paramsSymm w) − B)·QL) = fromBlocks (P00−1) P01 P10 P11 [= hconj, conjunct (a)].
S4 (reg-energy identity (b)): ∑(E_full(split w))² = Sreg. E_full reads the reg blocks of
   reindex(prod(framedParamsPivot(split w))) = (by S2) reindex(P0·prod(paramsSymm w)·QL) = (S3) the SAME
   P00,P01,P10 blocks as hconj. So packing by regResidualPack (atom 8) gives the energy = Sreg.
S5 (leak (c) + core (d,e)): fullProduct_core_split (atom 7) + core_comparability_squeeze (atom 6) +
   the per-layer Schur ↔ global Schur ideal membership for the core comparability.
</my_proposed_decomposition>

<questions>
1. Is the decomposition S1–S5 COMPLETE for conjuncts (a)–(e)? What's missing or mis-ordered?
2. S1' (last-layer pivot column variant of atom 1): is this genuinely a SEPARATE lemma, or does atom 1
   transfer by a column-relabel? The pivot split is rThresholdSplit precomposed with a column PERMUTATION
   (pivot columns to front). Does the entry-wise decode survive the permutation, or is it a fresh proof?
3. The endpoint frames: S2 needs P0=P_first, QL=Q_last CONSTANT (independent of w). They ARE (the frame
   is the deepest-point frame, w-independent). But S3 needs the SAME J/Q as exists_deepest_lastLayer_
   pivotFrame, and S1/S2 use the deepest-point frame's last-layer Q. Is there a consistency obligation
   that the deepest-point frame's last-layer arm EQUALS the pivot frame Q from atom 5? (i.e. are the two
   frame sources reconciled, or is that an open gap?)
4. Which single step is the genuine exact-algebra / highest-risk one? My guess: S1' (the pivot decode).
</questions>

<output_contract>
Per question: VERDICT + reasoning. Mark exact-algebra vs structural inference. Flag any missing
sub-lemma or hidden consistency obligation I omitted (esp. the frame-source reconciliation in Q3).
End with: "The highest-risk step is ___ because ___; the decomposition is [COMPLETE / missing ___]."
</output_contract>

<grounding_rules>
Reason about the dependency structure + the matrix algebra. Distinguish a genuine new lemma from a
relabel of a banked one. If a consistency obligation between two frame sources is unstated, name it.
</grounding_rules>

codex
I’ll ground this in the local Lean/exposition context first, then answer at the dependency level. I’m going to look for the theorem and the banked atoms you named, especially the pivot-frame and endpoint-frame definitions.
exec
/bin/bash -lc 'pwd && rg -n "framedParams_split_eq_frame_raw|reindex_fromBlocks_reads_eq_deviation|deepestPoint_frame_normal|endpoint_telescoping|exists_deepest_lastLayer_pivotFrame|core_comparability_squeeze|fullProduct_core_split|framedParamsPivot|pivotThresholdSplit|rThresholdSplit" -S .' in /home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability
 succeeded in 0ms:
/home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability
./codex/framedbody-run.log:25:corM`, banked as `deepestPoint_frame_normal`).
./codex/framedbody-run.log:27:GOAL (a single theorem body, `framedParams_split_eq_frame_raw`): produce constant endpoint frames
./codex/framedbody-run.log:35:reindex(prod(framedParamsPivot(split w))), and framedParamsPivot is the per-layer reconstruction
./codex/framedbody-run.log:40:1. reindex_fromBlocks_reads_eq_deviation: reindex(fromBlocks readX readY readZ readT)(deepestSplit w)
./codex/framedbody-run.log:42:2. deepestPoint_frame_normal: P_s · deepestPoint_s · Q_s = corM.
./codex/framedbody-run.log:43:3. endpoint_telescoping: if C_s = P_s·A_s·Q_s and all INTERIOR interfaces collapse (Q_s=1 ∧ P_{s+1}=1
./codex/framedbody-run.log:46:5. exists_deepest_lastLayer_pivotFrame: ∃ J,Q: reindex(rThr, pivotThr J)(deepestPoint_last · Q) =
./codex/framedbody-run.log:48:6. core_comparability_squeeze: from P11 = leak + Rcore entrywise + ∑leak² ≤ t²∑E², get the two-sided
./codex/framedbody-run.log:50:7. fullProduct_core_split: the Frobenius block split + P11 = (P10 P00⁻¹ P01) + (P11 − P10 P00⁻¹ P01).
./codex/framedbody-run.log:52:9. pivotThresholdSplit_symm_inl/inr: the pivot column-split inverse decode.
./codex/framedbody-run.log:53:NOTE atom 1 (reindex_fromBlocks_reads_eq_deviation) uses rThresholdSplit on the COLUMN side; but
./codex/framedbody-run.log:54:framedParamsPivot's LAST layer uses pivotThresholdSplit (pivotJSucc J) on the column side instead.
./codex/framedbody-run.log:63:S1' (last-layer pivot variant): the SAME identity but the column reindex is pivotThresholdSplit, so
./codex/framedbody-run.log:69:   reindex(prod(framedParamsPivot(split w))) = (by S2) reindex(P0·prod(paramsSymm w)·QL) = (S3) the SAME
./codex/framedbody-run.log:71:S5 (leak (c) + core (d,e)): fullProduct_core_split (atom 7) + core_comparability_squeeze (atom 6) +
./codex/framedbody-run.log:78:   transfer by a column-relabel? The pivot split is rThresholdSplit precomposed with a column PERMUTATION
./codex/fullreg-scoping-prompt.md:25:- `framedParams_split_eq_frame_raw` is ALREADY a `sorry` (its body): a ~200-300 LoC geometric cert.
./codex/fullreg-scoping-prompt.md:36:  (A) DELETE h00/h01/h10 from `framedParams_split_eq_frame_raw`'s conclusion; ADD instead a single
./codex/framedbody-prompt.md:11:corM`, banked as `deepestPoint_frame_normal`).
./codex/framedbody-prompt.md:13:GOAL (a single theorem body, `framedParams_split_eq_frame_raw`): produce constant endpoint frames
./codex/framedbody-prompt.md:21:reindex(prod(framedParamsPivot(split w))), and framedParamsPivot is the per-layer reconstruction
./codex/framedbody-prompt.md:26:1. reindex_fromBlocks_reads_eq_deviation: reindex(fromBlocks readX readY readZ readT)(deepestSplit w)
./codex/framedbody-prompt.md:28:2. deepestPoint_frame_normal: P_s · deepestPoint_s · Q_s = corM.
./codex/framedbody-prompt.md:29:3. endpoint_telescoping: if C_s = P_s·A_s·Q_s and all INTERIOR interfaces collapse (Q_s=1 ∧ P_{s+1}=1
./codex/framedbody-prompt.md:32:5. exists_deepest_lastLayer_pivotFrame: ∃ J,Q: reindex(rThr, pivotThr J)(deepestPoint_last · Q) =
./codex/framedbody-prompt.md:34:6. core_comparability_squeeze: from P11 = leak + Rcore entrywise + ∑leak² ≤ t²∑E², get the two-sided
./codex/framedbody-prompt.md:36:7. fullProduct_core_split: the Frobenius block split + P11 = (P10 P00⁻¹ P01) + (P11 − P10 P00⁻¹ P01).
./codex/framedbody-prompt.md:38:9. pivotThresholdSplit_symm_inl/inr: the pivot column-split inverse decode.
./codex/framedbody-prompt.md:39:NOTE atom 1 (reindex_fromBlocks_reads_eq_deviation) uses rThresholdSplit on the COLUMN side; but
./codex/framedbody-prompt.md:40:framedParamsPivot's LAST layer uses pivotThresholdSplit (pivotJSucc J) on the column side instead.
./codex/framedbody-prompt.md:49:S1' (last-layer pivot variant): the SAME identity but the column reindex is pivotThresholdSplit, so
./codex/framedbody-prompt.md:55:   reindex(prod(framedParamsPivot(split w))) = (by S2) reindex(P0·prod(paramsSymm w)·QL) = (S3) the SAME
./codex/framedbody-prompt.md:57:S5 (leak (c) + core (d,e)): fullProduct_core_split (atom 7) + core_comparability_squeeze (atom 6) +
./codex/framedbody-prompt.md:64:   transfer by a column-relabel? The pivot split is rThresholdSplit precomposed with a column PERMUTATION
./restatement-spec.md:67:- `framedParams_split_eq_frame_raw` (~1327): **DELETE `h00/h01/h10`** (the false exact equalities).
./restatement-spec.md:92:- (ii) `endpoint_telescoping` needs `hinterface (s):Q_s=1∧P_{s+1}=1` for every interior `(s)+1<L`;
./restatement-spec.md:97:`dlnLoss_two_sided_of_frame` (leaf, `Sreg+Score ≍ dlnLoss`), `core_comparability_squeeze` (#54),
./restatement-spec.md:98:`endpoint_telescoping` (+ interior frame id for L≥3), `exists_deepest_lastLayer_pivotFrame`,
./restatement-spec.md:99:`deepestPoint_frame_normal`, `regResidualPack` (bijection), `deepestEPivot_regSlice_fderiv` (PIN1 —
./restatement-spec.md:111:`framedParams_split_eq_frame_raw`'s `h00/h01/h10`; `deepest_loss_squeeze`'s `hSreg_eq`;
./thread.md:117:  `pivotThresholdSplit r (H last.succ) (pivotJSucc J)` on the column side; the bundle's `hcorner` is
./thread.md:121:- (ii) `endpoint_telescoping` needs `hinterface (s) : Q_s = 1 ∧ P_{s+1}=1` for every **interior**
./thread.md:159:  `framedParams_split_eq_frame_raw` (~1327, the `h00/h01/h10` exact-equality conjunctions) +

exec
/bin/bash -lc "rg --files -g 'CLAUDE.md' -g 'AGENTS.md' -g '*.lean' -g '*.md' | sed -n '1,200p'" in /home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability
 succeeded in 0ms:
thread.md
claim-card.md
transfer-cert.md
restatement-spec.md
codex/reduce-peel-prompt.md
codex/squeeze-soundness-prompt.md
codex/squeeze-soundness-answer.md
codex/fullreg-scoping-prompt.md
codex/reduce-peel-answer.md
codex/pin1-survival-prompt.md
codex/pin1-survival-answer.md
codex/fullreg-scoping-answer.md
codex/framedbody-prompt.md

codex
The local thread directory looks like an analysis bundle rather than the full Lean tree, so I’m using its scoping notes as the available source of truth. I’ve found prior notes that already separate the “exact equalities” issue from the endpoint-frame/pivot-frame issue; I’m reading those now to avoid relying only on the prompt wording.
exec
/bin/bash -lc "sed -n '1,180p' restatement-spec.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability
 succeeded in 0ms:
# Build-ready repair spec — PIN2 (post-refutation) + PIN1 survival

**Verdict recap.** Option 2 (`Sreg ≍ ∑deepestEPivot²`) is UNSOUND (both directions; thread 31).
`loss_squeeze` is FALSE as typed. The repair is: the squeeze's **regular term must read the FULL
product's reg blocks**, which depend on the core slot — so `regStraighten`'s reg-OUTPUT must read the
core. **PIN1 survives verbatim** (the invertible reg-slice derivative `F` is unchanged — leaks are
degree-2). All algebra exact; decorrelated Codex (xhigh) on both the squeeze-soundness and the
PIN1-survival points; both in `codex/`.

---

## The non-negotiable fact that sets the architecture

The squeeze needs `∑(regStraighten q).1² ≍ dlnLoss − coreterm`. The only reg quantity comparable to the
loss's regular part is the **FULL product** reg energy `Sreg = (P00−1)²+P01²+P10²` (the leaf lemma).
`Sreg` DEPENDS on the core `T` (leak `P01 = (1+X0)Y1 + Y0·T1`). Therefore:

- A core-INDEPENDENT reg output (`E_pivot : (reg,spec)→reg`, the current `deepestEPivot`) CANNOT match
  `Sreg`. Confirmed dead three ways: `∑deepestEPivot²` over-counts on line A (`(T1Y0)²` vs `dln=0`);
  `∑deepestEPivot² + per-layer-Schur` fails (current); `∑deepestEPivot² + GLOBAL-Schur` ALSO fails
  (the over-count is in the *added* reg term, which no core term can subtract).
- So `E_pivot` must become `E_full : (reg, spec, core) → reg` — taking ALL THREE slots, returning the
  FULL product's three reg blocks (= `P00−1, P01, P10` from the leaf lemma's `hconj`).

## PIN1 survives — exact (the gating question, answered)

`E_full − E_zero = (0, Y0·T1, T0·Z1)` — **purely degree-2** (Codex re-derived independently, agrees).
- Reg-slice derivative at 0 (core+spec held 0): `D(E_full)(r0,0,0) = D(deepestEPivot)(r0,0) = F`
  (the block-triangular invertible `regBlockCLE`). IDENTICAL — the leaks vanish at core=0.
- Core-direction derivative at 0: `∂E_full/∂T0(0) = ∂E_full/∂T1(0) = 0` (leaks are degree-2).
- So `D(E_full)(0)` in block form (rows reg-out; cols reg-in, core-in, spec-in) is `[F | 0 | G]`
  (`G` = spectator block, possibly nonzero — coordinate-dependent).

**`deepestEPivot_regSlice_fderiv` (PIN1) is RE-USED verbatim** as the reg-slice fact, via a one-line
bridge `E_full(r0, 0, 0) = deepestEPivot(r0, 0)` (the core+spec-zero restriction kills the leaks —
`Matrix.ext`, each leak carries a zeroed factor). **NOT** a new invertibility argument, **NOT**
orphaned. `deepestEPivot` stays as the reg-slice witness; only the squeeze's reg OUTPUT changes object.

## The chart-derivative invertibility (the IFT-peel input) survives

Corrected `regStraighten q := (E_full(q.1, q.2.2, q.2.1), q.2.1, q.2.2)` — reg OUTPUT reads all slots,
core/spec OUTPUT slots fixed. Derivative at 0 (blocks reg/core/spec):

        [[ F   0   G ]
         [ 0   I   0 ]
         [ 0   0   I ]]

block-triangular, diagonal `(F, I, I)` ⇒ `det = det F ≠ 0` ⇒ **invertible**. The IFT/`#72` bounded-unit
local-diffeo peel (`rlctAtOn_boundedUnit_localHomeomorph`) consumes exactly an invertible derivative at
0 + `ContDiff` + a local inverse on an open `V` — all intact. (`D_core E_full(0)=0` is what makes the
reg-slice = `deepestEPivot` for the PIN1 bridge; invertibility itself only needs `F` invertible.)

## What changes in Lean (build-ready)

### (1) `DeepestRegAbsorbIFT.lean` — generalize the straightening object
`regStraightenOf`, `regStraightenTotalCLM`, `hasStrictFDerivAt_regStraightenOf_gen` currently take
`E_pivot : R × S → R`. Generalize to `E_pivot : R × (C × S) → R` (full split `(reg, core, spec)`):
- `regStraightenOf E_pivot q := (E_pivot q, q.2.1, q.2.2)` (reg-out reads all; core/spec-out fixed).
- `regStraightenTotalCLM D_E` for `D_E : (R×(C×S)) →L R`: `δ ↦ (D_E δ, δ.2.1, δ.2.2)` — invertible
  ⟺ the reg-block `D_E ∘ regIn` is a unit. Shear shape `[[F,0,G],[0,I,0],[0,0,I]]` block-tri, SAME
  unit criterion on `F`.
- `hasStrictFDerivAt_regStraightenOf_gen` re-proves with `proj := id` (no longer `(q.1,q.2.2)`).
- `regStraightenTotalCLM_equiv_of_regBlock_isUnit` (`DeepestRegSliceFderiv.lean:616`) generalizes —
  invertibility from the reg-block unit, now over the full domain.

### (2) `DeepestGaugeConstruction.lean`
- `framedParams_split_eq_frame_raw` (~1327): **DELETE `h00/h01/h10`** (the false exact equalities).
  Keep `hconj`, `hleak`, `hcore_le/hcore_ge`. (Optionally ADD `hregval_full : E_full(split w) =
  regResidualPack of (P00−1,P01,P10)` — an IDENTITY by `regResidualPack` bijectivity + `hconj`, no leak.)
- Define `E_full : DeepestSplit → (Fin nReg → ℝ)` = the regResidualPack of the FULL product
  `reindex(P0·(prod(paramsSymm w)−B)·QL)` reg blocks (= directly the `hconj` blocks `(P00−1,P01,P10)`).
- `deepestEPivot_deriv` (~1188): re-aim to produce `HasStrictFDerivAt E_full D_E 0` with `D_E`'s
  reg-block `= F`, via PIN1 + the bridge `E_full(·,0,0) = deepestEPivot(·,0)`. The core-block-zero fact
  (`∂E_full/∂core(0)=0`, the quadratic-leak lemma) is the new small atom.
- `deepest_loss_squeeze` (~1478): **DELETE `hSreg_eq`** (line 1541). Replace `hregval` with
  `hregval_full : (regStraighten q).1 = E_full q`. Then `∑(regStraighten (split w)).1² = Sreg` is the
  identity `‖E_full‖² = Sreg` (regResidualPack + hconj). The `c₁/c₂` arithmetic (lines 1566–1602) is
  UNCHANGED (it only ever needed `∑(regStraighten).1² = Sreg`, never `Sreg = Ereg`).

### (3) `DeepestGaugeChart.lean` — the structure
`regStraighten_core`/`regStraighten_spectator` (OUTPUT core/spec slots fixed) STAY TRUE — `E_full`
changes only the reg OUTPUT. `regAbsorb_rlct` (the peel) re-proves with the generalized
`regStraightenOf`/`regStraightenTotalCLM`; the `loss_squeeze` field is now TRUE.

### (4) `deepest_regAbsorb_exists` (~1697 wiring) + producer
Change `E_pivot : (reg,spec)→reg` to `E_full : (reg,core,spec)→reg`; `hEp_deriv` the full-domain
fderiv (reg-block `= F`); the defining identity `(regStraighten q).1 = E_full q`.

## Secondary fixes
- (i) last-layer pivot/threshold column: NOT an inconsistency; same `J` threaded (`hpivJ`). With
  `framedParamsRegPivot` only feeding PIN1's reg-slice witness now, the concern is contained.
- (ii) `endpoint_telescoping` needs `hinterface (s):Q_s=1∧P_{s+1}=1` for every interior `(s)+1<L`;
  `hQf0/hPfL` cover the boundary; for `L≥3` thread `deepestPoint_interior_frame_id` (`DeepestFrame.lean:108`).
  For `L=2` (current target) no strict-interior interface — `hQf0/hPfL` suffice.

## Sound banked atoms (stay)
`dlnLoss_two_sided_of_frame` (leaf, `Sreg+Score ≍ dlnLoss`), `core_comparability_squeeze` (#54),
`endpoint_telescoping` (+ interior frame id for L≥3), `exists_deepest_lastLayer_pivotFrame`,
`deepestPoint_frame_normal`, `regResidualPack` (bijection), `deepestEPivot_regSlice_fderiv` (PIN1 —
RE-USED as the reg-slice fact), `regBlockCLE`, `regStraightenTotalCLM_equiv_of_regBlock_isUnit`
(generalize the domain).

## Net effort
NOT a localized lemma fix; NOT a re-architecture of the invertibility either. The genuine new work:
(a) generalize `regStraightenOf`/`regStraightenTotalCLM` from `(reg,spec)→reg` to `(reg,core,spec)→reg`
(the existing proofs with `proj:=id`); (b) define `E_full` + the identity `‖E_full‖²=Sreg`; (c) the
bridge `E_full(·,0,0)=deepestEPivot(·,0)` + `∂E_full/∂core(0)=0` (degree-2) feeding PIN1's `F` into the
full-domain `D_E`. **PIN1's invertibility argument and the leaf squeeze are RE-USED, not re-proved.**

## DELETE from the squeeze path (the false load-bearers)
`framedParams_split_eq_frame_raw`'s `h00/h01/h10`; `deepest_loss_squeeze`'s `hSreg_eq`;
`deepestEPivot_sq_sum_eq_blocks` (the `∑deepestEPivot² = T=0 product reg energy` summing identity — was
only there to feed the false `hSreg_eq`).

exec
/bin/bash -lc "sed -n '1,240p' thread.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability
 succeeded in 0ms:
# Thread 31 — PIN2 comparability re-architecture (the L2 geometric heart)

**Seat:** pen-and-paper (obstruction). **Direction asked:** validate-or-refute the brief's option 2
(weaken `h00/h01/h10` to a two-sided comparability `Sreg ≍ ∑deepestEPivot²`, folding the Y·T leak into
γ₁/γ₂). **Level:** the loss-squeeze germ (the matrix-block / energy-comparability level, below the RLCT
cap). **Verdict: option 2 is UNSOUND.** Both directions of `Sreg ≍ ∑deepestEPivot²` are false by exact
witnesses. The real fix is to read the regular energy off the **FULL product** (which the leaf lemma
`dlnLoss_two_sided_of_frame` already does) and to **not** identify `Sreg` with `∑deepestEPivot²` at all.

All algebra exact (sympy, exact-rational/symbolic). MC used only as a guide and clearly flagged.

---

## The objects (as instantiated for the smallest separating case)

`L = 2`, `H = [2,2,2]`, `r = 1`. Each layer block-split `1 ⊕ (H−r)=1 ⊕ 1`:
`C0 = [[1+X0, Y0],[Z0, T0]]`, `C1 = [[1+X1, Y1],[Z1, T1]]`. `B = corM = [[1,0],[0,0]]`.
Deepest point: all 8 deviations `= 0`. The 8 are independent **raw** chart coordinates
(`X,Y,Z` off the `(reg,spec)` slot through the homeomorphism `regGaugeSlotEquiv`; `T` off the separate
core slot `.2.1`). `split` is a homeomorphism onto a neighborhood, so all 8 are jointly free near 0.

- `Sreg`  = FULL-product reg energy `(P11−1)²+P12²+P21²` of `C0·C1` (what `hconj` + the leaf lemma read).
- `Ereg`  = `∑deepestEPivot²` = the SAME three blocks of the **T=0** product `C0|_{T0=0}·C1|_{T1=0}`
  (verified to equal the actual `framedParamsRegPivot` product reg-energy at `J=id`, frames `=1`).
- `coreΦ` = `deepestCoreF((coreAbsorb ·).2.1)` = `‖∏ S_s‖²`, the product of the **per-layer Schur**
  cores `S_s = T_s − Z_s(1+X_s)⁻¹Y_s` (`deepestCoreAbsorb` = the cutoff Schur shear `schurCutoffShift`).
- `Φ`     = `∑deepestEPivot² + coreΦ` = `Ereg + coreΦ` (the squeeze headline target).

## The leak (witness 1, exact)

`(C0·C1)₁₂ = (1+X0)Y1 + Y0·T1`; the T=0 product `₁₂ = (1+X0)Y1`. **Leak = `Y0·T1`** (and symmetrically
`Z1·T0` in `₂₁`). `Y0` is a `(reg,spec)`-slot deviation, `T1` a core-slot deviation — independent. So
the exact equality `h01 : P01 = (T=0 product)₁₂` is false in every neighborhood. (Matches the brief.)

## The obstruction (witnesses A, B — option 2 dies BOTH ways)

`P11` is identical for FULL and T=0 (no T enters it here); the leak lives only in `P12, P21`.

- **Line A** (`X0=X1=Z0=Z1=T0=0, Y1 = −T1·Y0`; free `Y0,T1`): a **2-surface** through the deepest pt.
  - FULL product `= [[1,0],[0,0]] = corM` exactly ⇒ `Sreg = 0`, `coreΦ = (S0·S1)² = (0·T1)² = 0`,
    `dlnLoss = 0`.
  - T=0 product `= [[1, −T1Y0],[0,0]]` ⇒ `Ereg = (T1Y0)² > 0`, so `Φ = (T1Y0)² > 0`.
  - ⇒ option-2 **lower** bound `γ₁·Ereg ≤ Sreg` becomes `γ₁·(T1Y0)² ≤ 0`: impossible for `γ₁>0`.
  - ⇒ squeeze **lower** bound `c₁·Φ ≤ dlnLoss` becomes `c₁·(T1Y0)² ≤ 0`: impossible. (The headline
    squeeze statement, not just its `Sreg=Ereg` phrasing, is false on line A.)
- **Line B** (`X0=X1=Y1=Z0=Z1=0`; free `Y0,T1,T0`): `Sreg = (T1Y0)² > 0`, `Ereg = 0`.
  ⇒ option-2 **upper** bound `Sreg ≤ γ₂·Ereg` fails.

The brief's premise "the leak is higher-order, dominated by `‖Y‖²` in `∑E²`" is **false**: `Y0·T1` is
degree-2, the same order as the `Y1`-type signal, and it produces exact cancellation (line A) — it is
not a higher-order perturbation foldable into a constant.

## Why this does NOT refute the headline RLCT (the gauge resolution — decorrelated Codex)

Independent re-derivation (Codex `xhigh`, decorrelated; gauge claim then re-verified exactly here):
`Y0` is a **gauge** direction, not a product transversal. Linearizing the internal gauge action
`(C0,C1) ↦ (C0·G, G⁻¹·C1)` at the deepest point: `δC0 = corM·A`, `δC1 = −A·corM` with `A=[[a,b],[c,d]]`
gives gauge tangents `{X0−X1, Y0, Z1}`; transversals `{X0+X1, Y1, Z0}`. On line A the explicit gauge
element `G=[[1,−Y0],[0,1]]` sends `C0·G = corM`, `G⁻¹·C1 = [[1,0],[0,T1]]` — i.e. line A is a pure gauge
orbit of the point `(corM, diag(1,T1))`, whose loss is genuinely `T1²` (carried by the CORE, where it
belongs), NOT `(T1Y0)²`. So the geometry is fine; the **chart** is the problem: `deepestEPivot` reads
the reg blocks off the **T=0 product**, where the gauge coordinate `Y0` contributes a spurious
`(T1Y0)²` that the true loss does not see.

## The correct comparable quantity (the fix the data points to)

`dlnLoss ≍ Sreg + Score` where BOTH are off the **FULL** product:
`Sreg = (P11−1)²+P12²+P21²` (full), `Score = ‖P22 − P21 P11⁻¹ P12‖²` (full global Schur). This is
**exactly** what the banked leaf lemma `dlnLoss_two_sided_of_frame` proves (`hconj` reads `P00,P01,P10,P11`
off `reindex(P0·N·QL)`; the bound is `(Sreg+Score) ≍ dlnLoss` with explicit endpoint-frame constants).
- Verified (sympy + MC): `inf(dlnLoss / (Sreg+Score)) → 1` as scale → 0 on line-A-biased neighborhoods,
  including the **corank-2** case `H=[3,3,3], r=1` (global Schur `D − C A⁻¹ B = det(P)/A`).
- Codex's note: `D − C A⁻¹ B = det(C0)det(C1)/A` — the invariant reduced core, matching the FULL global
  Schur, NOT the raw `T0T1` or the per-layer `∏S_s`.

So the bug is **localized** to the downstream identification, not the leaf core: `deepest_loss_squeeze`
lines 1531–1547 set `Sreg/Score` to the FULL blocks (correct), then `hSreg_eq` (line 1541) rewrites
`Sreg` into `∑deepestEPivot²` via the false `h00/h01/h10`. Delete that rewrite path; phrase the squeeze
target as the FULL `Sreg + Score` (or the RLCT-equivalent reparametrization), not `∑deepestEPivot²`.

## RLCT-sufficiency (brief's question 2) — the SUBTLE part, resolved

The brief asserts "comparability ⟹ rlctAt equal, so the headline value is unaffected." Two corrections:

1. **Comparability is the thing that FAILS** — so the squeeze cannot be the instrument. The
   `DeepestGaugeChart` structure (`DeepestGaugeChart.lean:275`) HARD-CODES the squeeze target as
   `Φ_struct = ∑(regStraighten (split w)).1² + deepestCoreF(coreAbsorb (split w)).2.1`, with
   `regStraighten` required to fix the core/spectator slots (`dE(0)=id`). With `regStraighten`'s output
   `= deepestEPivot` (the T=0 reg blocks), `Φ_struct` has zero set `V(Φ_struct) ⊊ V(dlnLoss)` (line A ∈
   `V(dlnLoss)`, ∉ `V(Φ_struct)`), so NO `c₁>0` gives `c₁·Φ_struct ≤ dlnLoss`. **`loss_squeeze` as
   currently typed is FALSE.** (Confirms the harness's own g161 note line 231 — "loss_squeeze over the
   raw reg slot is FALSE" — was right and `deepestEPivot` did not fix it; the leak is inter-layer.)

2. **The headline RLCT value is very likely SAFE — but via a NONLINEAR diffeo, not comparability.**
   Exact, on the minimal gauge slice (free `Y0,Y1,T1`, rest 0): `dlnLoss = (Y1+Y0T1)²`,
   `Φ_struct = Y1²`. The squeeze `c₁·Y1² ≤ (Y1+Y0T1)²` FAILS pointwise (line A `Y1=−Y0T1`). YET
   `rlct(dlnLoss) = rlct(Φ_struct) = ½`, because `u := Y1 + Y0T1` is a local diffeo (`∂u/∂Y1 = 1`), so
   `(Y1+Y0T1)²` and `Y1²` are analytically equivalent. **Comparability is sufficient for rlct-equality,
   not necessary** — a `dE(0)=id` change of coords also does it. The FULL reg blocks have unit
   transversal Jacobian (`A−1 ~ X0+X1`, `B ~ Y1`, `C ~ Z0`, the 3 = `nReg` transversal dirs) with the
   leaks `Y0T1, T0Z1, Y0Z1` PURE QUADRATIC — exactly absorbable by a `dE(0)=id` straightening. So the
   genuine `E` IS the FULL reg blocks straightened; `deepestEPivot` is `E` with the quadratic leaks
   wrongly dropped (T=0). **This is the actual fix: `regStraighten` must straighten the FULL product's
   reg blocks, not the T=0 product's.**

**Caveat I cannot close (controller's call):** that `rlct(Φ_struct) = rlct(dlnLoss)` on the minimal
slice does NOT prove it for the full 8-dim (or general `H`) problem — the diffeo `u=Y1+Y0T1` is slice-
local. Whether the global `Φ_struct` (T=0) still has the right rlct despite the failed squeeze, OR
whether the chart genuinely needs the FULL-reg `regStraighten`, is the open soundness question. The
SAFE route is to make `regStraighten` produce the FULL reg blocks (option-1-flavoured) so the squeeze
becomes the leaf lemma's TRUE comparability — not to gamble that the wrong-zero-set `Φ_struct` happens
to have the right rlct.

## Secondary issues (brief's (i),(ii))

- (i) last-layer column: NOT a real inconsistency. `framedParamsRegPivot`'s last layer uses
  `pivotThresholdSplit r (H last.succ) (pivotJSucc J)` on the column side; the bundle's `hcorner` is
  `reindex(rThr, pivotThr J)(deepestPoint_last · Q_last) = fromBlocks 1 0 0 0` — also pivot-column.
  Consistent **provided** the same `J` threads through both (`deepest_gauge_construction`'s `hpivJ:
  pivotJSucc J = Jb` does this). It's a typecheck tripwire, not a soundness hole.
- (ii) `endpoint_telescoping` needs `hinterface (s) : Q_s = 1 ∧ P_{s+1}=1` for every **interior**
  `(s:ℕ)+1 < L`. `hQf0/hPfL` cover only the two boundary frames. For `L=2` there are no strict-interior
  interfaces, so `hQf0/hPfL` suffice. For `L ≥ 3` the missing hyp is `deepestPoint_interior_frame_id`
  (`Q_s = 1 ∧ P_s = 1` for `1 ≤ s ≤ L−2`), banked in `DeepestFrame.lean:108`. Thread it into `hinterface`.

## PIN1 survival under E_zero→E_full (the gating question for the repair — SETTLED)

**PIN1 (`deepestEPivot_regSlice_fderiv`) survives VERBATIM** (exact sympy + decorrelated Codex xhigh,
`codex/pin1-survival-*`, independent re-derivation agreeing):
- `E_full − E_zero = (0, Y0·T1, T0·Z1)` — purely degree-2.
- Reg-slice Jacobian at 0 (core+spec held 0): `D(E_full)(r0,0,0) = D(deepestEPivot)(r0,0) = F` (the
  invertible `regBlockCLE`). Leaks vanish at core=0; `O(‖h‖²)` ⇒ zero strict derivative at 0.
- Core-direction Jacobian at 0: `∂E_full/∂T0(0)=∂E_full/∂T1(0)=0`.
- So `D(E_full)(0) = [F | 0 | G]` (reg-in `F` invertible, core-in `0`, spec-in `G`).

**BUT the chart architecture must change** (the deeper consequence): the squeeze's reg term MUST be
`Sreg` (FULL reg blocks), which DEPENDS on the core. So `regStraighten`'s reg OUTPUT must read the core
— `E_pivot : (reg,spec)→reg` becomes `E_full : (reg,core,spec)→reg`. The corrected chart
`regStraighten q = (E_full q, q.2.1, q.2.2)` has derivative `[[F,0,G],[0,I,0],[0,0,I]]` at 0
(block-tri, diag `(F,I,I)`, det = det F ≠ 0 — INVERTIBLE), so the IFT/`#72` peel input is intact.
Verified `∑(new regStraighten).1² = ‖E_full‖² = Sreg` matches `dln=0` on line A — over-count gone.

**Architecture verdict (brief Q2):** PIN1 RE-USED as-is (the reg-slice fact + 1-line bridge
`E_full(·,0,0)=deepestEPivot(·,0)`), NOT a new analog, NOT orphaned. The new Lean work is generalizing
the `regStraightenOf`/`regStraightenTotalCLM` straightening object from `(reg,spec)→reg` to
`(reg,core,spec)→reg` (existing invertibility argument with `proj:=id`). Full build-ready spec:
`restatement-spec.md`. This also CLOSES the open rlct risk I flagged earlier — the safe full-reg route
makes the squeeze the leaf lemma's TRUE comparability, so the headline rlct no longer rests on the
unverified `rlct(Φ_struct)=rlct(dlnLoss)` gamble.

## Files

- Cert scripts: `/tmp/witness_yt.py`, `comparability.py`, `lower_confound.py`, `exact_lineA.py`,
  `epivot_exact.py`, `full_with_schur.py`, `option2_test.py`, `gauge_check.py`, `corank2.py`,
  `inf_correct.py`, `ratio_inf.py`, `pin1_survival.py`, `route_decision.py`, `arch_final.py`,
  `rlct_compare.py`, `rlct_minimal.py`, `diffeo_unit.py` (one-off; algebra reproduced in this thread).
- Codex artefacts: `codex/squeeze-soundness-{prompt,answer}.md`, `codex/pin1-survival-{prompt,answer}.md`.
- The false lemmas: `lean/DLNFibre/DLN/RLCT/Validate/DeepestGaugeConstruction.lean`
  `framedParams_split_eq_frame_raw` (~1327, the `h00/h01/h10` exact-equality conjunctions) +
  `deepest_loss_squeeze` (~1478, `hSreg_eq` ~1541).

exec
/bin/bash -lc "sed -n '1,220p' claim-card.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability
 succeeded in 0ms:
# Claim card — PIN2 option-2 comparability (`Sreg ≍ ∑deepestEPivot²`)

**Statement (the candidate, brief's option 2).** For `L=2, H=[2,2,2], r=1` (and `r=1` corank-≥2,
e.g. `H=[3,3,3]`), near the deepest point: ∃ `γ₁,γ₂>0` and a neighborhood `U` with, ∀ `w∈U`,
`γ₁·∑deepestEPivot²(split w) ≤ Sreg(w) ≤ γ₂·∑deepestEPivot²(split w)`, where `Sreg` = the FULL-product
regular block energy `(P00−1)²+P01²+P10²` (from `hconj`) and `∑deepestEPivot²` = the T=0
(`framedParamsRegPivot`) product regular block energy. (The proposed weakening of the exact `h00/h01/h10`.)

**Kill-condition (stated before hunting):** a point arbitrarily close to the deepest point where one of
`Sreg`, `∑deepestEPivot²` is 0 and the other is bounded away from 0 — refuting one direction of the
two-sided bound for any constant.

**Status: REFUTED (new tier).** Both directions killed by exact witnesses:
- Lower (`γ₁·Ereg ≤ Sreg`): **line A** `X0=X1=Z0=Z1=T0=0, Y1=−T1·Y0` → `Sreg=0`, `Ereg=(T1Y0)²>0`.
- Upper (`Sreg ≤ γ₂·Ereg`): **line B** `X0=X1=Y1=Z0=Z1=0` → `Sreg=(T1Y0)²>0`, `Ereg=0`.

**Tier:** new (our framing). **Evidence:** thread 31 (`thread.md`), sympy certificates
(`/tmp/option2_test.py`, `exact_lineA.py`, `comparability.py`), decorrelated Codex (`codex/`).

**Mechanism:** the inter-layer leak `(C0C1)₁₂ − (T=0)₁₂ = Y0·T1` (degree-2, same order as the signal,
produces exact cancellation). `Y0` is a GAUGE direction (verified: `δC0=corM·A` ⇒ `Y0` free; `G=[[1,−Y0],
[0,1]]` gauges line A to `(corM, diag(1,T1))`), so the T=0 product reads spurious gauge energy the true
loss does not see.

---

# Claim card — the correct comparable quantity (the repair)

**Statement.** `dlnLoss ≍ Sreg + Score` near the deepest point, where BOTH `Sreg = (P00−1)²+P01²+P10²`
and `Score = ‖P11 − P10⅟P00 P01‖²` are read off the FULL product `reindex(P0·N·QL) = fromBlocks
(P00−1) P01 P10 P11`. (= the banked leaf lemma `dlnLoss_two_sided_of_frame`.)

**Kill-condition:** a near-deepest point with `dlnLoss=0` but `Sreg+Score>0`, or vice-versa.

**Status: SURVIVED (new tier).** No witness found; `inf(dlnLoss/(Sreg+Score)) → 1` as scale→0 on
line-A-biased neighborhoods (`H=[2,2,2]` and `H=[3,3,3]`, `/tmp/inf_correct.py`, `corank2.py`); on
line A both = `det(P)/A`-equivalent and agree to machine epsilon. `Score = D − C A⁻¹B = det(C0)det(C1)/A`
(invariant core; Codex-confirmed). MC is a guide; the leaf lemma is the exact proof.

**Tier:** new framing of an already-banked sound lemma. **Evidence:** `dlnLoss_two_sided_of_frame`
(`DeepestGaugeBlocks.lean:558`, banked sorry-free); thread 31.

---

# Open risk (NOT a claim — flagged for controller)

`rlctAtOn(Φ_struct) = rlctAtOn(dlnLoss)` where `Φ_struct = ∑deepestEPivot² + ‖∏T‖²` (the structure's
hard-coded target). **Unresolved.** `V(Φ_struct) ⊊ V(dlnLoss)` (line A). On the minimal slice the two
RLCTs coincide (`= ½`) via the diffeo `Y1↦Y1+Y0T1` — but this is slice-local; the global statement is
NOT certified. The SAFE repair (repoint `regStraighten` to the FULL reg blocks) sidesteps this gamble.

exec
/bin/bash -lc "sed -n '1,220p' transfer-cert.md" in /home/ubuntu/workspace/geometry-of-dln-fibre/expeditions/2026-06-20-aoyagi-full/threads/31-pin2-comparability
 succeeded in 0ms:
# Transfer certificate — `regStraightenTotalCLM` to a core-reading reg block

Pre-staged paper certificate for the L2-PIN2 repair build (`l2-pin2-fullreg`)'s flagged-hardest piece:
the `regStraightenTotalCLM` invertibility when the reg output `E_full` reads the core slot. **Headline:
the transfer is a SIMPLIFICATION of the existing `_isUnit` lemma, not a new generalization** — the
block-triangular invertibility argument is agnostic to whether the carried (non-reg) slot is the
spectator `S` or the joined `W = C × S`. No new math; the settled facts are staged in build-ready form.

All settled algebra is from thread 31 (`thread.md`); this only re-states it against the exact Lean
objects (`DeepestRegAbsorbIFT.lean`, `DeepestRegSliceFderiv.lean`).

---

## (0) The objects, exactly (current Lean)

- `regInCLM : R →L[ℝ] R × S := (id).prod 0`, i.e. `r ↦ (r, 0)` (`DeepestRegAbsorbIFT.lean:498`).
- `regStraightenTotalCLM (D_E : (R × S) →L[ℝ] R) : (R × (C × S)) →L[ℝ] (R × (C × S))`,
  `δ ↦ (D_E (δ.1, δ.2.2), δ.2.1, δ.2.2)` (`:428`). Reg-out reads `(reg, spec)`; core/spec carried.
- `regStraightenTotalCLM_equiv_of_regBlock_isUnit (D_E) (F : R ≃L[ℝ] R)
   (hF : ↑F = D_E.comp regInCLM) : ∃ e ≃L, ↑e = regStraightenTotalCLM D_E` (`DeepestRegSliceFderiv.lean:616`).
  Proof: linearity `D_E(r,s) = F r + D_E(0,s)`; explicit inverse `(r',(c',s')) ↦
  (F⁻¹(r' − D_E(0,s')), c', s')`. `S` enters ONLY via the carried term `D_E(0, δ.2.2)`.

In the chart `R = (Fin nReg → ℝ)`, `C = (Fin (flatDim (deepestM)) → ℝ)` (core), `S = (Fin nGauge → ℝ)`
(spectator); `F = Fmap` the `regBlockCLE`-built `≃L` (`DeepestGaugeConstruction.lean:742`).

## (1) The generalized shear's total derivative at the origin = `[[F, 0, G],[0,I,0],[0,0,I]]`

The repair's reg output `E_full : R × (C × S) → R` reads ALL slots (`reg, core, spec`); the chart is
`regStraighten q := (E_full q, q.2.1, q.2.2)` (core/spec OUTPUT fixed). Write its derivative at 0 as
`D := fderiv ℝ regStraighten 0`. In block form, rows = (reg-out, core-out, spec-out), columns =
(reg-in, core-in, spec-in):

        D = [[ Dr E_full(0)   Dc E_full(0)   Ds E_full(0) ]      [[ F   0   G ]
             [      0              I             0        ]   =   [ 0   I   0 ]
             [      0              0             I        ]]      [ 0   0   I ]]

- `Dr E_full(0) = F` — PIN1's invertible `regBlockCLE`. (`E_full(·,0,0) = deepestEPivot(·,0)`; the
  reg-slice fderiv is `deepestEPivot_regSlice_fderiv`'s `F`. Thread 31: exact, sympy + Codex.)
- `Dc E_full(0) = 0` — the core-direction block vanishes (the leaks `Y0·T1, T0·Z1` are degree-2;
  `∂E_full/∂T(0) = 0`). Thread 31 + Codex pin1-survival, exact.
- `Ds E_full(0) = G` — the spectator block, possibly nonzero (coordinate-dependent); IRRELEVANT to
  invertibility.
- The core-out / spec-out rows are the literal carries `q.2.1, q.2.2`, derivative `[0,I,0]` / `[0,0,I]`.

(Row/col ordering matches `DeepestSplit = R × (C × S)`: `.1` reg, `.2.1` core, `.2.2` spec — the same
ordering `regStraightenTotalCLM` reads with `fst`, `snd∘snd`, `fst∘snd`, `snd∘snd`.)

## (2) Invertibility — det = det F ≠ 0 by block-triangularity

`D` is block UPPER-triangular with diagonal blocks `(F, I, I)`. Hence `D` is invertible ⟺ `F` is
invertible (the off-diagonal `G` and the zero `Dc` do not affect a triangular determinant / inverse).
`F` is invertible: it is `Fmap`, a `ContinuousLinearEquiv` built by `regBlockCLE` from `IsUnit (Pf
firstLayer)` (= `hPf`, the unit row frame) and `hQf22` (the pivot frame's `B₂₂`-unit block,
`DeepestGaugeConstruction.lean:740`). So `regStraightenTotalCLM`'s generalized form is a genuine `≃L`,
and the IFT/`#72` peel input (`HasStrictFDerivAt regStraighten D 0` with `D` an invertible `≃L`) survives
the `E_zero → E_full` swap. **The headline rlct value is unaffected** — the squeeze becomes the leaf
lemma's true comparability `dlnLoss ≍ Sreg + Score`.

The explicit inverse (matching the existing `_isUnit` shape, with `W := C × S` carried):
`(r', w') ↦ (F⁻¹(r' − D_E(0, w')), w')` where `w' = (c', s')` is carried identically. Verified
`left_inv`/`right_inv` reduce to `F.symm_apply_apply` / `F.apply_symm_apply` + `add_sub_cancel` /
`sub_add_cancel` — IDENTICAL to the existing proof (`:656–663`) with the `(c',s')` pair collapsed to `w'`.

## (3) The clean build target (the one transfer step the formaliser is likeliest to stall on)

Do **NOT** instantiate the existing lemma with `S := C × S` — that inserts a PHANTOM second core slot
`C'` (the def splits `(C × ·)` around its `S`). Instead re-state the straightening with the non-reg slot
**UNSPLIT** as a single `W`. This is STRICTLY SIMPLER than the current lemma (one fewer `Prod` layer):

    -- W := C × S, carried as a single slot.  regInCLM : R →L[ℝ] R × W,  r ↦ (r, 0).
    noncomputable def regStraightenTotalCLM2 (D_E : (R × W) →L[ℝ] R) : (R × W) →L[ℝ] (R × W) :=
      (D_E).prod (ContinuousLinearMap.snd ℝ R W)
      -- δ ↦ (D_E δ, δ.2)

    theorem regStraightenTotalCLM2_equiv_of_regBlock_isUnit
        (D_E : (R × W) →L[ℝ] R) (F : R ≃L[ℝ] R)
        (hF : (F : R →L[ℝ] R) = D_E.comp (regInCLM : R →L[ℝ] R × W)) :
        ∃ e : (R × W) ≃L[ℝ] (R × W),
          (e : (R × W) →L[ℝ] (R × W)) = regStraightenTotalCLM2 D_E := by
      -- D_E (r, w) = F r + D_E (0, w)   (linearity, hF)
      -- explicit inverse:  (r', w') ↦ (F.symm (r' − D_E (0, w')), w')
      -- left/right_inv: exactly the existing _isUnit proof with (c',s') ⟶ w' (one fewer Prod.ext).
      sorry

**Hypotheses the formaliser supplies** (all banked, unchanged): `F := Fmap` (the `regBlockCLE` `≃L`,
from `hPf` + `hQf22`); `hF : ↑F = D_E.comp regInCLM` (the reg-slice fderiv `= F`, from PIN1 + the bridge
`E_full(·, 0) = deepestEPivot(·, 0)` where here `0 : W = (C × S)` is BOTH core-zero and spec-zero); the
core/spec-out carry is `ContinuousLinearMap.snd`, so `regStraighten_core` (`(regStraighten q).2.1 =
q.2.1`) and `regStraighten_spectator` (`.2.2 = q.2.2`) both hold by `δ.2` being carried identically.

**If the formaliser prefers minimal churn** (keep `C`/`S` split in the *type* `DeepestSplit = R×(C×S)`):
the `W`-unsplit `regStraightenTotalCLM2` still applies with `W := C × S`, and the output `(D_E δ, δ.2)`
is DEFEQ to `(D_E δ, δ.2.1, δ.2.2)` — so `regStraighten_core`/`_spectator` are `rfl`. No phantom slot.

## Why this is low-risk

The invertibility argument (block-triangular, `F` unit) is the SAME as the banked `_isUnit` lemma; the
only delta is dropping one `Prod` layer in the carried slot. `F`'s invertibility source (`hPf` +
`hQf22` via `regBlockCLE`) is unchanged from PIN1. The two facts feeding `F = Dr E_full(0)` — the
reg-slice bridge and `Dc E_full(0) = 0` — are exact (thread 31, sympy + decorrelated Codex). No
re-derivation needed; this is the settled math in build-ready shape.

codex
**Q1 Verdict: incomplete as stated.**

Your S1-S4 spine is the right order for `(a)` and `(b)`, but S5 is too compressed and two obligations are missing.

**Exact-algebra obligations:**

- `E_full` must pack the **residual** regular blocks `(P00 - 1, P01, P10)`, not the raw product blocks `(P00, P01, P10)`. If its definition is “reg blocks of `prod(framedParamsPivot)`” without subtracting the normal corner in the `00` block, `(b)` is false at the deepest point.
- S1 needs the affine bridge
  `((paramsEquivFlat).symm (w - wstar)) s = (paramsSymm w)_s - deepestPoint_s`.
  If atom 1 already includes that bridge, fine; if not, it is a separate exact lemma.
- S5 needs an explicit lemma proving
  `Rcore := P11 - P10 P00⁻¹ P01`
  is the global Schur core and is comparable/equal to the `deepestCoreF(coreAbsorb(split w))` object. Atom 6 only compares `P11 = leak + Rcore` inside a regular-plus-core sum once a leak bound is known; it does not by itself identify `Rcore` with the coreAbsorb core functional.

**Structural/topological obligations:**

- Choose/shrink `U` so `P00` is invertible and `P00⁻¹` is uniformly bounded.
- Prove the leak estimate
  `∑(P10 P00⁻¹ P01)² ≤ t² Sreg`.
  This is not supplied by `fullProduct_core_split`; it is a small-neighborhood quadratic estimate using `P01,P10 → 0` and bounded `P00⁻¹`.

So the correct order is: choose reconciled frames/pivot data, prove S1/S1', telescope S2, normalize S3, define/extract blocks and hconj, prove residual packing for E_full, then prove unit/leak/core estimates.

**Q2 Verdict: mathematically a relabel; Lean-wise probably a separate bridge lemma.**

This is exact algebra, but not fresh matrix algebra.

If `pivotThresholdSplit J` is literally `rThresholdSplit` after a column permutation, and the last-layer reads are defined using the inverse pivot decoder, then the entry-wise decode survives. The proof should be a column-relabel/cases proof using `pivotThresholdSplit_symm_inl/inr`.

But atom 1 will not transfer by blind rewriting unless it was stated polymorphically over the column split. In Lean, expect a separate lemma:

`reindex_fromBlocks_reads_eq_deviation_pivotColumn`

whose proof is the same entry-wise proof plus the pivot permutation decode. Risk: type/cast/reindex bookkeeping, not mathematical soundness.

**Q3 Verdict: yes, there is a real consistency obligation.**

This is structural, not a new algebra theorem.

S2 uses the frame family’s endpoint `QL = Q_last`. S3 uses the `J,Q` from `exists_deepest_lastLayer_pivotFrame`. These must be the same data, or related by a stated equality/cast lemma.

The safe ordering is:

1. obtain the pivot witness `J,Q` from atom 5;
2. construct/select the deepest-point frame family using that same `Q` as the last-layer right frame;
3. set `QL := Q_last`;
4. prove `Q_last = Q` or make it definitional;
5. thread the same `J` into `framedParamsPivot`.

If the current construction already has an `hpivJ`/witness-threading lemma, then this is discharged. If not, S3 is not justified from S2’s endpoint frames.

**Q4 Verdict: your guessed S1' is not the highest-risk step.**

S1' is exact and annoying, but it is only a pivot-column relabel if the reads are correctly pivot-decoded.

The higher-risk step is the frame-source reconciliation for S3, because without it the endpoint frame used to telescope the actual product need not be the endpoint frame that normalizes `B` in the pivot block split. After that, the next real risk is S5’s core identification plus leak-smallness, because atom 6 assumes rather than proves the leak bound and does not identify `Rcore` with `deepestCoreF`.

The highest-risk step is **S3 frame-source reconciliation** because the same endpoint `QL` and pivot `J` must simultaneously drive telescoping, last-layer pivot decoding, and target normalization; the decomposition is **missing the explicit frame/pivot reconciliation, residual-packing clarification for `E_full`, the `P00` unit/neighborhood lemma, the leak-smallness lemma, and the global-Schur/coreAbsorb identification**.
tokens used
27,120
**Q1 Verdict: incomplete as stated.**

Your S1-S4 spine is the right order for `(a)` and `(b)`, but S5 is too compressed and two obligations are missing.

**Exact-algebra obligations:**

- `E_full` must pack the **residual** regular blocks `(P00 - 1, P01, P10)`, not the raw product blocks `(P00, P01, P10)`. If its definition is “reg blocks of `prod(framedParamsPivot)`” without subtracting the normal corner in the `00` block, `(b)` is false at the deepest point.
- S1 needs the affine bridge
  `((paramsEquivFlat).symm (w - wstar)) s = (paramsSymm w)_s - deepestPoint_s`.
  If atom 1 already includes that bridge, fine; if not, it is a separate exact lemma.
- S5 needs an explicit lemma proving
  `Rcore := P11 - P10 P00⁻¹ P01`
  is the global Schur core and is comparable/equal to the `deepestCoreF(coreAbsorb(split w))` object. Atom 6 only compares `P11 = leak + Rcore` inside a regular-plus-core sum once a leak bound is known; it does not by itself identify `Rcore` with the coreAbsorb core functional.

**Structural/topological obligations:**

- Choose/shrink `U` so `P00` is invertible and `P00⁻¹` is uniformly bounded.
- Prove the leak estimate
  `∑(P10 P00⁻¹ P01)² ≤ t² Sreg`.
  This is not supplied by `fullProduct_core_split`; it is a small-neighborhood quadratic estimate using `P01,P10 → 0` and bounded `P00⁻¹`.

So the correct order is: choose reconciled frames/pivot data, prove S1/S1', telescope S2, normalize S3, define/extract blocks and hconj, prove residual packing for E_full, then prove unit/leak/core estimates.

**Q2 Verdict: mathematically a relabel; Lean-wise probably a separate bridge lemma.**

This is exact algebra, but not fresh matrix algebra.

If `pivotThresholdSplit J` is literally `rThresholdSplit` after a column permutation, and the last-layer reads are defined using the inverse pivot decoder, then the entry-wise decode survives. The proof should be a column-relabel/cases proof using `pivotThresholdSplit_symm_inl/inr`.

But atom 1 will not transfer by blind rewriting unless it was stated polymorphically over the column split. In Lean, expect a separate lemma:

`reindex_fromBlocks_reads_eq_deviation_pivotColumn`

whose proof is the same entry-wise proof plus the pivot permutation decode. Risk: type/cast/reindex bookkeeping, not mathematical soundness.

**Q3 Verdict: yes, there is a real consistency obligation.**

This is structural, not a new algebra theorem.

S2 uses the frame family’s endpoint `QL = Q_last`. S3 uses the `J,Q` from `exists_deepest_lastLayer_pivotFrame`. These must be the same data, or related by a stated equality/cast lemma.

The safe ordering is:

1. obtain the pivot witness `J,Q` from atom 5;
2. construct/select the deepest-point frame family using that same `Q` as the last-layer right frame;
3. set `QL := Q_last`;
4. prove `Q_last = Q` or make it definitional;
5. thread the same `J` into `framedParamsPivot`.

If the current construction already has an `hpivJ`/witness-threading lemma, then this is discharged. If not, S3 is not justified from S2’s endpoint frames.

**Q4 Verdict: your guessed S1' is not the highest-risk step.**

S1' is exact and annoying, but it is only a pivot-column relabel if the reads are correctly pivot-decoded.

The higher-risk step is the frame-source reconciliation for S3, because without it the endpoint frame used to telescope the actual product need not be the endpoint frame that normalizes `B` in the pivot block split. After that, the next real risk is S5’s core identification plus leak-smallness, because atom 6 assumes rather than proves the leak bound and does not identify `Rcore` with `deepestCoreF`.

The highest-risk step is **S3 frame-source reconciliation** because the same endpoint `QL` and pivot `J` must simultaneously drive telescoping, last-layer pivot decoding, and target normalization; the decomposition is **missing the explicit frame/pivot reconciliation, residual-packing clarification for `E_full`, the `P00` unit/neighborhood lemma, the leak-smallness lemma, and the global-Schur/coreAbsorb identification**.
