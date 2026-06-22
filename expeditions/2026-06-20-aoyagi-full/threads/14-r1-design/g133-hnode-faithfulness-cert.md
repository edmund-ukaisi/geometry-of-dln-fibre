# Fidelity cert — `schur_straighten_squeeze_exists` + `hnode` (the per-node producer, #16)

Reviewer: early independent fidelity pass on `fm2/r1-squeeze-complete` @9694641
(`lean/DLNFibre/DLN/RLCT/Validate/GeneralR1Recursion.lean`). crux2 authored `hnode`, so this is the
decorrelated eye. Decorrelated Codex xhigh (`codex/g133-hnode-faithfulness-{prompt,answer}.md`). Build
GREEN (2673 jobs). Triggered early to de-risk fm3's discharge.

## Verdict: SURVIVED — `hnode` is a faithful, appropriately-tight Schur-node CONTRACT

The four foci all pass. One scope observation (the contract is not a recognizer — by design, lands on
fm3's (b1) discharge).

### (1) HONEST — does NOT smuggle the coord identity. CONFIRMED.
`schur_straighten_squeeze_exists` (line 610) concludes `∃ c₁ c₂, IsSchurStraightenSqueeze M S flatCore
G redEmbed c₁ c₂` with `flatCore` a FREE function argument. Grep confirms: the only `dlnLoss` in the
theorem is `dlnLoss S.red 0` (the REDUCED chain, via the free hypothesis `hredCore`). **`dlnLoss M 0`
(the full-chain node loss) appears NOWHERE** — the theorem does not assert "dlnLoss M 0 ∘ pivotBlowupOn
= ‖Â·A2‖²". `hnode` only PRESENTS the abstract `flatCore` in Schur-node form near (0,0); it does not
define it. Verifiable from the statement alone. HONEST.

### (2) hnode FAITHFUL (the high-value one). CONFIRMED (Codex-decorrelated).
hnode conjunct (1) `flatCore w = (∑ⱼ w.1ⱼ²) + ∑ᵢⱼ (bcol·w.1ⱼ + SΓ)²` is EXACTLY ‖Â·A2‖² for
`Â = [[1,a],[b,D]]`, `A2 = [[β],[Γ]]`, identifying `w.1 = E_row = β + a·Γ` (pivot-row product, the
regular generators), `bcol = b` (pivot column), `SΓ = (D−b·a)·Γ = S·Γ`:
- Matches the GREEN ring identity `schur_row_decomp` (lower = `b·E_row + S·Γ`) and g127's witnessed
  loss identity on the (3,3,3) reduced node.
- Regular block is unit-coefficient `∑(w.1ⱼ)²` — correct for the hard pivot `Â[0,0]=1` and standard
  Frobenius loss. NO cross term between the top (regular) row and the lower block (different Frobenius
  entries); the only regular/core coupling lives INSIDE `(bcol·w.1 + SΓ)²`. Codex confirms.
- Conjunct (2) `G² = ∑(SΓ)² = ‖S·Γ‖²` is the genuine smaller matrix-chain core (the next recursion
  node), faithful (NOT ‖Â·A2red‖² or another residual).
- Conjunct (3) `∑bcol² ≤ T²` (bounded pivot column) is the RIGHT and SUFFICIENT smallness for a UNIFORM
  point-independent two-sided constant squeeze (`∑(bcol·w.1)² = ‖bcol‖²·∑w.1² ≤ T²·∑w.1²` is an EQUALITY
  feeding `squeeze_bounds_abstract`). No hidden `b→0` requirement (b→0 only sharpens c₁→½, c₂→2); only
  local boundedness is needed.
- The `x²` monomial blow-up Jacobian is correctly EXCLUDED (separate cover lane), per the file's lane
  split and g126.

### (3) NON-VACUITY — a CONCRETE real node (NOT the trivial ⊤-regime). CONFIRMED by a compiled witness.
Built and compiled `∃ c₁ c₂, IsSchurStraightenSqueeze M0 S0 flatCore0 G0 redEmbed0 c₁ c₂` via
`schur_straighten_squeeze_exists` with M=![2,1] (real dim drop), Y=ℝ, nReg=1, Mblk=Fin 1, T=0, **G = id
so G 0 = 0** (the genuine deepest point, finite RHS — addressing my prior FLAG-B: this is NOT the
`G 0 ≠ 0` ⊤-regime). `Gne` holds (`id ≠ 0` a.e., only {0} null). All three hnode conjuncts discharge on
a nbhd and are jointly consistent with `hredCore` (both pin G²: `dlnLoss S.red 0 (redEmbed w.2) =
∑SΓ²` holds). Not self-contradictory; not vacuously satisfiable by degenerate data in a misleading way.

### (4) clean-three / S2-free. CONFIRMED.
`#print axioms` on all 7 producer decls: `schur_straighten_squeeze_exists`, `schur_node_squeeze_unif`,
`schur_node_squeeze`, `squeeze_bounds_abstract` are clean-three `[propext, Classical.choice, Quot.sound]`;
the two pure ring lemmas `schur_lossDiff_eq_cofactor`, `schur_lossDiff_mem_ideal` are even cleaner
`[propext, Quot.sound]`. NO `monomial_rlct`/S2 (S2 stays in the cover/blow-up lane, downstream).

## Same-zero-set (the c₁>0 structural point, re-confirmed)
`squeeze_bounds_abstract`'s lower bound `Φ ≤ 2(1+t²)·F` is genuine because `p = bcol·E_row` is E-TIED:
`flatCore = 0 ⇔ E_row = 0 ∧ (b·E_row + SΓ) = 0 ⇔ E_row = 0 ∧ SΓ = 0 ⇔ Φ = 0`. This is exactly why the
prior `F=(G+E)²`-vanishing-on-`G=−E` counterexample (raised in my g132 pass) is EXCLUDED here: crux2's
`p = b·E_row` keeps the perturbation inside the E-ideal, so the squeeze's c₁>0 is structural, not
accidental. The ideal-membership-insufficiency caveat is met.

## Scope observation (NOT a flag — by design)
hnode is a CONTRACT, not a RECOGNIZER: arbitrary bounded `bcol` + arbitrary `SΓ` satisfying (1)-(3)
need not come from a real Schur chart. This is correct architecture — the theorem proves "IF the node
has this form THEN the datum exists", isolating the (b1) obligation. fm3's discharge must prove hnode
from the actual block data: `bcol = b`, `SΓ = (D−b·a)·Γ`, `w.1 = β + a·Γ`, `flatCore = ‖Â·A2‖² =
dlnLoss M 0 ∘ pivotBlowupOn` (modulo the x² weight lane), `G² = dlnLoss(reduced)`, local boundedness of
b. If those are the discharge obligations, fm3 is chasing the RIGHT shape.

## Net
The interface is correct; the cover/fm3 can build on it. The fuller pass (hnode DISCHARGED from
`dlnLoss M 0 ∘ pivotBlowupOn` (b1) + the FLAG-A (b2) RLCT-transport closed) comes after fm3 lands green.

## CLOSURE (2026-06-22, the (b1) sharpening — convergence with fm3)
fm3's discharge surfaced the exact quantitative form of the (b1) obligation this cert named. The
"contract, not recognizer" caveat is sharper than a caveat: **`dlnLoss M 0 ∘ pivotBlowupOn = x_p²·Q`**,
NOT the bare residual `Q = ‖Â·A2‖²` (`x_p` = the blow-up pivot coord). I verified this decorrelated
(sympy, a 3-layer toy: `loss∘blowup − x_p²·Q = 0` exactly), independent of fm3's (2,2,2) sympy and
Codex — three reads converged. The `x_p²` is forced by MULTILINEARITY: the loss is degree-2 in the
first-factor block, `pivotBlowupOn` (S1G5Charts:384) scales the WHOLE block by `x_p` (pivot entry
`= x_p`, active off-pivot `= x_p·x_j`), so `‖prod‖² = x_p²·‖Â·A2‖²`. No reading makes it the bare `Q`.

Consequence: `hnode` + `schur_straighten_squeeze_exists` are FAITHFUL to `flatCore := Q` (the residual);
fm3's `schur_node_loss_presentation` (`Q = ∑E²+∑(b·E+S·Γ)²`, green, clean-three) anchors that reading.
They are UNFAITHFUL if read as the presentation of `dlnLoss∘blowup` (off by `x_p²`). Folding `x_p²` into
`Q` (the surfaced option A) is UNSOUND, not merely lossy: `rlct(x_p²) = 1/2` (`∫|x|^{−2c}` converges iff
`c<1/2`), so dropping it per-node telescopes to ambient/2 (= 4 for (2,2,2)) — the documented-FALSE error
of the file's SOUNDNESS NOTE (GeneralR1Recursion.lean:18-24) + g128. The controller's decision (C) routes
the `x_p²` through the banked monomialThreshold/cover lane (which yields the verified 3/2), keeping the
per-node squeeze toolkit clean-three / S2-free and off the critical path. Architecture settled correctly;
no defect in crux2's per-node toolkit — the finding was a pre-emptive wiring guard (no consumer wires
`flatCore := dlnLoss∘blowup` on any branch yet).
