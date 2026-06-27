# Certificate (addendum) — the achiever-path ↔ minAdm correspondence ∀M (KC1) + the pack shape (KC2)

**Seat:** pen-and-paper (witness). **Date:** 2026-06-27. Extends `certificate-decoder-fix.md` (the (C)-fix
verdict). Resolves the genuine crux KC1: pin the ∀M achiever descent path + the active-coord set with
`active.card = minAdm M`, with the correspondence proven to formalisation precision.

Decorrelated Codex (xhigh, independent — confirms the uniform rule + the kill-check): `codex/achiever-path-{prompt,answer}.md`.
Exact scripts: `scripts/mval_anchors.py`, `block_sizes.py`, `recheck_anchors.py`, `minimizer_choice.py`.

**Headline (NOT a research wall):** a UNIFORM rule exists ∀M — `active.card = minAdm M` always, by the very
definition of `minAdm` as the minimised sum of per-layer residual-block codims. The only caveat is the
*choice* of minimizer `T*` (the construction must FIX one explicit witness; any argmin works, the det is
invariant). No layer obstruction. KC1 is RESOLVED, not a wall.

---

## 1. The minAdm definition, restated as a sum of per-layer block codims (the load-bearing identity)

`minAdm M = (Adm M).inf' Mval` (`RouteMLayerSplit.lean:51`), where (`Foundations/Lambda.lean:35-42`):

    Mval M T = ∑_{j : Fin L} (tPrev M T j − T j) · (M_{j+1} − T j),   tPrev M T 0 = M_0, else T_{j−1}.

So writing the Aoyagi exponent vector `T = (t⁽¹⁾,…,t⁽ᴸ⁾)` (admissible: weakly decreasing, `t⁽ᴸ⁾ = 0`,
`t⁽ʲ⁾ ≤ admBound_j`; `t⁽⁰⁾ := M_0` by convention), **each summand is exactly the codim of a residual block:**

    term_j = r_j · c_j,   r_j := t⁽ʲ⁻¹⁾ − t⁽ʲ⁾   (rows dropped at boundary j),
                          c_j := M_{j+1} − t⁽ʲ⁾   (residual columns; the AFTER-width M_{j+1}).

`Mval M T = ∑_j r_j·c_j` by definition. Hence for the minimizer `T*`:

    **minAdm M = Mval M T* = ∑_j r_j·c_j  = the total count of residual-block entries of the achiever path.**

This is the correspondence: `minAdm` IS `∑ (block sizes)`, not derived — definitional. (`scripts/mval_anchors.py`,
`block_sizes.py`.)

---

## 2. The ∀M achiever chart's radial active set + `active.card = minAdm` (the uniform rule)

**The achiever descent path** is any minimizer `T* ∈ Adm M` of `Mval` (`Mval M T* = minAdm M`; exists since
`minAdm = min Mval` over the nonempty finite `Adm M`).

**The radial active set** = the disjoint union over all boundaries `j` of the `r_j × c_j` residual-block
coordinates (the normal directions to the achiever center at boundary `j`), placed in the chart's `Params`
matrix slots. Therefore

    **active.card = ∑_j r_j·c_j = minAdm M**  →  radialFactor det = |x_p|^{active.card − 1} = |x_p|^{minAdm − 1}.

This is the binding `leafH_pivot : leafH p = minAdm M − 1`. The rule is **uniform** (Codex Q1): a blow-up of a
smooth codim-`m` center has exactly `m` normal coordinates; the achiever center (the locus where the product
attains `T*`'s rank pattern) has codim `m = minAdm`, so the radial blows up exactly `minAdm` normals at ONE
pivot.

**ONE GLOBAL pivot, not per-layer** (Codex Q3, load-bearing for the rate). The radial is a SINGLE
`pivotBlowupOn(active, p)`: one chosen entry `p` among the `minAdm` residual normals is the fixed-1 / pivot
(`x_p ↦ x_p`), the other `minAdm − 1` residual normals across ALL layers are free actives (`x_q ↦ x_p·x_q`).
Per-layer pivots would introduce several independent radial parameters and break the single `F = (x_p)²·U`
rate. The single global pivot makes the leading product defect scale like `x_p` ⟹ `F = x_p²·U`. (The rate's
`u²` and the det's `x_p^{minAdm−1}` are the two orthogonal invariants of the SAME one-pivot blow-up — §certificate-decoder-fix.)

**The layer-op factors** (Schur shear det 1; the `b=aβ`/LDU substitutions, `pivotBlowupOn`s with their own
pivots) reparametrize the Schur frame and carry the GENUINE spectator monomials on `k=0` axes (the (3,3,4)
`|u 1|²`). They do not affect the radial `active.card`.

---

## 3. THREE-ANCHOR VALIDATION (the path + active set + active.card = minAdm; all exact)

| `M` | minAdm | minimizer `T*` (t⁽¹⁾…t⁽ᴸ⁾) | per-layer `(r_j, c_j, r_j c_j)` | `active.card = ∑` | banked radial card |
|-----|--------|---------------------------|--------------------------------|------------------|--------------------|
| (4,4,2,2) | 4 | (4,2,0) | (0,0,0), (2,0,0), (2,2,4) | **4** | `pb4422` card 4 ✓ |
| (3,3,4) | 8 | (1,0) | (2,2,4), (1,4,4) | **8** | `pb334` card 8 ✓ |
| (2,2,1) | 2 | (1,0) | (1,1,1), (1,1,1) | **2** | (new — §4b of decoder-fix cert: det `|u₀|¹`) ✓ |

(`scripts/mval_anchors.py`, `block_sizes.py`, `recheck_anchors.py` — exact integer arithmetic. The banked
`pb4422 = pivotBlowupOn {0,1,2,3} 0` and `pb334 = pivotBlowupOn {0,6..12} 0` have `active.card` exactly 4 and
8, matching `minAdm`.) For (4,4,2,2) all codim is in the deepest layer ([0,0,4]); for (3,3,4) it splits
[4,4]; for (2,2,1) it splits [1,1] — the rule covers all distributions.

**CRITICAL WIDTH-CONVENTION CAVEAT for the formaliser (a confound I hit and ruled out).** The radial active
count is the **Aoyagi** block sum (`c_j = M_{j+1} − t⁽ʲ⁾`, the AFTER-width). It is NOT the chain decoder's
Schur-frame `E`-block count (`c_s = M_s − Text(s+1)`, the BEFORE-width), which is a DIFFERENT number:
for (3,3,4) the chain E-blocks sum to 7, for (2,2,1) to 3 — neither equals minAdm (8, 2). (`scripts/recheck_anchors.py`.)
**Do NOT count the radial actives from `genBlkFlatStruct`'s `E`-slots.** Place them by the Aoyagi `r_j × c_j`
blocks directly in the `Params` matrix entries, exactly as the hand-built `pb4422`/`pb334` do (they chose the
active sets to match the Aoyagi codim, NOT the chain frame). This is consistent with the (C)-fix verdict: the
degenerate chain decoder is not the chart; the chart places actives by the Aoyagi codim structure.

---

## 4. The kill-check (Codex Q4) — uniform per minimizer; the ONLY caveat is minimizer choice

**No layer obstruction**: the `minAdm` residual normals (across all layers) form ONE normal space to the
achiever center; a single global pivot blows them all up. So a uniform rule exists ∀M.

**The one caveat — non-uniqueness of `T*`.** `minAdm` can have multiple minimizers (e.g. (2,2,1): `T*=(1,0)`
gives blocks [1,1]; `T*=(2,0)` gives [0,2] — both sum to minAdm=2). There is NO unique `M`-only active set;
the construction must FIX one minimizer first. **But this is benign:** any minimizer gives `active.card =
minAdm` (invariant), pivot exponent `minAdm − 1` (invariant), rate `u²` (invariant); the choice only shifts
the spectator-monomial distribution (all on `k=0` axes, threshold-irrelevant). (`scripts/minimizer_choice.py`.)
So the formaliser supplies ONE explicit witness `T*` with `Mval M T* = minAdm M` (an argmin — exists by the
`inf'` definition; can be a per-`M` `decide` witness or a chosen-minimizer function), and the rule is uniform
from there. **This is a design requirement, not a wall.**

---

## 5. KC2 (sketch) — the full-rank pack `Q_M` shape over opaque widths

The pack is ALREADY a banked reusable: **`measurePreserving_paramsPack_of_flatIdxEquiv M e pack hpack`**
(`Foundations/ParamsReshapeMP.lean`) takes ANY bijection `e : Fin (routeMAmbient M) ≃ FlatIdx M` and a
slot-equation `hpack : pack w q.1.1 q.1.2 q.2 = w (e.symm q)`, and yields `pack` measure-preserving (det ±1,
full-rank). The (4,4,2,2)/(3,3,4) `pack`s are exactly this with explicit `decide`-checked `Fin N ≃ FlatIdx`
tables (`fin28EquivFlatIdx4422`, `RouteM4422.lean:418`).

**General shape (the formaliser's build):** `Q_M := paramsEquivFlatCLE M ∘ pack_M CLM`, where `pack_M` sends
the `N = ∑_k M_k M_{k+1}` flat coords bijectively to the `Params M` layer-matrix entries. The bijection
`e_M : Fin N ≃ FlatIdx M` must:
- place the `minAdm` radial-active coords (the Aoyagi `r_j × c_j` block entries, §2) into the Params slots
  that carry the achiever center's residual directions (the bottom-right Schur residual of each layer);
- the pivot coord `p` into the chosen fixed-1 residual entry;
- the remaining `N − minAdm` coords (the spectators + layer-op directions) into the rest — **every flat coord
  lands in exactly one Params entry (bijection ⟹ NO dead slots ⟹ full rank).**

**The guard against reproducing the dead-slot bug (D1):** `e_M` is an `Equiv` (`left_inv`/`right_inv`), so by
construction NO output entry is unreached and NO input coord is dead. `measurePreserving_paramsPack_…` then
gives `|det Q_M| = 1` for free. **Verify `e_M` is a genuine `Equiv` BEFORE trusting the det** (the lesson of
D1: the degenerate `genBlkFlatStruct` was NOT a bijection — `Text(L)·M(L)` coords were dead). The opaque-width
build is the dependent-`Fin` reassociation kernel (`lean/CLAUDE.md`), routine but substantial; it is the
remaining KC2 engineering, NOT an open design question.

---

## Close

**Firmest result (KC1 resolved):** `active.card = minAdm M = ∑_j r_j·c_j` (`r_j = t⁽ʲ⁻¹⁾−t⁽ʲ⁾`, `c_j =
M_{j+1}−t⁽ʲ⁾`) is a UNIFORM ∀M rule — definitional from `minAdm = min Mval`; one global pivot scales one
fixed-1 residual, the other `minAdm−1` normals free; det `|x_p|^{minAdm−1}`, rate `x_p²·U`. Validated exact on
(4,4,2,2)/(3,3,4)/(2,2,1) against the banked radial `active.card`. Triple-confirmed (hand / integer / xhigh
Codex). **NOT a research wall.**

**Most likely to bite:** (a) the minimizer-choice requirement — the construction must fix ONE explicit `T*`
witness ∀M (benign: det invariant, but must be supplied, e.g. a chosen-argmin function or per-`M` witness);
(b) the width-convention trap — count actives by the Aoyagi `r_j × c_j` (AFTER-width `M_{j+1}`), NEVER the
chain `E`-blocks (BEFORE-width); (c) KC2 — `e_M` must be a genuine `Equiv` (no dead slots) before its det is
trusted.

**Next construction that settles the open part:** build `e_M : Fin N ≃ FlatIdx M` placing the chosen-`T*`
Aoyagi blocks into the Params residual slots (the dependent-width bijection), then `Q_M` via
`measurePreserving_paramsPack_of_flatIdxEquiv`, then `φ_M = Q_M ∘ pivotBlowupOn(active, p)` with the layer-op
factors — the explicit (C) chart, det `∏_j |x_j|^{leafH j}` via `phiTarget_abs_det_of_factored`.
