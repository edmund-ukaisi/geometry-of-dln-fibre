# Chart-architecture fork — FOLDED vs DECOMPOSED (pen-and-paper adjudication, pnp-chartarch)

**Seat:** pen-and-paper (adjudication). **Direction:** settle the fork surfaced by routeP-p1's 5b STOP.
**Method:** exact algebra (sympy, exact-rational/symbolic) + decorrelated Codex (xhigh). NO Lean edits.
**Verdict:** the fork is a **near-false dichotomy** — recommend **(B) DECOMPOSED**, with the correction
that **(B) does NOT re-open the crux**. The "folded" chart already IS a shear∘blow-up composite; the
banked crux transfers by an extensional identity, and the Jacobian follows by the chain rule over banked
atoms — no 21×21 determinant, no crux re-proof.

## The one-line answer

`gWrap = sigmaPiv ∘ gFaithful` is **exactly** the banked-atom composite (sympy-verified, exact):

```
gWrap  =  sigmaPiv  ∘  H  ∘  P  ∘  A0  ∘  A1
```
| atom | what | |jacDet| | banked as |
|---|---|---|---|
| `A1` | `blockBlowupMap {1,5,6,7} 1` | `u1³` | `jacDet_blockBlowupMap` (O9) |
| `A0` | `blockBlowupMap {0,1,…,7} 0` | `u0⁷` | `jacDet_blockBlowupMap` (O9) |
| `P`  | permutation of slots 0–11 = `[8,9,10,11,1,5,6,7,0,2,3,4]` | `1` (det −1, 45 inversions) | `Matrix.det` of a perm / reindex equiv |
| `H`  | unipotent block-shear (reads only kept coords) | `1` | `jacDet_blockShear` (GeneralGeoAtlas) |
| `sigmaPiv` | `blockBlowupMap {0..7,20} 20` | `u20⁸` | `jacDet_blockBlowupMap` (O9) |

`|jacDet gWrap u| = u0⁷·u1³·u20⁸` (= the routeP-p1 sympy monomial), by `jacDet_comp` composition, **with
no 21×21 determinant**. Every atom's Jacobian is already proven general + axiom-clean.

## The four fork questions, settled

### Q1 — general-`d` charts are necessarily DECOMPOSED. CONFIRMED.
`DLN/Aoyagi/GeneralGeoAtlas.lean` already builds the general-`d` L6/L7 for the **decomposed** chart
`shear ∘ blockBlowupMap`, sorry-free + axiom-clean, over general `Fin D`: `GeoStep.stepMap =
shear ∘ blockBlowupMap S p` (blow-up inner, shear outer); `abs_jacDet_geoPath` gives the whole-branch
`|jacDet| = ∏ per-node blow-up monomials` (unit ≡ 1 down the branch); `shearBlowup_hjac` /
`outerShearBlowup_hjac` are the dom-wide `Chart.hjac` field; `outerShearBlowup_injOn` the
`hg_inj`/`hexcep`; the cover assembly is `covers_fanOfSteps`/`exists_ball_subset_outerFan_leafImages`.
The general-`d` leaf chart is a `List (GeoStep)` composition — decomposed by construction.

### Q2 — the folded `gFaithful` was the (3,3,4) DE-RISK, not a general-`d` chart. CONFIRMED.
`gFaithful` is a hand-crafted (3,3,4)-`t=(1,0)`-specific explicit polynomial map; the crux proof
`peeled_comp_gFaithful` is a `fin_cases i <;> fin_cases j <;> ring` brute-force over the 12 entries —
it does NOT template general-`d` **as a proof**. Its value is the DE-RISK it discharged (banked,
doubly-confirmed): the terminal monomialisation `⟨peeled∘g⟩=⟨E⟩` **closes two-sided on a genuinely
coupled instance**. That measurement is done and stays banked whichever path we take.

### Q3 — THE CRUX-TRANSFER: sub-case (i), transfers FREE (up to one funext). CONFIRMED exact.
The folded `gFaithful` **is** the decomposed chart, just written collapsed. Sympy-exact:

- **(F1)** `gFaithful = H ∘ P ∘ A0 ∘ A1` extensionally (all 21 coords match); `det Jac H = 1` (unipotent),
  `det Jac(P∘A0∘A1) = −u0⁷u1³`.
- **(F2)** `peeled ∘ gFaithful`: all 12 entries divisible by `E=u0`; pivot `peeled[0][0]∘gFaithful = u0`
  exactly (cofactor 1) — the banked crux.
- **(F3)** `peeled ∘ (blow-up only, shear H dropped)`: **0 of 12** entries divisible by `E`
  (`peeled[0][0]∘B = u0 + u12·u8 + u16·u9`). So **the shear H is LOAD-BEARING for the monomialisation**.
- **(F4) the mechanism:** `H`'s shear terms `−u8u12−u9u16 …` in slots 8–11 EXACTLY cancel the `Q2inv`
  recoord terms `+x0x12+x1x16 …` that `peeled`'s row 0 carries, leaving pure `E`; `H`'s `+v0v2 …` terms
  cancel `diag(1,Δ)`'s `−x0x2 …`, leaving pure `u0·u1`. The shear undoes the block-elim recoord so the
  blow-up can extract the exceptional monomial. This is precisely the `GeoStep` `shear ∘ blockBlowupMap`
  structure.

Because `gFaithful = H∘P∘A0∘A1` is the **same map**, the banked two-sided `hideal`
(`Corank2FaithfulComposite.crux_radial_monomialise`, `hideal_faithful_*`, `Corank2CoreGenWrap.hideal_coreGen_*`)
holds for the decomposed presentation verbatim. Sub-case **(i)** — no monomialisation re-proof. The only
new obligation is the extensional identity `gFaithful = H∘P∘A0∘A1` (funext + fin_cases on 21 explicit
degree-≤4 coordinate polynomials — detail-at-scale, bounded), after which the crux/`hideal` are rewritten
along it and the Jacobian is assembled from the atoms.

**FLAG check — is (B)'s crux-transfer clean?** YES. The folded convenience did NOT hide a genuine gap: the
E-factorisation is not an accident of the collapsed writing — it is the shear-cancels-recoord mechanism
(F4), which is exactly what the decomposed spine does node-by-node. No STOP.

### Q4 — RECOMMENDATION: (B) DECOMPOSED, corrected.
Recommend **(B)**, i.e. present `gWrap` as the banked-atom composite and get rung 5b (L6 `hjac`/`jac`/
`hg_inj`/`hexcep`) from `jacDet_comp` + the banked per-atom Jacobians (`jacDet_blockBlowupMap`,
`jacDet_blockShear`, permutation det), reusing `GeneralGeoAtlas`'s proven L6. Keep the banked folded
two-sided `hideal` (rung 5a) untouched — rewrite it along `gFaithful = H∘P∘A0∘A1`. This dominates (A):
- avoids the (A) 21×21 symbolic block-triangular determinant (heavy at scale; `Matrix.ext` per-entry
  simp blow-up — see lean/CLAUDE.md det-at-scale notes);
- does NOT pay (B)'s feared "re-open the crux" — that premise is false (Q3);
- reuses the general-`d` L6 machinery (not a (3,3,4)-throwaway, unlike a bespoke 21×21 det), and confirms
  the general-`d` chart form + the load-bearing role of the shear (structural de-risk for the general build).

**The one load-bearing caveat (Codex Q4 + F1):** the coordinate permutation `P` (det −1, 45 inversions,
`[8,9,10,11,1,5,6,7,0,2,3,4]` on slots 0–11) MUST be represented explicitly — omitting it, or reversing
the composition order, breaks the extensional identity and the det sign. It is benign (a permutation +
its det ±1, absorbed by `|·|` in the `hjac` field shape), NOT open math, but it is named and load-bearing.

## The general-`d` chart-architecture TEMPLATE (deliverable)

**Chart form.** A leaf chart is a root→leaf composition over `buildTree` of per-node steps, each
`step = (unipotent block-shear sh_node) ∘ (blockBlowupMap S_node p_node)` (blow-up inner, shear outer) —
the `GeoStep.stepMap` form. Between nodes, coordinate roles are relabelled by a benign permutation
(det ±1); build it into the node's center/pivot indexing to avoid a standalone `P`, or carry it as an
explicit reindex factor.

**Per-step Jacobian.** `|jacDet (sh ∘ blockBlowupMap S p) u| = |u_p|^(|S|−1)` (shear-pin `jacDet sh ≡ 1`
+ `jacDet_blockBlowupMap`). The branch composite is `|jacDet g_leaf u| = ∏_node |run_p_node|^(|S_node|−1)`
via `abs_jacDet_geoPath` — unit ≡ 1 down the whole branch (no residual unit factor; the germ-only trap is
structurally void). This is the `Chart.hjac` field with `unit := fun _ ↦ 1`.

**Per-step ideal identity (the spine that composes to `hideal`).** At each node:
1. **L-A block-elim** (banked `blockElim_step_fwd/_bwd`, `regionRepresents_of_matrix_mul`): the unimodular
   Schur clearing `Q1·C1·Q2 = diag(1,Δ)` changes generators `⟨C1·C2⟩ = ⟨peeled⟩`, both directions,
   polynomial cofactors — no chart, no substitution.
2. **the shear** (edge-shear, load-bearing per F4) cancels the `Q2⁻¹`/Schur recoord terms that L-A leaves
   in `peeled`, so that
3. **the blow-up** `blockBlowupMap S_node p_node` extracts the node exceptional monomial: every pulled-back
   entry becomes `b_node · (poly)`, the cleared pivot `= b_node` exactly (cofactor 1).
4. **L-B maintenance** (banked `maintenance_step_two_sided`): the b-chain `b_p ∣ b_i` makes the residual
   row-clear a two-sided ideal identity with continuous cofactor `c_i·r_i` (reverse absorbed by the chain).
5. **L-C terminal** (banked `terminal_bezout` / `hideal_terminal_both`): at the terminal block, the
   cleared-pivot unit `≡ 1` gives the reverse `⟨b⟩ ⊆ ⟨resid∘g⟩` with cofactor `1/unit` continuous — the
   two-sided `⟨(∏C)∘g⟩ = ⟨diag b⟩`.

Composed via `regionRepresents_comp` (precompose with the continuous node chart) + `RegionRepresents.trans`.
The mechanisms are proven two-sided + general in isolation; the general-`d` build is the **structural
induction over `buildTree`** assembling them + the (benign) inter-node relabelling — bounded
detail-at-scale, NOT new math. The (3,3,4) instance is the first, fully-worked case: shear cancels recoord
(F4) → blow-up extracts E → terminal cofactor-1 reverse — end-to-end, exact.

## Codex (decorrelated, xhigh) — independent read
Fired with frame + facts, my conclusion withheld. Codex independently:
- Q1: "genuinely shear-after-blow-up; the shear is load-bearing, not accidental" (from F2/F3).
- Q2: reconstructed **the same** `B = P ∘ A0 ∘ A1` factorisation (pivots u1 center {1,5,6,7}; u0 center
  {0..7}; the identical permutation tuple `(8,9,10,11,1,5,6,7,0,2,3,4)`, 45 inversions, det −1) — verified
  exact here.
- Q3: "No crux re-proof is required. Prove `gFaithful = H∘B` pointwise, rewrite the already-proved
  divisibility/ideal identity along that equality; derive the Jacobian independently."
- Q4: "Main trap: silently omitting the coordinate permutation" (det sign / non-extensional).
Independent recommendation matches: decompose, transfer the crux free, mind the permutation.

## Artifacts
- `/tmp/decomp_check.py` — `gFaithful = H∘B`, `det H = 1`, `det B = −u0⁷u1³`, chain-rule product.
- `/tmp/peeled_div2.py` — `peeled∘gFaithful` 12/12 E-divisible (pivot = E); `peeled∘B` 0/12 (shear load-bearing).
- `/tmp/verify_B_decomp.py` — `B = P∘A0∘A1` exact, perm `[8,9,10,11,1,5,6,7,0,2,3,4]`, 45 inversions, dets.
- `threads/pnp-chartarch/codex/fork-answer.md` — the decorrelated Codex answer.
