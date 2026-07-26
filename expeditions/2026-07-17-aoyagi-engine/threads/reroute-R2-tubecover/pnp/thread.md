# pnp nodewise residual-at-center (3,3,4) — thread

Seat: pen-and-paper, `obstruction`-leaning (pin N_singular exactly + catch the hidden monument).
Dispatched by main. Scout accelerator (9-type table + PIN1/PIN2) + elder heads-up (hidden-#172 vs
monument) folded in.

## Established EXACTLY (sympy, exact algebra)

Scripts in this dir:
- `residual_at_center_334.py` — first pass, mechanism map.
- `loss_gcd_toggle.py` — the DECISIVE toggle on the canonical chart (uses the exact Lean maps A0,A1,
  gFaithful, sigmaPiv).
- `deep_coupled_recursion.py` — the self-similar deepest-block survivor check (PIN 2).

### F1 (canonical minimiser chart is SINGULAR; both shears load-bearing) — EXACT
`loss_gcd_toggle.py`: the 12 loss generators P∘gWrap, monomial GCD:
- both shears ON: GCD = u0·u20, residual generator[0]=1 at center → SURVIVOR present (sandwich fires).
- recoord shear OFF: GCD collapses to u20, ALL residuals vanish at center → OVER-VANISHES.
- within-layer Schur (of the S=2 Δ-block) OFF: GCD → u20, all residuals vanish → OVER-VANISHES.
=> the S=2 minimiser chart is SINGULAR; the born (recoord+Schur) shear is what exposes the pivot
   survivor P[0,0]∘g = E·1. Matches census fact 4 (SHEAR-FREE IS REFUTED on the minimiser).

### F2 (no structural-zero pivot at any level → NO deep {R=0}) — EXACT
`deep_coupled_recursion.py`: the coupled recursion peeled rows≥1 = E·α·(D̄·S) is a smaller self-similar
product; resolve level by level r=3,2,1. At EVERY level the T-row pivot = the RECOORDED B-pivot:
  r=3: a01·b10 + a02·b20 + b00   (≠0)
  r=2: a01·b10 + b00             (≠0)
  r=1: b00                       (≠0);  deepest 1×2 row [w0,w1] → blow up → [E·1, E·t], pivot 1.
None is a structural zero → the radial normalizes each to E_r·1 (a UNIT). Survivor at every level.

### F3 (Δ-block descendants are non-binding) — EXACT
Exceptional-degree: T-row pivot = E (deg 1), Δ-block = E·α·(…) (deg 2). T-row strictly minimal ⇒ the
binding (exponent-8) divisor is ALWAYS a T-row pivot, never a coupled Δ-block. So the binding chart
always has a clean unit survivor after its shear.

## Classification of the 9 shear-step types

Discriminant: does dropping the shear at that type kill the leaf's survivor? Survivor is the pivot
entry = (leaf monomial)·1. KEY structural fact: K is on the PRODUCT P=A1·A0 — the loss survivor needs
BOTH layers cleared, so it is born at S=2 (a single-layer S=1 clearing exposes P∘g = E1·(deeper stuff)
which still vanishes at 0). Hence:

- T1,T2,T3 (S=1 case2, within-layer Schur only, NO recoord): SMOOTH. The survivor is born at S=2, so
  dropping the S=1 Schur does not kill it. Verified: on gWrap the S=1 clearing = `sigmaPiv` (the c11 =
  9-coord = 3×3-center blow-up) is BARE (shear-free) and the survivor still fires; the u20 it
  contributes is NON-binding (jac 8; binding is u0, jac 7). T3's 1×1 center blow-up is identity anyway.
- T4–T9 (S=2 case12/case2, recoord + Schur): SINGULAR. The recoord shear is load-bearing (F1). Same
  self-similar recoord mechanism at each depth (bounded fill, one mechanism × 6 instantiations).

=> **N_singular = 6  (T4–T9),  N_smooth = 3  (T1–T3).**
   (PIN 1's "large N_smooth" is at the LEAF granularity — many case11-reuse leaves expose the binding
    shear-free; the TYPE count is 3 smooth of 9.)

## HIDDEN-MONUMENT VERDICT: **NO monument.**
- No residual survives-vanishing after its shear (F2: every pivot is a nonzero recoorded coordinate).
- The binding is always a clean T-row pivot (F3), so PIN 2's deepest 1×2 (T9) is NON-binding on any
  leaf where it is a Δ-descendant, and where it IS the last clearing its own pivot is a unit survivor.
- Since NOTHING survives-vanishing after shear, we are in the SIMPLEST regime: a bounded born-α fill
  (one recoord shear per S=2 type, survivor exposed), NOT even a hidden-#172 recursion. The self-
  similar peel terminates (depth −1/level, bottoms at the 1×2 = L=1 Morse), ratio = ½·minAdm = 4.
  So even the elder's fallback (hidden-#172, bounded) is not triggered — the (3,3,4) discharge is a
  clean bounded fill.

### F4 (deep-level SINGULAR + survivor — the PIN 2 exact second data point) — EXACT
`deep_chart_ablation.py`: the corank-1 coupled block M = D̄·S (2×3 = T8, 1×2 sub-row = T9), explicit
faithful chart with the recoord shear S[0,j] = E·(1,t1,t2)[j] − d01·S[1,j]:
- recoord ON : GCD = E, pivot residual M[0,0]/E = 1 at center → SURVIVOR (the recoord cancels d01·S10,
  M[0,0] = (E − d01·S10) + d01·S10 = E exactly — the gFaithful mechanism at the deeper level).
- recoord OFF: GCD = 1, all residuals vanish at center → OVER-VANISHES → SINGULAR.
- T9 (1×2) in isolation: recoord ON → survivor 1; OFF → over-vanishes.
So the DEEPEST blocks (T8,T9) are SINGULAR-with-survivor by the IDENTICAL self-similar recoord
mechanism as the corank-2 canonical (T6). PIN 2 settled: the deepest 1×2 has a clean unit survivor
AFTER its shear; no deep {R=0}.

## Decorrelated Codex (`codex/nodewise334-{prompt,answer}.md`) — reconciliation
- CONFIRMS Q2 (no monument) INDEPENDENTLY: "if every original residual vanished, every unimodular
  combination would vanish too, contradicting the pivot unit E_k" + Δ-descendants ≥9 can't be
  binding-8, recursion bounded 3×4→2×3→1×2, "cannot form a non-terminating or ratio-below-½ monument."
- PUSHES on the COUNT: grants only T6 as exact-singular from the brief; says the exact N needs the
  full-tree single-edge ablation table (per-type). I have since added T8/T9 exact (F4). T4,T5,T7
  (case12 splits) remain mechanism-inference (fresh-pivot needs the recoord — same as T6/T8/T9).
- Its "biggest risk" = a COVER risk: some case12/Δ/zero-pivot branch not routed to a finite chart with
  continuous unimodular recoord → a NEW exceptional divisor on an unresolved branch. This is a
  set-cover obligation (route-a hcover), DISTINCT from the survivor value; it does NOT reintroduce a
  monument (F2/F3 are cover-independent), but it is the honest open edge of the discharge.

## Residual risk / what would overturn "no monument"
- The one non-exact step is the S=1-benign classification of T1,T2,T3 (rests on "survivor born at S=2"
  + the gWrap sigmaPiv-shear-free verification for T1). If the FLAT tree cover is FORCED (cannot use
  gWrap-compressed charts) AND a deep S=1 Schur turns load-bearing on a t1=2/3 non-minimiser leaf,
  N_smooth could drop from 3. It cannot ADD a monument (F2/F3 are cover-independent), only shift the
  smooth/singular boundary among the S=1 types.

## ×6 born-α HPULL TEMPLATE (r2build pnp, 2026-07-26) — the formaliser's build cert for #188

Scripts (exact sympy): `born_alpha_cert_334.py` (universal mechanism × 6 block-shapes),
`leaftype_census_334.py` (288-leaf fixed-shear census), `jac_divisormin_334.py` +
`perleaf_divisormin_334.py` (concrete full-composite Jacobian / divisorMin),
`permconj_jac_334.py` (perm-transport of the jac). Codex `codex/bornalpha-cert-*`.

**F5 (the universal born-α, EXACT).** At EVERY (3,3,4) block-shape (r,c) ∈
{(3,3)=T6,(2,3)=T8,(1,2)=T9,(2,2)=T4,(3,4)=T5,(1,3)=T7}, the block-recoord shear
`S[0,:] := E·(1,t₂..t_c) − Σ_{i≥1} D̄[0,i]·S[i,:]` (unipotent |det|=1, reads only residual
rows) makes the pivot `M[0,0] = E` EXACTLY (block-elim cross-term cancels), so the pivot
residual `= M[0,0]/GCD = 1` a CONSTANT. Single-entry survivor at index 0. recoord-OFF
over-vanishes on the coupled shapes (T4,T5,T6,T8); the terminal 1×c rows (T7,T9) keep the
survivor via the radial alone.

**F6 (survivor exactly 1 ⟹ global sandwich).** resid₀ = 1 everywhere ⟹ ρ_leaf = ∞;
`loss∘g = (monomial)²·Σresid² ≥ (monomial)²·1`, cst = 1, on the WHOLE chart (no radius
shrink from the survivor). R (scale-join) = the chart-dom radius (=1), survivor-unconstrained.

**F7 (concrete divisorMin = 8, full-composite Jacobian).** jacDet(gWrap) = −u0⁷·u1³·u20⁸
(exact). Binding = {c11=u20 jac 8, E=u0 jac 7}, squarefree; α=u1 non-binding (survivor carries
no α). divisorMin = min(8+1,7+1) = 8, rlct_chart = min(4, 9/2) = 4. Verified concretely on the
canonical + 8 non-canonical survivor leaves (node-2/node-3 pivot variants: value monomials
u0·u20,u2·u20,u3·u20,u4·u20 — all divisorMin 8). Under the loss's coord-perm symmetry the
binding-8 exponent transports EXACTLY to the moved dominant (u4⁸), never deepens.

**Fixed-shear caveat (COVER lane, not value).** The gWrapFan-as-defined (ONE shear
shearH∘permP, 288 pivot leaves) over-vanishes on 8/9 node-1 and 4/8 node-2 pivots — each
singular leaf needs its OWN native born-α (NOT the fixed shear). The 9 node-1 pivots are all
equivalent under the (3,3,4) coord-perm symmetry (transitive on A0's 9 entries) ⟹ the "T1-T9,
N_sing=6" is the resolution-TREE shear-step bookkeeping; the VALUE mechanism is ONE born-α ×
6 block-shape instantiations, all sharing the F5–F7 certificate.

**KILL-CONDITIONS: (a) SURVIVED, (b) SURVIVED, (c) SURVIVED** (concrete on survivor leaves +
perm-transport; residual = the native born-α per non-canonical dominant, mechanism-verified,
is the formaliser's instantiation — Codex-flagged as the one place census ≠ composite cert).

## F8 — the cover/value SEAM, SETTLED (true toric rlct LP; controller follow-up)

Scripts: `true_rlct_perleaf_334.py` (toric-LP true per-chart rlct), `seam_symconj_334.py`
(loss-symmetry-conjugate constructive half). LP = min_{w>=0}(w·κ+Σw)/(2·min_m w·m), validated
(canonical = 4.0 EXACT).

**RED for the fixed-shear gWrapFan as a VALUE family (concrete, not artifact).** The over-
vanishing node-1 leaves p1 ∈ {4,5,6,7} (the bottom-right 2×2 A0 = Δ-block entries) have TRUE
rlct = 2.5, 1.0, 1.0, 1.0 — BELOW 4. Over-vanishing = loss vanishes to HIGHER order = for a
LOWER bound, LOWER rlct. If these leaves are in the value cover, rlct≥4 BREAKS (min would be 1.0).
(node-1 p1∈{0,1,2,3}=4.5 safe, p1=20=4.0; node-2 and node-3 pivots all 4.0 safe — only the
Δ-block DOMINANT choice is fatal.)

**The RIGHT {g_c} = the PER-PIVOT born-α family (elder's L1/L2 unification answer).** Each
dominant A0-entry gets its OWN recoord shear (native block-recoord = the symmetry-conjugate
σ⁻¹∘shearH∘σ, NOT the fixed shearH). Verified on the WORST case (dominant A0[1,1]=u4, was 2.5):
g'=σ⁻¹∘gWrap∘σ has TRUE rlct = 4.0, single-entry survivor (idx 1), value monomial u2·u4,
jacDet = u2⁷·u4⁸·u5³ (divisorMin = min(8,9)=8). So the per-pivot born-α RESTORES a valid
resolution (rlct 4, survivor, divisorMin 8) — the F5-F7 certificate holds for the RIGHT family.

**Consequences.** (1) `rlctAt_coreGen334_ge_four_of_family` must range over the per-pivot-born-α
family (or EXCLUDE the fixed-shear Δ-block-dominant leaves). (2) The COVER lane (P2) must show
the per-pivot-born-α family covers = the K-orbit cover. (3) W3 tension: the natural per-pivot
born-α IS the symmetry-conjugate — building it NATIVELY (block-recoord per dominant, avoiding
Transport334) vs adopting the K-orbit honestly is the elder's route call. My verification uses
the conjugate as a tool; the formaliser writes the explicit native shear.

## F9 — value family UNIFORMLY sound (all 9 A0-dominants restore rlct-4; #188 confirmed)

Script: `seam_all9_dominants_334.py`. For EVERY A0-dominant entry, the per-pivot native born-α
(symmetry-conjugate σ⁻¹∘gWrap∘σ) gives true rlct = 4.000, SINGLE-entry survivor, divisorMin = 8:
  A0[0,0]/[1,0] → u0·u20 (idx0) ; A0[0,1]/[1,1] → u2·u4 (idx1) ; A0[0,2]/[1,2] → u3·u6 (idx2)
  A0[2,0] → u0·u1 (idx0) ; A0[2,1] → u4·u5 (idx1) ; A0[2,2] → u6·u7 (idx2).
NO A0-dominant is a genuine monument — the RED (fixed-shear rlct 1.0 on Δ-block dominants, F8)
is a MIS-SHEAR, fully repaired by the per-pivot native born-α. #188 (value family = per-pivot
native) is UNIFORMLY sound. Value-side certificate F5–F9 COMPLETE for the right family.
