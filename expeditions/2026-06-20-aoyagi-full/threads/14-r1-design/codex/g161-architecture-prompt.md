<task>
I am formalising in Lean 4 + Mathlib a "gauge-slice normal form" for the loss landscape of a deep
linear network at its deepest (most singular) point. I need a soundness check on the ARCHITECTURE of
one bundled existence statement, BEFORE I sink ~500 lines into building it. There may be a subtle
self-contradiction in the bundle. Find it if it exists, or confirm the bundle is consistent.

## Setup (math, not Lean)

A deep linear network has L layers; layer s is a real matrix A_s : (H_s) × (H_{s+1}). The "flat"
parameter space is R^N where N = flatDim H = Σ_s H_s·H_{s+1} (all matrix entries concatenated). The
loss is dlnLoss(A) = ‖A_1·A_2·…·A_L − B‖²_Frobenius for a fixed target matrix B of rank r.

At the "deepest point" w0 (every layer has rank exactly r), we gauge-slice. Locally each layer
factors C_s = [[I_r + X_s, Y_s],[Z_s, T_s]] in adapted coordinates, with T_s the (H_s−r)×(H_{s+1}−r)
"reduced block". Define:
- the "regular" residuals E = the (0,0),(0,1),(1,0) blocks of (∏C_s − blockdiag[I_r, 0]) — count nReg
  = r(H_0 + H_L − r) of them;
- the "reduced core" = the reduced widths M_s = H_s − r, with core loss dlnLoss_M(T) = ‖∏ S_s‖²
  where S_s = T_s − Z_s(I_r+X_s)⁻¹Y_s is the per-layer Schur complement (the gauge-normalized core,
  NOT the raw ∏T_s — that's a known earlier error);
- "spectator" / gauge directions = the remaining nGauge = N − nReg − flatDim(M) coordinates.

## The bundled existence statement (the thing I must prove)

It claims there exist nGauge : ℕ, a homeomorphism split : (R^N) ≃ₜ ((R^nReg) × ((R^flatDim(M)) × (R^nGauge)))
[call the three slots .1 = regular, .2.1 = core, .2.2 = spectator], and a self-homeomorphism
coreAbsorb of the codomain, such that ALL of:

(a) split is MEASURE-PRESERVING (volume → volume);
(b) split(w0_flat) = 0 (carries the deepest point to the origin);
(c) coreAbsorb 0 = 0, coreAbsorb fixes the .1 (regular) slot and the .2.2 (spectator) slot
    pointwise: (coreAbsorb q).1 = q.1 and (coreAbsorb q).2.2 = q.2.2 for all q;
(d) [RLCT peel] rlctAtOn(q ↦ ∑(q.1)² + dlnLoss_M((coreAbsorb q).2.1)) 0
              = rlctAtOn(q ↦ ∑(q.1)² + dlnLoss_M(q.2.1)) 0
    (the RLCT — real log-canonical threshold, a germ invariant at 0 — is unchanged by coreAbsorb);
(e) [loss squeeze] ∃ c₁,c₂ > 0 and a neighbourhood U of w0_flat such that for all w ∈ U:
    0 ≤ Φ(w),  c₁·Φ(w) ≤ dlnLoss(flat⁻¹(w)) ≤ c₂·Φ(w),
    where Φ(w) = ∑((split w).1)² + dlnLoss_M((coreAbsorb(split w)).2.1).

So Φ uses split's regular slot squared, plus the core loss of coreAbsorb-applied-to-split's core slot.

## My worry (the potential contradiction)

(a) forces split to be measure-preserving: |det D(split)| = 1 a.e. But for (e) to hold, split's
REGULAR slot (split w).1 must — near w0 — be (a reparametrization of) the residual blocks E, because
Φ's regular term ∑((split w).1)² must two-sidedly match the "regular part" of dlnLoss. The map
w ↦ E(w) (the residual blocks) is NONLINEAR (E is built from products of the layer matrices) and is
generically NOT volume-preserving. So it looks like split cannot be both measure-preserving AND have
its regular slot equal the E-residuals.

Two candidate resolutions I want you to adjudicate:

RESOLUTION 1 ("split is a plain relabel; coreAbsorb does NObut the regular slot is just RAW
coordinates"): split is a literally-linear measure-preserving reindex (det = ±1) whose regular slot
holds RAW gauge coordinates (X,Y,Z entries), NOT the nonlinear E. Then (e)'s ∑((split w).1)² is
∑(raw X,Y,Z entries)², and the squeeze c₁·Φ ≤ loss ≤ c₂·Φ must hold with Φ = ∑(raw gauge entries)²
+ core. QUESTION: is it TRUE that near w0, dlnLoss ≍ ∑(raw X,Y,Z entries)² + ‖∏S_s‖²? i.e. is
‖E(w)‖² two-sidedly comparable to ∑(raw X,Y,Z entries)² near w0? (E is a smooth function vanishing at
w0; is its squared norm comparable to the squared norm of the raw gauge coordinates, given dE(w0)
might be rank-deficient or might be an iso onto the regular directions?)

RESOLUTION 2 ("coreAbsorb is the ONLY nonlinear map; split is linear MP; but then (e) is FALSE as
stated because raw≠E"): the bundle is internally inconsistent and needs a SECOND nonlinear absorption
(a regAbsorb fixing core+spectator, turning raw gauge coords into E) which is ABSENT from this bundle.

Which resolution is correct? Specifically:

1. Can a single measure-preserving `split` (linear or not) have BOTH the basepoint property (b) AND
   make (e)'s squeeze TRUE, WITHOUT any additional nonlinear absorption on the regular slot? Under
   what condition on E and the raw gauge coordinates?
2. Is the squeeze "dlnLoss ≍ ∑(raw gauge entries)² + ‖∏S_s‖²" actually TRUE near w0? Give the
   mechanism (a Taylor/Morse argument) or a counterexample (a direction where raw gauge entries are
   O(ε) but dlnLoss is o(ε²), or vice versa).
3. If RESOLUTION 1 holds, the construction is: linear MP split (raw slots) + coreAbsorb (raw core T_s
   → Schur S_s). Confirm coreAbsorb (which fixes regular+spectator, acts only on core) is enough, and
   that the squeeze closes with RAW regular coordinates. If RESOLUTION 2 holds, state precisely what
   extra map the bundle is missing.

Concretely test on L=2, H=(2,1,2), r=1 (so M=(1,0,1), the reduced core has a zero middle dimension):
each layer C_s = [[1+x_s, y_s],[z_s, t_s]] with the reduced block t_s a (H_s−1)×(H_{s+1}−1) scalar
(t_1 is 1×0 empty, t_2 is 0×1 empty — so the core is trivial here; good degenerate check). Then
∏C = C_1·C_2, E = the residual, and the loss is ‖C_1 C_2 − B‖² with B rank 1. Is loss ≍ ∑(x,y,z)²
near the deepest point here?
</task>

<output_contract>
1. VERDICT: RESOLUTION 1 or RESOLUTION 2 (or a third you name), one line.
2. The squeeze truth-value: is dlnLoss ≍ ∑(raw gauge entries)² + ‖∏S_s‖² TRUE near w0? Mechanism or
   counterexample, with the specific gauge directions that are/aren't controlled.
3. The condition that makes a single MP split work (or the precise missing map if it can't).
4. The L=2 (2,1,2) r=1 check: explicit answer.
Keep it under ~500 words. Be concrete and adversarial — I would rather find the hole now.
</output_contract>

<grounding_rules>
Distinguish what you can PROVE (an algebraic identity, a derivative computation) from what you
CONJECTURE. If you assert the squeeze is true, give the rank/iso condition on dE(w0) it rests on. If
you find a counterexample, give explicit numbers. Flag any step where you are guessing the geometry.
</grounding_rules>
