<task>
Decorrelated soundness check. Lean/Mathlib formalisation of one step of Aoyagi's resolution of
singularities for deep linear networks. I claim a stated theorem is UNPROVABLE as written because of a
free "shear" displacement; verify or refute my reasoning independently.

SETUP (all real-valued functions on ℝ^D = (Fin D → ℝ); "the deepest point" is 0; ⟨u_p⟩ = the ideal of
continuous functions divisible by the pivot coordinate `u ↦ u p`, i.e. functions vanishing on {u_p=0}
with a continuous quotient):

- A block-center blow-up `blockBlowupMap S p` (center S ⊆ Fin D, pivot p ∈ S): pivot `p ↦ u_p`; other
  center coords `j ∈ S\{p} ↦ u_p·u_j`; SPECTATORS `j ∉ S ↦ u_j` (fixed). So every CENTER coordinate of
  `blockBlowupMap S p u` lies in ⟨u_p⟩ (gains a u_p factor); spectators do NOT.
- A shear `blockShear φ (w) = w + φ(w)`, with φ a FREE displacement constrained only by:
  jacDet(blockShear φ) = 1 (unipotent) and φ(0) = 0.
- The per-step coordinate change is `stepMap = blockShear φ ∘ blockBlowupMap S p`, i.e.
  `stepMap(u) = blockShear φ (blockBlowupMap S p u)` — the shear applied AFTER the blow-up.
- Residual `resid` satisfies "SupportedOn S": `resid(u) = ∑_{i∈S} c_i(u)·u_i` (c_i continuous) — an
  IDEAL-MEMBERSHIP form: resid ∈ ⟨center coords⟩, so resid vanishes when all center coords vanish.
- The parent invariant gives `(coreGen_i ∘ g)(v) = ∑_j q_ij(v)·(b(v)·resid_j(v))`, q continuous.
- The δ=1 child step sets the child dominant `b'(u) = u_p · b(stepMap u)` (an EXTRA u_p factor) and the
  child residual `resid'_j(u) = resid_j(stepMap u)` (pure pullback). The child invariant requires
  `∃ q' continuous, (coreGen_i ∘ g ∘ stepMap)(u) = ∑_j q'_ij(u)·(b'(u)·resid'_j(u))` for all u.

MY CLAIM: for a FREE φ this child invariant is UNPROVABLE. Reason: the RHS carries `b'` which is in
⟨u_p⟩ (δ=1), so at any u with u_p=0 the RHS = 0, forcing `(coreGen_i ∘ g ∘ stepMap)(u) = 0` there. But
`(coreGen_i∘g∘stepMap) = ∑_j (q∘stepMap)·(b∘stepMap)·(resid_j∘stepMap)`, and
`resid_j∘stepMap = ∑_{i∈S} (c_i∘stepMap)·(stepMap u)_i`, where for a CENTER coord i,
`(stepMap u)_i = (blockBlowupMap u)_i + φ(blockBlowupMap u)_i = u_p·quot_i + φ(blockBlowupMap u)_i`.
The first term ∈ ⟨u_p⟩; the second, `φ(blockBlowupMap u)_i`, at u_p=0 equals `φ(center=0, spectators)_i`
which for a free φ (only φ(0)=0, i.e. φ(all coords 0)=0) need NOT vanish when spectators ≠ 0. So
`resid_j∘stepMap ∉ ⟨u_p⟩`, and `(coreGen∘g∘stepMap)` is nonzero at some u_p=0 point ⟹ no q'.

CONCRETE WITNESS (D=3, S={0,1}, p=0, spectator 2): φ(w) = (0, w_2, 0) (jacDet(blockShear φ)=1, φ(0)=0).
`stepMap(u) = (u_0, u_0·u_1 + u_2, u_2)`; center coord 1 = u_0·u_1 + u_2, which is u_2 ≠ 0 at u_0=0.
Take resid = (center coord 1). Then resid∘stepMap = u_0u_1+u_2 ∉ ⟨u_0⟩.

I also claim: re-adding the injectivity condition "CenterCoordAligned" (stepMap injective off {u_p=0})
does NOT fix it — the witness φ above IS injective off {u_0=0} (inverse u_1=(c_1−u_2)/u_0) yet breaks
divisibility. And: the fix is either (A) apply the blow-up OUTERMOST (`stepMap = blockBlowupMap ∘
blockShear φ` with φ keeping the pivot), or (B) constrain φ so its center-coordinate displacements lie
in ⟨center coords⟩ (so they gain u_p under the blow-up), matching the real Schur shear (a product of
center coords).
</task>

<questions>
1. Is my claim correct that the δ=1 child invariant is unprovable for a free φ (jacDet=1, φ(0)=0)?
   Independently confirm or refute the concrete witness and the general reason.
2. Is my diagnosis of the composition ORDER right — that "shear AFTER blow-up" is what admits the break,
   and "blow-up outermost (shear first), φ keeping the pivot" (FIX-A) avoids it for any such φ?
3. Is my claim that injectivity (CenterCoordAligned) does NOT suffice correct?
4. What is the MINIMAL honest constraint on φ (or the composition) that makes it provable? Is FIX-B
   ("φ's center displacements ∈ ⟨center coords⟩") the tightest, or is there something weaker/cleaner?
</questions>

<output_contract>
Four short sections, one per question. State clearly CONFIRM or REFUTE for each of my claims, with the
sharp reason. If you find a hole in my reasoning (e.g. the child invariant is actually provable via a
route I missed, or a weaker constraint suffices), say so explicitly. Under ~600 words. Mark inference
vs. definite fact.
</output_contract>
