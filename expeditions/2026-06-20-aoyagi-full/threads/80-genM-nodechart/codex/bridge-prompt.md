# Bridge fact: phiFlatLiveR1 M222 (fixed-pivot genBlkFlatLiveR1) vs the (2,2,2) phi222 template

## Setup (DLN interior-det, L=2)
The BData interface / headline targets `phiFlatLiveR1 M t ha hN p hp1 hp2 rfin` (the R1 live-leaf decoder
`genBlkFlatLiveR1`). The banked (2,2,2) template `phi222` uses a DIFFERENT decoder `B_det222`:
- B_det222 (free-pivot): boundary-1 Rmat = [[0,0],[0,x6]] (FREE coord x6 at the E-slot); leaf Rfin = [1,x7]
  (fixed leaf-anchor 1 + free x7).
- genBlkFlatLiveR1 (fixed-pivot): boundary-p Rmat = rmatPad(pivotEIndicator) = [[0,0],[0,1]] (FIXED literal-1
  at E(0,0)); leaf Rfin = the LIVE free reader (the freed pivot budget rerouted to the leaf).
They are the SAME achiever-chart family with the gauge-fixed "1" relocated (E-slot ↔ leaf-slot).

## What I computed concretely (sympy, on the ACTUAL genBlkFlatLiveR1 M222 blocks via the Cgen/Agen recursion)
boundary-1 blocks: Bmat1 = bmatStack(K,X) = [[a],[b·a]] (K=readK=[a], X=readX=[b]); Nblk1=[n]; Wblk1=[w0,w1];
Rmat1 (fixed) = [[0,0],[0,1]]; Cgen2 (live leaf) = u·[lf0,lf1].
- Agen0 = C1 = Bmat1·[1|n] + u·[[0,0],[0,1]] = [[a, a·n],[a·b, a·b·n + u]]
- Agen1 = [C2 − N·W ; W] = [[u·lf0 − n·w0, u·lf1 − n·w1],[w0,w1]]
- The 8 chart coords are (u, a, b, n, w0, w1, lf0, lf1).
- **det Dφ = a²·u²** (sympy exact). minAdm(2,2,2)=3, so u² = u^{minAdm−1}; a² = |K|^{r+c} (r=c=1) = the engine.
So **det Dφ = u^{minAdm−1}·engine**, the faithful headline, with the engine u-free.

## My finding (please confirm or refute)
1. `phiFlatLiveR1 M222` and `phi222` are NOT literally equal (different decoders: fixed-E+live-leaf vs
   free-E+fixed-leaf-anchor), so the banked `phi222`/`T222`/`pack222` is a STRUCTURAL GUIDE for
   `phiFlatLiveR1`, NOT a literal bridge equality.
2. BUT `phiFlatLiveR1 M222` independently has the faithful structure: det = u^{minAdm−1}·engine (verified
   a²·u² above), so `φ = B ∘ pivotBlowupOn` with B u-free local-iso (det DB = a² = engine ≠ 0) HOLDS for the
   fixed-pivot decoder directly. The fixed-pivot's additive "+u" at Agen0[1,1] does NOT break the pure-mult
   radial: u is the pivot coordinate; the "+u" is u read at that output (the pivot direction), and the
   leaf coords lf0,lf1 are the u-scaled actives (active = {pivot u} ∪ {lf0,lf1}, card 3 = minAdm).
3. So the GENERALIZATION (delegated formaliser) should build the pack/T for `genBlkFlatLiveR1`'s blocks
   DIRECTLY (fixed-E 1 + live leaf), using the (2,2,2) T222 as the structural template — NOT try to prove
   `phiFlatLiveR1 = phi222` (false).

## Questions
A. Is finding (2) correct — det Dφ(phiFlatLiveR1 M222) = u^{minAdm−1}·engine with B a u-free local iso, so
   the faithful φ = B ∘ pivotBlowupOn holds for the FIXED-pivot decoder (the additive +u being the pivot
   coordinate, NOT requiring an affine radial layer)? I flip-flopped on this twice (the additive +u looked
   like the affine-radial problem); the concrete det = a²·u² says it factors cleanly. Confirm or find the hole.
B. Is the right delegation spec: "build the pack/T (radial pivotBlowupOn + boundary Schur-frame + shear)
   for genBlkFlatLiveR1's ACTUAL blocks, generalizing T222 structurally, target phiFlatLiveR1 — NOT a
   phi222-equality bridge"? Any reason the fixed-pivot additive-+u blocks the general-M (L=2) pack/T where
   it didn't block (2,2,2)?
C. Sanity: the active set for the FIXED-pivot decoder = {structPivot} ∪ {leaf free coords} (NOT the E-slot,
   which is the fixed 1) ∪ {E-free slots if r·c>1}. At (2,2,2): {pivot} ∪ {lf0,lf1}, card 3. Is that the
   correct active (vs the genm-detradj pin which had {pivot} ∪ {E-free excl (0,0)} ∪ {leaf})? At (2,2,2)
   E-free is empty (1×1 E = just the fixed (0,0)), so active = {pivot}∪{leaf} — consistent. Confirm.

Be concrete + skeptical. I conflated abstract-vs-concrete 3× before; verify finding (2) against the det = a²·u².
