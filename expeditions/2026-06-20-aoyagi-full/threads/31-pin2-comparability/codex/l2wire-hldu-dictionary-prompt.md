<task>
Lean4/Mathlib DLN-fibre RLCT formalisation. I must close a MATRIX identity `hLDUtie` and have NUMERICALLY
FALSIFIED the bridge as I read it. I need you to adjudicate WHICH product the LHS equals, and whether the
identity is true with a corrected reading, BEFORE I build a (possibly subtly-wrong) green proof.

SETUP (L=2, rank r, widths H : Fin 3 → ℕ; deepestM s = H s − r):
- A fixed fibre point `deepestPoint`. Its reindexed BOUNDARY layers are NOT the identity-corner `corM`:
  layer 0 reindexed = fromBlocks A11 0 A21 0 (leading r×r block A11 a UNIT ≠ 1, tail cols 0);
  last layer reindexed = fromBlocks B11 B12 0 0 (B11 a unit ≠ 1, tail rows 0). Interior layers = corM.
- Endpoint frames: endpointP0 = block-LOWER normalizer fromBlocks (⅟A11) 0 (−A21⅟A11) 1 (identity ₂₂);
  endpointQL = block-UPPER fromBlocks (⅟B11) (−⅟B11 B12) 0 1 (identity ₂₂). They send
  P0·deepestPoint_0·(interior=1) and (interior=1)·deepestPoint_last·QL toward corM.
- Gauge reads off a point q = deepestSplit w0 x: readX_s, readY_s, readZ_s, core_s decode the DEVIATION
  (decode(x − w0))_s. The "l2* dictionary": l2A_s = 1 + readX_s, l2Y0=readY_0, l2Z1=readZ_last,
  l2Y1=readY_last, l2T1=core_last; l2P00 = l2A0·l2A1 + l2Y0·l2Z1; l2K = l2Z1·l2P00⁻¹·l2Y0;
  l2S1 = l2T1 − l2Z1·l2A1⁻¹·l2Y1; schurCorrection_s = −readZ_s·(1+readX_s)⁻¹·readY_s (BARE gauge reads).

THE LHS of hLDUtie = prod(deepestM)(C) where C_s = (decode q core)_s + schurCorrection_s = the per-layer
Schur core S_s = core_s − readZ_s·(1+readX_s)⁻¹·readY_s, last overridden to (1−l2K)·l2S1. At L=2 this is
S0·((1−l2K)·l2S1), which by a banked block-LDU lemma = Schur₂₂(C0·C1), C_s = fromBlocks (1+readX_s) readY_s readZ_s core_s.

THE RHS of hLDUtie = the (1,1)-Schur integrand `Rcore` of the FRAMED reindexed product
Mw = endpointP0·(prod(decode x) − B)·endpointQL, pivot (Mw₁₁ + 1)⁻¹, where B = prod(deepestPoint).
I have PROVEN: (corner-split, since reindex(P0·B·QL)=fromBlocks 1 0 0 0) Rcore = Schur₂₂(reindex(P0·prod(decode x)·QL))
with pivot M̂₁₁⁻¹; and (schur_frame_transform, DP=DQ=1 from identity ₂₂-blocks) that = Schur₂₂(reindex(prod(decode x))).

NUMERICAL FALSIFICATION (r=1, H=[2,2,2], A11=3,A21=0.9,B11=2,B12=0.6, reads X0=.2 Y0=.3 Z0=.5 T0=.7,
X1=.11 Y1=.13 Z1=.17 T1=.19):
- LHS = Schur(C0·C1) with 1+readX dict = 0.0942.
- RHS = Schur(reindex prod(decode x)) [layer-0 (1,1) = A11+X0 = 3.2] = 0.0741.
- RHS = Schur(framed0·framed1) where framed0=P0·decode0, framed1=decode1·QL, framed (1,1) ≈ 1.067 = ALSO 0.0741.
- LHS = RHS ONLY when deepest boundary = pure corM (A11=1,A21=0,B11=1,B12=0).
So LHS (1+readX) ≠ RHS (framed-conjugated or A11+X). The "1+readX = framed (1,1)" identity is FALSE at the boundary.
</task>

<output_contract>
Answer in 4 short sections, decisive:
1. VERDICT: Is hLDUtie (LHS prod(deepestM)(C) with BARE 1+readX schurCorrection = RHS framed-product Schur)
   TRUE, FALSE, or TRUE-ONLY-UNDER-A-CONDITION? One line.
2. WHICH PRODUCT does the LHS prod(deepestM)(C) actually correspond to — the framed product Schur, the raw
   decode Schur, or neither? Given schurCorrection uses BARE (1+readX)⁻¹ (not frame-conjugated).
3. THE FIX (if any): does correctness require (a) schurCorrection/l2A to use FRAME-CONJUGATED reads (so
   1+readX becomes the framed (1,1)), or (b) deepestCoreF to be DEFINED via the framed product (so the LHS
   is intrinsically the framed Schur, and my "LHS = Schur(C0·C1) with 1+readX" reading is the ERROR — i.e.
   prod(deepestM) is itself in frame-normalized coordinates), or (c) the identity is genuinely false and the
   producer's deepestCoreF=frobSq(prod(deepestM)(...)) claim is the thing to re-examine?
4. CHEAPEST DISCRIMINATING CHECK to decide between 3(a)/3(b)/3(c) that I can run in Lean or numerically.
</output_contract>

<grounding_rules>
Reason from the stated algebra only. Flag any step where you INFER vs where the numerics OBSERVE. If you
think my numerical setup mis-models the actual objects (e.g. prod(deepestM) is NOT Schur(C0·C1) with bare
reads), say so explicitly and state what the correct model is. Do not assume the identity is true because
it "should be" — the producer itself flagged this exact bridge as UNBUILT.
</grounding_rules>
