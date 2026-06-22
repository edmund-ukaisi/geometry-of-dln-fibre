# g164 — the gauge-frame locus: gaugeDecode/regAbsorb must apply a NON-trivial frame (option a), and it carries B's rank factors

The gauge frame for the deepest point is NOT trivial, and it lives in `gaugeDecode`/`regAbsorb`
(option a), not in `split` (which must stay MP). Grounded in `deepestPoint_exists`'s actual
construction, NOT the cert's idealization.

## What `deepestPoint` actually IS (Skeleton.lean `deepestPoint_exists`)

For `r > 0, L ≥ 2`, the deepest point is `wLayers H r U V` where:
- `U = P⁻¹ · embM` and `V = projM · Q⁻¹` are the rank-`r` factors of `B = U·V` (from
  `block_elimination H r B`), general rank-`r` matrices;
- the boundary layers carry `U` and `V`: layer 0 `= U · [I_r|0]` (`H 0 × H 1`), layer `L−1` involves
  `V`; middle layers `= corM` (the corner block `[[I_r,0],[0,0]]`).

So `deepestPoint` is rank-`r`-exact (`IsDeepLayers`) but its boundary layers are `U·…`, `…·V` with
`U, V` general rank-`r` — NOT the block-normal `[[I_r,0],[0,0]]`. The cert g125's "identity corners,
no gauge needed" is an IDEALIZATION (or a differently-constructed point); the Lean `deepestPoint`
genuinely carries the `U, V` boundary frames.

## Consequence: the gauge frame is real, non-trivial, and lives in gaugeDecode (option a)

The `(X_s, Y_s, Z_s, T_s)` blocks are the deviation of layer `s` from its deepest value, expressed in
a frame that block-normalizes the deepest layers. With `deepestPoint`'s boundary layers `= U·…`,
`…·V`, the frame must include `U⁻¹`/`V⁻¹`-type boundary corrections (the `P, Q` of
`block_elimination`). So:

- **(a) is forced:** `gaugeDecode q = roleSplit ∘ (per-layer frame applied to (split.symm q))`, the
  frame a FIXED per-layer GL conjugation (continuous linear iso, basepoint-preserving since the
  framed deepest layer is block-normal). `split` stays the MP index reindex (det = ±1; crux2's
  `split_mp` proof unaffected).
- **(b) is WRONG:** baking the frame into `split` breaks `split_mp` — the gauge frame `P_s, Q_s`
  (`= P⁻¹·embM`, `projM·Q⁻¹`) has det ≠ ±1 in general, so a frame-incorporating split is not
  measure-preserving. The frame's non-MP-ness is exactly why it belongs in the absorption layer
  (where the RLCT machinery peels the bounded-unit Jacobian), NOT in the MP `split`.

## The blocker this surfaces

The frame terms (`P, Q, U, V` from `block_elimination`/`deepestPoint_exists`) are currently BURIED
inside `deepestPoint_exists`'s `Classical.choice` — not exposed as accessible Lean terms. To build
`gaugeDecode`/`regAbsorb` I need the per-layer deepest-point frame exposed (the `P_s, Q_s` with
`P_s · (deepestPoint s) · Q_s = blockdiag[I_r, 0]`, or equivalently the layer's
already-block-normalizing conjugation). This is a Skeleton-level exposure (crux2 single-writer):
either expose the frame from `deepestPoint_exists`, or provide a lemma `deepestPoint_frame_exists`
giving the per-layer `(P_s, Q_s)` units. Asked crux2.

## Why this matters (not a detour)

This is the load-bearing geometric content the squeeze rests on: `loss = ‖∏A_s − B‖²` in raw coords
equals `‖U_bdry · (∏C_s − blockdiag[I,0]) · V_bdry‖²` in framed coords (interior frames telescope,
`Q_s P_{s+1} = I` by compatible choice), comparable to `‖∏C − blockdiag[I,0]‖²` up to the bounded
invertible boundary factors `U_bdry, V_bdry`. Those bounded factors are part of the squeeze constants
`c₁, c₂`. So the frame is not cosmetic — getting its locus right (a, in gaugeDecode) is what makes
the squeeze well-posed.

## RESOLVED (controller, decisive): option (a), frame = CONSTANT unit-Jacobian iso

The controller confirmed **(a)** with the decisive reason: **(b) breaks `split_mp`** — the gauge
frame's flat-space determinant is `∏_s det(P_s)^{cols}·det(Q_s)^{rows} ≠ 1` in general, so a
frame-incorporating split is NOT measure-preserving (sub-6's `rlctAtOn_comp_homeomorph` needs
`split_mp`). `split` MUST stay the pure MP index reindex; the frame lives in `gaugeDecode`.

Key refinement (controller): the frame is a **CONSTANT linear iso** — evaluated at the FIXED deepest
point, it does not vary with `w` — so its Jacobian is a nonzero constant (unit). Hence:

    gaugeDecode = roleSplit ∘ frame ∘ (split.symm − deepestFlat),

where `frame ∘ (· − deepestFlat)` is a global AFFINE iso (constant det ≠ 0), and
`regAbsorb = (the nonlinear E-straightening Ψ) ∘ (the constant affine frame)` is a unit-Jacobian
local diffeo — peels via `#72` (same machinery as the E-map alone). The frame part is even simpler
than `Ψ`: a global affine iso, det = nonzero constant. Build target cleared; gated only on crux2
exposing the per-layer frame `(P_s, Q_s)` + the `RegGaugeIdx` slot roles.

## Frame shape = (ii) per-layer; telescoping VERIFIED (no hidden confound)

The frame crux2 exposes (#77) is **(ii) per-layer** `(P_s, Q_s)` with
`P_s · (deepestPoint s) · Q_s = corM r (H s.castSucc) (H s.succ)` (the layer's block-normal corner).
Reading `wLayers` (Skeleton:750): the deepest point's layers are layer 0 = `U·projM`
(`U = P⁻¹·embM`), layer `L−1` = `embM·V` (`V = projM·Q⁻¹`), interior = `corM` (already block-normal).
So the frame is NOT arbitrary per-layer `block_elimination`:

- **interior layers** (`0 < s < L−1`): already block-normal ⟹ `P_s = Q_s = I` (identity);
- **layer 0**: `P_0 =` the `block_elimination P`, `Q_0 = I`;
- **layer `L−1`**: `P_{L−1} = I`, `Q_{L−1} =` the `block_elimination Q`.

Only the two BOUNDARY frames are nontrivial; both are the `P, Q` already inside `deepestPoint_exists`.

**Telescoping (the one compatibility worry) — VERIFIED, no confound** (numpy, L=3):
With interior frames `= I` and boundary frames only on the outer chain ends (`P_0` left, `Q_{L−1}`
right), EVERY interior seam has `Q_s · P_{s+1} = I` (all identity), so they cancel. Hence

    ∏ A_s = P_0⁻¹ · (∏ framed C_s) · Q_{L−1}⁻¹,   and   B = P_0⁻¹ · blockNormal · Q_{L−1}⁻¹

at the deepest point, so `loss = ‖∏A − B‖² = ‖P_0⁻¹((∏C) − blockNormal)Q_{L−1}⁻¹‖²`, comparable to
`‖(∏C) − blockNormal‖²` up to the bounded invertible boundary factors `P_0⁻¹, Q_{L−1}⁻¹`. Those two
factors are the ONLY non-trivial frame, and they are exactly the bounded constants feeding the squeeze
`c₁, c₂`. So the framed-block `∑E² + core` decomposition is valid and the telescoping holds — the
frame is a clean READING device, not a source of cross-layer entanglement. (Verified: the deepest
product `= B` exactly on L=3 `H=(2,2,2,2)` r=1.)

## CORRECTION (simpler #77 route): per-layer block-elim on the EXPOSED rank, NOT wLayers' U,V

The "frame = wLayers' U,V" framing above is OVER-complicated (and unsound to extract): `deepestPoint =
Classical.choice (deepestPoint_exists …)` is an OPAQUE witness — the `U,V`/`wLayers` structure is NOT
recoverable from it, and a fresh global `block_elimination B` need not match the chosen witness.

The clean route: `deepestPoint_isDeep.2 s : (deepestPoint … s).rank = r` EXPOSES that each layer is
rank-`r`. So the per-layer frame `(P_s, Q_s)` is just `block_elimination` applied to EACH LAYER
`deepestPoint s` directly (a rank-`r` matrix) — `P_s · (deepestPoint s) · Q_s = [[I_r,0],[0,0]]`. No
`wLayers`, no `U,V`, no `Classical.choice` spelunking; the frame is reconstructed per-layer from the
EXPOSED rank, not extracted from the opaque witness.

The only gap: the existing `block_elimination` (Skeleton:279) is stated H-network-specifically
(`B : H_0 × H_last`), though its core (`block_elimination_rank_data`, the construction) is general
`{a b r}`. So #77 = generalize `block_elimination` to `{a b r}(M : Matrix (Fin a)(Fin b) ℝ)(hM :
M.rank = r)` (a thin generalization, same proof body) + apply per layer (`M = deepestPoint s`,
`hM = isDeep.2 s`). Much smaller than re-stating `deepestPoint_exists`.

**IMPORTANT — telescoping is NOT trivial under independent per-layer frames** (correcting the
over-clean claim above): with EACH layer `deepestPoint s` (rank-`r` but NOT block-normal) getting its
OWN `block_elimination` frame `(P_s, Q_s)`, the interior frames are generally `≠ I`, so the interior
seams `g_s := Q_s⁻¹ · P_{s+1}⁻¹ ≠ I` do NOT cancel. So `∏ A_s = P_0⁻¹ · (C_1 g_1 C_2 g_2 ⋯ C_L) ·
Q_{L−1}⁻¹` carries nontrivial interior **g-units** `g_s` between the framed layers `C_s` (= pp2's
g177 between-layer gauge units). This is NOT a bug — it is exactly why the honest core is the
GAUGE-NORMALIZED Schur chain `R = ∏ S_s` (the g-units absorbed), NOT the raw `∏ T_s` (g150-fix/g153).
The `coreAbsorb` (Schur shear) + `coreAbsorb_rlct` peel the g-units; `core_comparability_squeeze`
(#54) consumes the resulting `P11 = leak + Rcore` split. So the per-layer frame is the right reading
device for `gaugeDecode`, and the interior g-units it exposes are handled DOWNSTREAM by coreAbsorb —
consistent with the whole `(e)`-architecture. (The clean-telescoping `loss = ‖P_0⁻¹(∏C −
blockNormal)Q_{L−1}⁻¹‖²` form only holds for the SPECIFIC `wLayers` witness with interior block-normal
layers — which the opaque `deepestPoint` is not provably, hence the g-units. The squeeze is robust to
them either way.)
