# Thread-38 — per-step composition-order certificate (pnp, decorrelated)

Narrow second instrument on ONE question, adjudicated BLIND then compared. Gates the WALL leaf's
consumption of the FIX-A ruling. Read the frame: `charter.md`, `.agent-team/roles/pen-and-paper.md`.

## THE QUESTION
In Aoyagi 2023's Case-1(2) recursion step, composing the monomial blow-up `B` (d-block = pivot·d′)
and the unipotent shear `S` (Q/P Schur transforms), as a function-composition on parameter space
(parent coords = f(child coords)), is the per-step atom `B ∘ S` (blow-up outermost) or `S ∘ B`
(shear outermost)?

## VERDICT: `B ∘ S` — BLOW-UP OUTERMOST.  CONFIRM the elder's FIX-A ruling.

Independently derived from the PAGE IMAGES (PDF = printed page, offset 0), pp.16-20, BEFORE reading
the ruling/journal (blind derivation locked 2026-07-21T19:00:37Z, `blind-derivation.md`).

### Page-anchored derivation (pp.16-20)
- p.16 (Case-1(2)): the blow-up substitution is written FIRST — the whole d-block factored by the
  pivot, `d_ij = u_{S,J+1} · d′_ij` (top-left of `d′` normalised to 1). This expresses each OLD (parent)
  block coord as `u` times a NEW (intermediate) coord: `parent = B(intermediate)`, `B` = multiply-by-pivot.
- pp.17-18: the unipotent shear is written SECOND, acting on the POST-blow-up `d′`-block: `Q` (built
  from `d′`-entries) clears the pivot row, `P` clears the pivot column, `P·D′_J·Q = [[1,0],[0,D_{J+1}]]`.
  `D_{J+1}` is the child block; this expresses the intermediate `d′` in terms of the child coords +
  shear params: `intermediate = S(child)`.
- Reversal rule (`parent = B(x)`, `x = S(child)` ⟹ atom `= B∘S`): parent `= B(S(child)) = B∘S`.
- p.18-19 composite identity confirms it: `P·diag(b)·D_J·C = u_{S,J+1}·diag(b′)·(P D′_J Q)·C′` — the
  pivot `u` is factored out ONCE, on the OUTSIDE, wrapping the entire Q/P-sheared block. The shear
  matrices are built from `d′`-entries (child frame), never the parent `d`-entries.

### Mechanism (the math-level why)
Under `B∘S` every parent-frame center coord `= u · [S(child)]` — the OUTER multiply-by-pivot wraps the
whole sheared block, so the `u`-factor is STRUCTURAL for ANY pivot-keeping shear. Under `S∘B` the shear
acts on top of the `u`-scaled block and can re-inject `u`-free terms (a spectator content), breaking the
`δ=1` division. The order is exactly the difference between a structural divisibility (`hshear_pivot`
alone) and one needing center-support (`hshear_center`, withdrawn under the flip).

## Sufficiency battery (`order_battery.py`, EXIT 0; exact sympy)
Config 1 (toy D=3, center {0,1}, pivot 0, spectator 2), Config 2 (real thread-34 Schur displacement
`δ → δ + γβ`), Config 3 ((3,3,4) S=2 J=0 step, D=4, center {0,1,2}, pivot 0, spectator 3):
- (a) `B∘S`: every center coord divisible by pivot for a GENERIC pivot-keeping shear.  PASS.
- (b) `φbad = Pi.single c (w_s²)` (pivot-keeping, jacDet 1): does NOT break division under `B∘S`
  (`w0·w1 + w0·w2²`, divisible); DOES break it under `S∘B` (`w0·w1 + w2²`, the `w2²` term carries no
  pivot factor → NOT divisible).  PASS both directions, both configs.
- (c) the real Schur displacement IS pivot-keeping, jacDet 1, and `B∘S` divides every center coord.  PASS.
- (d) Jacobian: `|det D(B∘S)| = |pivot|^(|center|-1)` for a jacDet-1 pivot-keeping shear (toy `w0^1`,
  (3,3,4) `v0^2`).  PASS.

## Codex (decorrelated, xhigh; `codex/order-*.md`)
Fired blind on the same narrow question, conclusion withheld. Independently derived `B∘S` (blow-up
outermost) by its own route; confirmed the divisibility consequence YES and that `S∘B` "need not give
the same answer — applying the shear outside the blow-up can introduce terms not uniformly multiplied
by u." Fully decorrelated agreement.

## Comparison to the elder's ruling (read LAST — journal 2026-07-21 FIX-A, l.8683)
CONFIRM. The elder ruled the atom is `blockBlowupMap ∘ edgeShear` (BLOW-UP OUTERMOST) with the stated
consequence "under B∘S every parent-frame center coordinate = (S v)_pivot·(…) — δ=1 divisibility is
STRUCTURAL for any pivot-keeping shear; hshear_center WITHDRAWN, single field hshear_pivot." Identical
to my verdict, mechanism, and (a)/(b)/(d). The elder's "substitutions compose in reverse" and my
"first-written substitution is outermost" are the same fact viewed from the reduction vs the resolution
direction (`g = reduction⁻¹` composes the inverse steps in reverse order).

## CONSUMPTION-SITE FLAG (load-bearing for the WALL seat)
At THIS worktree's HEAD (`7aab28941`; FIX-A bundle `e9608bbf4` NOT yet integrated here):
- Core `BlockDivision.lean` (commit `cee0887d8`) is correctly flipped: `blockBlowupMap S p ∘ sh`
  (blow-up outermost), `blockBlowupMap_shear_center_eq` gives structural `/u_p` for any pivot-keeping shear.
- `MonumentAtlas.lean` `stepMap` (l.298, l.304) is STILL the pre-flip order:
  `edgeShearRaw … ∘ blockBlowupMap` / `edgeShear d ed ∘ blockBlowupMap` = `S∘B` (shear outermost).
  In Lean's `∘` this applies blow-up first, shear last — the OPPOSITE of the ruling and of the Core lemma.
- ACTION for the WALL/L3 seat: `stepMap` must become `blockBlowupMap ed.center ed.pivot ∘ edgeShear d ed`
  (blow-up OUTER) so it consumes `blockBlowupMap_shear_center_eq`. As written (`S∘B`) the `δ=1` division
  is refuted by `φbad` (w0l3's witness, journal l.8630) and would need the withdrawn `hshear_center`.
  This flip is presumably what the pending FIX-A integration (`e9608bbf4`) carries; verify it lands on
  the stepMap def, not only in Core.
