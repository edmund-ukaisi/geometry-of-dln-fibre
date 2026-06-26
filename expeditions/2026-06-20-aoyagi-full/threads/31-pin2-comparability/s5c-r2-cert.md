# S5c — matrix core (r≥2 / M>1) generalization (adjudicated)

The headline needs the rank-`r` reduced core (M = H−r > 1), so the scalar unit `u = ∏(1+X_s)/A` of the
r=1 case becomes a matrix factor. Adjudicated: **WITNESS, but the comparability is a GERM statement, not
uniform on a box** — and the clean build-ready route is the EXACT middle-factor identity + charging the
higher-order remainder inside the germ (Codex's in-sum form). Decorrelated Codex (xhigh) found a genuine
counterexample to the naive standalone-uniform claim that my first numerics missed; I then pinned the
exact germ-vs-box boundary. All structural algebra exact (sympy); MC flagged as guide.

## The exact matrix identity (verified, r=1, M=2; mechanism general)

Block-LDU: `C_s = L_s·diag(a_s, S_s)·U_s`, `L_s=[[1,0],[Z_s/a_s,I]]`, `U_s=[[1,Y_s/a_s],[0,I]]`
unipotent; `S_s = T_s − Z_s a_s⁻¹ Y_s` the per-layer Schur (`a_s` the r×r pivot, scalar here). Schur is
invariant under the outer `L0`-left / `U_{L-1}`-right unipotents, so for L=2 (verified exact,
`Matrix.ext` zero):

    R = S0 · W · S1,      W = I − Z1·A⁻¹·Y0,      A = a0a1 + Y0·Z1.

`W` is `I` minus a **rank-≤1** term `Z1·Y0/A` (Y0 a 1×M row, Z1 an M×1 column). `det W = a0a1/A → 1`, so
`W` is a bounded-invertible matrix factor → I at the deepest point. (For general L: telescopes,
`R = S0·W0·S1·W1·…·S_{L-1}`, each interface `W_k = I − Z_{k+1}·A_k⁻¹·Y_k → I`.) This is the matrix
analogue of the scalar `R = u·∏S`; the scalar `u` becomes the inserted middle factors `W_k`.

## The CONFOUND Codex caught (and the exact germ-vs-box resolution)

Naive claim "standalone `∑‖R‖² ≍ ∑‖∏S‖²` on a box" is **FALSE for M>1**. Codex's counterexample:
`S0 = ε·E12`, `S1 = ε·E21` (rank-1, ∏S = ε²·E11 ≠ 0), with `W[1,1] = 0` ⇒ `R = S0·W·S1 = 0`. So
`‖R‖²/‖∏S‖² = 0` — the lower bound fails. The rank-≤1 `W`-correction gives **no rank protection** when
`S0,S1` are themselves rank-deficient.

**BUT** (the resolution, exact): `W[1,1]=0` requires `Y0_1·Z1_1 = A`, i.e. `a0a1 + Y0_0·Z1_0 = 0`, i.e.
**off-pivot `Y0·Z1 ≈ −1` — NOT a germ path** (the off-pivot data must stay `O(1)`, not → 0). On a TRUE
germ (ALL deviations, incl. `Y,Z`, → 0): `W = I − O(ε²)`, and with `S_s = O(ε)`,
`R − ∏S = −S0·(Z1A⁻¹Y0)·S1 = O(ε⁴)` while `∏S = O(ε²)` — **strictly higher-order** (verified: `∏S`
entry `O(ε²)`, `R−∏S` entry `O(ε⁴)`). So `‖R‖²/‖∏S‖² → 1` along every path into the deepest point.

**Verdict:** the comparability is a **GERM statement** (holds as all deviations → 0), NOT uniform on a
coordinate box (fails where off-pivot stays `O(1)`). For the local RLCT this is the right scope —
`rlctAtOn` is a germ invariant — but the build statement must be a germ/in-sum form, NOT a box bound.

MC confirms (TRUE germ, rank-1 `S`-adversary): `sup (∑E²+‖∏S‖²)/(∑E²+‖R‖²) → 1` (1.0008 at scale 1e-2,
1.0000 at 1e-4); the blow-up (`~1e10`) appears ONLY on the non-germ slice (off-pivot `O(1)`, core → 0).

## Build-ready statement (Codex's in-sum form, the SAFE route)

Do NOT assert a standalone box comparability. Use the EXACT middle-factor identity + the in-sum charge:

    R = S0·(I − Z1·A⁻¹·Y0)·S1          [EXACT, the matrix Schur-of-product identity; L=2, telescopes]
    R − ∏S = −S0·(Z1·A⁻¹·Y0)·S1        [the remainder, carries Y0 AND Z1]
    ‖R − ∏S‖_F ≤ C·‖Y0‖·‖Z1‖·‖S0‖·‖S1‖ ≤ C'·‖Y0‖·‖Z1‖·‖∏S-magnitude‖   [on a nbhd, A,a_s units]

Then, since the off-pivot `Y0, Z1` are controlled by `√(∑E²)` near the deepest point (the regular blocks
`P01 ≈ Y0`, `P10 ≈ Z1` to leading order), the remainder is charged to `∑E²` INSIDE the squeeze sum:

    ∑E² + ‖R‖²  ≍  ∑E² + ‖∏S‖²      ON A GERM (uniform on the deepest-point germ, NOT a box).

Feed the squeeze the global `R` (as in the r=1 cert), get `loss ≍ ∑E²+‖R‖²` (banked), then transfer to
`∑E²+‖∏S‖² = ∑E²+deepestCoreF(coreAbsorb)` by this germ-charged remainder. **Build-ready atom:**

    theorem schur_core_germ_comparability … :
      R = S0·(I − Z1·A⁻¹·Y0)·S1   ∧   (germ bound) ∃ U ∈ 𝓝 0, ∀ q ∈ U,
        |∑‖R‖² − ∑‖∏S‖²| ≤ C·∑E²(q)        -- the remainder charged to the regular energy

(the `|·| ≤ C·∑E²` form, NOT a two-sided ratio bound — that is what survives the rank-deficient slice,
because there `∑E²` is bounded below too).

## r≥2 MATRIX-PIVOT confirm (the residual — now CLOSED, 2026-06-25)

Confirmed (sympy germ-orders + numeric across 3 decades + decorrelated Codex `codex/s5c-r2pivot-*`,
independent block-LDU re-derivation). Case: r=2 (a_s an r×r MATRIX pivot, a_s → I_r), M=1 core, L=2.

- **The identity is the SAME form** (Codex's clean `D0·M·D1` block derivation, `M = U0·L1`):
  `D0·M·D1 = [[a0a1+Y0Z1, Y0·S1],[S0·Z1, S0·S1]]`, top-left = the global product pivot `A = P11`, so
  `R = S0·S1 − (S0 Z1)·A⁻¹·(Y0 S1) = S0·(I_M − Z1·A⁻¹·Y0)·S1`. **`W = I_M − Z1·A⁻¹·Y0` — IDENTICAL to
  the r=1 form**, now with `A = a0a1 + Y0Z1` a MATRIX (r×r). `A → I_r` ⇒ `A⁻¹` bounded near 0.
  (My first parenthesized symbolic attempt mis-spelled the `ε`-scaling and returned False; Codex's
  block derivation + my numeric/order checks confirm the form.)
- **The germ orders SURVIVE the matrix pivot** (the load-bearing check; sympy + numeric, ratios stable
  across scale 1e-1→1e-3): `S_s = O(ε)`, `∏S = O(ε²)`, `W − I = O(ε²)`, `R − ∏S = (W−I)·∏S = O(ε⁴)`.
- **The contamination worry is RESOLVED** (Codex Q4): `a_s⁻¹ = (I+X_s)⁻¹ = I − X_s + O(ε²)` — the
  X-LINEAR term does NOT leak into `W − I`. `W − I = −Z1·A⁻¹·Y0` carries Y0 AND Z1 (two off-pivot
  factors), so `W − I = O(ε²)` regardless of the pivot's `O(ε)` X-deviation (the X is absorbed by the
  pivot block `A`, not the off-diagonal). So `R − ∏S` stays `O(ε⁴)`, NOT dropped to `O(ε³)`.
- ⇒ `|∑‖R‖² − ∑‖∏S‖²| ≤ 2‖∏S‖‖R−∏S‖ + ‖R−∏S‖² = O(ε⁶)`, charged to `∑E²` on the germ — the in-sum
  comparability survives the matrix pivot with NO new obstruction.

**Verdict: CONFIRMED germ for r≥2 matrix pivot.** The build-ready atom `schur_core_germ_comparability`
is unchanged: same `W = I_M − Z1·A⁻¹·Y0` (matrix `A`), same `|∑‖R‖²−∑‖∏S‖²| ≤ C·∑E²` germ form. Verified
at r=2/M=1; the LDU mechanism is general in r,M,L (the per-interface `W_k = I − Z_{k+1}A_k⁻¹Y_k`
telescoping). **No residual flag remains** — S5c is fully closed (germ-scoped, r≥2 included).

## Scope / caveat (honest)

- The **middle-factor identity `R = S0·W·S1`** is EXACT (r=1 M=2 AND r=2 M=1 verified; the LDU mechanism
  is general in r, M, L — the per-interface `W_k` telescoping, `W_k = I − Z_{k+1}A_k⁻¹Y_k`). General
  r×r-pivot, M×M-core, all-L is the same block-LDU; the r=2/M=1 + r=1/M=2 cases pin both the matrix-pivot
  and the matrix-core generalizations. Not every `(r,M,L)` triple symbolically enumerated — but the two
  orthogonal generalizations (matrix pivot, matrix core) are each confirmed, and the mechanism is uniform.
- The **germ-not-box** distinction is the load-bearing subtlety: the formaliser must state the
  comparability as a `𝓝 0` germ with the remainder `≤ C·∑E²`, NOT a uniform `[m,M]` ratio. `rlctAtOn`'s
  germ-invariance makes this sufficient for the headline.

## Files
- `/tmp/s5c_matrix_identity.py`, `s5c_similarity.py`, `s5c_ldu.py`, `s5c_lower.py` (timed out — superseded),
  + the inline exact derivations in this thread (`R = S0·W·S1`; `R−∏S = O(ε⁴)` germ; the box blow-up only
  off-germ). Codex: `codex/s5c-r2-{prompt,answer}.md`.

## Net
Matrix-core S5c is **TRUE on a germ, NOT uniform on a box** (Codex's counterexample is real but off-germ).
The build-ready form is the EXACT middle-factor identity `R = S0·W·S1` + the in-sum remainder charge
`|∑‖R‖²−∑‖∏S‖²| ≤ C·∑E²` on a `𝓝 0` germ — NOT a standalone box comparability. This closes the last
named open dependency (with the r≥2-matrix-pivot LDU confirm as a small residual flag). The r=1
`s5c-cert.md` standalone-unit claim should be NARROWED to a germ for consistency (it's true standalone
in r=1 because the scalar `W=u` can't cause rank cancellation — but the germ framing unifies both).
