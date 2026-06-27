<task>
A reachability question: does a specific adversarial curve, which breaks an additive bound in the
ABSTRACT block-Schur algebra, actually exist inside a CONSTRAINED parameterized chart? The constraint
is what I need you to adjudicate. Set it up yourself; do not assume the curve survives.
</task>

<setup>
L=2 deep linear network, reduced rank r, widths H0,H1,H2; M_s = H_s - r.

The chart coordinate w (small, near a "deepest point" w0) maps to PER-LAYER framed blocks. Each layer
s ∈ {0,1} reindexes to the (r ⊕ M_s) block grid with four blocks:
  A_s = I_r + X_s   (the (1,1) pivot block),  Y_s = (1,2),  Z_s = (2,1),  T_s = (2,2) core.
The reads (X_s, Y_s, Z_s) for BOTH layers and the cores T_s are FREE independent coordinates of w
(verified: the chart's reg/gauge slot is a homeomorphism onto the full per-layer (X,Y,Z) index set).

THE FRAMED PRODUCT and its blocks:
  Mw blocks = toBlocks of (C0·C1), C_s = fromBlocks(A_s, Y_s, Z_s, T_s):
    P00 = A0 A1 + Y0 Z1   (corner-shifted pivot, → I),  P01 = A0 Y1 + Y0 T1,
    P10 = Z0 A1 + T0 Z1,  P11 = Z0 Y1 + T0 T1.
  Rcore = P11 - P10 (P00)^{-1} P01,   coreΦ = ‖S0 S1‖_F²  (S_s = T_s - Z_s A_s^{-1} Y_s).

THE KEY CONSTRAINT (this is the crux):
The loss-visible "regular energy" is
    Sreg = ‖P00 - I‖_F² + ‖P01‖_F² + ‖P10‖_F²,
BUT the chart routes coordinates into TWO disjoint slots:
  * the "reg" (nReg) slot, which the loss reads, maps ONLY to the BOUNDARY generators:
        X_first = X_0   (layer-0 (1,1)),  Y_last = Y_1 (layer-1 (1,2)),  Z_first = Z_0 (layer-0 (2,1)).
  * EVERYTHING ELSE — X_1 (layer-1 (1,1)), Y_0 (layer-0 (1,2)), Z_1 (layer-1 (2,1)), plus interior — maps
    to the "gauge/spectator" (nGauge) slot, which is ABSORBED by a measure-preserving shear (coreAbsorb)
    and is NOT directly in Sreg.
So as free coordinates: X_0, Y_1, Z_0 are "reg" (loss-visible via the product blocks); X_1, Y_0, Z_1, and
all cores T_s are "spectator/core" (free but not in the reg slot).
Sreg is STILL the product-block energy ‖P00-I‖²+‖P01‖²+‖P10‖² (a function of ALL the reads through the
product), it is just that the chart's FREE reg coordinates are only X_0, Y_1, Z_0.

THE ADVERSARIAL CURVE I want to test for reachability (it breaks |frobSq Rcore − coreΦ| ≤ C·Sreg in the
abstract algebra): scale t→0, keep the cores and K-drivers T_0,T_1,Y_0,Z_1 = Θ(t); set X_1 so that
P00 = I exactly (X_1 chosen as a function making A0 A1 + Y0 Z1 = I); choose Z_0 to null P10; choose Y_1
to make P01 = Θ(t³). Then Sreg = Θ(t⁶) but the cores stay Θ(t), so the gap = Θ(t⁶) = Θ(Sreg), and the
constant is unbounded.
</setup>

<questions>
1. Given the free coordinates (reg: X_0, Y_1, Z_0; spectator/core: X_1, Y_0, Z_1, T_0, T_1), is the
   adversarial curve REACHABLE? Specifically:
   - Can X_1 be set to make P00 = I exactly, GIVEN X_1 is a free (spectator) coordinate? (yes/no + why)
   - P10 = Z0 A1 + T0 Z1: to null it we need Z_0 = -T0 Z1 A1^{-1}. Z_0 is a REG coordinate. Is that a
     valid free choice? Does nulling P10 cost anything (it sets the reg coord Z_0 to Θ(t²))?
   - P01 = A0 Y1 + Y0 T1: to make it Θ(t³) we need Y_1 = A0^{-1}(Θ(t³) - Y0 T1). Y_1 is a REG coordinate.
     Y0 T1 = Θ(t²), so this forces Y_1 = Θ(t²). Is that a valid free choice?
2. After these choices: Sreg = ‖P00-I‖² + ‖P01‖² + ‖P10‖² = 0 + Θ(t⁶) + 0 = Θ(t⁶). Meanwhile the cores
   S0,S1 = Θ(t) (driven by T_0,T_1,Y_0,Z_1 which are free spectator/core coords still Θ(t)), so
   coreΦ = Θ(t⁴) and the gap |frobSq Rcore − coreΦ| = Θ(t⁶). Confirm or refute: G/Sreg → const, unbounded.
3. Is there ANY hidden chart constraint that couples these reads so the curve is NOT a valid path w(t)?
   E.g. does setting X_1 (spectator) to a specific value, AND Z_0, Y_1 (reg) to specific Θ(t²) values,
   AND keeping Y_0,Z_1,T_0,T_1 (spectator/core) Θ(t), violate any relation? (The reads are claimed
   independent; I want you to find a coupling if one exists.)
4. FINAL: does the additive bound |frobSq Rcore − coreΦ| ≤ C·Sreg survive on the REAL chart domain
   (S5a ∩ nbhd), or is it broken by a reachable curve? If it survives ONLY because some reads are
   spectator (absorbed) and cannot enter Sreg, say exactly which coordinate's spectator-ness saves it.
</questions>

<output_contract>
- Separate FACT (what the algebra/constraints force) from INFERENCE.
- Give a yes/no on reachability with the precise reason.
- If the curve is reachable, confirm the additive bound is broken (non-uniform). If a chart constraint
  blocks it, name the constraint and the coordinate.
</output_contract>

<grounding_rules>
- The reads X_0,X_1,Y_0,Y_1,Z_0,Z_1,T_0,T_1 are claimed FREE and independent (homeomorphic chart).
- "Reg slot = boundary generators only" means the loss's reg ENERGY is the product-block energy
  ‖P00-I‖²+‖P01‖²+‖P10‖²; the chart's free reg COORDINATES that are not also functions of spectators are
  X_0,Y_1,Z_0. But P00,P01,P10 still depend on spectator reads through the product.
- Do not assume my conclusion; check whether the curve is a genuine path.
</grounding_rules>
