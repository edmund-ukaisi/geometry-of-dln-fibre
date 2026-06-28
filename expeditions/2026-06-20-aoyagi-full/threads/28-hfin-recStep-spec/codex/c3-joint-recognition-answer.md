**RECOMMENDED STRUCTURE**

1. Work only in the `2 < c' < 4` branch for this wiring. Handle `c' ≤ 2` outside by exponent bump / monotonicity, as in the existing `RouteM334Ratiofin` pattern.

2. Normalize the pivot `p` to `(0,0)` first. Use row/column swaps on `Rmat3 p (e.symm (0,z))` and the corresponding row permutation on `S`. Mirror `schurInner_S_bound_pivot`.

3. Split the `z : Fin 8 → ℝ` cube by a measurable equivalence
   ```lean
   zE p : (Fin 8 → ℝ) ≃ᵐ ((Fin 2 × Fin 2 → ℝ) × (Fin 4 → ℝ))
   ```
   where `q.1` is the raw `M22` block and `q.2` is the four boundary coordinates `(g0,g1,b0,b1)`. This is the cleanest Lean move. It is the same pattern verified in `RouteM334Ratiofin`: `zσ`, `cellOf`, `zE`, `bgShift`.

4. After N2b + row split + row0 shear, aim for the joint resolved form before integrating out the Morse block:
   ```lean
   ∫ v in vbox, ∫ M in boxP 1, ∫ Sbot in matBox 2 4 T,
     ∫ P in morseBox 4 (3*T),
       ofReal ((∑ j, (P j)^2 + frobSq ((matOf M - Sh v) * Sbot)) ^ (-c'))
   ```
   with `Sh v = bgShift v`, `|Sh v i j| ≤ 1`.

5. For each fixed `v`, use the fixed-shift translation/enlargement. Prefer a `_le` form, not only:
   ```lean
   schurResid2_translate_lt_top
   ```
   You need a bound uniform in `v`, e.g.
   ```lean
   residualShift v ≤
     ∫ Δ in matBox 2 2 K, ∫ S in matBox 2 4 K,
       ofReal ((frobSq (Δ * S)) ^ (-(c' - 2)))
   ```
   with `K := max 1 (3*T)` or Lean-friendlier `K := 1 + 3*T`.

6. Apply the Morse peel only on the joint `(Δ,Sbot)` outer space, using the a.e. wrapper:
   ```lean
   core_T_peel_le_ae
   ```
   if imported, or a local copy derived from `radial_morse_residual_power_le` via `lintegral_mono_ae`.

7. Close the shifted residual with `schurResid2_translate_lt_top` / its `_le` refactor at
   ```lean
   c'' := c' - 2
   ```
   using `0 < c''` from `2 < c'` and `c'' < 2` from `c' < 4`.

8. Finally integrate over the boundary `vbox`. This is valid only after you have a uniform bound independent of `v`:
   ```lean
   ∫ v in vbox, C ≤ C * volume vbox < ⊤
   ```

For Q3: yes, the one-radius issue is harmless. Enlarge both boxes to a common radius. `max 1 (3*T)` is sharp; `1 + 3*T` is often easier for `linarith`.

**THE w=0 EDGE**

Do not apply `radial_morse_residual_power_le` pointwise for each fixed `Sc` and `Sbot`. That is the wrong structure.

The sound handling is: keep the Morse block and residual coupled until the outer variables include both `Δ` and `Sbot`, then apply the a.e. peel. The zero set
```lean
{(Δ,S) | frobSq ((Δ - Sh) * S) = 0}
```
is null for fixed `Sh`, by translating `Δ` and using the banked unshifted nonvanishing/null-set lemma if available. Verified nearby repo lemma: `frobSq_core334_ne_zero_ae` exists in `RouteM334Hfin`. Verified wrapper: `core_T_peel_le_ae` exists there too, but it is not imported by `RouteMSchurCorank3.lean` as currently shown.

So:

- Option (a) is false in the fixed-`Sc` formulation, especially at `Sc = 0`.
- Option (c) undershoots the threshold.
- Option (b) is the right direction, but phrase it as: keep the full joint `∑P² + frobSq(Sc*Sbot)` and peel only a.e. over joint `(Δ,Sbot)`.

**RISKS**

1. Highest: `schurResid2_translate_lt_top` is only `< ⊤`. Pointwise finiteness in `v` does not imply integrability over `vbox`. Mitigation: expose a uniform `_le` version from its proof, then multiply by `volume vbox`.

2. Medium: shifted a.e. positivity. Lean may thrash proving `0 < frobSq ((Δ-Sh)*S)` a.e. Mitigation: translate `Δ` before the peel, or prove a small shifted wrapper from `frobSq_core334_ne_zero_ae`.

3. Medium: `Fin 8` slot bookkeeping. Mitigation: use a single `zE p` measurable equivalence like `RouteM334Ratiofin`; avoid ad hoc coordinate projections throughout the proof.