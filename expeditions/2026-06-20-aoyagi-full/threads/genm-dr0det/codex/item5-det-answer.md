**Q1.** For the stated `phiFlatLiveAt` with direct `readE x`, `|det DB| = 1` is not compatible with an E-slot pivot. The banked `Cgen_live_interior_eq_schurFrameProd` and `schurFrameProd_u_to_E` imply the chart uses `(x p₀) • readE x`; since `readE x` at the pivot is itself `x p₀`, the pivot E entry becomes `(x p₀)^2`. So yes: the current chart-param map does read the pivot E-slot; it is not automatically consumed by the radial axis. The pure `|u_p|^(minAdm-1)` note is correct only for a gauge-fixed E-pivot chart where the chart-side E reader pins/skips the pivot residual.

**Q2.** For the current stated chart, the exact matching B-reader must be:
```lean
Ehat y i j =
  if activeSlotE ... ⟨0⟩ i j = p₀ then (y p₀)^2
  else y (activeSlotE ... ⟨0⟩ i j)
```
because at `y = pivotBlowupOn active p₀ x`, this equals `(x p₀) • readE x`. But this B is not determinant-one: the pivot coordinate is quadratic, giving an extra local factor. For determinant one, the chart itself must use the gauge-fixed E reader `Echart x pivot = 1`, `Echart x nonpivot = x slot`, and then B may read directly:
```lean
Ehat y i j = y (activeSlotE ... ⟨0⟩ i j)
```

**Q3.** For `M=(1,1,2)`, `active={p₀}`, so `pivotBlowupOn active p₀ = id`; current direct-read chart gives `|det Dφ(u)| = |d(u_p^2)/du_p| = 2|u_p|`, while the gauge-fixed E-pivot chart gives `|det Dφ(u)| = |u_p|^0 · 1 = 1`.

**Q4.** The right general statement `|det Dφ| = |u_p|^(minAdm-1)` with identity-like B is valid only after the E pivot is gauge-fixed on the chart side. The non-pivot E slots do not create hidden extra factors: their scaling is exactly the `pivotBlowupOn` Jacobian counted by `active.card - 1`. The only uncancelled extra comes from the pivot E slot if it is still read as a residual coordinate. That is the double-counting: radial axis plus residual E coordinate.

VERDICT:
(a) Is `|det DB|=1` correct? **Yes only for the gauge-fixed E-pivot chart; no for the stated direct-read `phiFlatLiveAt`.**
(b) Correct det-one B E-reader: **direct read, `Ehat y i j = y (activeSlotE ... i j)`, with the chart-side pivot E entry pinned to `1`.**
(c) Biggest risk: **the pivot E-slot is silently still read by `readE`, producing `(u_p)^2` and an extra Jacobian factor.**