**1. VERDICT**

OBSERVED: Your gauge-absorption lemma is a linear-algebra surjectivity statement, while `sjJointResolution` needs finiteness of a measure integral.

INFERENCE: Your middle read is basically right. It is not a plug-in “one lemma” for the banked freed-Γ contract, because it does not supply the three failed pointwise hypotheses. It suggests a different seam-chart proof: normalize, split orbit/slice variables, transport measure, reduce to the shifted chain plus monomial endpoint. The “~4-10 tides” estimate is plausible but not guaranteed; the number depends almost entirely on how much finite-dimensional CoV/IFT/chart-cover infrastructure already exists.

**2. THE KEY RISK**

INFERENCE: The key risk is the upgrade from infinitesimal surjectivity to an actual measurable product-coordinate change with controlled Jacobian and loss comparison.

OBSERVED: The lemma only gives linearized base-change surjectivity at a block-normalized corank-q point.

INFERENCE: That suffices for a local submersion/IFT statement, not automatically for a global or measure-preserving CoV. “Jacobian 1” is especially suspect unless the nonlinear coordinate map is explicitly triangular/unipotent, not merely obtained by IFT. For finiteness, bounded-above/below Jacobian may be enough, but Lean still needs the local cover, measurability, domain restriction, Fubini, and comparison to the shifted-chain integral. This is the most likely place the route balloons.

**3. RANK-DEFICIENT `Q_b` WALL**

OBSERVED: The native route hits rank-deficient `Q_b Q_bᵀ` on bottleneck charts and therefore cannot use the banked inner Γ lemma pointwise.

INFERENCE: Gauge-absorption plausibly avoids that specific wall because it no longer asks `Q_b Q_bᵀ` to be positive definite; the BR shifted-complement block becomes the normal direction and the rest is absorbed along gauge directions.

INFERENCE: The wall may reappear as a slice-regularity problem: if deeper bottlenecks make the orbit/slice rank fail, or make the shifted-chain loss comparison nonuniform, then the same geometry returns under a different name. Your stated lemma suggests the first-order rank issue is handled, but it does not by itself prove nonlinear uniformity across the boundary.

**4. RECOMMENDATION**

INFERENCE: Drive the seam-chart route, but treat it as a new proof path, not a cheap patch to the freed-Γ machinery. The spend is justified if the controller wants to avoid the native carrier descent’s rank-deficient and coupled-boundary machinery. First milestone should be a local CoV theorem around one normalized seam chart with controlled Jacobian and an explicit reduced-loss comparison to the shifted chain. If that theorem lands cleanly, continue. If it requires rebuilding a large decorated carrier anyway, switch back to the native route.