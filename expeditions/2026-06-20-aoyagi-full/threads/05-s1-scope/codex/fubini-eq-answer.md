1. **PIECE 1: SOUND, with one technical FLAG**

(a) **SOUND.** On the cusp `x² ≤ H`, we have `x² + H ≤ 2H`; since `-c < 0`, `t ↦ t^(-c)` is antitone, so `(2H)^(-c) ≤ (x² + H)^(-c)`. This is the correct lower bound: divergence of the cusp lower bound forces divergence of the joint integral.

(b) **FLAG, minor but real.** The exponent algebra is correct:
`(2H)^(-c) · 2√H = 2^(1-c) H^(1/2-c) = 2^(1-c) H^{-(c-1/2)}`.
But over `Icc(-R,R)` the slice volume is literally `2 min(R, √H)`, not always `2√H`. The written equality needs either `H ≤ R²` on the relevant neighborhood, or the standard local-finite-measure truncation argument restricting to `{H ≤ R²}`, where core divergence occurs for the negative exponent.

(c) **SOUND.** The implication
`joint integrable at c > 1/2 ⇒ core integrable at c - 1/2`
is exactly the contrapositive needed for
`λ(x² + H) ≤ 1/2 + λ(H)`, since any `c > 1/2 + λ(H)` gives `c - 1/2 > λ(H)`.

2. **PIECE 2: SOUND, assuming the stated measure/product hypotheses**

(a) **SOUND.** RLCT thresholds are invariant under a measure-preserving homeomorphism: neighborhoods correspond topologically, and measure preservation transports local integrability of `|F|^{-c}` and `|F ∘ e|^{-c}`.

(b) **SOUND.** If `G² > 0` a.e., then each peeled core
`Σ_{i<m} xᵢ² + G²`
is also nonzero a.e.; indeed it is pointwise `≥ G²`. This uses the product-measure/a.e. inference.

(c) **SOUND, with standard convention.** For `n = 0`, `Fin 0 → ℝ` is a singleton, the empty sum is `0`, and the product with the singleton is measure-preservingly identified with `Y`; hence the statement reduces to `λ(G²) = 0/2 + λ(G²)`.