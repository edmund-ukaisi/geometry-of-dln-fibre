1. **MAYBE / conditional YES.**

A second squeeze route works if you can prove a local comparison with the **shared reg term**:

`∃ a A > 0, ∀ᶠ x in 𝓝 wstar,`
`a * (reg x + coreΦ x) ≤ reg x + Score x ∧ reg x + Score x ≤ A * (reg x + coreΦ x).`

Then brick (2) gives the second sandwich against `dlnLoss`, and hstep2 follows by transitivity through `rlctAt(dlnLoss)`.

A clean sufficient lemma is:

`∀ᶠ x in 𝓝 wstar, ‖P x - Q x‖_F^2 ≤ B * reg x`

where

`P x = prod_M (core_s + correction_s)` and `Q x = Schur(Mw x)`.

Then triangle inequalities give `reg + ‖P‖² ~ reg + ‖Q‖²`.

**Inference:** this needs `K`, correction mismatches, and any Schur-vs-flat encoding error to vanish in directions controlled by `reg`. Brick (1)+(3) alone do not state that. If you can prove this `O(reg)` error estimate, the sandwich route is probably Lean-easier than the full Ψ.

2. **NO for pure core-vs-Score sandwich as stated. YES only with reg absorption.**

`frobSq(prod(core+correction))` and `frobSq(S0 (1-K) S1)` are not generally mutually bounded just because `1-K → 1`.

Reason: for variable matrices, inserting a near-identity middle factor can change the zero set. One can have `S0 S1 = 0` but `S0 (1-K) S1 ≠ 0` for small nonzero `K`. Then no positive constant can satisfy `Score ≤ C * coreΦ`.

So the shortcut is **not**:

`coreΦ ~ Score`.

The viable shortcut is:

`reg + coreΦ ~ reg + Score`

via an estimate like

`‖S0 (1-K) S1 - S0 S1‖_F^2 ≤ B * reg`

plus analogous estimates if `P` is not literally `S0 S1`.

**Lean tractability ranking:**

1. Best: prove `‖P-Q‖² ≤ B*reg`, then squeeze `reg+...`.
2. Worse: full joint Ψ with exact reparametrization.
3. Do not pursue: pure `coreΦ ~ Score`; likely false unless special scalar/central/rank constraints apply.

3. **If the shortcut fails, sequence `reg`-preservation first.**

If you cannot prove the reg-absorbed comparison, then yes, the Ψ route is genuinely required.

The highest-risk sub-lemma is **reg-preservation E2**: proving the joint `(T1,Y1)` action leaves the syntactic `reg` term unchanged through the flat encoding.

`W⁻¹` smoothness is technical and annoying, but standard-ish once invertibility is localized. E2 is the mathematical keystone: if it fails, the bridge does not prove equality of the actual `Φscore`/`Φcore` germs.