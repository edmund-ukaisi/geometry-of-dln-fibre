**1. Route Verdict**
Sound, and likely the lightest. For `t ≠ 0`, the family with recombination row `[t, 1]` has the upstairs rank pattern.

No hidden bad `(i,j)`: the only sensitive products are those crossing edge `b`, i.e. `i ≤ b < j`. There:
- if `a ≤ i < c` and `b < j ≤ e`, the product is `[t]`, rank `1` for `t ≠ 0`, rank `0` at `t = 0`;
- if `c ≤ i ≤ b` and `b < j ≤ e`, the product is `[t, 1]`, rank `1` for all `t`.

That is exactly upstairs for `t ≠ 0` and downstairs at `t = 0`. `[Std]` rank of nonzero `1×1` scalar and nonzero row into a `1`-dimensional target is `1`. `[Verify]` exact matrix orientation/signature in your encoding.

**2. The Recombined Chain**
Use option **(b')**: define a scalar-parametric one-edge edit of the two-summand upstairs tuple, not a downstairs `dirSum`.

Concretely:
- set `d₂ l := intervalDim a e l + intervalDim c b l`;
- set `U₂ := dirSum (intervalModule a e) (intervalModule c b)`;
- define `splice λ : Tuple d₂` to equal `U₂` on every edge except `b`;
- at edge `b`, define the block matrix in long/short coordinates:
  ```text
  source at b:     long ⊕ short = 1 ⊕ 1
  target at b+1:   long ⊕ short = 1 ⊕ 0

  recomb(λ) = [ λ  1 ]
  ```
  preferably as one `fromBlocks`/`reindex finSumFinEquiv` matrix:
  ```text
  top-left:  λ : long_b → long_{b+1}
  top-right: 1 : short_b → long_{b+1}
  bottom blocks: zero, because short_{b+1}=0
  ```

Then `R := splice 0`, and `Fpoly` is the same construction with `λ = Polynomial.X`. This localizes `finSumFinEquiv` pain to one arrow.

Edge matrices by region, in coordinates `(long, short)` on `[c,b]`:
```text
a ≤ p < c-1      1→1   [1]
p = c-1          1→2   [1; 0]
c ≤ p < b        2→2   [[1,0],[0,1]]
p = b            2→1   U=[1,0], R=[0,1], F(t)=[t,1]
b < p < e        1→1   [1]
start/end/outside        unique zero-sized maps
```

**3. Rank-Pattern Induction**
Use three lemmas, not one large symbolic calculation.

1. `edge_ne_b`: `splice λ p = U₂ p` for `p ≠ b`.

2. `submult_avoid_b`: if the product does not cross `b`, i.e. `j ≤ b` or `b < i`, then
   ```text
   submult (splice λ) i j = submult U₂ i j.
   ```
   Then use your existing `rankPattern_dirSum`.

3. `submult_cross_b`: if `i ≤ b < j`, factor the product as
   ```text
   submult (b+1,j) using U₂
   * recomb(λ)
   * submult (i,b) using U₂
   ```
   using a local `submult` concatenation lemma, name to verify/prove locally.

Do not try to prove crossing products are block diagonal. They are not. They are “block-diagonal segment, recombination row, block-diagonal segment.” The rank stays upstairs for `λ ≠ 0` because:
- first-strand-only inputs cross as scalar `[λ]`, rank `1`;
- overlap inputs cross through `[λ,1]`, rank `1`;
- target after `b` is only one-dimensional anyway.

**4. Pitfall Check**
Worst trap: transporting too early between
```text
foldDim [(a,e),(c,b)]
foldDim [(a,b),(c,e)]
intervalDim a e + intervalDim c b
intervalDim a b + intervalDim c e
```
while also unfolding `finSumFinEquiv`.

Sidestep: prove the no-rest construction over the explicit local dimension
```text
d₂ l := intervalDim a e l + intervalDim c b l
```
first. Only after closure for `R` is proved, transport the genuine downstairs tuple using the pointwise dimension equality and your existing downstream transport/common-summand wrapper. Also avoid hardcoding `Fin 2`/`Fin 1`; define the special arrow in block coordinates and let `fromBlocks` carry the indexing.

**5. Fallback**
Best value/effort order:

1. **General no-rest non-split move over `d₂`**: prove `splice 0` is in the closure of `U₂`. Highest value; rest should glue via your existing wrapper.

2. **Bank the two rank-pattern lemmas only**:
   ```text
   λ ≠ 0 → rankPattern (splice λ) = rankPattern U₂
   rankPattern (splice 0) = downstairs formula
   ```
   The engine application is then mechanical.

3. **Bank only the crossing lemma** for `i ≤ b < j`; no-cross follows from edge equality with `U₂`.

4. Fixed small `N` / `(1,2,1)` witness is lowest value; useful only as a sanity test, not as infrastructure.