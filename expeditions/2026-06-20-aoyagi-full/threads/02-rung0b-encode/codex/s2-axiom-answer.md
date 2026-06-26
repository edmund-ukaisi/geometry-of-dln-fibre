Bottom line: your draft is **faithful to Aoyagi’s normal-crossing formula**, but it is **not minimal** if S2 is supposed to cite only the irreducible monomial-integral content. Also, the phrase “proper analytic diffeo” is a real problem: a resolution/blow-up map is not a diffeomorphism along the exceptional divisor.

1. **λ as `⨅ᵢ ⨅ⱼ (h+1)/(2k)`**: **FAITHFUL-WITH-CAVEAT**.

`k_j = 0` should contribute `⊤`, because that axis gives `∫ u^h du`, independent of `c`, so it never constrains the threshold. Do not exclude it unless you prefer a filtered finite min over `k_j > 0`.

Lean caveat: make sure division happens in `ENNReal`, not `ℝ`, `ℚ`, `NNReal`, or `ℕ`.

```lean
def axisRatio (h k : ℕ) : ENNReal :=
  ((h + 1 : ℕ) : ENNReal) / ((2 : ENNReal) * (k : ENNReal))
```

If you compute in `ℝ` first, `a / 0 = 0` in Lean, which is wrong here. Add hypotheses ensuring the intended finite-singular case: nonempty chart family, `F w* = 0`, `F` not locally zero, and at least one relevant `k > 0`. Otherwise the locally-nonvanishing case gives `rlctAt = ⊤`, and the pole order is not really the Aoyagi object.

2. **Bump in hypotheses, bump-free `rlctAt` conclusion**: **FAITHFUL-WITH-CAVEAT**.

It is clean only if S1 is genuinely outside S2. As drafted, an axiom with bump data concluding directly about bump-free `rlctAt` does silently include bump-independence.

Cleaner fix: define or at least name a bumped threshold/order, let S2 conclude the normal-crossing formula for that, then prove in S1 that the bumped value equals `rlctAt`.

Also, the bump should be positive on a small neighbourhood of `w*`; after pullback it is a positive smooth unit. Do not let arbitrary bump vanishing be absorbed into `h_j`, or the formula becomes bump-dependent.

3. **Hypothesis list vs monomial fact**: **NOT-MINIMAL as drafted**.

The implication

```lean
cover + proper analytic map + monomial pullback + Jacobian form
  → rlctAt = min ratios
```

uses cover, change of variables, unit-boundedness, and local-to-global assembly. If those are meant to be proved in R1/S1, they should not be inside the cited axiom’s logical jump.

The sharp fix is: R1/S1 prove that local integrability of `|F|^{-c}` is equivalent to integrability of a finite family of monomial integrals. S2 only says those monomial integrals give the ratio formula.

Also replace “proper analytic diffeo onto its image” with:

```text
proper analytic map π, analytic in local coordinates,
an analytic isomorphism only off the exceptional divisor / zero locus
```

A blow-up chart has vanishing Jacobian on the exceptional divisor, so it cannot be a diffeomorphism there. Requiring diffeomorphism would force essentially `h_j = 0` and would miss the actual resolution situation.

4. **Order conclusion bundled with value**: **FAITHFUL-WITH-CAVEAT**.

Aoyagi explicitly states the order as the max chart-count, so bundling it with the value is faithful to the cited normal-crossing extraction. But it is not a consequence of the bare `L¹` convergence criterion. It also cites the meromorphic pole-order computation for products of one-variable factors.

So: sound, but document S2 as “normal-crossing extraction of value and pole order,” not merely “the monomial integrability criterion.” Positivity of the pulled-back density/unit matters to rule out cancellation of leading pole terms.

5. **Simpler faithful statement**: best bedrock is a **monomial chart extraction axiom**, not the full resolution-map axiom.

I would not make the axiom mention `π`, properness, covers, or diffeomorphisms. State S2 at the level:

```text
For exponents k_j, h_j and positive bounded units,
the threshold of ∏ |u_j|^(h_j - 2 k_j c)
is min_j (h_j+1)/(2k_j),
and the pole order is the number of axes attaining the minimum.
```

Then prove cover/change-of-variables/chart assembly outside S2.

The 1-D criterion is even smaller, but deriving the full chart formula plus the pole order in Lean will require Fubini/Tonelli and meromorphic-order bookkeeping. For a “one citation only” standard that is still practical, the d-dimensional monomial extraction is the right size.

6. **Sign/convention hazards to pin**:

- Real case: Aoyagi’s `k = 1`, so `rlctAt` uses `|F|^{-c}`.
- For squared loss / ideal sum of squares, the normal-crossing exponent is `2k_j`, hence `(h_j+1)/(2k_j)`.
- Zeta convention: `Z(z) = ∫ |F|^z φ`; the pole is at `z = -λ`, not `+λ`.
- Use `|det Dπ|` and `|u_j|`; signed monomials are wrong for real integrability.
- If you ever switch from `F = sum of squares` to unsquared generators, the factor `2` changes.

Final verdict: **faithful but over-broad**. Move cover/properness/change-of-variables/bump-independence out of the axiom, fix the “diffeo” wording, compute ratios directly in `ENNReal`, and label the θ half honestly as pole-order extraction, not just integrability.