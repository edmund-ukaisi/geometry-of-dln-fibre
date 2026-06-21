# L2 architecture + S1.5 restatement — the smooth-block Fubini lemma

- **Seat:** `pp` (design). **Read-only; /tmp scratch; no Lean.** Task #34 (S1.5/L2-additivity strategy).
- **Verdict:** the abstract disjoint-block additivity (S1.5 as fm-2 found it — FALSE two ways + needs
  Laplace machinery, uncitable) is NOT needed. Replace it with the **smooth-block/monomial Fubini
  lemma**, proven by integrating the smooth block out in closed form. Me + decorrelated Codex agree,
  independently, via the same route.

## The question

After the L2/Theorem-3 split, the loss is, in disjoint variable blocks,
`F = Σ_{i=1}^n x_i² + ‖∏C‖²` (n = r(H¹+H^{L+1})−r² smooth regular coords + the singular core in the
complementary vars). Target `rlctAt F = n/2 + λ_core`. Does L2 need the abstract additivity
`λ(f(x)+g(y)) = λ(f)+λ(g)`?

## Verdict: NO — three options adjudicated

**(a) R1-on-full-loss (resolve regular+core together) — does NOT work directly.** `F = Σx² + core`
is a SUM, not monomial×unit. The regular coords are NOT extra normal-crossing factors: a monomial
zero-set is a union of coordinate hyperplanes, but `Σx² + m² = 0 ⟺ x=0 ∧ m=0`. Even after blowing up
the x-cone (`Σx² = r²·unit`, Jac `r^{n-1}`) the full loss is `r²·unit + m²·unit` — still a sum, S2
inapplicable. Making (a) work needs **mixed principalization of `(x_1,…,x_n, m(u))`** — a genuine
extra resolution theorem, heavier in Lean than the analytic estimate. (Codex + pp agree.) AVOID.

**(b)-general full additivity — AVOID** (fm-2's finding: false without hyps — non-measurable g; g≡0 ⟹
RHS=⊤; and even with hyps needs Laplace/Mellin `L_F(t)L_G(t)~t^{−(λ_F+λ_G)}`, Mathlib-gap, uncitable).

**(b)-special / (c) — THE ANSWER: the smooth-block Fubini lemma.** Integrate the SMOOTH block out in
closed form (the smoothness is exactly what makes it explicitly integrable):

> **S1.5 (restated) — smooth-block Fubini-product RLCT.** In a core normal-crossing chart where
> `core∘φ = unit·∏_j u_j^{2k_j}` and `|det Dφ| = unit'·∏_j |u_j|^{h_j}`, the full loss
> `F = Σ_{i=1}^n x_i² + core` has
> `rlctAt F = n/2 + min_j (h_j+1)/(2k_j)`.
> Equivalently, adding `Σx_i²` shifts the chart's RLCT by exactly `n/2`.

## The proof (light — radial scaling + Fubini, NO Laplace)

The load-bearing identity (verified exactly, sympy `/tmp/l2_scaling_check.py`, n=1,2,3):
> `∫_{|x|<ε} (|x|² + s)^{−c} dx = C(n,c)·s^{n/2−c}` for `s ≥ 0`, with `C(n,c) = ∫(ρ²+1)^{−c}ρ^{n−1}dρ`
> **finite iff `c > n/2`** (substitute `x = √s·ρ`; Beta-function convergence).

Then by **Fubini** (x-block integrated first, `s = core(y) ≥ 0`):
`∫∫ |Σx² + core|^{−c} dx dy = C(n,c) · ∫ |core(y)|^{−(c − n/2)} dy`.
The y-integral is the core's RLCT integral at the **shifted exponent `c' = c − n/2`**, so it converges
iff `c − n/2 < λ_core` iff `c < n/2 + λ_core`. Hence `rlctAt F = n/2 + λ_core`. ∎

Codex's independent asymptotics match: `I_c(A) := ∫_{|x|<ε}(|x|²+A²)^{−c}dx` is bounded for `c<n/2`,
`~log(1/A)` at `c=n/2`, `~A^{n−2c}` for `c>n/2` — same `s^{n/2−c}` scaling, giving the core integral
`∫∏|u_j|^{h_j + k_j(n−2c)} du`, finite iff `c < n/2 + min_j (h_j+1)/(2k_j)`.

**What it needs from Mathlib (all reachable, NO Laplace/Mellin):**
1. the radial-scaling identity `∫(|x|²+s)^{−c}dx = C·s^{n/2−c}` (a polar-coordinates + `x=√s·ρ`
   change-of-variables computation; `C` a Beta integral, finite iff `c>n/2`);
2. Fubini on the product domain (x-block × core-vars), legitimate (nonneg integrand);
3. the shifted-exponent comparison to the core's RLCT (which R1/S2 already supply as
   `min_j (h_j+1)/(2k_j)`).
The smooth-block-ALONE value `rlctAt(Σx²) = n/2` (fm-2 is proving it) is the `core ≡ const` /
`s→` special case — a sublemma, useful but it does NOT combine the blocks by itself.

## Where it lives in the architecture

The restated S1.5 is applied **per chart, inside R1**: each core normal-crossing chart (from the
binding-divisor resolution) carries the regular `Σx²` block alongside; the Fubini lemma shifts that
chart's RLCT by `n/2`. Then
`λ_full = min_chart (n/2 + λ_{core,chart}) = n/2 + min_chart λ_{core,chart} = n/2 + λ_core
       = n/2 + ½·min_t Mval(t)`.
So L2's regular⊕core combination is the Fubini lemma + R1's core resolution + the min-over-charts —
NOT a standalone additivity theorem. The `n = r(H¹+H^{L+1})−r²` regular count is the L2 §3 figure
(½·n = the regular term; design-spec terminology already corrected to "rank-r stratum dim").

## Recommendation (one line)

**Restate S1.5 as the smooth-block Fubini-product RLCT lemma** (`rlctAt(Σx² + monomial·unit, Jac
weight) = n/2 + min_j(h_j+1)/(2k_j)`), prove it by the radial-scaling identity + Fubini (light,
one-citation-clean, NO Laplace), and apply it per-chart inside R1. Drop the abstract additivity (false
+ heavy) and the R1-on-full-loss mixed-principalization (heavier). The smooth-block-alone `n/2` value
is a sublemma. This is L2's analytic engine, one-citation-compliant.
