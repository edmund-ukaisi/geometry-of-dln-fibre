# Thread 05 — Wave 1b: R3-route probe (resolution datum + the resolved-chart Newton gamble)

**Type:** pen-and-paper / scout (exact algebra + decorrelated Codex; **no Lean writing** — output is a
spec/certificate the R3 tide will formalize).

## The decision this resolves

The lower bound `rlct ≥ ½·codim` (the wall) needs the pair `(ℝ^N, c·I_fibre)` log canonical
(`lct(I_fibre)=c`). R1 proved the STANDARD-coordinate Newton route is DEAD (the DLN loss is
Newton-degenerate: explicit torus point `A₁=A₂=A₃=[[1,1],[1,1]], A₄=[[1,−1],[2,−2]]` gives `K=0,∇K=0`;
naive toric bound 2 ≠ 3/2). The surviving gamble: after the rank/SVD change of coordinates (Aoyagi's
resolution), is the loss **Newton-nondegenerate in the resolved chart** — so ONE citable theorem
(Saito–Varchenko in the resolved chart) discharges the per-divisor inequalities — OR does it genuinely
need Aoyagi's full recursive bespoke blow-up (Cases 1/2 induction)?

## Inputs

- R1's resolved toric model for `(2,2,2,2,2)` r=0: SVD/rank blow-up → ideal `J = ⟨zr−cp, a(c−zq), dr,
  adq⟩`, lct 3 (half for sum-of-squares → 3/2). (In R1's `thread.md`,
  `threads/02-deepest-stratum-rlct/thread.md`, + its `codex/`.)
- Aoyagi's paper (the bespoke real resolution, Cases 1/2). Lehalleur–Rimányi Thm 8.6 (the formula-match
  `2λ = C`, already Lean: `Aoyagi.two_lambda_eq_codimFormula`, `codimRepCanonical_fibre_eq_two_aoyagiLambda`).
- The DLN loss `K = ∑_{ij}(A_N…A_1)²_{ij}` and the orbit/rank-pattern stratification (the geometry is
  banked in `Core`).

## Deliverables (certificate, no Lean)

1. **Verdict:** R3-Newton-resolved VIABLE (one citable theorem in the resolved chart) vs R3-resolution
   NEEDED (full bespoke blow-up). Test on `(2,2,2,2,2)` r=0 first, then check whether the structure
   generalizes (the rank/SVD chart is uniform across strata?).
2. **The resolution datum spec** the R3 tide will formalize: the chart(s), the divisor multiplicities
   `(kⱼ,hⱼ)`, and the per-divisor inequality `hⱼ+1 ≥ c·kⱼ` to verify; OR, if Newton-resolved, the exact
   citable theorem + the nondegeneracy condition to check.
3. **Cost estimate** for the R3 tide(s): how many charts, whether it reduces to a combinatorial
   `min_T (something) ≥ cCodim` (the kind of inequality the team has discharged before — cf. the
   `cCodim·0` monotonicity work), and the biggest risk.
4. Decorrelated Codex consult banked in `codex/`.

## Discipline

Exact algebra only (sympy/sage/Gröbner as instruments; Monte-Carlo only guides — R1 showed float can't
discriminate here, m=5 log factor). name=content. Flush to `thread.md`; report the verdict + spec to
`main`. **In-repo only — never write to `~/.claude` global memory.**
