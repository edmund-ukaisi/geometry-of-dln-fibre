**Q1.** No. Closing `sjJointResolution` in one tide is not realistic.

The current target at [RouteMSJResolution.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a36fc727f90973663/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJResolution.lean:803) is still a raw matrix-box `lintegral`. The terminal ledger at [RouteMSJLedger.lean](/home/ubuntu/workspace/geometry-of-dln-fibre/.claude/worktrees/agent-a36fc727f90973663/lean/DLNFibre/DLN/RLCT/Validate/RouteMSJLedger.lean:236) is over resolved coordinates with monomial Jacobian. There is no bridge between those worlds.

The missing bridge is a real construction: finite chart tree, explicit iterated blow-up maps `Φ`, image/cover/null-set control, per-node injectivity or measure transport, Jacobian product, pulled-back generator identities, and assembly of leaf finiteness. The banked pieces cover useful local algebra and endpoints, but not the resolution map.

Estimate: maybe **25-35% bankable plumbing**, **65-75% genuinely new construction**. The new part dominates. I would expect multi-module work, plausibly hundreds to low thousands of LoC depending on how reusable the chart-tree interface is. Pointwise `frobSq` bricks cannot shortcut the `lintegral` change-of-variables gap.

**Q2.** Piece 1 is buildable, but only if it introduces a non-terminal generator carrier. `SJSupport` alone is terminal data; it cannot describe linear residual generators.

The clean carrier should be something like:

```lean
structure SJLinGenState (ζ ν ι : Type*) [Fintype ν] [Fintype ι] (d : ℕ) where
  supp  : SJSupport ι d
  coeff : ζ → Matrix ι ν ℝ
```

with evaluation

```lean
residual z x i := ∑ v, coeff z i v * x v
gen u z x i := genMonomial supp i u * residual z x i
loss u z x := ∑ i, (gen u z x i)^2
```

Here `ζ` are spectator/unit parameters, `ν` are still-unresolved active linear variables, and `ι` indexes generators. A step map should be generator-level, not `frobSq`-level:

```lean
structure SJGenStep (G : SJLinGenState ζ ν ι d)
                    (G' : SJLinGenState ζ' ν' ι' d') where
  phiζ : ζ' → ζ
  phiν : ζ' → (ν' → ℝ) → (ν → ℝ)
  row  : ζ' → Matrix ι' ι ℝ
  residual_eq :
    ∀ z x j,
      residual G' z x j =
        ∑ i, row z j i * residual G (phiζ z) (phiν z x) i
  support_ok :
    -- either equal-support mixing, or an explicit proof that each new row has the claimed monomial factor
```

For the first useful brick, I would prove a **support-compatible row-mix lemma**: if every row of the unit block-elimination mixes only generators with the same support vector, then the support and shared-divisor exponents are preserved row-by-row. Then instantiate it for the `step3_blockFactor` / unit-absorption map.

So: there is a clean intermediate carrier. Piece 1 is not vacuous. But any formulation that only states `pref * frobSq = pref * u^2 * residual` is too coarse and does not advance the ledger.

**Q3.** I do not see a new stratum obstruction from the current banked material. The obstruction is not “some `(S,J)` stratum refuses single-radial decomposition”; it is that the full explicit decomposition and its c.o.v. assembly are not built.

So my blunt verdict is: **piece 1 is a worthwhile algebraic brick; pieces 2 and 3 need the large unbanked resolution-map/change-of-variables construction; `sjJointResolution` should not be expected to close this tide.**