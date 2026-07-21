## SCOPE VERDICT

**multi-tide-monument — ~5%** chance the full obligation lands within 1500 new lines.

Code fact: the existing tree is combinatorial—its steps use `localSub := id`, and terminal leaves have `numB := 0`, `chartMap := id`. The missing work therefore includes the semantic invariant relating actual substituted matrices to the ledger.

The one biggest blowup reason is formalising that dependent, arbitrary-width matrix invariant through coupled Case 1: substitutions, Schur/shear coordinates, cofactors, index transports, and continuity must evolve coherently with the combinatorial state.

A useful simplification, inferred from the record: full `U·M·V = diag(b₁,…,bₘ)` is unnecessary. Since `hchain` makes the monomial ideal principal, take `M' = 1` and prove only:

- every entry of `∏C ∘ g` is divisible by `b₁`;
- `b₁` is a continuous Bézout combination of those entries.

This improves the odds, but not enough for one tide.

## DECOMPOSITION

Introduce an algebraic path invariant `PrincipalInv d s g b q r` expressing those two identities.

1. `principalInv_regionRepresents` — divisibility plus Bézout witnesses imply both `RegionRepresents` directions. **high × very-high**

2. `coordinateCenterBlowupResolution` — `0 < m → ∃ res : Resolution (centerCoordFam m spectators) 0, …`. **very-high × high**

3. `case2_preserves_principalInv` — `PrincipalInv … s … → PrincipalInv … (case2Child s) …`. **very-high × medium**

4. `case1_preserves_principalInv` — parent invariant produces both coupled Case-1 child invariants. **maximum × low**

5. `leaf_principalInv_of_path` — fold the one-step results along a root-to-leaf path. **maximum × medium**

6. `leafPath_chartGeometry` — path map is analytic, origin-fixing, a.e.-injective, with the ledger Jacobian and squarefree `b₁`. **high × medium**

7. `leafPath_compactCover` — `∃ ρ > 0, volume (ball 0 ρ \ ⋃ p, g p '' dom p) = 0`. **maximum × low-medium**

8. `leafPath_realizesExponents` — binding axes correspond to terminal `t̃=0` divisors and `jac+1 = divExp`. **high × medium**

## BEST SLICE

**(c): a general coordinate-centre max-pivot blow-up resolution, with bounded spectators.** Candidate (a) is its two-dimensional specialization; the general version remains a complete `Resolution` term while directly matching every recursive blow-up atom. It exercises analytic nonidentity charts, Jacobians, null exceptional hyperplanes, two-sided principal ideal witnesses, and a finite compact cover. Candidate (b) is currently risky scaffolding because the existing tree’s geometric fields are placeholders.

The likely Lean bite is the cover: spectator coordinates must also be bounded so each source domain is compact; a convenient `pivotDomain × univ` formulation will not inhabit `Resolution`.

## BLINDSPOT

The likely false assumption is that `g` is purely a composition of monomial substitutions. Coupled Schur reduction generally needs determinant-one coordinate shears—or an equivalent algebraic reparameterisation—to make the next residual block coordinates. Treating all `Q,P` solely as generator changes risks producing the right ideal argument but the wrong recursive chart map.