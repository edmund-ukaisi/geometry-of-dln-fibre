# C5 e=0 sub-branch — the cascade does NOT pin e≠0, but e=0 is a deeper lex-dropping node (pp-r1realize #98) (pp-hall, 2026-06-23)

**pp-r1realize's residual on the cascade↔C5 alignment:** does my g219 cascade guarantee a nonzero
downstream coupling `e` at the C5 partial-drop (so their Fubini-shear `loss = ‖e‖²δ'² ⊞ survivor`, which
needs `‖e‖² ≠ 0`, applies), or does the `e = 0` sub-branch need separate handling (their #98 lex-termination
residual)? **Honest answer (against the hoped-for "cascade pins e≠0"): the cascade does NOT pin `e ≠ 0` —
its center has `e = 0`. BUT the `e = 0` sub-branch is a DEEPER lex-dropping node, NOT a stall.**

## The cascade center has e = 0 (verified g222)
At `t = (3,3,2,2,2,0)`, the cascade `C_s = diag(1^{t_{s+1}}, 0)`: the C5 node is `s=2` (`3→2`), complement =
the dropped 3rd coordinate. `e =` the downstream `C_3 C_4 C_5` applied to the complement direction. At the
cascade center, `C_3 C_4 C_5 = diag(1,1)·diag(1,1)·diag(0,0) = 0` (since `t_5 = 0` kills everything). So
`e = 0` AT THE CENTER. pp-r1realize's `‖e‖²δ'²` shear needs `‖e‖² ≠ 0` — which FAILS at the center. **The
cascade does NOT pin `e ≠ 0`** (the center — the deepest — sits ON the `e = 0` locus, the most-degenerate
stratum).

## But e=0 is a DEEPER lex-dropping node, not a stall (the #98 answer, g223)
The C5 chart cover splits:
- **`e ≠ 0` charts:** the complement direction survives downstream until some later layer kills it. The
  Fubini-shear `δ' = δ + (G·q·e)/‖e‖²` applies, `loss = ‖e‖²δ'²` (regular ½) `⊞` survivor reduced chain —
  pp-r1realize's form, the rank-1 complement a smooth Morse ½.
- **`e = 0` sub-locus:** the complement's downstream vanishes immediately ⟹ the complement is a FURTHER
  rank-defect to resolve — a DEEPER C-node on the complement sub-chain. **It lex-DROPS:** the complement is
  a rank-`(t_{s-1}−t_s)` strict sub-block, `ΣM_complement < ΣM_parent`, so `lex(L, ΣM, ncDefect)` decreases
  on the `e = 0` sub-branch. The recursion on it terminates by the same lex measure. NOT a stall.

So the C5 atlas cover = `{e ≠ 0 charts: Fubini-shear, regular ½}` ∪ `{e = 0 sub-locus: recurse on the
complement, lex-drops}`. **Lex-termination holds on BOTH branches** — pp-r1realize's #98 closes: `e = 0` is a
deeper node, not a stall. (The cascade center is the deepest = the `e = 0` deepest stratum, which is why the
recursion must continue there — the deepest IS the most-degenerate point.)

## For the Lean (#98 + the C5 cell-cover)
The C5 node's cells must include BOTH the `e ≠ 0` charts (where the shear gives the regular ½) AND the
`e = 0` deeper-recursion node (the complement sub-chain). The lex measure drops on both: the `e ≠ 0` charts
resolve the node (the complement becomes a regular ½, `ΣM` drops via the survivor descent); the `e = 0`
sub-locus recurses on the complement (`ΣM_complement < ΣM_parent`). So `routeStep`'s C5 branch has cells
covering `e ≠ 0` (the principal Fubini-shear charts) + the `e = 0` sub-node (a recursion on the complement),
both lex-decreasing — the no-stall guard for #98.

## Decorrelation
pp-hall exact algebra (g222: the cascade center has `e = 0` for `t=(3,3,2,2,2,0)`, the downstream
`C_3 C_4 C_5 = 0`; g223: the `e = 0` sub-branch lex-drops on the complement sub-chain). Cross-checked with
pp-r1realize's C5 hnode cert (#97, the Fubini-shear) — CONVERGENT on the `e ≠ 0` branch; the `e = 0`
residual (their #98) resolved here as a deeper lex-dropping node. Codex down env-wide — exact-algebra +
the lex-measure structural argument carries it. Builds on g219 (the cascade), g194 (the C5 = C2-survivor ⊕
C1-complement), pp-r1realize's #97 (the Fubini-shear), the lex(L, ΣM, ncDefect) termination (g138 §3).
