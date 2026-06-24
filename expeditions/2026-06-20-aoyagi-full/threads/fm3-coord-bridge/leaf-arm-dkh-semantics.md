# RouteMTree (d,k,h) accumulation semantics — CORRECTED to the committed decls (fm3)

The per-leaf `MonoData (d,k,h)` for the value fold, as ACTUALLY committed (`RouteMState.lean` +
`RouteMRecursion.lean` + `Case222RouteStep.lean`). **CORRECTION (fm3, against the decls):** `MonoData.d`
is the **MONOMIAL-AXIS COUNT** (the length of the accumulated divisor list), NOT the geometric flat ambient.
The earlier draft of this note said `d = flatDim M` — that wording was WRONG (it would assert `flatDim`-many
spectator axes the leaf does not carry). The fix below matches the committed `appendDivisor`/`foldDivisors`.

## `MonoData.d` = monomial-axis count (the divisor-list length)

- `MonoData = ⟨d : ℕ, k h : Fin d → ℕ⟩`. `d` is the number of monomial axes, NOT the ambient dimension.
- `MonoData.appendDivisor md c = ⟨md.d + 1, Fin.snoc md.k 1, Fin.snoc md.h (c-1)⟩` — each branch node ADDS
  ONE axis (`d ↦ d+1`), with `(k,h) = (1, c-1)` (the codim-`c` pivot divisor). `Fin.snoc` extends `k`/`h`
  over the new `Fin (d+1)`.
- `MonoData.foldDivisors cs = cs.foldr appendDivisor (leafMonoData 0)` — a leaf's datum is the fold over its
  path's codim-list `cs`, so `d = cs.length` (the number of branch nodes on the path), `k ≡ 1`, `h = c-1`.
- `monomialThreshold (foldDivisors cs) = ratioMinFold cs = ⨅ over cs of (c/2)` (`monomialThreshold_foldDivisors`).

## The leaf datum = `leafMonoData 0` (d=0, ⊤ terminator)

- `leafMonoData 0 = ⟨0, fun _ => 0, fun _ => 0⟩` — the EMPTY monomial (zero axes). `monomialThreshold = ⊤`
  for ANY `d` (the empty `⨅` / all-spectator), `leafMonoData_threshold`.
- `routeStep`'s leaf arm = `.leaf (leafMonoData 0)` (d=0). It appends NOTHING; the `⊤` is the non-binding
  path-TERMINATOR (the value rides the ACCUMULATED branch-divisors above it, not the terminal's own d). A
  `d := flatDim M` leaf would be WRONG (asserting spectator axes the leaf doesn't carry); `d=0` is correct.
- `routeStep`'s branch arm appends `appendDivisor (codim c)` per branch node (the recursion in `routeAtlas`:
  `data x = (child.data x.2).appendDivisor (codim x.1)`).

## Anchor (the committed proof): (2,2,2) → 3/2

`Case222RouteStep.case222_routeStep_value = 3/2` PROVES this: the achiever path's `codimsOf222 = [4, 3]`
(the 2 BRANCH nodes' root-anchored `Mval`: `Mval((2,2,2),(0,0))=4`, `Mval((2,2,2),(1,0))=3=minAdm`); the
TERMINAL `(0,0,2)` is the `⊤` leaf appending `[]`. `foldDivisors [4,3]` via `foldFamily_iInf_eq_half_minAdm`
→ `min(4/2, 3/2) = 3/2 = ½·minAdm`. The `⊤` leaf does NOT bind the `⨅`; the value rides `[4,3]`.

## flatDim is the SEPARATE #104 descent carrier (never `MonoData.d`)

The geometric chart ambient `Fin (flatDim M)` (the lintegral's domain in the #104 cover/descent) is carried
SEPARATELY (the `NodeChartFamily` / the geometric chart / `routeMAmbient`), NEVER read off `MonoData.d`.
`MonoData.d` is the abstract monomial-axis count for the VALUE fold (`foldFamily_iInf`); `flatDim` is the
DESCENT's coordinate ambient. They are different objects — conflating them was the note's original error.

## Why the leaf is the ⊤ terminator, not an additive `nReg/2`

The leaf carries NO binding axis (`leafMonoData 0`, `⊤`); the `½·minAdm` value comes ENTIRELY from the
accumulated branch pivot-divisors `(1, c-1)` via `monomialThreshold = ⨅ axisRatio`. The `nReg/2`
(degenerate-ROOT direct-Morse, `#70`) is OUTSIDE this fold (L2's regular shift / the degenerate-root headline
case), a #104 descent concern — never a per-leaf value. (Pinned in `foldFamily_iInf_eq_half_minAdm`'s docstring.)
