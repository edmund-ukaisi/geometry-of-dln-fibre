# R1 per-node chart: clean-MP-factor vs squeeze — VERDICT (pp-hall, 2026-06-22, #129)

**Gating crux-design question.** A formaliser + a Codex read claimed the clean MP change-of-variables
factorisation `flatCore ∘ χ =ᶠ[𝓝 0] u·(ΣEᵢ² + G²)` (u a single bounded unit, G the E-free Schur core)
is NOT reachable at the R1 per-node (post-blow-up, hard-pivot) chart — the honest route is the two-sided
SQUEEZE `c₁·Φ ≤ F ≤ c₂·Φ` (as g128 found for L2). My own #127 result block-diagonalized the matrix via a
det-1 transvection pair `(L,R)` and read off a "clean decoupling" of the loss. Reconcile, exactly.

## VERDICT: SQUEEZE-NEEDED. The R1 per-node chart needs `c₁·Φ ≤ F ≤ c₂·Φ`, NOT a clean MP single-unit factor.

The crux + Codex read is **correct**; my #127 "clean decoupling" was a **matrix** identity misread as a
**loss-value** identity. The R1 per-node chart resolves by exactly the L2 mechanism: the structural
squeeze to `Φ = ΣEⱼ² + ‖S·A2red‖²` (clean form, G = the Schur core), `rlctAt_mono` both ways + unit-strip,
then smooth-block additivity on `Φ`. Two decorrelated exact-algebra legs converged (matrix-isometry +
completed-square derivation; direct squeeze test on two distinct node shapes). **Codex CLI was unavailable
in this sandbox** (`codex doctor`/`codex --version` hang on a cargo rebuild of `aisi-inspect-tools` with no
network); per policy I did not substitute Claude's answer — I ran a second independent exact leg instead.

## The reconciliation, exactly (the (3,3,3) reduced node)
Setup: `Â = [[1,p,q],[r,s,t],[u,v,w]]` (Â[0,0]=1 HARD), `A2` = 3×3 (entries `b0..b8`), loss `F = ‖Â·A2‖²`
(the actual `dlnLoss M 0` at this node). `g129-scripts/verify_summary.py` checks all six facts exact.

| # | Fact | exact result |
|---|------|--------------|
| 1 | `L=[[1,0,0],[−r,1,0],[−u,0,1]]`, `R=[[1,−p,−q],[0,1,0],[0,0,1]]` | det L = det R = **1** (transvections) |
| 2 | `L·Â·R = blockdiag[1, S]`, `S=D−ba=[[s−pr,t−qr],[v−pu,w−qu]]` | **0** — the **matrix** identity holds |
| 3 | `‖Â·A2‖² − ‖L·(Â·A2)‖²` | **≠ 0** — `L` is unipotent but **NOT orthogonal**; the transvection changes the loss **VALUE** |
| 4 | deg-3 part of `F` at 0 | `2b0(b3·p+b6·q)+2b1(b4·p+b7·q)+2b2(b5·p+b8·q)` ≠ 0 |
| 5 | `(F − Φ)│{E=0}`, `Φ = ΣEⱼ² + ‖S·A2red‖²`, `Eⱼ=(Â·A2)[0,j]` | **0** ⟹ `F − Φ ∈ ideal(E)` (structural squeeze) |
| 6 | best MP rename `bⱼ ↦ Eⱼ`: coeff of `Eⱼ²` | `1+r²+u²` (a **unit ≠ 1**) ⟹ **weighted**, not single-unit clean |

### The gap in #127 (FACT 2 vs FACT 3) — a matrix identity is not a value identity
`L·Â·R = blockdiag[1,S]` is a true **matrix** identity, and `g127_loss_identity.py` correctly shows
`L·(Â·A2) = [row0; S·A2red]`. But `L` is **not orthogonal** (det 1 ≠ orthogonal), so the Frobenius norm —
which **is** the loss — is **not** invariant: `‖Â·A2‖² ≠ ‖L·(Â·A2)‖²` (FACT 3, an explicit nonzero
polynomial). #127 block-diagonalized the **matrix** and re-grouped its entries; squaring/summing the
re-grouped entries is a **different number** than the loss. The "regular pivot row + ‖S·A2red‖²" reading is
the entrywise decomposition of `L·(Â·A2)`, **not** of `Â·A2`. So #127's "clean decoupling" was a
matrix-level statement misattributed to the loss function.

### Why no MP c-o-v reaches the clean single-unit form (FACT 4, FACT 6)
- **FACT 4:** `F` has a nonzero **degree-3** (odd) part coupling the regular block `(b0,b1,b2)` to the core
  vars. A literal `u·(ΣEᵢ²+G²)` with `G` bilinear is **even** (`G²` is deg-4) up to the unit `u(0)`; its
  lowest deviation from the rank-3 quadric `Σb_j²` is even. The odd deg-3 cross term is exactly g128's
  `2·E·h·g` coupling — it cannot be a single-unit-times-even-form.
- **FACT 6:** the natural MP c-o-v — rename the 3 regular pivot-row gens `Eⱼ := (Â·A2)[0,j]` to coordinates
  (`bⱼ ↦ Eⱼ`, Jacobian = Identity on `(b0,b1,b2)`, **det 1**, measure-preserving) — gives, after completing
  the square (no `EᵢEⱼ` cross terms; shift `β = −lin/(2a)` with denominator `a=1+r²+u²` a unit near 0, so a
  valid smooth MP shift): `F∘χ = a·(E0'²+E1'²+E2'²) + G'`. The weight `a = 1+r²+u²` multiplies **only** the
  E-squares (not the whole expression), and `G' ≠ ‖S·A2red‖²` exactly — it is only **squeeze-equivalent**
  (`g129-scripts/gp2.py`: `G'/‖S·A2red‖² ∈ [0.854,1]` at scale 0.3 → 1 as scale→0). So even the best MP
  c-o-v lands on a **weighted regular-squares + core** form, and still needs a squeeze (to strip `a` and to
  identify `G'` with the reduced core). It is **not** the clean `u·(ΣEᵢ²+G²)`.

### The sound route (FACT 5) — the L2 squeeze, verbatim, holds per-node
`Φ = ΣEⱼ² + ‖S·A2red‖²` (the **clean** form: 3 regular squares with coefficient 1 + the E-free Schur core).
`F − Φ = (lower rows of Â·A2)² − ‖S·A2red‖² ∈ ideal(E)` — verified exactly: `(F−Φ)│{E=0} = 0` (FACT 5).
Hence `F = ΣEⱼ² + (S·A2red + E·h)·(…)` is a bounded-linear-perturbation of `Φ`, so `c₁·Φ ≤ F ≤ c₂·Φ` near 0
(`g129-scripts/test_l2squeeze_on_r1.py`: `F/Φ → 1`, range `[0.737,1.469]` at 0.3 tightening to `[0.998,1.003]`
at 0.01). Same zero-set `{Â·A2 = 0} = {E=0, S·A2red=0} = {Φ=0}`. Then the **g128 build chain** transfers
verbatim:

    rlctAt(F)  = rlctAt(Φ)              -- squeeze c₁Φ≤F≤c₂Φ + rlctAt_mono ×2 + unit-strip (rlctAtOn_unit_invariant_aux)
               = nReg/2 + rlctAt(G²)    -- smooth-block additivity (Φ's 3 unit-coeff regular squares ⊥ core vars)
    G² = ‖S·A2red‖² = the smaller matrix-chain zero-core  →  recurse (ΣM' < ΣM)

No change of variables on the loss, no measure Jacobian, no clean-MP factor, no constant rank. The R1
per-node obligation is the **squeeze inequality + the structural fact `F − Φ ∈ ideal(E)`**, identical in form
to L2's g128 — not the `rlctAtOn_comp_homeomorph`/MP-transvection route #127 proposed.

## Uniformity (second node — (4,3,2)-shape, non-square Â)
`g129-scripts/test_node2.py`: reduced node `Â` 4×3 (hard pivot) × `A2` 3×2. Same result — `F/Φ` bounded
(`[0.689,1.564]` at 0.3 → `[0.991,1.006]` at 0.01) and `(F−Φ)│{E=0} = 0` (structural squeeze). The squeeze
mechanism is generic across reduced-node shapes (square and non-square), so the per-node R1 obligation is
uniformly the squeeze, not a shape-dependent clean factor.

## Net for `schur_straighten` / the crux
- **Corrected obligation:** the R1 per-node chart-existence obligation is the **squeeze** form
  `∃ c₁,c₂>0, Φ: c₁·Φ ≤ flatCore ≤ c₂·Φ near 0` with `Φ = (nReg unit-coeff regular squares) + ‖S·A2red‖²`,
  resting on the **exact structural fact** `flatCore − Φ ∈ ideal(E)` (the regular gens), **NOT**
  `flatCore ∘ χ =ᶠ u·(ΣEᵢ²+G²)` and **NOT** the MP-transvection `rlctAtOn_comp_homeomorph` route.
- **Consequence for the prior tasks:** task "(3) MP-of-transvection (HEAVY) — the det-1 Schur straighten as
  a `MeasurePreserving` homeomorphism, the χ that `schur_straighten_of_data`'s `hfactor` consumes" is
  **proving the wrong interface**. The transvection IS det-1, but the loss is not invariant under it
  (FACT 3); `schur_straighten_exists` should consume the **squeeze + structural-ideal** fact, reusing the
  GREEN g128 L2 tooling (`rlctAt_mono`, `rlctAtOn_unit_invariant_aux`, smooth-block additivity), NOT
  `rlctAtOn_comp_homeomorph`. The mechanism is the SAME as L2 — no new machinery.
- **What #127 keeps:** the blow-up→hard-pivot interface, the Schur complement `S = D − ba` as the reduced
  core, and the uniform recursion `ΣM' < ΣM` are all correct and survive. Only the "clean MP decoupling of
  the loss VALUE" claim is retracted — it is the squeeze, as for L2.

## Most likely thing to break this
The squeeze constants `c₁,c₂` and the smooth-block additivity both rest on `Φ`'s regular squares having
**unit (coefficient-1) leading parts disjoint in leading vars from the core vars**. FACT 6 shows the MP
rename introduces a unit weight `a=1+r²+u²` on the E-squares; the squeeze route avoids this by comparing `F`
to the **coefficient-1** `Φ` directly (no rename), so it is clean — but the formaliser must use the squeeze-
to-`Φ` route (compare at the same point), not the completed-square route (which carries the weight `a` and
needs a second squeeze). If `smoothBlockND_rlct` were instead fed `a·ΣE'² + G'`, it would need `a` stripped
as a unit first — extra work the direct squeeze avoids.

## Next construction to settle the open part
The structural fact `flatCore − Φ ∈ ideal(E)` at a **general** reduced node (arbitrary `m×k` hard-pivot Â)
should be stated and certified once (it follows from `lower rows of Â·A2 = b·E + S·A2red` — the same Schur
identity as #127, but now read as the **ideal-membership** that powers the squeeze, not a value identity).
That, plus the g128 build chain, is the complete corrected `schur_straighten_exists` interface. The
decorrelation gap to close: re-run the Codex consult when the CLI is reachable (the prompt is at
`g129-scripts/`-adjacent `/tmp/r1reconcile/codex-prompt.md`; it hung here on a cargo rebuild, not auth).

Builds on #127 (the matrix block-diag — kept), #128 (the L2 squeeze — now shown to be the per-node R1 route
too), #125/#126 (outer/per-node distinct). Scripts: `g129-scripts/` (8 exact scripts).
