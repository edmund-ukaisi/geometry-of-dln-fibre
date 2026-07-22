# E-lane arc — Object E / P6.2 (the θ-count, combinatorial half)

First-hand account by the integration owner (seat-E), banked at Tier-3 close for the close synthesis.
Object-level: what was built, the design calls and their reasons, what held, what was deferred.

## The ladder

1. **P6.1 — the band count (name-neutral).** `bandCount ℓ a = a(ℓ−a)+1` as an abstract banded-interval
   count (`Core.Aoyagi.OrderCount`), with `chainHeight_boxPart` (`Core.Aoyagi.OrderChain`) proving the
   box-partition lattice `BoxPart ℓ a` has `chainHeight = a(ℓ−a)+1`. Both name-neutral.
2. **P6.2 Tier 2 — the θ-attachment (value identity).** `OrderBinding.lean` attaches the closed-form
   value: `thetaCount d r := bandCount (ell d r) (residueA d r).toNat`, and
   `thetaCount_eq_aoyagiTheta : thetaCount = aoyagiTheta` — an unconditional identity between two
   formulas (both `a(ℓ−a)+1`), instantiated at the certified Def-3 selectors `ell`/`residueA`.
3. **The #42 certificate.** A pen-and-paper certificate (thread-42) adjudicated that the genuine
   binding-minimiser poset is order-isomorphic to `BoxPart(ℓ,a)` — verified on 993 cores + a trap
   kill-set. This is the *adjudication* record; the Lean modules are the *construction* record. The two
   constructions (the cert's Lemma-4-step recipe and Codex's adjacent-swap map) are different and their
   equivalence is not needed — any valid order-iso discharges the `Nonempty` headline.
4. **P6.2 Tier 3 — the realization iso (this lane).** Build, in Lean, `bindingSet M ≃o BoxPart(ℓ,a)`
   for the real binding poset, hence `chainHeight(bindingSet M) = a(ℓ−a)+1`, hence the *faithful* count.
5. **Integration + closure.** Three tracks → one terminal assembly → wired + AxCheck-registered +
   kernel-gated green.

## The three-track build and the resourcing shape

The Tier-3 iso factored as a composite of three order-isos (`.trans`): (a)+(b) one adjacent
width-swap; (c) sort to ascending widths; the sorted-case box iso. The lane started as one seat
(seat-E) and split into three tracks once the factors passed the handoff-profile test — each factor is
a self-contained `Nonempty (≃o)` over a frozen statement, with a clean interface (the shared floor) and
no shared mutable proof state:

- **seat-Ecore** — the sorted-box factor `SortedBox.sortedBox_orderIso` (`OrderRealizeSortedBox.lean`),
  stated over a general monotone-positive `D` via the primitives. Upstream: imports only
  foundations/ClosedForm/QIP, never `OrderRealize`.
- **seat-Eswap** — the swap factor `swapBinding_orderIso_impl` (`OrderRealizeSwap.lean`), the frozen
  `swapBinding_orderIso` statement verbatim. Imports the `OrderRealize` floor; reuses `bindingSet`,
  `swapWidths`, `swapR`, `swapProfile` + the four proved bricks as-is (none re-defined).
- **seat-E** — owner: the floor, the (c) transport, integration, and the capstone.

Zero rework across the split: both cores landed on the frozen statements and every wiring bridge held
on the first attempt. The interface that made this hold was the `Nonempty (≃o)` discipline (below).

## Design calls, and why

### The `Nonempty (≃o)` interface

Each factor is stated as `Nonempty (subtypeA ≃o subtypeB)`, not as raw `≃o` data. The order-iso is
data (an explicit encoding); stating the *existence* is all the `chainHeight` transport consumes
(`chainHeight_eq_of_orderIso` transports strict `chainHeight` across a subtype-`≃o`). This kept each
track's interface a `Prop` with a frozen signature, decoupling the three constructions — a seat could
build any valid iso without coordinating the exact encoding with the others.

### The Q4 collapse (the domain is `Adm`, not a looser lattice)

An earlier framing filtered `Adm` by a run-min bound (cap `min(M⁰,M¹)` everywhere). The collapse:
`Adm` already satisfies the run-min bound (`Adm_le_runMin`), so the filter is vacuous
(`adm_runMin_filter_eq : (Adm M).filter (· ≤ runMin) = Adm M`). `bindingSet` is therefore
`{T ∈ Adm M : Mval M T = minAdm}` directly. The genuinely-loose object (the over-loose lattice capping
`min(M⁰,M¹)` everywhere) is a **negative certificate**, not the domain: its `minAdm` collapses to `≤ 0`
at e.g. `[4,4,1,1]→0`, `[5,5,1,1]→−1`, destroying the `a(ℓ−a)+1` count. That negative certificate is
recorded in `adm_runMin_filter_eq`'s docstring. Taste line held throughout (elder): every poset-iso and
count statement is over `bindingSet`, never plain `Adm` — a statement phrased over `Adm` would be false
(admissibility preservation under a swap needs minimality; the (2,0,0,2,1) counterexample is why (a)+(b)
are bundled rather than an atomic `swapR`-in-`X` monotonicity, which is false).

### The import cycle → terminal assembly (not the defs-split)

`OrderRealizeSwap` imports `OrderRealize` (for the `swapR`/`swapProfile` floor), so `OrderRealize`
cannot import `OrderRealizeSwap` to fill the swap sorry — a cycle. Two resolutions were on the table:

- **defs-split** (controller's recommendation): extract the shared defs into an upstream
  `OrderRealizeDefs`, re-point `OrderRealizeSwap` to import only it, and make `OrderRealize` the pure
  assembly.
- **terminal assembly** (chosen): `OrderRealize` stays the floor + the (upstream-safe) sorted-box
  factor; a new terminal `OrderRealizeAssembly` imports `OrderRealize` + `OrderRealizeSwap` and holds
  the swap-dependent cluster (swap discharge, transport, headline, count).

I chose the terminal route because it touches **neither** core's delivered file — `OrderRealizeSwap`
keeps importing `OrderRealize` unchanged, `OrderRealizeSortedBox` is untouched, and the only code that
moves is the swap-dependent cluster I own. The defs-split would re-point `OrderRealizeSwap`'s import
(touching a landed seat file) and move the shared defs. Both kill the cycle and both keep the headline
chain in one home; the terminal route does it with strictly less disturbance to landed work. The
sorted-box factor stays in `OrderRealize` (its module is upstream, so no cycle) rather than moving to
the terminal, keeping `OrderRealize` a genuine floor + one factor.

Final module DAG:

    OrderRealizeSortedBox   (Ecore; foundations only)
    OrderRealize            (floor + sorted-box factor)   ← imports SortedBox
    OrderRealizeSwap        (Eswap)                        ← imports OrderRealize
    OrderRealizeAssembly    (terminal: transport+headline+count+capstone)  ← imports both + OrderBinding

## The rfl-bridge verifications (what held, why it mattered)

The one open fidelity item at wiring was whether the sorted-box factor's codomain/domain at
`D = sortedWidths M` match the scaffold's `(ell M 0, (residueA M 0).toNat)` and `bindingSet
(sortedWidths M)`. All three bridges hold by pure `rfl` (verified in isolation before wiring):

- `bindingSet (sortedWidths M)` unfolds to the primitive set `{T ∈ Adm D ∧ Mval D T = inf' …}` — defeq.
- `ell M 0 = qipM (sortedWidths M)` — defeq (`ell d r := qipM (shiftedSorted d r)`,
  `sortedWidths M := shiftedSorted M 0`).
- `residueA M 0 = SortedBox.sbResidueA (sortedWidths M)` — the flagged one; holds by `rfl` because
  `sbCeil`/`sbResidueA` were built to match `ClosedForm.{ceilingM,residueA} · 0`'s formula, and
  `qipS`/`qipM (sortedWidths M)` are defeq to `activeSum`/`ell M 0`.

No bridge lemma with content was needed — the selectors line up definitionally. This mattered: a
non-`rfl` bridge that needed actual content would have been a statement-fidelity gap (the stop-condition
the controller flagged), not plumbing.

## The faithful-count capstone (the lane's precision story)

Tier 2's `thetaCount_eq_aoyagiTheta` is a value identity: two formulas (`bandCount` and `aoyagiTheta`)
agree, both `a(ℓ−a)+1`. That alone does not say the count is the chain-height of anything — it is an
arithmetic coincidence of formulas until tied to an object. The capstone

    bindingSet_chainHeight_eq_thetaCount :
      (bindingSet M).chainHeight (· < ·) = (thetaCount M 0 : ℕ∞)

composes `bindingSet_chainHeight` (the realization iso's count) with the Tier-2 identity to land that
value on the **actual binding poset** — the count is faithful to the object, not just a numerically
agreeing formula. This is the E-lane payoff in honest form (name = content: the theorem says exactly
`chainHeight(bindingSet M) = thetaCount M 0` and proves exactly that). It is a registered,
kernel-gated theorem of the library — no citation.

## Gates and closure

- Force-elaborated `#print axioms = [propext, Classical.choice, Quot.sound]` on `swapBinding_orderIso`,
  `bindingSet_transport_sorted`, `bindingSet_orderIso_boxPart`, `bindingSet_chainHeight`,
  `bindingSet_chainHeight_eq_thetaCount`.
- `scripts/sorries`: zero across the four lane files.
- Clash: the green `OrderRealizeAssembly` build loads all four lane modules + `OrderBinding` into one
  environment (a combined-load test of the family), plus a grep of every lane name and Eswap's
  enumerated list against the rest of the tree — zero collision. The wired full build (controller) was
  green at 8995 jobs, cordon OK, census +0.
- Commits: sorted-box wire `0040c2731`, integrate `3196e7e6e`, capstone `230909c60`; merged to the
  expedition branch `dc257854e`; closed `c9a4003fe`. Cores: Ecore `d0e24afc7`, Eswap `abe9e8e55`.
- Fidelity review (rev-Elane): SURVIVED across all seven items; three non-blocking findings disposed.

## Residue ledger

- **The ρ-seam is deferred (monument-class).** The interpretive identification of `thetaCount` with
  Aoyagi's analytic RLCT/zeta-pole multiplicity `ρ` (the number of top-dimensional components of the
  exceptional fibre) is NOT claimed in any name or docstring — it needs meromorphic continuation Mathlib
  lacks. Recorded in `OrderBinding.lean`'s module docstring. The lane proves the combinatorial count of
  the binding poset, not the analytic pole order.
- **The `ell`/`residueA = qipM/qip surrogate` caveat** is carried at both aggregator wiring sites (`ell`
  yields Aoyagi's λ value but need not equal her `Card(𝓜)−1` pointwise; see `ClosedForm.ell`'s
  docstring).
- **Hygiene unit (post-monument):** the Q3 `Adm`/`Mval`/`bindingSet` cluster migration into `Core`
  (blocked now only by the import direction — it consumes `DLN`-side `Adm`/`Mval`; migrates with the
  M4/M9 upstreaming unit) + the lint nits (long-line reflows in `OrderRealizeSortedBox`). Non-blocking.
