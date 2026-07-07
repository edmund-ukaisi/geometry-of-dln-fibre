# De-risking probe — the R-BLOWUP recursive loss identity on the coupled corank-2 case

**Seat:** pen-and-paper (the A-vs-B hinge test I registered as "cheapest thing to test before committing
the multi-tide build"; exact algebra + decorrelated Codex, leaning withheld). **Question:** does the
general-`L` single-radial blow-up chart lemma's RECURSIVE LOSS IDENTITY (`transformed loss → reduced-chain
× explicit monomial radial factors`) hold on the smallest genuinely-COUPLED corank-2 case via SEQUENTIAL
single-radial-per-block charts — or does the shared deeper product force a SIMULTANEOUS resolution a finite
explicit chart cover cannot express?

---

## VERDICT — SEQUENTIAL reaches normal crossing. The identity HOLDS. GREEN-LIGHT the multi-tide build.

**The `(2,2,2)` `Case111/Case222` template GENERALISES to the coupled corank-2 case by sequential
single-radial charts; NO simultaneous resolution is required. The A verdict (R1-UPPER = bounded labor via
R-BLOWUP) does NOT flip to B.**

The mechanism (verified symbolically, exact; independently corroborated by decorrelated Codex xhigh):

1. **Single-radial factors cleanly.** For a corank-2 block `Δ` (2×2) coupled to any downstream product `Z`,
   `‖Δ·Z‖² = u²·‖Δ'·Z‖²` (one radial `u`, `Δ=u·Δ'`), Jacobian `u^{4−1}=u³`. Exact, `Z`-agnostic.
2. **The pivot-clear is `Z`-INDEPENDENT.** Unit-triangular (det-1) transforms `L=[[1,0],[−b,1]]` (rows),
   `R=[[1,−a],[0,1]]` (cols) — depending ONLY on `Δ'`, NOT on `Z` — reduce `Δ'` to `diag(1, δ')`,
   `δ'=d−ab`. The reduced loss `= ‖pivot row‖²` (a MORSE direction) `+ δ'²·‖(downstream row)‖²` (a
   corank-1 coupled residual). The transforms absorb into the ADJACENT downstream factor
   (`C² ↦ Q⁻¹C²`), leaving the DEEPER shared factor `C³` UNTOUCHED (product associativity — exact, not
   merely RLCT-preserving).
3. **The corank-2 step REDUCES to corank-1 coupling.** `corank-2 block → [one radial u] → u²·(Morse pivot
   + δ'²·‖(downstream row)·(rest)‖²)`. The residual `δ'²·‖(downstream row)·(rest)‖²` is the SAME object as
   the corank-1 `(3,3,3,3)`-type recursion — already closed by the decorated induction. So corank-2 and
   `L≥3` coupling are INDEPENDENT novelties that COMPOSE; corank-2 adds no obstruction beyond corank-1.
4. **The re-coupling concern is VOID — the resolution is genuinely sequential.** After layer-1's
   resolution the introduced radials (`u`, `δ'`) and layer-1 chart vars (`a,b,d`) appear ONLY as an
   OVERALL SCALAR MONOMIAL PREFACTOR `u²δ'²…` on the active residual; the deeper term is `u`/`a,b,d`-FREE
   (verified). A later downstream chart map `φ` acts on the downstream block variables only, so
   `φ*(u²δ'²·G) = u²δ'²·φ*(G)` — each later radial simply APPENDS to the product; no later blow-up centre
   compares `u` with a downstream radial or `δ'` with a deeper rank-drop parameter. Sharing `C³` means the
   same downstream radial appears in several terminal monomials (`b_i = u v…`, `u δ' v…`) — still normal
   crossing `∑ b_i²`. (Codex: "old exceptional coordinates are passive parameters; each recursive
   downstream resolution is pulled back under a monomial prefix" — a *relative* resolution invariant.)

## Exact-algebra DATA (mine — `sjj_chart_probe.py`, `sjj_sequential.py`, `sjj_find_coupled_corank2.py`)

- **Test case (smallest genuinely-coupled corank-2):** `M=(3,3,3,4)`, binding branch `T=(1,0,0)`,
  per-layer charges `[4,3,0]`, `Σ = 7 = Mval = minAdm`, `½minAdm = 3.5`. Layer-1 corank block `2×2`
  (corank 2); layer-2 charge `3 > 0` shares `C³` with layer-1 ⟹ genuinely coupled (not the decoupled
  `L=2` `(3,3,4)`). (The absolute smallest, `(2,2,3,3)` `T=(0,0,0)`, has all charge at layer 1 — coupling
  charge 0 — so `(3,3,3,4)` is the smallest with the coupling *biting*.)
- **Crux step (`sjj_chart_probe.py`, sympy exact):** `‖Δ·Z‖²/u²` is `u`-free (single radial factors);
  `L·Δ' = [[1,a],[0,d−ab]]`, `(L·Δ')·R = diag(1, d−ab)`, `det L = det R = 1`, `L,R` functions of `Δ'`
  ONLY; reduced loss `− (‖row1‖² + δ'²‖row2‖²) = 0`.
- **Sequential independence (`sjj_sequential.py`, sympy exact):** the deeper term is `u`-free and
  `a,b,d`-free ⟹ earlier radials factor out as an overall scalar; the deeper resolution is independent.
- **Accounting reaches `½minAdm`:** charges `[4,3,0] → 7 = minAdm` (and the general fact — every terminal
  branch exponent `= Mval ≥ minAdm`, threshold monotonicity `0/171` — is in `outer-construction-cert.md`).

*Instrument caveat:* the symbolic checks establish the STRUCTURE of one corank-2 → corank-1 reduction step
and the monomial-prefactor independence exactly. The full multi-layer monomialisation to `∑ b_i²` for the
whole `(3,3,3,4)` loss was not run end-to-end symbolically (19-var product); the verdict rests on (i) the
exact crux + independence steps, (ii) the reduction of corank-2 to the already-closed corank-1 recursion,
(iii) the certified value, and (iv) decorrelated Codex agreement.

## Codex INTERPRETATION (decorrelated, xhigh, leaning withheld — `codex/chartprobe-{prompt,answer}.md`)

**VERDICT: sequential-reaches-normal-crossing.** "The re-coupling concern is void because the already
introduced radials are only external monomial prefactors on the active residual … `φ*(u²δ'²·G_downstream)
= u²δ'²·φ*(G_downstream)` … every later radial simply appends to the existing product … the
unit-triangular row/column reductions are chosen from the normalized active block and do not use `Z`,
`u`, `δ'` … a relative resolution invariant: old exceptional coordinates are passive parameters."
Hardest bounded formalisation step (matches mine): the **relative corank-step invariant** — preserving all
existing monomial prefixes under the downstream coordinate changes without dividing by them.

---

## Formaliser-ready general-`L` chart construction (the green-lit spec)

The recursive loss identity, one `(S,J)` step, at general widths:

**INPUT (invariant):** loss `= (monomial prefactor ∏ b_i²) · ‖ [E_J | D_J] · ∏_{s>S} C^{(s)} ‖²`, `D_J`
the current `(M(S)−J)×(M^{(S+1)}−J)` residual block coupled to the downstream product `Z = ∏_{s>S}C`.

**STEP (single-radial Case-2 / partial Case-1):**
1. **Finite pivot-chart cover** of the residual block's rank strata → banked
   `pivotChartCover_matBox_le_sum` / `pivotLocus_eq_iUnion`.
2. **Single radial blow-up** of the whole current block `D_J = u·D_J'` (top-left normalised); the loss
   picks up `u²` (clean factor) and the divisor `u` gets Jacobian power = block codim (charge) → banked
   radial engine `radial_morse_residual_power_le` (the `p×q`→`Fin(pq)` `eMatFlat` radial).
3. **`Z`-independent unit reduction** `D_J' → [[1,O],[O,D_{J+1}]]` via det-1 row/col transforms
   (functions of `D_J'` only), absorbed into the adjacent factor `C^{(S+1)}` (gauge, exact); deeper
   `C^{(s)}` (`s>S+1`) untouched. Loss `→ ‖pivot rows‖²` (Morse) `+ ‖D_{J+1}·(reduced downstream)‖²`.
   [The `(2,2,2)` instance is banked `Case111`/`Case222`; generalise the block-elimination to general widths.]
4. **Advance `(S,J)`**, appending `u` to the running monomial prefactor `b_i`. Recurse (strictly-decreasing
   `(S,J)` / arity).

**BASE:** `L=1` free-matrix Morse (banked `sjBase1_freeMatrix`) + the terminal monomial endpoint
`∑ b_i²` closed by banked `monomialIntegrand_integrable_of_lt` / `monomialThreshold_ge_of_mult`.

**EXPONENT:** terminal-divisor exponent `= Mval(branch) ≥ minAdm` (banked `minAdmRec_eq_minAdm`,
`sjChargeUpdate_accum`, `sjSubordination`; threshold monotonicity `0/171`), so `c' < ½minAdm ⟹ c' <
Mval/2` on every divisor ⟹ the monomial endpoint converges.

**The single hardest (bounded) sub-brick** (mine = Codex): the **relative corank-step invariant** —
formalise step 3 (the `Z`-independent unit block-elimination + adjacent-factor absorption) uniformly at
general widths, proving the existing monomial prefactors are PRESERVED (never divided by), across the
finite pivot-chart cover. This is where the `(2,2,2)` `Case111/Case222` template must be lifted to
opaque widths. Large chart algebra, NOT resolution-of-singularities.

## Closing

- **Firmest.** The recursive loss identity holds on the coupled corank-2 case via sequential single-radial
  charts: single-radial `u²` factors cleanly, the pivot-clear is `Z`-independent (deeper shared factor
  untouched), corank-2 reduces to the already-closed corank-1 coupling, and earlier radials are passive
  monomial prefactors so the deeper resolution is independent. Value reaches `½minAdm`. Decorrelated Codex
  identical (`relative resolution invariant`). **Verdict A confirmed — green-light the multi-tide build.**
- **The de-risking outcome:** the risk I registered (simultaneous resolution needed) is RETIRED — the two
  novelties (corank-≥2, `L≥3` coupling) are independent and compose sequentially.
- **What to hand the formaliser:** the general-`L` chart construction above; the one hardest brick is the
  relative corank-step invariant (bounded chart algebra lifting `Case111/Case222` to general widths).
