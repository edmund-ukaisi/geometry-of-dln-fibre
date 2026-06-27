<task>
Lean 4 Mathlib v4.29. Design the cleanest proof of a WITNESS for an opaque-width matrix telescope.

GOAL: `∃ w : Fin N → ℝ, achieverUfun M hL hN w ≠ 0` (for `2 ≤ L`; L=1 handled separately).
Banked reductions: `achieverUfun w = ∑_{i,j} (Hmat0 i j)²` where `Hmat0 := (chainOfMt (w p) M (tach M)
(genBlkFlatStruct M (tach M) ha w) hle).toChain.Hmat 0`. So it suffices to find `w` and indices `(i,j)`
with `Hmat0 i j ≠ 0`, then `achieverUfun w ≥ (Hmat0 i j)² > 0`.

THE CHAIN (all banked, over a CommRing; here ℝ): `Hmat` is a downward telescope
`Hmat s = B_s · Hmat(s+1) + E_s · suffix(s+1)`, `Hmat L = R`, `suffix s = A_s···A_{L-1}`, `suffix L = 1`,
with (for `chainOfMt … (genBlkFlatStruct … w) …`):
- `B_s = Bmat_s` (the kept block; `Bmat_0 = reindex I` at the identity boundary, `Bmat_{k+1} =
  bmatStack [K_k ; X_k·K_k]` reading flat coords),
- `E_s = Rmat_s · A_s`, `Rmat_0 = 0`, `Rmat_{k+1} = rmatPad(E_k bottom-right)`,
- `R = Rfin_L = 0` (DEAD leaf),
- `A_s = chainA(N_s)(W_s)(C_{s+1})`: kept rows `= C_{s+1} − N_s·W_s`, lift rows `= W_s`,
- `C_{s+1} = Bmat_{s+1}·chainQ(N_{s+1}) + (w p)·Rmat_{s+1}` (interior), `C_L = (w p)·Rfin_L = 0`.

SYMPY-VALIDATED WITNESS (L=2 (3,3,4) and L=3 (3,3,3,3)): set `w` so that all `K_k = I`, all `X_k = 0`,
all `N_k = 0`, all `W_k = 0` EXCEPT at the DEEPEST interior boundary `k* = L−2` (chart slot, GenBlk
boundary `s = L−1`): there `E_{k*}` top-left `= 1` and `W_{k*}` first entry `= 1`. Then `Hmat0` has exactly
one nonzero entry `= 1` (so `‖Hmat0‖² = 1`). Mechanism: the non-`u` parts telescope to `Bmat·C = 0` via
`chainQ·chainA = C` (the `hQA` identity) and `C_L = 0`; the ONE surviving term is `Rmat_{L-1}·A_{L-1}` =
`E·(W lift rows)` propagated up through the identity `Bmat`s and the `A_s = C_{s+1}` (since N=W=0 ⟹
`A_s` kept = `C_{s+1}`, lift = 0).

THE PROBLEM: proving `Hmat0 i j = 1` (one entry) at this `w` over OPAQUE widths `Text M (tach M) k` /
`Wext M k`. The dependent-`Fin`-width cast kernel (lean/CLAUDE.md: `have`+`exact` at explicit `⟨_,by decide⟩`
indices) handles CONCRETE nodes, but here widths are opaque (`L`-parametric).

QUESTIONS:
Q1. The cleanest proof SHAPE for `Hmat0 i j = 1` over opaque widths. Options:
  (a) Evaluate `Hmat0` directly via the `Hmat_succ`/`suffix_succ` recursion at `w`, showing most terms
      vanish (B/E/suffix entries 0) — a downward induction on the boundary, carrying "Hmat s = a specific
      e-vector" through the kept-identity `Bmat`s. RISK: the dependent-width row/col indices of the
      surviving entry shift per boundary.
  (b) Use the banked `prod = u·Hmat0` (the rate identity) + evaluate the LAYER PRODUCT `A_0···A_{L-1}` at
      `w` instead — at `w`, `A_s` (N=W=0) = `[C_{s+1} ; 0]` (kept = C_{s+1}, lift = 0), so the product
      telescopes; the deepest `A_{L-1}` carries the lift-W. Is the layer product easier than `Hmat`?
  (c) A MUCH WEAKER witness that still gives `≠ 0`: instead of `Hmat0 i j = 1` exactly, show `Hmat0 ≠ 0`
      by showing ONE entry is a NONZERO POLYNOMIAL in `w` (not necessarily = 1) — e.g. leave the deepest E
      and W as free coords `e, ω`, and show `Hmat0 (r,0) = e·ω` (a product of two coords, obviously a
      nonzero poly). Does the telescope give a clean `Hmat0 (r,0) = (deepest E entry)·(deepest W entry)`
      over opaque widths, via a SHORT argument (the deepest boundary's `Rmat·A` contributes `E·W`, and the
      identity `Bmat`s + `chainQ·chainA=C` collapse everything else)? This avoids picking a numeric witness
      and reduces to "one entry is a 2-coord monomial".
  RANK (a)/(b)/(c) by Lean tractability over opaque dependent widths.

Q2. For the recommended route, the KEY lemma chain (signatures only, Lean-shaped). What is the minimal
    set of per-boundary facts to establish (e.g. `at w: A_s = [C_{s+1} ; 0]`, `C_{s+1} = Bmat_{s+1}·I + ...`,
    `the deepest Rmat·A = E·W`), and how does the downward induction carry the surviving entry's
    (row,col) index through the opaque widths without per-node `decide`?

Q3. The L=1 case: dead-leaf `achieverUfun ≡ 0` (so the witness is FALSE for L=1). Confirm the rate-side
    `Ubound` for the DEAD-leaf chart is genuinely only provable for `2 ≤ L`, and that L=1 requires either a
    live-leaf decoder OR a separate L=1 chart. Is stating the rate-side `Ubound`/positivity for `2 ≤ L`
    (with L=1 deferred to a live-leaf/pure-radial sub-case) the right scoping, or is there a dead-leaf
    trick for L=1 I'm missing?

OUTPUT CONTRACT:
- Q1: ranked (a)/(b)/(c) + the single cleanest, ≤ 10 sentences. I lean toward (c) (one entry = 2-coord
  monomial, no numeric witness) — confirm or redirect.
- Q2: the lemma-chain skeleton for the winner (signatures + the induction's carried invariant), ≤ 14 lines.
- Q3: confirm the `2 ≤ L` scoping for the dead leaf + the L=1 plan, ≤ 5 sentences.
- End: ONE recommended path + the biggest dependent-width risk, ≤ 4 sentences. Flag INFERENCE vs known API.
</task>
