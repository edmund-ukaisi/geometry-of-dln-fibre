# Thread 03 — Q-series route: consolidated findings

> Homed by the controller from `probe-qseries`'s consolidated report (the pen-and-paper seat hit a
> harness block on writing `.md`; content is the seat's, verbatim). Verification scratch + Codex
> artefacts committed at `baeaeed`. All claims exact-arithmetic verified.

**Verdict: CRACKED (full)** — but the combinatorial proof is PUBLISHED (RWY 2018), already cited by the
source, not new math. Kill-condition (does Thm 5.5 need a genuinely topological input?) did NOT fire.
Genuinely **zero-cited at the math level** (every input reprovable, no black box) — but it costs a
**`~6–8 file Core.QSeries` sub-library, ~2–3 weeks**.

## 1. Full zero-cited chain, end-to-end, Lean-targetable

Against the real Core.CTheta objects: `codimForm N m` (CTheta.lean:67), `kostantPartitions d r` (:108),
`cCodim d r h = (kostantPartitions d r).inf' h (codimForm N ∘ extendℤ)` (:151), `numTop` = card of
minimisers (:157). The q-series layer is ENTIRELY net-new — no q-series object exists in Core today.

New objects (Core.QSeries namespace): `P s = ∏_{k=1}^s (1−q^k)⁻¹` (inverse q-Pochhammer, P 0 = 1;
truncated poly or PowerSeries ℤ); `Pm m = ∏_{i≤j} P(m i j)`; `Pmult h = ∏ P hᵢ`;
`Qseries d r = ∑_{m ∈ kostantPartitions d r} q^{codimForm N (extendℤ m)} · Pm m`.

Ladder (⟸ = "reduces to"):
```
(perm-inv of (C,θ))                                          [Cor 5.10 — headline]
 ⟸ L0  cCodim d 0 = cCodim (sort d) 0  ∧  numTop d 0 = numTop (sort d) 0
 ⟸ L1  (C,θ)-EXTRACTION: lowestTerm(Qseries d r) = numTop d r · q^{cCodim d r}
 ⟸ L2  Qseries d r = P r · ∑_{s=0}^{min d−r} (−1)^s q^{C(s,2)} · P s · Pmult(d−r−s)   [Thm 5.5]
       (factor Pmult(d−r−s)=∏ᵢP(dᵢ−r−s) MANIFESTLY multiset-symmetric ⟹ L0 given L1)
 ⟸ S4  r>0 from S1 (shift) on the r=0 case
 ⟸ S3  power-series inversion of ∑ P s xˢ via q-binomial inverse
 ⟸ S2  eqn:key:  Pmult d = ∑_{s=0}^{min d} P s · Qseries(d−s) 0
 ⟸ S1  shift lemma 5.7:  Qseries(d−s) 0 = (q)_s · Qseries d s  (add-longest corner bijection)
 ⟸ S0 = Thm 5.6 (5gon):  Pmult d = ∑_{m ⊢ d} q^{codimForm} · Pm m   [the ONLY hard link]
 ⟸ PEEL  induction on N (§4), the load-bearing content
```
Every link exact-verified (verify_chain.py: S1–S4; verify_induction.py: PEEL; qseries.py: L2 and S0 for
monotone + non-monotone + all r, matching the paper's worked examples).

### L1, the (C,θ) extraction — IS IT CLEAN? YES.
cCodim/numTop are defined as a min/count over Kostant partitions with NO reference to the q-series; L1 is
the bridge (the paper's Lemma 5.2), elementary and non-circular. Mechanism (verified): every `Pm m` has
constant term 1 AND all coefficients ≥ 0. So in `Qseries d r = ∑_m q^{c(m)} Pm m`: minimum degree =
`min_m c(m) = cCodim`; coefficient of `q^{cCodim}` = `#{m : c(m)=cCodim} = numTop` — with NO cancellation,
because all `Pm` coefficients are non-negative. Lean shape: `Qseries_coeff_lt_cCodim_eq_zero`,
`Qseries_coeff_cCodim_eq_numTop`; non-cancellation is a `Finset.sum` of non-negative terms. L1 is NOT a
hidden hard step; the hard content is all in S0/PEEL.

## 2. Elementary inputs and what Mathlib has (v4.29 pin)

| input | needed by | in Mathlib v4.29? | size to build |
|---|---|---|---|
| (q)_n / inverse P_n | every link | NO (only ascPochhammer/descPochhammer, no q-deformation) | small: Finset.prod over PowerSeries; ~1 file |
| Gaussian binomial [n k]_q | S3, PEEL transfer | NO (qBinomial empty; "Gaussian" = Gauss-norm) | medium; AVOIDABLE — transfer statable without it |
| q-binomial theorem / inverse | S3 | NO | medium: truncated identity by induction; the one classical q-fact S3 rests on |
| q-Vandermonde / q-Chu–Vandermonde | PEEL transfer | NO (vandermonde → only Matrix.vandermonde) | medium IF used; AVOIDABLE — transfer directly verified, provable by own induction |
| N=1 Durfee identity | PEEL base | NO (durfee empty) | small–medium; the base case |
| Nat.Partition gen. funcs | conceptual P_s↔partitions | PARTIAL (Partition/GenFun.lean) | infinite-R⟦X⟧ by part-multiplicity, NOT "≤ n parts" truncated — NOT a drop-in |
| Finset.inf'/card, PowerSeries.coeff | L1, defs | YES | reuse |

The four classical q-series facts are ALL absent at this pin. "Zero-cited" means BUILDING a small
Core.QSeries sub-library, not citing — every fact elementary and provable from Finset/PowerSeries
primitives, but none free.

## 3. Honest size + verdict
- Core.QSeries primitives (P, Pm, Pmult, Qseries, non-negativity/constant-term): ~1–2 files.
- L1 extraction: ~1 file, CLEAN.
- S1–S4 chain: ~2 files — S1 REUSES the EXISTING `codimForm_update_corner` / corner bijection at
  CTheta.lean:206+; adds S3 q-binomial inverse + power-series inversion.
- S0 = Thm 5.6 via PEEL (load-bearing): peeling bijection + codim split + local transfer + inductive
  step: ~2–3 files, the bulk.

TOTAL **~6–8 substantive files, ~1.5–3 weeks** — comparable to the landed QIP/explicit modules plus new
q-series primitives.

- **LOAD-BEARING LEMMA:** the local transfer identity (§4) inside PEEL.
- **MOST-LIKELY-TO-BREAK Lean step:** S3's q-binomial inverse as a PowerSeries identity (formal inversion
  in a second variable x), OR the transfer's q-Vandermonde underpinning — both q-series facts with no
  Mathlib support, each a self-contained grind.
- **r_w = codim subtlety:** RWY's general-orientation Thm 1.7 (Euler-form) is NOT needed — for the
  EQUIORIENTED quiver `r_w(η) = codimForm(m) = c(m)` is the elementary computation verified here
  (verify_rwy.py, 243 partitions, 0 mismatch). The Lean target only needs the equioriented codimForm we
  already have.

## 4. The PEEL route (load-bearing S0), spelled out
Decorrelated Codex proposed it; verified every decomposition exactly (verify_peeling.py, verify_induction.py).
- **Peeling map (a BIJECTION):** `m ⊢ d ↔ (m', x)`, `m'` = Kostant partition of `(d_0..d_{N−1})` (merge
  column N into N−1: `m'_{i,N−1}=m_{i,N−1}+m_{i,N}`), `x_i=m_{i,N}` (`0≤x_i≤b_i:=m'_{i,N−1}`, i<N),
  `x_N=m_{N,N}`, `∑x=d_N`.
- **Codim split (299+132 partitions):** `c(m)=c(m')+Δ_b(x)`, `Δ_b(x)=∑_{0≤a<u≤N}(b_a−x_a)x_u`, `b_N:=0`.
- **Local transfer identity (exact, all (b;d_N)):** `P_{d_N}∏_{i<N}P_{b_i} = ∑_x q^{Δ_b(x)} P_{x_N}∏_{i<N}(P_{b_i−x_i}P_{x_i})`.
- **Inductive step (exact, incl. wide non-monotone):** summing transfer over m' gives
  `RHS_5gon(d)=P_{d_N}·RHS_5gon(d_0..d_{N−1})`; with Pmult multiplicative + IH ⟹ `RHS_5gon(d)=Pmult d`.
  Base N=0: single orbit, codim 0.

Codex's read that the transfer is "q-Vandermonde over the b_i blocks × N=1 Durfee" is INFERENCE, not yet
proved from primitives (the identity is verified; its clean decomposition is the one remaining "why").
Pinning it symbolically is the recommended pre-formalisation step.

## 5. Reconcile: thread-01 "open problem" vs RWY 2018
Both right about DIFFERENT objects; one correction.
- TRUE (thread 01): no proof from `eqn:dim_formula` + Kostant combinatorics ALONE — the authors say so
  (main.tex:979, 1122), and `|M⁺_d| ≠ |M⁺_{σd}|` (2932 vs 3868) blocks any direct value-preserving
  Kostant bijection. PEEL does NOT contradict this: it proves the generating-function identity (Thm 5.6),
  then reads off (C,θ); it never builds `M⁺_d ↔ M⁺_{σd}`.
- ALSO TRUE + the correction: a machine-free combinatorial proof of THM 5.6 IS published and IS cited —
  Rimányi–Weigandt–Yong, J. Algebraic Combin. 47 (2018) 129–169, arXiv:1608.02030, the source's own
  `[RWY]` (main.tex:977). So Thm 5.6 is NOT open; only the DIRECT-KOSTANT-BIJECTION form of perm-invariance is.
- **RECORD TO CORRECT:** thread-01's "purely combinatorial proof of the q-series identity is an open
  problem the authors lack" is WRONG as stated. It is the DIRECT-BIJECTION proof of perm-invariance the
  authors lack — the identity (Thm 5.6) is RWY 2018.

## Close
- Firmest result: Thm 5.5 ⟸ Thm 5.6 is a certified elementary chain (S1–S4; L1 extraction CLEAN); Thm 5.6
  certified by two routes (RWY 2018 published; self-contained PEEL induction, all decompositions
  exact-verified incl. wide non-monotone d) ⟹ Cor 5.10 via manifest symmetry of `∏ᵢP(dᵢ−r−s)`.
- Most likely to break it: the local transfer identity's clean proof-from-primitives, and S3's PowerSeries
  q-binomial inversion — both q-series facts absent from Mathlib.
- Next step: pin the transfer as q-Vandermonde × (N=1 Durfee) symbolically, then Core.QSeries (~6–8 files,
  ~2–3 wk).

Artifacts (committed `baeaeed`, pushed): `scratch/{qseries,verify_rwy,verify_chain,verify_peeling,verify_induction,explore_recursion,ctheta}.py`,
`codex/5gon-{prompt,answer}.md`. RWY paper: arXiv:1608.02030.
