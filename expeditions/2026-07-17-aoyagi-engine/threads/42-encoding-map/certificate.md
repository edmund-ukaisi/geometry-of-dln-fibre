# Thread-42 — P6.2 Tier-3 encoding-map certificate (pnp, decorrelated)

Charge: the five-part cert on (3a) `{T | admTight ∧ Mval = minAdm} ≃o BoxPart(ℓ)(residueA)` — the E-lane's
last trap-laden object. Instruments: exact arithmetic (`encoding_battery.py`, EXIT 0), decorrelated Codex,
Def-3 CHECK-0 selector (not crude max-ℓ). No Lean. Composition target: my cert IS (3a)'s adjudication;
(3b) tree-binding composes separately (the DivChain nesting, thread-41 confirmed).

## VERDICT: (3a) HOLDS. `{T | admTight ∧ Mval=minAdm} ≃o BoxPart(ℓ,a)` is a genuine order-isomorphism.
Bijection + order-embedding both directions, verified on 993 cores + all ground truths + the trap kill-set;
Codex-corroborated. **Plus a load-bearing correction to the charge's premise (part v).**

### (i) The explicit encoding — profile → increments → a-subset → box-partition
- **increments.** From a binding profile `T=(t¹,…,t^L)` (weak-decreasing, t^L=0), the per-layer descents
  `eⱼ = t^{j-1} − tʲ ≥ 0` (t⁰ := M¹), `∑ⱼ eⱼ = M¹`. On the certified (ℓ,a) the binding constraint forces
  exactly `a` of the ℓ "Lemma-4 steps" to be the large (M) step and `ℓ−a` the small (M−1) step.
- **a-subset.** `A(T) ⊆ [ℓ]`, |A|=a = the positions of the M-steps (Lemma-4). `T̃` (min) = M-steps FIRST
  (`A={1..a}`), `T̃'` (max) = M-steps LAST (`A={ℓ−a+1..ℓ}`).
- **box-partition.** `A = {p₁<…<p_a}` ↦ the Young diagram `λᵢ = (#(M−1)-steps before the iᵗʰ M-step)`,
  giving antitone `f ∈ BoxPart(ℓ,a)` (parts ≤ ℓ−a). Componentwise ≤ on profiles ↔ Young inclusion.
- **Canonical form (Birkhoff, Codex-confirmed):** `enc(T) = {j ∈ J(P) : j ≤ T}` (down-set of
  join-irreducibles); after identifying `J(P)` with the `a×(ℓ−a)` cell grid these ideals ARE `BoxPart(ℓ,a)`.
  The iso is unique once the grid labelling is fixed (a transpose automorphism exists only for a square box
  a=ℓ−a; the profile side pins the labelling). The battery constructs and verifies this iso directly (cover
  structure, not just numeric invariants — Codex's caveat).

### (ii) Bijectivity on the tight domain at (paperEll, residueA)
For EVERY scanned core (993, L∈{2,3,4}) and all ground truths: `|{T | admTight ∧ Mval=minAdm}| = C(ℓ,a) =
|BoxPart(ℓ,a)|` and a poset order-iso exists (verified by explicit cover-matching). Ground truths:
(2,2,2)&(3,3,4)&(2,2,3,2)→(ℓ,a)=(2,2), |P|=1; (2,2,2,2)→(3,2), |P|=3; (2,1,2)→(2,1), |P|=2.

### (iii) strictMono BOTH directions (order-embedding); the reverse is load-bearing
- The canonical `enc` is an order-EMBEDDING both ways (`T≤T' ⟺ enc T ≤ enc T'`) at the full trap kill-set:
  [1,1,2,1], [2,2,4,3], [2,2,2,2,2], and the admTight trap cores [2,2,5,3], [2,3,4,2].
- **The reverse implication is the hazard the OrderIso pin exists for.** A naive coord-sum encoding
  (`rank = ∑tʲ`, staircase box) is NOT an order-embedding: at [2,2,2,2,2] the incomparable profiles
  `(1,1,1,0)` and `(2,1,0,0)` (both ∑=3) map to the SAME box `(2,0)` — comparable image from incomparable
  sources, inventing an order relation (reverse fails). Worse, `∑tʲ` is not even a graded rank: at [1,1,2,1]
  the cover `(0,0,0) ⋖ (1,1,0)` jumps the sum by 2. So the encoding MUST use the box/inversion (Young-cell)
  rank, never the profile coordinate-sum. (Codex, decorrelated: "sums discard coordinate distribution …
  may send incomparable T,T' to comparable diagrams — or the same diagram — inventing order.")

### (iv) Boundary at ℓ=1 and a=ℓ
- `a = ℓ` (e.g. (2,2,2),(3,3,4)): `BoxPart(ℓ,ℓ)` = antitone `f ≤ 0` = the single all-zero point; `|P|=1`,
  ρ = a(ℓ−a)+1 = 1. (ℓ=1 forces a=1=ℓ by 1≤a≤ℓ — same single-point case.)
- `a = 1` (e.g. (2,1,2)): `BoxPart(ℓ,1)` = antitone `f:Fin 1→ℕ, f≤ℓ−1` = a CHAIN of length ℓ; ρ = ℓ.
- The canonical (RHS) side is always total/clean; the profile side (LHS) carries the paper's domain
  constraints (admTight + Mval=minAdm), which the edges collapse correctly.

### (v) NEGATIVE certificate + a correction to the charge's premise
- **CORRECTION (proven + battery-verified):** Lambda's `Adm` (`admBound` = min(M0,M1) at j=0, M^(j+1)
  else) is NOT loose relative to the tight run-min set — **it EQUALS it as a SET.** The weak-decrease
  constraint reconstructs the running min: `t^j ≤ t^{j-1} ≤ … ≤ t¹ ≤ min(M¹,M²)` and `t^i ≤ M^{i+1}` at
  each i give `t^j ≤ min(M¹,…,M^{j+1}) = runmin(j)` by induction. So `admTight = Adm` (0 set-inequalities
  over 993 cores), and **`minAdm_tight_eq` is a SET identity — stronger than value-only.** No spurious
  binding profiles arise on Lambda's `Adm`; `|binding| = C(ℓ,a)` there too. seat-E can prove the seam as a
  set equality (the induction above), not a value clamp.
- **Where the encoding GENUINELY breaks (the honest negative cert):** the OVER-loose lattice (cap
  min(M0,M1) at EVERY position, dropping the M^(j+1)/run-min bound — the shape seat-E's abstract battery
  used for its 6 exceptions). There `t^j` can exceed `M^{j+1}`, the factor `(M^{j+1} − t^j)` goes NEGATIVE,
  and `minAdm` collapses to ≤ 0 (e.g. [4,4,1,1]→0, [5,5,1,1]→ −1) — unphysical. The FAILING DIRECTION is
  the PROFILE side (LHS): the domain no longer has `C(ℓ,a)` binding elements at the TRUE minAdm, so no
  bijection to `BoxPart` exists (Codex: "loosening first breaks the element count"). The run-min / M^(j+1)
  cap is thus load-bearing — and Lambda's `admBound` already supplies it (via the induction), which is why
  Lambda's `Adm` is safe and the over-loose one is not. Docstring reason for admTight: "the M^(j+1)/run-min
  cap keeps every `Mval` term ≥ 0 so `minAdm` is the true codimension; dropping it admits unphysical
  negative-Mval profiles and destroys the C(ℓ,a) count."

## Consequence for seat-E (Tier-3 scaffold unfreezes)
- Render (3a) as the order-iso `{T | admTight ∧ Mval=minAdm} ≃o BoxPart(ℓ,a)` via the Birkhoff/box-cell
  encoding; verify BOTH directions (the reverse is the OrderIso pin — coord-sum rank is the trap).
- The seam lemma is `Adm = admTight` as a **set identity** (induction: decrease + admBound ⟹ run-min),
  not a value clamp; this simplifies `Mval_clamp_le`/`minAdm_tight_eq`.
- Domain condition: non-degenerate (minMval ≥ 1 ⟺ positive reduced widths, thread-41); the run-min cap is
  load-bearing vs the over-loose lattice only. (3b) tree-binding is the DivChain nesting (thread-41).
