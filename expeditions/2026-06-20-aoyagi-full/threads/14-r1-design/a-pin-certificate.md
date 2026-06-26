# Prereq-(a) arbitrary-v shape — D1≥ GATING CERTIFICATE (pp-hall, 2026-06-21)

**Task #117.** a114e07e hit the gap pp-hall's D1≥ value-free cert (#112) flagged: prereq-(a) =
"homogeneous-residual split at an ARBITRARY fibre point v", but #111's `schur_chart_exists` is at the
ORIGIN. Resolve: is (a) = `schur_chart_exists` instantiated at `v` (D1≥ purely #111-gated), OR a SEPARATE
existence lemma? Output: the exact (a) Lean-hypothesis shape + D1≥'s precise gating.

**Verdict: (B) SEPARATE LEMMA. D1≥ is NOT #111-gated.** Prereq-(a) is a distinct local-analytic
constant-rank/Morse split at `v`; #111's origin-chart cannot supply it. Two decorrelated legs converged
(pp-hall exact algebra L=2 + L=3 + Codex xhigh, hypothesis withheld).

## Why (a) ≠ #111@v (the core distinction)
- **#111 `schur_chart_exists`** is a RESOLUTION statement at the ORIGIN of the reduced core:
  `‖prod(C)‖² = (monomial in exceptionals)·‖prod(C')‖²` (the Schur recursion, toward the VALUE).
- **Prereq-(a)** is a local normal form at an ARBITRARY fibre point `v`: `F(v+W) = [regular q-square
  block] + [homogeneous residual core]`, `q = generator-Jacobian rank at v`. At `v≠origin` the
  generators have a nonzero LINEAR leading part (Jacobian rank `q>0`) — that regular block must FIRST be
  split off by a constant-rank/Morse normal form. #111 resolves a core that ALREADY sits at a
  zero-origin (Jacobian rank 0); it does NOT produce the regular block. So translating #111 to `v`
  cannot give (a).
- D1≥ is VALUE-FREE (#112): it only needs the residual core HOMOGENEOUS, not RESOLVED. So D1≥ needs
  the (a)-split + Aoyagi homogeneity-scaling + `rlctAt_mono` — and NOT #111's resolution at all.

## The exact structural picture (pp-hall, exact algebra)
**Load-bearing identity (reconfirmed):** at every fibre point `v`, generator-Jacobian rank `= codim of
v's stratum = Mval(t)` (`a_pin_*` scripts).

**Where the residual core is empty vs non-empty — the L=2-vs-L≥3 distinction (a confound I caught):**
- **L=2 (2,2,2),(4,3,2):** the residual core is EMPTY at EVERY fibre `v` EXCEPT the origin. Every
  non-deepest `v` is a SMOOTH point of `{prod=0}` (e.g. `(A1=0, A2 invertible)`: 4 independent linear
  generators, Jacobian rank 4 = full; `(A1,A2)` both rank-1: rank 3, residual `=0` identically). So at
  L=2 the (a)-split at `v≠origin` is TRIVIAL (pure regular block, `λ_v = codim/2`). **This is an L=2
  artifact — do NOT generalise it.**
- **L=3 (2,2,2,2):** at an INTERMEDIATE fibre point `v ∈ S(1,0,0)` (or `S(1,1,0)`), the generator-Jacobian
  rank is `2`, NOT `4` — the residual core is genuinely NON-EMPTY (`a_pin_L3.py`). The split is
  non-trivial: `[regular dim-2 block] + [homogeneous residual core]`. So for L≥3 the (a)-split MUST
  handle non-empty cores at intermediate singular `v`. (The naive "core empty except at deepest" would
  have misled the formaliser.)

**The residual core's shape (bonus, not required):** at the L=3 intermediate `v`, the residual core's
leading form is `(w1+w5)(w8−w9−w10+w11)` — BILINEAR, a Schur-reduced 1×1·1×1 chain product, consistent
with #109's strict-transform (`a_pin_factor.py`). So the residual IS of chain-product form — but D1≥
treats it as an ABSTRACT homogeneous core; re-identifying it as `‖prod(C')‖²` is STRONGER than (a) needs
and not required (only homogeneity is). If a separate normal-slice theorem later proves it's a smaller
chain, #111 could apply to IT — but that's downstream of D1≥, not a gate.

## The exact (a) Lean-hypothesis shape (a114e07e's target, Codex-drafted + pp-endorsed)
The clean pointwise hypothesis (allow empty core via `core = 0`):

    LocalHomogeneousResidualSplitAt F generator v :=
      generator v = 0 ∧
      ∃ (q : ℕ) (Core OutCore : Type) (coord : AnalyticLocalEquiv (EuclideanSpace ℝ (Fin q) × Core) Param)
        (core : Core → OutCore),
        coord 0 = v ∧
        q = rank (fderiv ℝ generator v) ∧
        AnalyticAt ℝ core 0 ∧ core 0 = 0 ∧
        (∃ d : ℕ, 0 < d ∧ ∀ t z, core (t • z) = (t ^ d : ℝ) • core z) ∧   -- HOMOGENEOUS core
        (F ∘ coord =ᶠ[𝓝 0] fun xz => ‖xz.1‖² + ‖core xz.2‖²)               -- regular block + core

D1≥ then gates as: `∀ v ∈ fibre, LocalHomogeneousResidualSplitAt F generator v`, plus the rank identity
`rank(Jac generator at v) = Mval(t_v)`, plus the general analytic/RLCT lemmas already green
(`rlctAtOn_comp_homeomorph`, `rlct_unit_invariant_aux`, `smoothBlockND_rlct`, `rlctAt_mono`).

## Needed for ALL v, not just generic
D1≥ is pointwise `∀ v ∈ fibre, rlctAt F deepest ≤ rlctAt F v`, so the split is needed for ALL fibre `v`.
Generic stratum points are the EASY empty-core cases; the singular fibre points (non-empty core, present
for L≥3) are exactly the ones the generic argument does NOT cover. Both legs agree (FACT).

## Net — D1≥'s precise gating (for a114e07e)
- D1≥ is gated on a SEPARATE `(a)`-split lemma `LocalHomogeneousResidualSplitAt`, NOT on #111.
- (b) the cone `prod (t•A) = t^L·prod A` (deepest-in-closure) is value-free and a114e07e is building it
  now regardless. (a) is the blocker for the full D1≥ tide.
- Given (a) + (b), D1≥ = general analytic facts (the four green S1-germ tools + `rlctAt_mono` +
  homogeneity scaling), value-free, off the R1 critical path.
- The (a)-split itself is a constant-rank/Morse normal-form construction — a NEW existence lemma. It is
  NOT #111, but it is the SAME shape of analytic-chart work; the formaliser should scope it as its own
  rung (a "local rank-stratum normal form" lemma). It is provable (standard constant-rank theorem +
  homogeneity of the transverse chain core), not open math.

Decorrelation: pp-hall exact algebra (10 scripts in `a-pin-scripts/`: the L=2 empty-core finding, the
L=3 non-empty-core correction, the bilinear residual factorization, codim=Mval) + Codex xhigh
(independent: (B) separate lemma, the same Lean shape, same "all v" + "abstract homogeneous core" reads).
Converged. Consult banked at `codex/a-pin-{prompt,answer}.md`.
