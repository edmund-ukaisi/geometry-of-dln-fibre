> **⚠ CONCLUSION SUPERSEDED (2026-06-23, controller re-grounding).** The §4 conclusion below — "the
> realistic general-L route is **(ii) cite Aoyagi `rlct = ½·codim`**" — is **DRIFT and is RETRACTED**. It
> contradicts the brief's one-citation-only mandate (S2 alone) and `lessons.md` (citing `rlct = codim/2`
> was explicitly rejected — it cites away the new content and breaches Aoyagi-independence). The error:
> this note correctly refutes the **per-layer Morse recursion** (`M_last/2 + child`, L=2-only — that part
> STANDS), then concludes the determinantal resolution must be cited — having lost sight that the
> expedition **already built it as explicit charts**: the SETTLED g152/g153 mechanism (per-node blow-up +
> det-1 measure-preserving Schur peel + recurse, monomial-min-fold, codims = Mval) + pp2's landed #68
> RouteStep cert IS the rank-profile determinantal resolution, **proven from scratch, S2-only**. My #18
> partial-rank validation (2026-06-23) independently re-confirmed this (coupled Schur recursion, value
> `½·min Mval` robust general-L). So R1 is NOT a cite; the open R1 work is the **Lean grind** on the
> routeStep dispatcher (`fm3/routem`, mid-build) + integration. Keep §1–§3 (the per-layer-Morse refutation
> + the `Erow` degree-`(L−1)` structural root); discard §4's cite recommendation.

# Cross-check — the per-layer cover's inner Morse count is L=2-ONLY (the L≥3 wall)

**Seat.** pen-and-paper (decorrelated cross-check of a5f5ceb1's finding), DLNFibre aoyagi-full.
**Method.** exact-integer combinatorics + symbolic Erow-degree (sympy) + decorrelated xhigh Codex
(independent derivation, hypothesis withheld). **Scripts:** `g156-adjudication-scripts/Lge3_{check,struct,path}.py`.
**Codex:** `codex/Lge3-per-layer-scope-prompt.md`.

> **VERDICT (confirms a5f5ceb1, decorrelated).** The per-node cover's INNER squeeze
> `rlctAtOn(core) = M_last/2 + rlctAtOn(child)` (the `n = M_{L+1}` Morse count) is **L=2-ONLY**. For
> L≥3 it OVERCOUNTS. The headline's comparability-freeness + box-threading (verdict (a)) are
> UNAFFECTED — the Morse-count is a separate question verdict (a) did not probe. **The general-M
> headline is a NEW L≥3 wall**, and the honest general-L path is the **Aoyagi `rlct = ½·codim`
> cite** (the iterated determinantal resolution modulo-S2 is reachable only by re-proving Aoyagi).

## 1. The witness (confirmed exact)
The cover's per-node recursion `min{M₀M₁/2, M_last/2 + child}` vs true `minAdm/2`:
- ALL L=2 cases match (census `1..5²×1..7`, `Lge3_check.py`).
- L≥3 DIVERGES: **(3,3,3,3) cover = 7/2 (i.e. 7), minAdm/2 = 3 (i.e. 6)** — the witness reproduces.
  Also (2,2,2,3), (3,2,2,2), (4,4,4,4) diverge; (2,2,2,2), (2,3,3,2) happen to tie.

## 2. The structural root (confirmed)
At a node, blow up layer 0; `core = ‖Â·B‖²`, `B = A¹·A²···A^L`, `Erow = B[0,:] + u·Bred`.
- **L=2**: `B = A¹` a SINGLE free matrix ⟹ `Erow_j = B[0,j] + Σu_i B[i,j]` is a det-1 affine shear of
  free coords ⟹ `n = M_last` genuine Morse squares. VALID.
- **L≥3**: `B = A¹···A^L` a PRODUCT ⟹ `B[0,j]` is a degree-`(L−1)` form (e.g. L=3: `B[0,0] = P₀₀Q₀₀ +
  P₀₁Q₁₀`, bilinear) ⟹ `Erow_j` is NOT a free coordinate ⟹ `∑Erow²` is NOT a Morse block ⟹ the
  `n`-count overcounts. (sympy `Lge3_struct.py`; Codex independently: "Erow becomes a homogeneous form
  of degree L−1, vanishing to higher order, not Morse".)
- **Why unavoidable**: `schurStateRed` PRESERVES depth `L` (`redM = (M₀−1, M₁−1, M₂, …)`), so the
  recursion NEVER reaches the L=2 free-`B` base; every L≥3 node has a product `B`. The true increment
  `d = minAdm(M) − minAdm(redM)` is NON-LOCAL (depends on the whole tail profile, not just `M_last`):
  (3,3,3,3) `d=2 ≠ M_last=3`; (2,2,2,3) `d=2 ≠ 3`.

## 3. Impact on verdict (a) — UNCHANGED, but a NEW wall
Verdict (a) validated: (i) comparability-FREENESS (no `‖R‖²≍‖∏S_s‖²`) — HOLDS; (ii) the box-threading /
point-min collapse via homogeneity — HOLDS (the ordering `rlctAtOn(F,0) ≤ rlctAtOn(F,v)` is homogeneity,
depth-independent). What verdict (a) did NOT probe: the per-node Morse-COUNT `n = M_last`. That count is
where the L≥3 failure lives. So **verdict (a) stands for L=2; the general-M headline has a NEW L≥3
Morse-count wall** — the per-layer recursion computes the wrong value for L≥3.

## 4. The general-L path (the re-scope)
- The CORRECT resolution is the **rank-profile (determinantal) one**: `rlct = ½·min_T Mval(M,T)` over
  the FULL admissible-profile lattice (not a per-layer recursion). Each profile-`T` divisor carries
  Jacobian order `(t^{j-1}−t^j)(M_j+M_{j+1}−2t^j)` and loss order `2(t^{j-1}−t^j)(M_{j+1}−t^j)`, giving
  ratio `Mval(M,T)` (Codex Q2). Witnesses: (3,3,3,3) min at `T=(2,1,0)`; (2,2,2,3) at `(1,0,0)`.
- **Modulo-S2 vs cite (Q-B):** the per-profile divisor value FOLLOWS from S2 (normal-crossing min rule)
  ONCE an explicit iterated determinantal resolution is exhibited. BUT constructing that resolution
  uniformly for arbitrary `(L, widths)` IS Aoyagi's hard theorem — no simpler uniform construction is
  published. So: **(i)** build the general determinantal resolution (big, S2-only in principle, =
  re-proving Aoyagi), or **(ii)** cite Aoyagi `rlct = ½·codim` (beyond S2, smaller surface). Codex and I
  agree the realistic route is **(ii) the cite**; the per-layer cover was the shortcut that fails L≥3.

**Decisive reason (one line).** The depth-preserving per-layer blow-up cannot produce a Morse block once
L≥3 (`Erow` is a degree-`(L−1)` form, not free), so the `n=M_last` count overcounts and the recursion
never reaches a free-`B` base — forcing the full determinantal resolution, realistically the Aoyagi cite.

---

## Addendum — the MECHANISM-vs-VALUE distinction (deriv-finish's retraction, confirmed)

deriv-finish retracted an earlier "Route A closes general-L, recurses to monomial leaves" overclaim
(it was L=2-anchored). The retraction is CORRECT and precisely located (confirmed `confirm_retraction.py`):

- **MECHANISM (general-L SOUND):** the squeeze `core ≍ Φ = ∑Erow² + ‖SΓ‖²` (`schur_node_squeeze_unif`)
  is the Schur ROW-DECOMPOSITION + the algebraic two-sided bound (`∑b² ≤ T²`) — a pure identity +
  inequality in the ENTRIES of `(Erow, b, SΓ)`, holding for ANY `L`. The integrability TRANSFER
  `rlctAtOn(core) = rlctAtOn(Φ)` is general-L. And it is the sound R1 single-step (`SΓ = child`), NOT
  the refuted L2 `R`-core. This part stands.
- **VALUE (L=2-ONLY):** `rlctAtOn(∑Erow²) = n/2` needs `{Erow_j}` to be `n` FREE Morse coordinates.
  L=2: `B=A¹` free ⟹ `Erow` is a det-1 shear of free coords ⟹ Morse, `n/2`. L≥3: `B=A²···A^L` a
  product ⟹ `Erow` is a degree-`(L−1)` form (not free) ⟹ `rlctAtOn(∑Erow²) ≠ n/2` (higher-order
  vanishing). DOUBLE break: even the additivity split `rlctAtOn(Φ) = rlctAtOn(∑Erow²) + rlctAtOn(‖SΓ‖²)`
  can fail (Erow and SΓ may share variables for L≥3). So the per-node VALUE telescoping is L=2-only.

So: the squeeze MECHANISM (integrability transfer + the sound single-step squeeze) is general-L; the
per-node Morse VALUE `n/2` and its telescoping to monomial leaves are L=2-only. The L≥3 value
resolution (the degree-`(L−1)` Erow forms ⟹ the rank-profile determinantal resolution) is the open
operator scope call. #11 (ordering + subcover) is unaffected. Consistent with this note's main verdict
(`n = M_last` overcounts for L≥3).
