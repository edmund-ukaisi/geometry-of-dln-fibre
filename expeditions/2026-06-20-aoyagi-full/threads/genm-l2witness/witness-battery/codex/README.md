# Decorrelated Codex sanity-check — outcome

**Model:** gpt-5.x (`codex exec`, `model_reasoning_effort=xhigh`). **My conclusion WITHHELD**
(frame in, facts in, hypothesis out): Codex was asked to recompute the three exact-algebra facts
from scratch and was explicitly told NOT to assume my hinted formulas (`C_k`, the codim formula)
are correct — it was told to test them.

- `battery-prompt.md` — the contract-shaped prompt.
- `battery-answer.md` — Codex's last message (its derivations + tables).
- `battery-run.log` — the raw run.

## Method note (inference vs fact)

The read-only sandbox blocked Codex from EXECUTING Python (`approval policy is UnlessTrusted`
rejected the exec, see `battery-run.log`). So Codex's `output`/BigInt-DP blocks are its own
**analytic derivations presented in tabular form**, not verified runs. This makes the check
genuinely **decorrelated by method**: my exhibits are executed enumeration / Groebner / exact-rank
/ exact-DP (`../w*.out`); Codex's are closed-form derivations. The convergence below is between two
different methods, which is the point of the consult. The load-bearing verification remains MY
executed scripts; Codex is the independent cross-check.

## Convergence (Codex vs the battery exhibits)

| Question | Codex (independent) | Battery witness | Match |
|---|---|---|---|
| Q1 codim `V_k` | `= k^2 - floor(k^2/4) = C_k`; gap `= floor(k^2/4)`; n=4..7 tabulated; closed form proved via `q=c+e, s=a+c`, minimiser `(floor(k/2), ceil(k/2), floor(k/2))` | W2: `true codim == C_m`, gap `= floor(m^2/4) = a*c`, exact | YES |
| Q2 joint ideal | `I=(x,y,b)`, `det P=x`, `det Z=y`, `b in I` but `b not in (det P, det Z)=(x,y)` | W1: identical, via Groebner | YES |
| Q3 `m1 = min_k[C_k+n(n-k)]` | `= minAdm(n,n,n,n)` all n=2..8 | W3(C): identical | YES |
| Q3 `m3 = min_m[m^2+minAdm(n-m,n,n)]` | `= minAdm(n,n,n,n)` all n | W3(B): identical | YES |
| Q3 `m2 = min_k[C_k+minAdm(n-k,n,n)]` | UNDERSHOOTS for n>=4, deficits `1,1,1,2,3` (n=4..8) | W3(D) guard: strict undershoot, same deficits (in 1/2 units: `1/2,1/2,1/2,1,3/2`) | YES |

Codex flagged exactly the two facts the battery is built around, unprompted by any conclusion of
mine:
- **Q2:** `b in I` but `b not in (det P, det Z)` — the alignment coordinate escapes the
  single-factor divisors (W1's KILL).
- **Q3:** `m2(4..8)` fall below `minAdm` by `1,1,1,2,3` — the invalid `C_m`-plus-reduced-chain
  split undershoots (W3's guard D).

## Bonus closed forms (from Codex, independently re-verified against the DP here)

- `minAdm((a,n,n)) = a*n - floor(a^2/4)`.
- `minAdm((n,n,n,n)) = m1(n) = m3(n) = ceil(2 n^2 / 3)`.
- `m2(n) = ceil(5 n^2 / 8)` (the invalid split's minimum).
- `argmin m1 = {floor(2n/3), ceil(2n/3)}`, `argmin m3 = {floor(n/3), ceil(n/3)}`.

Both `minAdm((n,n,n,n)) = ceil(2n^2/3)` and `minAdm((a,n,n)) = a*n - floor(a^2/4)` were
re-checked against the executed `minAdm` DP here (n up to 12): exact match. These are corroborating
closed forms; the battery itself does not depend on them (it computes `minAdm` directly).

## One cosmetic (non-)discrepancy

For Q1 Codex reports argmin triples INCLUDING the transpose `(c,a,e')` (e.g. `k=3`:
`[[1,2,1],[2,1,2]]`), whereas W2's `e = max(0, k-c)` parametrization lists one representative
per codim value (e.g. `(1,2,1)`). Both give the same codim `C_k` and the same gap; the extra
triple is the `a<->c` symmetry of the balanced component, not a disagreement. No load-bearing
number differs.

## Verdict

The decorrelated consult CONVERGES with the battery on every load-bearing exhibit (W1 ideal +
membership, W2 codim + gap, W3 B/C equalities and D undershoot), by an independent (analytic)
method, and supplies corroborating closed forms. No discrepancy requiring a human double-check.
