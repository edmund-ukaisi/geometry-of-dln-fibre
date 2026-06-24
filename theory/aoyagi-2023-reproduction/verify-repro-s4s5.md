# Red-team certificate: Aoyagi (2023) worked reproduction §4 (Lemmas 3–5) and §5 (RRR)

**Function:** FIDELITY (decorrelated). **Seat:** reviewer (red-team).
**Method:** own reading formed from the **page images** first (authoritative; the pdf→text
extraction is garbled and was NOT used), then compared to `aoyagi-2023-worked.tex`. Exact arithmetic
in sympy / `fractions` (no floats for verdicts): `/tmp/verify_s4_lemma3.py`, `/tmp/verify_theta.py`,
`/tmp/verify_Htilde.py`, `/tmp/verify_rrr.py`, `/tmp/verify_consistency.py`. Decorrelated
`local-codex-consult` (gpt-5.1-codex-max, xhigh) fired on the θ section with the page text only (my
reproduction's prose withheld): `/tmp/codex_theta_{prompt,answer}.md` — it concurred independently on
all three structural points below.

Pages re-read visually (cropped + upscaled): p07 (Thm 1 / L=2 selector), p08 (Def 3), p09 (Thm 2),
p24 (Lemma 3), p25 (the two partial-sum families + Lemma 4), p26 (Lemma 5 proof / the count).

---

## Verdict summary

| Check | Subject | Verdict |
|---|---|---|
| 1 | Lemma 3 (§4.1) vs p.24 | **PASS** (algebra + image faithful; one minor domain note) |
| 2 | θ section (§4.4) vs p.25–26 | **broken-by-case** — STATEMENT faithful, but the **prose mechanism is wrong** (3 fidelity defects) |
| 3 | §5 RRR closed form + 3 ground-truth rows + clean form | **PASS** (all recomputed exactly) |
| 4 | Internal consistency (§4/§5 vs §2, ledger, name=content) | **PASS** with one caveat folded into Check 2 |

The θ section (§4.4) is the one with faithfulness gaps. Its *headline statement* `θ=a(ℓ−a)+1` and the
*at-risk-seam flag* are correct; its *derivation prose* misrepresents how the paper gets that number.
Concrete .tex fixes in the last section. **Codex independently reached the same three θ defects from
the page text alone.**

---

## Check 1 — Lemma 3 (§4.1) faithfulness to p.24: **PASS**

p.24 (read from the crop `/tmp/p24_lemma3.png`) prints, verbatim:

    Lemma 3. Let ℓ and 0 ≤ a, b ≤ ℓ−1 be natural numbers and let
      A(b)/ℓ² = b((ℓ−a)/ℓ)² + (ℓ−1−b)(−a/ℓ)² + (b(ℓ−a)/ℓ − (ℓ−1−b)a/ℓ)².
    Then,  min{A | b=0,…,ℓ−1} = A(a−1) = A(a) = aℓ(ℓ−a).
    [Proof] A(b)/ℓ² = [b(ℓ−a)² + (ℓ−1−b)a² + (b(ℓ−a)−(ℓ−1−b)a)²]/ℓ²
    ∂A(b)/∂b = (ℓ−a)²−a² + 2(b(ℓ−a)−(ℓ−1−b)a){(ℓ−a)+a} = ℓ²(1+2b−2a).

The `/ℓ²` divides **both sides**, so the object the .tex calls `A(b)` is the bracket
`b(ℓ−a)²+(ℓ−1−b)a²+(b(ℓ−a)−(ℓ−1−b)a)²`. The .tex (line 638) writes exactly this. sympy:

- `A(b)` bracket `=` `ℓ²b²+ℓ²(1−2a)b+a²ℓ(ℓ−1)` (.tex's expanded form) — **diff 0**.
- `∂A/∂b = ℓ²(1+2b−2a)` — **diff 0**, and matches the image's middle-expression chain.
- `A(a)=A(a−1)=aℓ(ℓ−a)` — **diff 0** each; real minimiser `b*=a−½` (.tex's claim) — exact.
- link `¼·A(a)/ℓ² = a(ℓ−a)/(4ℓ)` — **diff 0** (exactly λ's first variable term).

**No misrepresentation of Aoyagi's construction.** The .tex prose (line 634–636) says the binding
branches "differ only in how Aoyagi's local-coordinate construction distributes the split; parametrised
by an integer `b∈{0,…,ℓ−1}`" — this is a faithful framing: p.24's `b` is exactly that integer split
parameter with domain `0≤b≤ℓ−1`. The `\fnote` (line 651–655) correctly records the retracted (T-B)
typo and the `a≥1` domain caveat for `A(a−1)`.

**Minor note (not a defect):** p.24's Lemma 3 hypothesis is `0 ≤ a, b ≤ ℓ−1` — it bounds **`a ≤ ℓ−1`**
too (so `ℓ−a ≥ 1`). The .tex states the `b` domain but does not echo the `a ≤ ℓ−1` bound. Harmless to
the value layer; worth a parenthetical if precision is wanted.

---

## Check 2 — θ section (§4.4) faithfulness to p.25–26: **broken-by-case** (3 defects)

The **statement** `θ=a(ℓ−a)+1` (line 700) and **Lemma 5** are faithful (p.25 prints exactly
`Lemma 5. θ=a(ℓ−a)+1`; cross-checked numerically: `(2,2,2)→1`, `(2,1,2)→2`, `(2,2,2,2)→3`, all match
the doc's own ground truth). The **at-risk-seam flag is honest and correctly placed** (line 702–711:
the combinatorial-count = analytic-pole-multiplicity step is flagged as needing meromorphic
continuation Mathlib lacks; I did NOT attempt to close it, per dispatch). The `\gnote` "for ℓ=1, a=1 it
is 1, the unique minimiser" is correct.

But the **derivation prose** (lines 693–698) misrepresents the p.25–26 mechanism in three ways.

### Defect 2a — the partial-sum family is wrong (single naive family vs the image's two-piece pair)

.tex line 694: *"With the partial sums `H̃_j = Σ_{l=1}^{j+1} M^{(S_l)} − jM` (so `H̃_1 = H̃_ℓ = 0`)…"*

p.25 prints **two** families (`H̃_j` and `H̃'_j`), **each with two pieces**:

    H̃_j  = Σ_{l=1}^{j+1} M^{(S_l)} − jM                     for j=1,…,a
    H̃_j  = Σ_{l=1}^{j+1} M^{(S_l)} − aM − (j−a)(M−1)        for j=a+1,…,ℓ
    H̃'_j = Σ_{l=1}^{j+1} M^{(S_l)} − j(M−1)                 for j=1,…,ℓ−a
    H̃'_j = Σ_{l=1}^{j+1} M^{(S_l)} − (ℓ−a)(M−1) − (j−ℓ+a)M  for j=ℓ−a+1,…,ℓ

and asserts only `H̃_ℓ = H̃'_ℓ = 0` (here `M` denotes the integer `M*`).

The .tex's single naive formula is only the **first piece** of `H̃_j` (valid `j ≤ a`); it (i) omits the
second piece entirely, (ii) omits the whole `H̃'_j` envelope, and (iii) gets the boundary values wrong.
Exact (sympy, `/tmp/verify_Htilde.py`, with `P=a+(M−1)ℓ`):

- naive `H̃_ℓ = P − ℓM = a − ℓ` — **≠ 0** unless `a=ℓ`; image two-piece `H̃_ℓ = 0` ✓.
- naive `H̃_1 = M^{(S_1)}+M^{(S_2)} − M` — **not generally 0**; counterexample `(2,2,2)`: `2+2−3 = 1 ≠ 0`.

So the parenthetical "`(so H̃_1 = H̃_ℓ = 0)`" is **false** for the family as the .tex defines it. The
image makes no claim about `H̃_1`; it asserts the **terminal** equalities `H̃_ℓ = H̃'_ℓ = 0` for the
two-piece envelopes.

### Defect 2b — Lemma 4 needs a second condition the prose drops

.tex line 694–697: *"Lemma 4 characterises which terminal branch-vectors `T_{s,k}` attain the minimum:
those lying in the range `T̃ ≤ T_{s,k} ≤ T̃'` cut out by the `(H̃_j)` — precisely the balanced splits
tying in Lemma 3."*

p.25 Lemma 4 requires **both**: (1) the envelope `T̃ ≤ T_{s,k} ≤ T̃'`, **and** (2) a local-increment
condition `H_{j−1} − H_j + M^{(S_{j+1})} = t^{(S_j−1)}_{s,k} − t^{(S_{j+1}−1)}_{s,k} + M^{(S_{j+1})} =
M−1 or M`. The increment condition is what forces the step sizes (the `a` steps of size `M` and `ℓ−a`
steps of size `M−1` that the proof counts); the envelope alone is insufficient. The .tex's "cut out by
the `(H̃_j)`" describes only condition (1) and omits (2). (Codex, decorrelated, flagged this
independently: "a one-liner 'balanced-split range cut out by partial sums' omits the crucial increment
constraint and would be incomplete.")

### Defect 2c — Lemma 5 does NOT count "over the index range min{a,ℓ−a}<j≤max{a,ℓ−a}"

.tex line 697–698: *"Lemma 5 counts them over the index range `min{a,ℓ−a} < j ≤ max{a,ℓ−a}`, giving
θ=a(ℓ−a)+1."*

This is wrong twice over. p.26 prints the per-`j` interval count as a **three-range** piecewise function
(`1≤j≤min`, `min+1≤j≤max`, `max+1≤j≤ℓ`), and crucially says the number of binding vectors is **"less
than the sum"** of these counts (a union, not a disjoint sum), and then:
*"Because J is increased by one for Case 1(2) in the proof, we have θ ≤ a(ℓ−a)+1. Finally, by using
`T_{s,k}`, we construct the local coordinate for θ = a(ℓ−a)+1 as follows."*

So the value is an **upper bound (union of intervals + the Case-1(2) increment) plus a matching
explicit lower-bound construction** — a two-sided argument. It is **not** a single count over any one
index range. Exact check (`/tmp/verify_theta.py`, `/tmp/verify_consistency.py`):

- raw sum of the piecewise counts over `j=1..ℓ−1` **overcounts**: `a=2,ℓ=4` → sum `7`, but `a(ℓ−a)+1=5`;
  `a=2,ℓ=5` → `10` vs `7`; `a=3,ℓ=7` → `18` vs `13`. Never equal.
- the .tex's *named* "middle range" sum `Σ_{min<j≤max}`: `a=2,ℓ=4` → `0`; `a=1,ℓ=3` → `2`; `a=2,ℓ=2` →
  `2` vs target `1`. **Never** equals `a(ℓ−a)+1`.

(Codex, decorrelated: "It comes from the upper-bound union plus a constructive lower bound, not from
summing the interval counts… upper bound via Case 1(2) intervals, lower bound via explicit
construction." Its further lattice-point reading — `a(ℓ−a)+1` = integer points on a constrained 1-D
path — is its own *inference*, labelled "plausibly"; I do not certify it, but it is consistent with the
structure.)

**Verdict on Check 2:** the θ **statement** is faithful and the seam flag is honest, but the
**derivation prose is not a faithful reproduction of p.25–26**. The prose claims the value is read off a
single partial-sum family over one index range; the paper proves it by a two-sided
(upper-bound-union + explicit-construction) argument over a two-envelope, two-condition characterisation.
This is exactly the kind of "statement + structure" gap the dispatch warned the θ section might carry:
the statement survived, the structure prose did not. **Report-only** (fidelity function): I flag and
give a minimal repair below; I do not rewrite the mathematics.

---

## Check 3 — §5 RRR closed form + ground truth + clean form: **PASS**

Recomputed from the L=2 selector (p.07) + Thm 2 closed form, independently (`/tmp/verify_rrr.py`,
`fractions`):

| (H), r=0 | calM | ℓ | M* | a | λ | θ | expected | |
|---|---|---|---|---|---|---|---|---|
| (2,2,2) | {1,2,3} | 2 | 3 | 2 | **3/2** | **1** | 3/2, 1 | PASS |
| (2,1,2) | {1,2,3} | 2 | 3 | 1 | **1** | **2** | 1, 2 | PASS |
| (1,1,3) | {1,2} drop M³ | 1 | 2 | 1 | **1/2** | **1** | 1/2, 1 | PASS |

- **Clean-form agreement** `2·rlct_core = ½(Σq²−Σm²)` on each: `(2,2,2)` 3=3, `(2,1,2)` 2=2,
  `(1,1,3)` 1=1 — all **PASS**.
- **Dominated regime** (§5(b), ℓ=1): `rlct_core = ½·m₁m₂`, `θ=1`. For `(1,1,3)`: `rlct_core=½`,
  `½·m₁m₂=½` ✓; clean `½((m₁+m₂)²−m₁²−m₂²)=m₁m₂=1` ✓ (note: this is `2·rlct_core`, i.e. `Mval_min`,
  consistent with the .tex line 755 reading `clean = m₁m₂`). **PASS.**
- The .tex correctly keeps `(2,1,2)` in the **balanced** ℓ=2 regime (θ=2), not the dominated regime —
  no mislabelling.
- `(2,2,2,2)` L=3 equal-width → λ=3/2, θ=3 (the §2 Example), recomputed **PASS** (consistent with the
  RRR cross-check note, line 767).

§5 reproduces Thm 2|_{L=2} faithfully; the totality framing (line 725–733, F-1) matches
`verify-def3-underspec.md`.

---

## Check 4 — internal consistency: **PASS** (one caveat is Check 2)

- `θ=a(ℓ−a)+1` is consistent across every ground truth in the doc (§2 Example, §5 table) — verified.
- §4/§5 do not contradict §2 (Thm 1/2 statements) or the ledger (T-A/T-C/T-D/F-1): the closed-form
  template, the regular prefactor, the clean form, and the Def-3 totality story all line up with the two
  prior certs (which I re-derived rather than trusted — Lemma 3 algebra, the three rewrites' role, the
  L=2 selector all reconfirmed).
- **name = content:** §4.4's `\fnote` correctly bounds the θ claim ("driven only as far as it cleanly
  reaches"; the analytic identity flagged as the named seam). §5's `\fnote` correctly caveats
  general-L-first design. No overclaim of *proof* where only *statement+structure* is reproduced —
  **except** that the §4.4 derivation prose presents the θ mechanism as if reproduced faithfully when it
  is not (Check 2). That is a fidelity defect, not an overclaim of provenness.

---

## Concrete .tex line-level fixes (§4.4 only; §4.1 and §5 need none)

All in `aoyagi-2023-worked.tex`, the θ paragraph lines 693–698. Minimal, fidelity-restoring; they do
not change the (correct) statement `θ=a(ℓ−a)+1` or the (honest) seam flag.

1. **Line 694 — fix the partial-sum family + drop the false `H̃_1=0`.** Replace the single naive
   `H̃_j = Σ M^{(S_l)} − jM (so H̃_1 = H̃_ℓ = 0)` with the **two two-piece envelopes** `(H̃_j)`,
   `(H̃'_j)` as printed on p.25, asserting only the **terminal** equality `H̃_ℓ = H̃'_ℓ = 0`. (If a
   full transcription is out of scope for this statement-level section, at minimum: cite the two
   envelopes to p.25 and **delete the `(so H̃_1 = H̃_ℓ = 0)` parenthetical**, which is false for the
   naive family — counterexample `(2,2,2)`: `H̃_1 = 1`, `H̃_ℓ = a−ℓ = 0` only coincidentally there but
   `≠0` in general.)

2. **Lines 695–697 — Lemma 4 needs the second condition.** After "those lying in the range
   `T̃ ≤ T_{s,k} ≤ T̃'`", add the **local-increment condition** `H_{j−1} − H_j + M^{(S_{j+1})} ∈ {M−1, M}`
   that Lemma 4 also requires; "cut out by the `(H̃_j)`" alone is incomplete.

3. **Lines 697–698 — fix the Lemma 5 count mechanism.** Replace *"Lemma 5 counts them over the index
   range `min{a,ℓ−a}<j≤max{a,ℓ−a}`, giving θ=a(ℓ−a)+1"* with a faithful two-sided statement, e.g.:
   *"Lemma 5 bounds the count above by the union `⋃_{j=1}^{ℓ−1}{H : H̃_j ≤ H ≤ H̃'_j}` together with the
   Case-1(2) increment, giving `θ ≤ a(ℓ−a)+1`, and an explicit local-coordinate construction attains it,
   so `θ = a(ℓ−a)+1`."* The named single index range is not where the value comes from (the raw interval
   sum overcounts: `a=2,ℓ=4` → 7 ≠ 5).

**Optional (Check 1 precision):** echo p.24's full hypothesis `0 ≤ a, b ≤ ℓ−1` (the `a ≤ ℓ−1` bound,
not just `b`) in §4.1.

---

## Level discipline

This certificate is at the **fidelity-to-images level** for §4/§5 prose, plus **exact closed-form
arithmetic** for the numeric claims. It does **not** certify the resolution (Thm 4 / Case-1/2 blow-up),
the `Mval=codim` bridge, or the **analytic** identity "combinatorial θ count = pole multiplicity" — that
last is the at-risk seam, and the .tex flags it honestly (I confirmed the flag, did not close the seam).
The θ defects above are about **how the .tex describes p.25–26's combinatorial argument**, not about the
truth of `θ=a(ℓ−a)+1` (which holds on every checked ground truth).
