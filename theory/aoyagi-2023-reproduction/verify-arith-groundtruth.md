# Red-team certificate: Aoyagi (2023) closed-form arithmetic + ground truth

**Seat:** pen-and-paper (red-team, exact arithmetic). **Direction:** adversarial verification.
**Method:** sympy 1.14 exact-rational/symbolic + an independent decorrelated `local-codex-consult`
(gpt-5.x, high reasoning, frame-in/hypothesis-out). Scripts: `/tmp/aoyagi_verify*.py`,
`/tmp/aoyagi_lemma3.py`, `/tmp/lemma3_image.py`, `/tmp/aoyagi_check4b.py` (reproducible; pasted-in below).

**Sources:** every load-bearing formula re-read against the **page images**
`pages/p06.png … p24.png` (the pdf→text `aoyagi-2023-extracted-text.txt` garbles exponents/subscripts
and is **not** authoritative). Image-confirmed: Thm 1 (RRR) p.7; Thm 2 three rewrites + equal-width
Example p.9; Thm 3 split p.13; `M_{s,k}` p.22; Lemma 3 (`A(b)` def, `∂A/∂b`, min value) p.24.

Bottom line: **all five numerical/algebraic claims PASS.** No mathematical typo in the paper at any
checked formula. One pinned item for the typo ledger is *our worked `.tex`* transcription (T-A: a
parenthesisation ambiguity in the Thm 2 rewrite). One structural finding (F-1) extends the known
Def-3 underspecification into the L=2 (RRR) regime. **Correction to an earlier draft of this
certificate:** the Lemma 3 value was briefly flagged as a typo on the strength of the garbled
extracted text; the page image (p.24) shows the print is `aℓ(ℓ−a)` and it is **correct** for `A(b)`
as the paper defines it (the `/ℓ²` cancels on both sides) — see Check 5, no typo.

---

## Check 1 — Theorem 2's three printed rewrites are algebraically equal (PASS)

Paper p.9 prints `λ` in three forms; the regular prefactor `(−r²+r(H¹+H^{L+1}))/2` and the pair-sum
`P₂ := Σ_{i<j} M^{(Sᵢ)}M^{(Sⱼ)}` are common, so only the middle two terms vary. With
`S := Σⱼ M^{(Sⱼ)}` and the Def-3 relation `a = S − (M*−1)ℓ`, i.e. `S = a + (M*−1)ℓ`:

| form | middle term(s) |
|---|---|
| (A) | `a(ℓ−a)/(4ℓ) − ℓ(ℓ−1)/4·(S/ℓ)²` |
| (B) | `a(ℓ−a)/(4ℓ) − ℓ(ℓ−1)/4·(M* + (a−ℓ)/ℓ)²` |
| (C) | `−¼(ℓ−a−1)(ℓ−a) − ℓ(ℓ−1)/4·(M*² + 2(a−ℓ)/ℓ·M*)` |

sympy, substituting `S = a+(M*−1)ℓ` into (A):

    Form A (with S=a+(M*-1)l) - Form B = 0
    Form B - Form C                    = 0
    Form A (sub) - Form C              = 0

**PASS** — `(A) = (B) = (C)`. The link `S/ℓ = M* + (a−ℓ)/ℓ` is the substitution; Codex derived the
`(B)→(C)` step independently: with `d = ℓ−a`, the square term contributes
`a(ℓ−a)/(4ℓ) − (ℓ−1)d²/(4ℓ) = d(1−d)/4 = −¼(ℓ−a−1)(ℓ−a)`, matching (C).

### (T-A) — pinned transcription ambiguity in the worked `.tex`

The worked `aoyagi-2023-worked.tex` (Thm 2, line 282 area) renders the inner factor of (B) as
`((M*+a−ℓ)/ℓ)²`. Read literally that is `(M*+a−ℓ)/ℓ`, which is **not** equal to (A):

    LITERAL ((M*+a-l)/l)^2 vs Form A(sub):
        ((1 - ell)*(a + ell*(Mstar-1))^2 + (ell-1)*(Mstar + a - ell)^2)/(4*ell)   (≠ 0)

The paper's actual expression is `M* + (a−ℓ)/ℓ = (M*ℓ + a − ℓ)/ℓ` (the `M*` is *not* divided by `ℓ`).
**Fix in the worked doc:** write `(M* + (a−ℓ)/ℓ)²` or `((M*ℓ + a − ℓ)/ℓ)²`, never `((M*+a−ℓ)/ℓ)²`.
This is a rendering bug in our reproduction, not in Aoyagi; harmless to the math but a trap for a
future reader/formaliser who copies the `.tex` literally.

---

## Check 2 — equal-width Example reproduces the ground truth (PASS)

Equal widths `M^{(s)}=M₁` ⇒ `ℓ=L`, `M* = ⌈(L+1)/L·M₁⌉`, `a = (L+1)M₁ − (M*−1)L`,
`λ = (−r²+2rH¹)/2 + a(L−a)/(4L) + (L+1)/(4L)·M₁²`, `θ = a(L−a)+1`. Exact (sympy + Codex agree):

| case (H,r) | L | M₁ | M* | a | λ | θ | expected |
|---|---|---|---|---|---|---|---|
| (2,2,2), r=0 | 2 | 2 | 3 | 2 | **3/2** | **1** | 3/2, 1 ✓ |
| (2,2,2,2), r=0 | 3 | 2 | 3 | 2 | **3/2** | **3** | 3/2, 3 ✓ |

### Check 2b — (2,1,2) via general Thm 2 / Def 3 (PASS)

`H=(2,1,2)`, `r=0` ⇒ `M=(2,1,2)`. All `M^{(s)} < ½ΣM = 5/2` ⇒ `M = {1,2,3}`, `ℓ=2`,
`M̃ = 5/2`, `M* = 3`, `a = 5 − 2·2 = 1`. Closed form (r=0, H¹=H³=2):
`λ = a(ℓ−a)/(4ℓ) − ℓ(ℓ−1)/4·(5/2)² + ½·Σpairs`, `Σpairs = 2·1+2·2+1·2 = 8`.

    (2,1,2): Mset={1,2,3}, ell=2, Mstar=3, a=1, sum_pairs=8
             lambda = 1, theta = 2     [expect lambda=1, theta=2]

**PASS** — `λ = 1`, `θ = a(ℓ−a)+1 = 1·1+1 = 2`.

---

## Check 3 — Theorem-3 regular prefactor count (PASS)

The split (eq. thm3-split, paper p.13) peels the regular block `{C₁−Eᵣ, F₂, F₃}` with generator count
`n = r² + r(H¹−r) + r(H^{L+1}−r)`. sympy:

    n = r² + r(H1−r) + r(HLp1−r) = r(H1+HLp1) − r²        ✓
    n/2 = r(H1+HLp1−r)/2 = (−r² + r(H1+HLp1))/2           ✓

**PASS** — the contribution `n/2 = (−r²+r(H¹+H^{L+1}))/2` matches the printed prefactor exactly. This
is a single top-level Morse block (RLCT = ½·#generators), occurring **once**, not per layer — the
worked doc's `\gnote` after eq. thm3-split states this correctly.

---

## Check 4 — RRR (Thm 1, L=2) = Thm 2 specialised to L=2 (PASS on the formula; F-1 on the selector)

**Formula template:** identical. Thm 1's expression (Def over `{1,2,3}`, `H³`) and Thm 2's
(general Def 3, `H^{L+1}` with `L+1=3`) are the *same* template in `(ℓ, a, S, P₂)`:

    Thm1 template - Thm2 template (L+1=3) = 0     ✓

So once `(ℓ, a, M*, M)` are fixed, Thm 1 **is** Thm 2 at `L=2`. The only place they can differ is the
*selection of `M`*. Comparing Thm 1's explicit four-way case-split (p.7) against general Def 3 (p.8)
over all `M=(M¹,M²,M³)`, entries `0..7`:

    both unique & agree:                 238
    agree (Thm1 set ∈ Def3 solutions):   105
    Thm1 rule undefined (boundary):        0
    DIVERGENCES (Thm1 set ∉ Def3 sols):  169   — all of them Def3-EMPTY

### (F-1) — the Def-3 underspecification reaches into L=2

Every one of the 169 divergences is a case where **Def 3 returns no valid `M`** while Thm 1's
case-split does pick one. 126 of them have *distinct* widths (not a tie artefact). Smallest witness
`M=(0,1,2)` (hand-checked, all four subsets):

    sub={1,2}(0-idx) ell=1 S=1: (i)chosen<excl=T (ii)S>ell·M*=T? 1>1·1 = FALSE  -> no
    sub={1,3}        ell=1 S=2: (i) FALSE                                        -> no
    sub={2,3}        ell=1 S=3: (i) FALSE                                        -> no
    sub={1,2,3}      ell=2 S=3: (ii) 3 > 2·2 FALSE                               -> no

Thm 1 picks `{1,2}` (1-indexed, via case `M³ ≥ M¹+M²`), but Def 3's **strict** `Σ > ℓM^{(s)}` for a
chosen `s` is unsatisfiable. So Thm 1's case-split is the *total* version of the selector that general
Def 3 fails to be — extending task #15's `[4,2,1,3]` finding into the RRR (`L=2`) regime. This
reinforces the worked doc's standing decision: take the geometric `Mval_min` (always defined) as
primitive; Def 3 / the Thm-1 case-split are *computed consequences where they apply*. The Thm-1
case-split is strictly wider than the general Def 3, and itself does not cover *every* width vector
(ties among the smallest two widths are decided only by listing order).

---

## Check 5 — Lemma 3 minimisation + value (PASS; no typo — image-confirmed)

**Read from the page image `pages/p24.png`** (the line cropped + upscaled), the print is exactly:

    A(b)/ℓ² = [ b((ℓ−a)/ℓ)² + (ℓ−1−b)(−a/ℓ)² + (b(ℓ−a)/ℓ − (ℓ−1−b)a/ℓ)² ]
    ∂A(b)/∂b = (ℓ−a)² − a² + 2(b(ℓ−a) − (ℓ−1−b)a){(ℓ−a)+a} = ℓ²(1 + 2b − 2a)
    min{A | b=0,…,ℓ−1} = A(a−1) = A(a) = aℓ(ℓ−a)

The `/ℓ²` divides **both sides** (the bracket on the RHS is itself over `ℓ²`), so `A(b)` denotes the
bracket `b(ℓ−a)² + (ℓ−1−b)a² + (b(ℓ−a)−(ℓ−1−b)a)²`. With that definition (sympy, `/tmp/lemma3_image.py`):

    A(b) = ℓ²b² + ℓ²(1−2a)b + a²ℓ(ℓ−1)
    dA/db = ℓ²(1 + 2b − 2a)            ✓ matches the paper's printed derivative (p.24)
    A(a) = aℓ(ℓ−a),  A(a-1) = aℓ(ℓ−a),  A(a) − A(a−1) = 0
    min_b A(b) = aℓ(ℓ−a)               ✓ matches the printed value (real min b = a−½; integer mins a−1, a)
    consistency: ¼·[A(a)/ℓ²] = ¼·a(ℓ−a)/ℓ = a(ℓ−a)/(4ℓ)  ✓ (exactly λ's first variable term)

**PASS — no typo.** The printed `A(a) = aℓ(ℓ−a)` is correct for `A(b)` as defined. The earlier draft
flagged this as a typo (T-B) on the strength of the garbled extracted text and a misread of which
object `A` names; the image settles it. The downstream use is consistent: `λ`'s first term is
`a(ℓ−a)/(4ℓ) = ¼·(min A / ℓ²)`.

**One minor clarity caveat (not a typo):** `A(a−1)` is in the stated domain `b∈{0,…,ℓ−1}` only for
`a ≥ 1`; at `a = 0` only `b = a = 0` is valid, and the min is still `0 = aℓ(ℓ−a)|_{a=0}`. So the chain
`A(a−1)=A(a)` silently assumes `a ≥ 1` (harmless; both evaluate to `aℓ(ℓ−a)`).

(Codex, decorrelated, independently derived `A(b)=ℓ²b²+ℓ²(1−2a)b+a²ℓ(ℓ−1)`, `dA/db=ℓ²(2b+1−2a)`,
`min_b A(b)=aℓ(ℓ−a)`, and the `a=0` domain caveat, from a brief that withheld this seat's conclusions
— matching the image-confirmed result.)

---

## Typo ledger entries (for §6 of the worked doc)

- **(T-A)** worked `.tex` Thm 2 rewrite (B): render `(M* + (a−ℓ)/ℓ)²`, never `((M*+a−ℓ)/ℓ)²`.
  Our transcription bug; the math (all three forms equal) is sound. **This is the only typo, and it is
  ours, not Aoyagi's.**
- **(Lemma 3 — NOT a typo)** Image-confirmed (p.24): `A(b)` is the bracket (the `/ℓ²` cancels both
  sides), printed `min = aℓ(ℓ−a)` is correct, derivative `ℓ²(1+2b−2a)` correct, downstream `λ` term
  `a(ℓ−a)/(4ℓ)` consistent. Minor clarity caveat only: `A(a−1)` needs `a ≥ 1`. *(An earlier draft
  wrongly listed this as typo T-B, having trusted the garbled extracted text; retracted.)*
- **(F-1, structural)** Def 3's selector is unsatisfiable on many width vectors even at `L=2` (smallest
  `M=(0,1,2)`); Thm 1's explicit case-split is the wider total selector but still not total under ties.
  Confirms and extends the existing Def-3 underspecification ledger entry (task #15). Use geometric
  `Mval_min` as primitive.

## Level discipline

All checks above are at the **closed-form `(λ, θ)` arithmetic level** — the value the resolution
*outputs*. They do **not** certify the resolution itself (Thm 4 / the Case-1/Case-2 blow-up), nor the
`Mval(t)=codim S(t)` geometric bridge, nor the `rlct ≤ ½·codim` analytic cap (Cited). The `(2,2,2)→3/2`
etc. ground truths are matched at the formula level; that they equal the *geometric* `½·Mval_min` is a
separate (thread-03 / R1) claim not re-checked here.
