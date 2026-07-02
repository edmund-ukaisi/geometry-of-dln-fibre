# Certificate — the zeta-pole RLCT definition (spec for R2b)

_Pen-and-paper cross-check backing the operator's **zeta-pole** definition of the RLCT. This is the
spec the R2b formaliser builds against. NO Lean here — exact math + citations + the built/cited split._

_Grounding: Lehalleur–Rimányi 2024 §RLCT (`main.tex` L1782–1937); Watanabe SLT; R2a's cite-free
`RLCT.integrabilityThreshold` (`Core/Analysis/RLCT/{Basic,Integrability}.lean`, `rlct-r2` worktree);
the proved algebraic `λ = ½·codim` (`DLN/RlctPayoff.lean`); `DLN/Aoyagi/ThetaOrderDistinction.lean`._

---

## 0. The one-paragraph verdict

The zeta-pole definition is **sound and faithful to the paper**. The largest pole of the archimedean
zeta function `Z_{F,φ}(s)=∫|F|^s φ\,dvol` sits at `s = −λ` where `λ = rlct` is R2a's integrability
threshold, and the pole order gives the honest multiplicity `m = rlcm`. The **one** monument that must
be cited for the pair `(λ, m)` to *exist and equal the RLCT* (hence for the definition to be
well-defined) is the **meromorphic continuation of `Z` — poles on the negative rationals, largest pole
`= −rlct_x` — bundled** (Atiyah 1970 continuation + Saito/SLT for the maximal-pole = −threshold
identification). Decorrelated Codex sharpened this: a *bare* continuation axiom is **not** enough — the
"largest pole = −threshold" identity (Link 1) must be *in* the cited statement, not derived free from
meromorphy. The integrability threshold *value* `λ` alone (R2a, cite-free) does not need any of this;
the *pole reading*, `m`, and Link 1 do. The soundness chain to the payoff `rlct(K^{DLN}_B) = ½·codim
mult⁻¹(B)` has **no sign error and no gap** beyond the bundled continuation cite + the two named
analytic cites (Watanabe upper, Aoyagi lower, already isolated on the cordon). The pole order `m` is
**not** `θ` (proved distinct; the paper itself says "no simple relationship"). Normalization items the
formaliser must fix: **smooth `φ` not `1_U`**; **`+s` (zeta) vs `−c` (R2a)** sign; **no second `½`** on
the already-squared DLN loss; `|F|` only for sign-indefinite germs (inert for the nonneg DLN `K`).

---

## 1. The precise definition

### 1.1 The two paper definitions and how they relate

The paper gives the RLCT **twice**, and the formaliser must know both because the "zeta-pole
definition" is the *second*, made well-defined by the *first*'s integrability content plus a cited
continuation.

**(A) Integrability form (paper Def 4.1, `defn:rlct`, L1787).** For a real-analytic `F : X → ℝ` on a
real-analytic manifold `X`:

$$\operatorname{rlct}(F) := \sup\{ s \in \mathbb R \mid |F|^{-s} \text{ is locally integrable}\}\in\mathbb R\cup\{\infty\},$$

and the **local** version at `x ∈ X`:

$$\operatorname{rlct}_x(F):=\sup\{ s\in\mathbb R\mid |F|^{-s}\text{ is locally integrable at }x\}.$$

The global is the inf of the local (paper Prop `prop:rlct_elem` (iii)): `rlct(F) = inf_{x∈X} rlct_x(F)`
(inf attained when `X,F` algebraic — our DLN case).

**(B) Zeta-pole form (paper `propdefn`, L1804–1809 — the operator's chosen definition).** Fix a volume
form `dvol` on `X` and a relatively compact open neighbourhood `U ∋ x`. The **local archimedean zeta
function**

$$\zeta_{F,U}(s) := \int_U |F(x)|^{\,s}\, \mathrm{dvol}(x)$$

is a priori defined and holomorphic for `Re(s) ≫ 0`, and **extends to a meromorphic function on ℂ**.
For `U` small enough the poles are independent of `U` and are **negative real numbers**. Then:

- **`λ = rlct_x(F)`** is fixed by: *the largest pole of `ζ_{F,U}` is at `s = −λ`* (equivalently
  `λ = −(largest pole)`, i.e. `λ = min{ |s₀| : s₀ a pole }` since all poles are negative);
- **`m = rlcm_x(F) ∈ ℕ`** := the **order** of that largest pole.

There is no explicit smooth cutoff `φ` in the paper's `propdefn`; the role of `φ` is played by the
**relatively compact open `U`** (an indicator `1_U`; `U` small enough stabilizes the poles). The
standard SLT / cited normalization instead uses a **smooth compactly-supported `φ ≥ 0`, `φ(x) ≠ 0`**,
integrating `∫ |F|^s φ` (Watanabe). **These two localizations agree on the largest pole near `x`**, but
they are *not interchangeable in the cited theorem*: the clean continuation statement is proved for a
smooth `φ` (a `C_c^∞` density), and with a raw `1_U` the *full* pole set is cutoff-sensitive — only the
**maximal** pole is a robust invariant (decorrelated-Codex flag). **Recommendation (revised): use the
smooth `φ` form in the cited axiom** (matches the standard theorem the cite names), and — if R2b reuses
R2a's `∫_U`/`IntegrableOn U` machinery for the *value* — note in-file that `1_U` is a simplified variant
agreeing on the maximal pole (`λ`), not the verbatim cited object. Formalising the smooth `φ` is cheap
(`ContDiff` + `HasCompactSupport`, both in Mathlib) and buys fidelity to the cite.

### 1.2 The RLCT pair, pinned

$$\boxed{\ \operatorname{RLCTPair}_x(F) := (\lambda, m),\quad \lambda = -\sup\{\operatorname{Re}(s_0) : s_0 \text{ a pole of } \zeta_{F,U}\},\quad m = \operatorname{ord}_{s=-\lambda}\zeta_{F,U}.\ }$$

Because all poles are negative reals, `sup Re(s₀)` is the pole **closest to 0**, and `λ` is its
absolute value — this is the largest RLCT value / mildest singularity reading. **Pin `λ` as a positive
real** (the paper's `rlct`), *not* as the (negative) pole location; the sign flip is where a formaliser
slips (§3).

### 1.3 Cross-checks against Watanabe and the R2a substrate

- **Watanabe SLT.** Watanabe defines the RLCT `λ` as the largest pole of the zeta `ζ(z) = ∫ K(w)^z φ(w) dw`
  (his `K ≥ 0` is the KL divergence, already nonnegative — so `|K| = K`, no absolute value needed), with
  multiplicity `m` = pole order. Watanabe's normalization is `∫ K^z φ` over the parameter space with
  prior `φ`; the largest pole is `−λ`, `λ > 0`. **Identical structure** to the paper's `propdefn`. The
  paper's `|F|^s` reduces to Watanabe's `K^z` on a nonnegative loss (our `lossDLN ≥ 0`).
- **R2a `integrabilityThreshold`.** R2a builds, cite-free, `integrabilityThreshold K U = sSup{ c ≥ 0 :
  K^{−c} integrable on U }`, with the germ `K ≥ 0` (so `K^{−c}`, no `|·|`). This is **exactly paper
  Def 4.1 (A)** restricted to the nonnegative-germ / one-sided (`c ≥ 0`) case: the substrate's `c` is
  the paper's `s`, and `sSup` is the `sup`. R2a validates it: `K=|t|` gives threshold `1 = rlct(|t|)`
  (paper `ex:rclts`, `rlct(x^n)=1/n` at `n=1`). **So `integrabilityThreshold = λ = rlct` (value only)**,
  cite-free. The *pole* object (B) is the extra structure the zeta definition adds on top.

### 1.4 Flagged normalization ambiguities the formaliser MUST fix

1. **`|F|` vs `F` in the base** (see §3.1). Use `|F|^s` for a general real-analytic `F`; for the DLN
   loss `K^{DLN}_B ≥ 0` this collapses to `K^s`, matching both Watanabe and R2a. Decide once:
   define `RLCTPair` for a **nonnegative germ `K`** (matches R2a + the payoff) OR for a **general `F`
   with `|F|`** (matches the paper's full generality). Recommendation: **nonnegative germ `K ≥ 0`** —
   it is all the payoff needs, matches R2a verbatim, and avoids `|F|`-differentiability nuisance.
2. **`+s` (zeta) vs `−c` (R2a threshold).** The zeta integrand is `K^{+s}` (poles at negative `s`); the
   R2a integrand is `K^{−c}` (threshold a positive `c`). `s = −c`. The pole at `s₀ = −λ` corresponds to
   the threshold `c = λ`. **Do not let a `RLCTPair` field read `λ = the pole` — it is `−(the pole)`.**
3. **local vs global.** The paper's `rlct(F)` (no subscript) is the **global** `inf_x rlct_x(F)`. The
   payoff `rlct(K^{DLN}_B) = ½·codim` is the **global** rlct (an `inf` over the fibre; attained since
   algebraic). The zeta `propdefn` is stated **locally** (at `x`). The formaliser's `RLCTPair` is
   local; the payoff-facing `rlct` is the global `inf`. Keep the two typed apart, and note the payoff
   uses the global one. (R2a's `integrabilityThreshold K U` is already local-flavoured — a threshold on
   a neighbourhood `U`; the global value is the inf over base points, or — for the DLN algebraic case —
   directly `½·codim` via the cited bounds, sidestepping the inf.)
4. **boundedness of the `sup` / `sSup`.** In `ℝ`, `sSup ∅ = 0` and `sSup` of an unbounded set is junk.
   The honest value needs the admissible set **nonempty and bounded above** — the *pole* regime
   (`F⁻¹(0) ≠ ∅`, so `λ < ∞`). R2a already carries this as a `BddAbove` / nonempty guard ("name =
   content"). The zeta definition makes boundedness automatic *given the continuation* (a pole exists ⟹
   `λ < ∞`), which is one more reason the pole object is cleaner — but the price is the cite.

---

## 2. The exact cited statement (the bullet)

### 2.1 What must be cited, stated as it should appear in a `@[cited]` axiom

For the pair `(λ, m)` to exist AND to equal the RLCT, `ζ` must have a meromorphic continuation whose
largest pole is `−rlct_x` of finite order. **The cite must BUNDLE the "largest pole = −threshold"
identification** — a bare meromorphic-continuation axiom is *not enough* (decorrelated-Codex flag,
confirmed against the paper): with only "ζ extends meromorphically", the identity
`(largest pole) = −(integrability threshold)` would be a *further* cited lemma (it needs the
resolution/normal-crossing computation, or must be asserted). The paper's `propdefn` bundles it
("The largest pole is `−rlct_x(F)`"), so cite the **bundled** statement.

**Two conventions for the cutoff — pick the second (see the trap below):**

- The paper integrates `∫_U |F|^s dvol` over a relatively compact open `U` (an indicator `1_U`).
- The **standard cited theorem** uses a **smooth positive compactly-supported cutoff/density**
  `φ ∈ C_c^∞`, `φ ≥ 0`, `φ(x) ≠ 0`: `Z_{F,φ}(s) := ∫ |F|^s φ\,dvol`. This is the clean statement — the
  maximal pole is a robust germ invariant under it, whereas with a raw `1_U` the *full* pole set is
  cutoff-sensitive (only the maximal pole is safe). Use `φ`, not `1_U`, in the cited axiom.

**Cited axiom `cited_zeta_meromorphic_continuation` (Atiyah 1970 / Saito 2007).**

> **Hypotheses.** `X` a real-analytic manifold, `F : X → ℝ` real-analytic, `x ∈ X`, `dvol` a volume
> form, `φ ∈ C_c^∞(X)` a smooth cutoff with `φ ≥ 0` and `φ(x) ≠ 0`, supported in a small nbhd of `x`.
>
> **Conclusion.** `Z_{F,φ}(s) := ∫ |F|^s φ\,dvol`, holomorphic on `{Re s > 0}` (convergence —
> *buildable*, §3), admits a **meromorphic continuation** to all of `ℂ`, with poles a discrete set of
> **negative rationals**. When `F⁻¹(0) ∩ supp(φ) ∋ x`, there is a **largest pole `s₀ < 0`**, of finite
> order `m₀ ∈ ℕ₊`, and — the bundled identification — **`s₀ = −rlct_x(F)`** (equivalently
> `−s₀ = sup{c ≥ 0 : |F|^{−c} loc. integrable at x}`).

From this the pair is *defined*: `λ := −s₀ = rlct_x(F) > 0`, `m := m₀`.

**On-point source for the bundled real-threshold form:** T. Saito's / the SLT literature's statement
that the maximal pole of the real archimedean zeta equals `−rlct` directly (arXiv:math/0702056 and the
SLT treatments — Watanabe 2009 Ch. on zeta functions; Lin's thesis, the paper's `[lin:phd_thesis]`).
The *underlying continuation* is Atiyah 1970 (below); the *threshold-identification* is the SLT-facing
packaging. For the cordon, ONE `@[cited]` axiom carrying the bundled statement is cleanest (it is what
the definition consumes); if split, the split is {continuation (Atiyah)} + {maximal-pole = −threshold
(Saito/SLT)} — but do NOT ship only the former and treat the latter as free.

**Faithful source.** M. Atiyah, *Resolution of singularities and division of distributions*, Comm.
Pure Appl. Math. **23**(2) (1970) 145–150 — the classical statement that `|F|^s` (as a distribution)
continues meromorphically via resolution of singularities, poles in a finite set of arithmetic
progressions of negative rationals. This is exactly the paper's attribution (`main.tex` L1811: "This
proposition goes back to Atiyah [atiyah] and the proof is based on (real analytic) resolution of
singularities"). Equivalent monuments (any one suffices as the cite; Atiyah is the paper's choice and
the cleanest for the *real* archimedean case):

- **Bernstein–Sato / I. N. Bernstein 1972** (the `b`-function: `b(s)|F|^s = P(s)|F|^{s+1}` gives the
  continuation with poles among the roots of `b` shifted by `−ℕ`) — gives rationality of poles most
  directly, but is the *complex/algebraic* engine; Atiyah is the direct real statement.
- **Gelfand's problem / Bernstein–Gelfand, Atiyah** — the meromorphic continuation of `|F|^s`.
- **Hironaka 1964** resolution of singularities is the underlying tool inside Atiyah's proof; cite
  Atiyah (the packaged distribution statement), not Hironaka directly, for this object.

**Recommendation for the cordon:** ONE `@[cited "Atiyah 1970 (Comm. Pure Appl. Math. 23:145–150):
meromorphic continuation of ∫|F|^s, poles on ℚ_{<0}"]` axiom carrying the continuation + pole
existence/rationality/finite-order, as above. Keep the `λ`, `m` *definitions* (as `−s₀`, `ord`)
**built** on top of it (they are extraction, not new analysis).

### 2.2 The DLN analytic cites (separate, already on the cordon)

These are **not** part of well-definedness — they are the two bounds that *evaluate* `λ` for the DLN
germ. The repo already isolates them (`DLN/RLCT/AoyagiCited.lean`), and they stay:

- **`cited_watanabe_upper`** — Watanabe's universal `rlct ≤ ½·codim_ℝ` (paper `eqn:rlct_upper_bound`,
  L1825: `rlct_x(F) ∈ (0, codim/2] ∩ ℚ`; source: Watanabe, *Algebraic Geometry and Statistical
  Learning Theory*, CUP 2009). **This is itself a corollary of the same resolution monument** (the
  bound comes from the normal-crossing pole formula), but the repo cites it as a named analytic fact —
  correct: it is an evaluation, not the continuation itself.
- **`cited_aoyagi_lower`** — Aoyagi's DLN-specific matching `½·codim_ℝ ≤ rlct` (paper `thm:aoyagi-rlct`,
  L1889; source: M. Aoyagi, *Consideration on the learning efficiency of multiple-layered neural
  networks with linear units*, Neural Networks **172** (2024) 106132).

### 2.3 The BUILDABLE parts (do NOT cite these)

Sharply separated from the monument:

- **Convergence of `∫_U |F|^s` for `Re(s) ≫ 0`** — elementary: `|F|^s` is bounded on the
  relatively-compact `U` for `Re(s) ≥ 0` (continuous on a compact closure), so the integral converges;
  no continuation needed. This defines the half-plane of holomorphy (`{Re s > 0}` suffices for a
  bounded `F`; sharper: `Re s > −ε` for small `ε` before the first pole). *Buildable.*
- **The R2a integrability threshold `λ`** — `sSup{c ≥ 0 : K^{−c} integrable}` — **cite-free, already
  built** (R2a). This is the *value* half of the pair; it needs no continuation (it is defined by
  integrability, exactly paper Def 4.1(A)).
- **The 1-D Mellin gamma-type pole** `∫₀^1 t^{as+b}φ(t)\,dt` has a simple pole at `s = −(b+1)/a` — a
  direct integration-by-parts / gamma computation. *Buildable* (R3 in the ladder; Mathlib has
  `hasMellin_cpow`, per R0 recon). This is the *engine* of the continuation in the normal-crossing
  model, but on a normal-crossing germ it is elementary; only the *reduction of an arbitrary `F` to
  normal crossings* (resolution) is the monument.
- **The product normal-crossing pole formula** (R4) — in a normal-crossing chart `F∘π = u·∏ y_i^{N_i}`,
  `π^*dvol = v·∏|y_i|^{ν_i−1}dy`, the RLCT is `λ = min_i ν_i/N_i` and the pole order `m` is **the
  maximal number of minimal-ratio divisors `{i : ν_i/N_i = λ}` that meet SIMULTANEOUSLY on a chart
  hitting the support** — *not* the raw global count of minimisers unless they all meet at one point
  (decorrelated-Codex correction; the naive "`m = #minimisers`" over-counts when minimisers live on
  disjoint faces). Combinatorial, from the 1-D poles + Prop `prop:rlct_elem`(iv) (Thom–Sebastiani
  `rlct(FG)`, `rlct(F+G)`, paper L1838–1847, elementary from Fubini once each factor's continuation is
  in hand). *Buildable* — but state `m` with the "meet simultaneously" quantifier, not the flat count.
- **The smooth quadratic block** `rlct(x_1²+…+x_c²) = c/2` (paper `ex:rclts`, L1863–1867) — the smooth
  point of the fibre; *buildable* from the product formula.

**The built/cited line:** everything is buildable *once you may reduce `F` to a normal-crossing germ*.
That reduction — real-analytic **log-resolution / monomialization** (Hironaka), packaged as the
meromorphic continuation of `∫|F|^s` — is the single monument. Cite it once (Atiyah for the
continuation; Saito/SLT for the bundled "maximal pole = −threshold"); build the rest. **Note on
rationality:** "poles are negative *rationals*" is NOT a separate monument once the resolution is
cited — after resolution the poles come from one-variable factors and lie among `−(ν_i+k)/N_i`, so
continuation + pole-location + rationality all fall out of the *same* resolution computation. If R2b
instead axiomatizes only a *bare* "ζ extends meromorphically" (without resolution), then rationality
and the threshold-identification each need to be added to the axiom's conclusion (which is why §2.1
states the **bundled** form).

---

## 3. The soundness chain (the cross-check the operator wants)

The claim to verify, link by link, is:

$$\underbrace{\text{zeta-pole }\lambda}_{\text{def (B)}} \;=\; \underbrace{\text{integrability threshold}}_{\text{R2a}} \;=\; \underbrace{\tfrac12\,\operatorname{codim} \operatorname{mult}^{-1}(B)}_{\text{payoff}}.$$

### 3.1 Link 1 — zeta-pole `λ` = integrability threshold. **CITED (bundled into the continuation).**

**Statement.** For the germ `F` at `x` with `F⁻¹(0) ∋ x`: `−(largest pole of Z_{F,φ}) = sup{ c ≥ 0 :
|F|^{-c} locally integrable at x }`.

**Why it holds.** For `Re(s) > 0`, `Z(s) = ∫|F|^s φ` converges; running `s = −c` down the negative
axis, `∫|F|^{−c}φ` is (up to the smooth `φ`) the R2a integrand, finite exactly while `c < λ`. The
identification `s₀ = −λ` (largest pole = minus the abscissa where integrability breaks) is the content
of the bundled cite. One might hope to get it *free* from meromorphy via Landau's theorem (a real
boundary point of the convergence half-plane of a nonnegative density is a singularity, hence — given
meromorphy — a pole). **Decorrelated-Codex flag, adopted:** Landau gives that the boundary abscissa is
*a singularity*, but pinning it to be *the largest pole with `−s₀ = λ` exactly* is cleanest bundled
into the cited theorem — a *bare* meromorphic-continuation axiom does **not** on its own deliver
`s₀ = −λ` without the resolution/normal-crossing computation. So do NOT ship a bare-continuation axiom
and treat `s₀ = −λ` as a free lemma.

**Classification: CITED, and it must be IN the cited statement.** §2.1's axiom is written to *include*
`s₀ = −rlct_x(F)` in its conclusion (the paper's `propdefn` bundles it; Saito/SLT is the on-point
source). Then R2b proves `λ_zeta = integrabilityThreshold` by unfolding: `λ_zeta := −s₀` (def) `= rlct_x`
(cite) `= sSup{c≥0 : integrable}` (R2a's `integrabilityThreshold`, which *is* the paper's `rlct_x`
restricted to the nonneg germ). The value half (R2a) stays cite-free and *equals* `λ_zeta` *by the
cite*. **Do NOT** introduce a *separate* second axiom for "pole = threshold" — bundle it into the one
continuation cite. If R2b instead keeps `λ` = threshold as the *primary* value and uses the cite only
to supply `m` + the pole *reading*, then `λ_zeta = threshold` is `rfl`/definitional and only `m` carries
the well-definedness cite — the legitimate hybrid (§3.4).

**Sign check (the load-bearing item).** `s₀ = −λ`, `λ > 0`, `λ = threshold c`. **No sign error** in the
chain: R2a's `c` (positive) = paper's `−s` = `λ`. The trap a formaliser hits: writing `λ := s₀` (the
pole, negative) instead of `λ := −s₀`. The `RLCTPair.λ` field must be the **positive** `−s₀`.

**`K` vs `|F|`.** For the DLN germ `K^{DLN}_B = ‖mult−B‖² ≥ 0`, `|K| = K`, so `∫|K|^s = ∫K^s` — the
absolute value is inert. The sign map is unaffected by `K` vs `|F|`. (For a *general* `F` that changes
sign, `|F|^s` is the object; the DLN case never sees this.)

### 3.2 Link 2 — threshold = `½·codim_ℝ` (the analytic bracket). **CITED (Watanabe + Aoyagi), already isolated.**

**Statement.** `rlct(K^{DLN}_B) = ½·codim_ℝ mult⁻¹(B)`, from `le_antisymm` of:
- `rlct ≤ ½·codim_ℝ` (Watanabe universal upper, `cited_watanabe_upper`),
- `½·codim_ℝ ≤ rlct` (Aoyagi DLN-specific lower, `cited_aoyagi_lower`).

**Classification.** Two `@[cited]` axioms, already on the cordon (`AoyagiCited.lean`). The repo's
`rlct_lossDLN_eq_half_codimRealFibre` is exactly this `le_antisymm`. **No gap** — this is the analytic
heart, correctly cited, correctly scoped (the inhabited-fibre guard `0<N → B.rank=r → ∀k', r≤d k'`).

*Consistency note:* both bounds and the smooth-block example saturate `rlct = codim/2` for a smooth
quadratic (paper `ex:rclts`); the DLN fibre saturates it (Aoyagi) despite being singular — that is the
"mildly singular" content. The chain does not silently assume smoothness; it cites Aoyagi for the
non-smooth saturation.

### 3.3 Link 3 — `codim_ℝ` (real) = `codim_K` (complex `C`). **PROVED (not cited).**

**Statement.** `codimRealFibre d B = codimRepCanonical (fibre K d (B.map ι))` (real fibre codim =
complex fibre codim), and `= cCodim d r` (`= C`) at the corner.

**Classification.** **PROVED** in the repo:
`codimRealFibre_eq_codimRepCanonical_baseChange` (both sides are the same field-independent `C + δ` of
`Core.codimRepCanonical_fibre_eq_cCodim_add_shift`, valid over `[CharZero][Infinite]` — ℝ included, no
algebraic closure needed; target rank survives `ι` by `Matrix.rank_map_eq_of_injective`), then bridge
(b) `codimRepCanonical_fibre_zero_eq_cCodim`. This is the "real↔complex transfer" — algebra, not
analysis. **No gap.** The `x²+y²` pathology (real codim 2, generator-ideal height 1) is correctly
avoided because `codim_ℝ` is the *vanishing-ideal-of-real-points* height, pinned to `C + δ` combinatorially.

### 3.4 The composite: payoff soundness on the zeta-pole object.

**Verdict: SOUND.** Composing Links 1–3:

$$\lambda_{\text{zeta}} \overset{\text{L1, cited-cont}}{=} \operatorname{threshold} \overset{\text{L2, Watanabe+Aoyagi}}{=} \tfrac12\operatorname{codim}_{\mathbb R} \overset{\text{L3, PROVED}}{=} \tfrac12\,C.$$

Two honest architectures for R2b, both sound:

- **Zeta-primary.** `RLCTPair.λ := −s₀` from the continuation cite; prove `λ = integrabilityThreshold`
  (Link 1, from the cite); then the payoff is Link 1 ∘ L2 ∘ L3. Cites: `{continuation, Watanabe,
  Aoyagi}` (3 axioms; `rlctReal` becomes a *definition* off the pole, retiring the current opaque
  `rlctReal` axiom — a strict improvement).
- **Hybrid (R0's recommendation, controller-flagged).** Keep `integrabilityThreshold` (cite-free) as
  the payoff-bearing **value**; add the zeta-pole `(λ,m)` object behind the continuation cite *for the
  multiplicity `m` and the "this value is genuinely the pole" reading*, with `λ_zeta = threshold`
  proved from the cite. The payoff rides the cite-free value + Watanabe + Aoyagi; the continuation cite
  buys the honest `m` and the pole interpretation. Cites for the *payoff*: `{Watanabe, Aoyagi}` only;
  the continuation cite is needed for `m` / the pole reading, not for `½·codim`.

**Either is sound.** The operator chose zeta-pole (accepting the continuation cite as future-proofing).
The **only** delta vs today's repo: today `rlctReal` is itself an opaque `@[cited]` axiom (a bare map);
the zeta definition **replaces that opaque scalar with a constructed object** (`λ = −s₀`, `m = ord`)
resting on the *one* continuation cite — genuinely honest, exactly the expedition's goal. The two DLN
evaluation cites (Watanabe, Aoyagi) are unchanged.

**No sign error, no gap found** beyond the three named cites (continuation + Watanabe + Aoyagi), each a
genuine monument or named analytic theorem, each faithfully sourced.

### 3.5 One subtlety flagged for R2b: global-vs-local at the payoff.

The zeta `propdefn` is *local* (`rlct_x`, one pole at one `x`). The payoff `rlct(K^{DLN}_B) = ½·codim`
is the *global* `rlct = inf_x rlct_x` (paper Prop (iii)). For the DLN algebraic germ the inf is
attained. **The formaliser should not need to formalise the `inf_x` explicitly** if it keeps the
payoff-facing `rlct` as the value bracketed by Watanabe/Aoyagi (which are *global* statements,
`eqn:rlct_upper_bound_glob`); the *local* zeta pair is the definitional object, and the global rlct is
its inf. Keep the two typed apart (see §1.4 item 3). The current repo `RlctRealInterface.rlct` is
already the global map `(Tuple → ℝ) → ℝ`; the zeta `RLCTPair` is local-at-`x` — R2b connects them by
`rlct(F) = inf_x λ(RLCTPair_x F)`, or short-circuits via the cited *global* bounds (cleaner). This is a
**definitional bookkeeping** point, not a mathematical gap.

---

## 4. The `m ≠ θ` caveat — CONFIRMED, from the paper itself

The pole order `m = rlcm` is **NOT** the top-component count `θ`. This is not merely "proved distinct in
Lean" — **the paper states it directly** (`main.tex` L1933–1935, the remark after `thm:aoyagi-rlct`):

> "As far as we [know], there is no simple relationship between
> `rlcm(K^{DLN}_B) = m²{S̃/m}(1−{S̃/m})` and the number `k = C(m, S̃ − m⌊S̃/m + ½⌋)` of irreducible
> components of `mult⁻¹(B)`."

- **`rlcm` (the RLCT multiplicity `m`, the pole order)** `= m²{S̃/m}(1−{S̃/m})` (paper `thm:aoyagi-rlct`).
- **`θ = k` (top-component count)** `= C(m, S̃ − m⌊S̃/m + ½⌋)` (paper `thm:main-codim`).

The repo confirms the divergence concretely: `DLN/Aoyagi/ThetaOrderDistinction.lean` proves at
`d = (2,2,2,2,2)`, `r = 0` (so `ℓ=4`, `a=2`): the component count `numTop = cTheta = C(4,2) = 6`
`≠` `aoyagiPoleOrder 4 2 = a(ℓ−a)+1 = 5`; and `choose_eq_aoyagiPoleOrder_iff` characterizes the
agreement regime as exactly `min a (ℓ−a) ≤ 1` (the four edge cases). **Proved distinct, not cited.**

**API discipline for R2b (name = content):**
- the zeta pole order field must be named for what it is — `rlcm` / `poleOrder` / `multiplicity m` —
  **never** `theta` / `numComponents` / anything reading as a count;
- `RLCTPair.m` is the *analytic* pole order; `Core.cTheta` / `Core.numTop` is the *geometric* count;
  the two must not be `def`-unified, coerced, or `rw`-bridged. The `ThetaOrderDistinction` module is the
  guard: if any future lemma tries to equate them it will fail at the `(2,2,2,2,2)` witness.
- The payoff needs **only `λ`** (`= ½·codim`); it does **not** touch `m`. So even the zeta-primary
  architecture keeps `m` off the payoff's critical path — the `m ≠ θ` distinction is never at risk of
  entering the `½·codim` chain. Good separation; keep it.

---

## 5. Decorrelated Codex cross-check

Fired `local-codex-consult` (gpt-5.4, high effort) with the definition + citation structure framed in,
facts in, **conclusion withheld** (I did not tell it "zeta-pole is sound"; I asked it to adjudicate the
sign map, the well-definedness dependency, the built/cited boundary, and `m ≠ θ`). It ran an
independent web/literature pass and returned a full verdict. _(Env note: the Codex CLI at xhigh on the
long prompt exceeded the 2-min shell cap on the first synchronous attempt — exit 143, as the R0 recon
lesson recorded; a smoke test confirmed it responds, and the full consult ran in background to
completion, exit 0.)_

### 5.1 Codex verdict — AGREES on the core, sharpened three points (all adopted above)

**Agreement (independent confirmation).** Codex confirmed: the sign map `s₀ = −λ`, `threshold(K) =
rlct_x(F) = −s₀`; that `K` vs `|F|` is inert for a nonneg germ (only a sign-*indefinite* `F` needs
`|F|`); that the pole order `m` is genuinely finer than `λ` and is NOT the component count (citing the
paper's own "no simple relationship" remark), so the API must type `m` as "order of the maximal pole",
never a count; and that basic convergence for `Re s ≥ 0` on a relatively compact domain is elementary
(buildable), not part of the monument.

**Three sharpenings Codex added (folded into §§1.1, 1.4, 2.1, 2.3, 3.1):**
1. **The threshold=maximal-pole identity is NOT free from bare continuation.** A *bare* "ζ extends
   meromorphically" axiom does not by itself give `s₀ = −λ`; that identification needs the
   resolution/normal-crossing computation or must be *bundled into the cited statement*. → §2.1 now
   states the **bundled** axiom (paper `propdefn` bundles it; on-point source Saito 2007 /
   arXiv:math/0702056 + SLT), and §3.1 no longer leans on Landau as a free consequence.
2. **The cited theorem's clean input is a smooth `C_c^∞` cutoff `φ`, not a raw indicator `1_U`.** With
   `1_U` the full pole set is cutoff-sensitive; only the maximal pole is robust. → §1.1/§1.4 revised to
   recommend the smooth `φ` form for fidelity to the cite, flagging `1_U` as a simplified variant.
3. **Normal-crossing pole order:** `m` = max number of minimal-ratio divisors that *meet simultaneously*
   on a chart, **not** the raw global count of minimisers. → §2.3 R4 corrected.

**One Codex caveat NOT applicable to the DLN payoff:** the squared-loss factor-of-`½` warning
(`K = G²` ⟹ `threshold(K) = rlct(G)/2`). In the DLN case `K^{DLN}_B = ‖mult−B‖²` **is** the object whose
rlct the payoff computes (Aoyagi/Watanabe are stated for `K^{DLN}_B` directly, `rlct(K^{DLN}_B) =
½·codim`), so there is no hidden extra `½`: the `½` in `½·codim` is exactly the codim/2 bound, already
in the cited bounds. The formaliser must not *additionally* halve. (Confirmed against paper L1876–1891:
`K^{DLN}_B` is the squared Frobenius norm and its rlct — not the rlct of the unsquared residual — is
what equals `½·codim`.) This is a genuine trap Codex surfaced; recorded so R2b does not double-count.

**Net:** the zeta-pole definition is **sound**; the built/cited boundary is as in §6, with the cite
strengthened from "bare continuation" to the **bundled** continuation-plus-threshold-identification
(one monument, faithfully sourced), and the cutoff moved to smooth `φ`.

---

## 6. Summary for the formaliser (R2b spec, at a glance)

| Object | Definition | Status |
|---|---|---|
| `Z_{F,φ}(s)` | `∫ |F|^s φ dvol`, `φ ∈ C_c^∞` `≥0` `φ(x)≠0`, holo for `Re s > 0` | convergence **BUILT** |
| meromorphic continuation, poles ⊂ `ℚ_{<0}`, finite order, **AND `s₀ = −rlct_x`** | bundled | **CITED** (Atiyah 1970 + Saito/SLT) |
| `λ = rlct_x(F)` | `−(largest pole s₀)` = `−s₀ > 0` | **BUILT** (extraction) on the cite |
| `m = rlcm_x(F)` | `ord_{s=−λ} Z` | **BUILT** (extraction) on the cite |
| `λ_zeta = integrabilityThreshold` (Link 1) | `−s₀ = threshold` | **CITED** — must be IN the cite (NOT free from bare continuation) |
| `integrabilityThreshold` value | `sSup{c≥0 : K^{−c} integrable}` | **BUILT cite-free** (R2a); `= λ_zeta` by the cite |
| `rlct ≤ ½codim_ℝ` (Link 2 upper) | Watanabe | **CITED** (already on cordon) |
| `½codim_ℝ ≤ rlct` (Link 2 lower) | Aoyagi | **CITED** (already on cordon) |
| `codim_ℝ = codim_K = C` (Link 3) | real↔complex transfer | **PROVED** (repo) |
| `rlct(K^{DLN}_B) = ½·codim mult⁻¹(B)` | composite | **SOUND**, cites `{continuation-bundled, Watanabe, Aoyagi}` |
| `m = θ`? | — | **FALSE**, proved distinct (`ThetaOrderDistinction`); paper says "no simple relationship" |

**Load-bearing warnings:** (1) `λ = −s₀`, positive, not the negative pole. (2) `s = −c` between zeta
and R2a. (3) nonnegative germ `K` (not `|F|`) for the DLN payoff — and `K^{DLN}_B` is *already* the
squared loss, so **do not add a second `½`**: `rlct(K^{DLN}_B) = ½·codim` is the squared-loss rlct
directly (the `½` is the codim/2 bound, not a squaring artefact). (4) smooth `φ`, not raw `1_U`, in the
cited object (`1_U` only agrees on the maximal pole). (5) `λ_zeta = threshold` is **cited-and-bundled**,
not a free Landau lemma. (6) local pair vs global payoff `rlct = inf_x`. (7) `m` never equals `θ` —
separate names, separate types, off the payoff's critical path.

**Cited surface (the minimum):** ONE bundled continuation monument (Atiyah 1970 continuation + Saito/SLT
"maximal pole = −rlct") for well-definedness of `(λ, m)` AND Link 1 + the TWO DLN evaluation cites
(Watanabe, Aoyagi) already isolated. `λ`, `m` (extraction), the threshold value (R2a), and Link 3 are
built/proved. This is the honest boundary the payoff should read.
