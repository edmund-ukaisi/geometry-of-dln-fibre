# Cert — Aoyagi 2023 paper-map (recon 07), end-to-end at conceptual altitude

*Scout: reconnaissance thread 07 (paper-map). Source: `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf` (31 pp), read as PAGE IMAGES (all formulae pinned to page numbers below). Engine cross-read: `lean/DLNFibre/DLN/RLCT/{Engine,Validate,Foundations}/`. One decorrelated Codex consult fired (`codex/paper-map-{prompt,answer}.md`). Register conventions per `docs/policies/expedition.md`.*

**Register key:** [OBS] observation from source; [CLAIM] believed-with-evidence; [SPEC] plausible-no-evidence; [Q] open.

---

## 0. The single mathematical idea (lead)

[CLAIM] Aoyagi's whole proof is **one uniform idea**: *chartwise log-principalization of the matrix-product ideal by iterated blow-ups along the layer filtration; integrability on each chart is governed by discrepancy-to-vanishing-order ratios `(h_j+1)/(2k_j)`, and the minimum of those ratios over the atlas is reduced to a discrete quadratic optimization (a QIP).* The "cases" are not the theory — they are the charts/stages of the blow-up, and they are DERIVED from the uniform invariant, exactly as the compass's standing counsel demands.

The endgame is the **learning coefficient** `λ` (RLCT) in closed form (Theorem 2). The RLCT reads off the resolution by Hironaka's change-of-variables (§2): after monomialization `K∘π = ∏u_j^{2k_j}`, Jacobian×prior `= ∏u_j^{h_j}`, one has `λ = min_j (h_j+1)/(2k_j)`, `θ = max_u Card{j : (h_j+1)/(2k_j)=λ}` (p.6).

---

## 1. The paper as mathematics, section by section

Numbering is Aoyagi's own (§ headings on the page images). NB: the compass's "§5" = Aoyagi's **Section 5 "Proof of Main Theorem"** (pp.10–27); the construction/"cases" are pp.14–22.

### §1 Introduction (pp.2–5)
[OBS] Sets Watanabe's singular-learning frame. Model `Y=(∏A^{(s)})X+noise`; average log loss `L(w)`; optimal set `W_0={A^{(1)}A^{(2)}=A^{*(1)}A^{*(2)}}`. Free energy expansion `F_n(β)=nL(w_0)+(λ/β)log n −((θ−1)/β)loglog n+o_p(1)` (p.4). **PROVES:** nothing new; it fixes `λ` = RLCT and `θ` = its multiplicity as the targets, and points at sBIC/WAIC as consumers. **Role:** motivates that `(λ,θ)` is the deliverable.

### §2 Resolution of singularities & LCT (pp.5–6)
[OBS] **Definition 1** (p.5): `λ_{w*}(F,φ)=sup{c : ∫_U |F|^{−kc}φ dw<∞}` (`k=1` real), `=` largest pole of the zeta `∫|F|^{kz}φ`; `θ` its order. For an ideal `J=⟨F_1..F_m⟩`, `λ_{w*}(J):=λ_{w*}(∑F_i²)`. **Lemma 1** (cited [30,31,32], p.5): RLCT depends only on the ideal and is **monotone under ideal inclusion** — `G_i∈⟨F⟩ ⟹ λ(∑G²)≤λ(∑F²)`, and `⟨G⟩=⟨F⟩ ⟹ equality`. **Definition 2**: Frobenius norm + `⟨C⟩` = ideal of all entries. Then the **Hironaka read-off** (p.6): apply resolution `π:Q→V` to the Kullback function; `K(π(u))=∏u_j^{2k_j}`, `π'(u)φ(π(u))=∏u_j^{h_j}`, hence `λ=min_U min_j (h_j+1)/(2k_j)`, `θ=max_u Card{j: (h_j+1)/(2k_j)=λ}`.
**PROVES:** the analytic bridge — RLCT is an ideal invariant, computed by any resolution's monomial exponents. **CONSUMES:** Hironaka [15]. **Role:** every later step is "build the resolution, then apply this read-off."

### §3 Multiple-layered NN with linear units (p.6–7)
[OBS] **Theorem 1** (cited [12] = Aoyagi–Watanabe 2005, reduced-rank regression / L=2): the explicit `λ,θ` for the **two-matrix** base case, with `M^{(s)}=H^{(s)}−r`, a set `M⊂{1,2,3}`, `ℓ=Card(M)−1`, `M̃=(∑_{i∈M}M^{(i)})/ℓ`, integer `M`, `a=∑M^{(i)}−(M−1)ℓ`, and `λ=[−r²+r(H^{(1)}+H^{(3)})]/2 + a(ℓ−a)/(4ℓ) − ℓ(ℓ−1)/4·M̃² + ½∑_{i<j}M^{(i)}M^{(j)}`, `θ=a(ℓ−a)+1`. **Role:** the base case the deep induction generalizes; **subsumed** by our engine (which handles all `L≥1` uniformly), so it is not a separate obligation for us.

### §4 Main Theorem (pp.7–9)
[OBS] General deep setup `A^{(s)}: H^{(s)}×H^{(s+1)}`, `s=1..L`. **Definition 3** (p.8): `M^{(s)}=H^{(s)}−r`; the set `M={M^{(S_j)}}` selected by the corank-domination inequalities `∑_{k}M^{(S_k)}>ℓM^{(s)}` (in) / `≤(ℓ−1)M^{(s)}` (out). **Theorem 2** (p.9): the closed-form `λ` (three equivalent algebraic reshapings) and `θ=a(ℓ−a)+1`, generalizing Theorem 1 to all `L`. **Example** (all `M^{(s)}` equal): `λ=[−r²+2rH^{(1)}]/2 + a(L−a)/(4L) + (L+1)/(4L)(M^{(1)})²`, `θ=a(L−a)+1`; Figure 1 plots `λ,θ` vs `L`. **PROVES:** the headline formula (statement only; proof is §5). **CONSUMES:** §2, §3, and §5.

### §5 Proof of Main Theorem (pp.10–27) — the mechanism
The engine. Digested at altitude in §2 below; the four moving parts:
- **Lemma 2 + its proof** (pp.10–11): the **rank normal form** — any variable matrix `A` of rank `r_1` with a chosen regular `r×r` block `A_1` is reduced by *unipotent* `Q_1` (lower), `Q_2` (upper) to `[A_1 0; 0 C_4]`, `rank C_4=r_1−r`, via the explicit Schur complement `C_4=−A_3A_1^{-1}A_2+A_4`; the off-diagonal variables are **transformed to new coordinates** `F_2=−A_1^{-1}A_2`, `F_3=−A_3A_1^{-1}`. This is the atomic change-of-variables of the reduction.
- **Theorem 3 + proof** (pp.11–13): the **global regular peel** — an induction on the layer index `S` applies Lemma-2-style unipotent CoVs to block-diagonalize the whole product: `P_1(∏A^{(s)})P_2=[C_1 0; 0 ∏_{s=1}^L C^{(s)}]`, `C_1` regular `r×r`, `C^{(s)}` of size `M^{(s)}×M^{(s+1)}` (the **coranks**). Subtracting the true `diag(E_r,0)` and reading `Lemma 1`, the ideal splits into `r²+r(M^{(1)}+M^{(L+1)})` **transverse smooth generators** (`C_1−E_r`, `F_2`, `F_3`; each a nondegenerate coordinate, contributing `½` to `λ`) PLUS the pure corank-product ideal `⟨∏C^{(s)}⟩`. So (p.13) `λ⟨∏A−∏A*⟩ = [−r²+r(H^{(1)}+H^{(L+1)})]/2 + λ_O⟨∏_{s=1}^L C^{(s)}⟩`.
- **Theorem 4** (cited [22], p.14): the **deepest-point method** — for homogeneous generators, `λ` at the origin `(0,..,0)` is `≤` the LCT at any shifted point. Justifies computing `λ_O⟨∏C^{(s)}⟩` **at the origin** (all coranks zero), the worst singular point.
- **The recursive blow-up** (pp.14–22): monomializes `⟨∏C^{(s)}⟩` — see §2.

### §6 Conclusions (pp.27–28)
[OBS] `λ` **bounded as `L→∞`** (the abstract's headline: deep linear nets are "mildly singular", `λ ≪ dim`), while `θ→∞`. References [12]=base, [15]=Hironaka, [22]=deepest-point.

---

## 2. Her endgame precisely: the recursive monomialization + `λ` read-off

### 2.1 The invariant (the uniform object; pp.14–15)
[CLAIM] A **double induction on `(S,J)`** (`S` = layer processed `0..L+1`, `J` = pivots cleared in layer `S`). Carried objects: a running-min corank `M(S)=min{M^{(s)}:s≤S}`; per-blow-up-coordinate `u_{s,k}` a **vector** `T_{s,k}=(t^{(1)}_{s,k},..,t^{(L)}_{s,k})` and its running min `t̃_{s,k}=min_{S'} t^{(S')}_{s,k}`; a Jacobian exponent `M_{s,k}`. **Definition 4** (p.14): the partial order `T≤T'` componentwise. The inductive statement (p.14):

$$\langle \textstyle\prod_{s=1}^L C^{(s)}\rangle = \langle \operatorname{diag}(b_1,\dots,b_{M(S)})\,[E_J\;0;\,0\;D_J]\,\textstyle\prod_{s=S+1}^L C^{(s)}\rangle,$$

with `b_i` monomials in the `u_{s,k}` (`b_0=1`, `b_i=∏_{t̃_{s,k}=i-1}u_{s,k}·b_{i-1}` — the **divisibility chain**), `D_J` the residual un-cleared block, and a **monomial Jacobian** `∏du_{s,k}^{M_{s,k}−1}` (p.15). A **total-comparability** invariant `T_{s,k}≤T_{s',k'} or ≥` holds throughout — this is what makes the p.15 minimality tie-break well-defined.

[OBS, Codex correction] A diagonal-of-monomials is a *principalization* only with the divisibility chain + SNC-divisor structure + the monomial-Jacobian form all present. This is precisely why the engine carries `bChain : Monotone bExp` at TYPE strength (compass fork 3): flattening it is a type error, not just a battery failure.

### 2.2 The cases = charts/stages of the blow-up (pp.15–22)
[CLAIM] Each blow-up event resolves one more of the structure; its "cases" are the coordinate charts:
- **Case 1** (p.15): a *run* `b_{J+1}=..=b_{J+J_1}`, `b_{J+J_1+1}≠` (the **`J₁` gap condition**: `{t̃=i}=∅` for `i` in the run interior). Blow up along `{d_{ij}=0, u_{s,k}=0}`; fix the `T`-minimal `u_{s,k}` attaining `t̃=J+J_1` (the **p.15 minimality tie-break**, Def 4). Two charts:
  - **1(1)** (p.16): factor `u_{s,k}` across the whole run of rows (`b'=u·b`), exponent bump `M'=M+J_1(M^{(S+1)}−J)`; does NOT advance `J`; decrements the count `{u:t̃=J+J_1}` by one.
  - **1(2)** (pp.16–18): the corner becomes a unit; unipotent `Q` (columns) then `P` (rows, ratios `b'_{i}/b'_{J+1}`) clear one pivot `E_J→E_{J+1}, D_J→D_{J+1}`; exponent same increment; **advances `J`** by one.
- **Case 2** (pp.19–21): the uniform-run/**layer** step — `b_{J+1}=..=b_{M(S)}`. Blow up the whole residual block; factor `u_{S,J+1}`, exponent `(M(S)−J)(M^{(S+1)}−J)`; clear one pivot; **`J` increases by exactly ONE per Case-2 step** (p.21 — a `+=resRows` fast-forward would DROP the strictly-smaller-exponent divisors of the skipped steps, one of which can be binding: this is the compass's page-21 truth-witness catch). When `J+1>min(M(S),M^{(S+1)})` the block is exhausted → **advance `S→S+1`**, folding in `C^{(S+1)}` (via `C'^{(S+1)}=Q^{-1}C^{(S+1)}`).

[OBS, Codex nuance] "Cases = charts of ONE blow-up" is right only for 1(1)/1(2) (two charts of the single Case-1 blow-up); Case 1 vs Case 2 are DISTINCT blow-up events (within-run vs whole-block/layer). The engine's edge-carrier already models this: one Case-1 blow-up emits both a 1(1) and a 1(2) edge (fork 7).

### 2.3 Termination + `λ` read-off (p.22)
[CLAIM] At `S=L+1`: `⟨∏C^{(s)}⟩=⟨diag(b_1,..,b_{M(L+1)})⟩` — fully monomial (the engine's `IsFullMonomialization`). Per-chart candidate:

$$\lambda_{\text{chart}}=\tfrac12\min\{M_{s,k}:\tilde t_{s,k}=0\},\qquad M_{s,k}=(M^{(1)}-t^{(1)})(M^{(2)}-t^{(1)})+\textstyle\sum_{j=2}^{L}(t^{(j-1)}-t^{(j)})(M^{(j+1)}-t^{(j)}).$$

[OBS, Codex correction — precision] `M_{s,k}` is `h_j+1` with `k_j=1` for the `t̃=0` divisors; the Jacobian *power* is `M_{s,k}−1`. So `½·M_{s,k}=(h+1)/(2·1)` is the correct Hironaka ratio. The engine is faithful: `LeafJacobian` carries `|det Dβ|=∏|u|^{divExp−1}` (the `h=divExp−1` power) and the threshold is `divExp/2` (`region_glue`'s `hrat : c'<e/2`).

### 2.4 The optimization → closed form (pp.22–25)
[CLAIM] Reparametrize `M_{s,k}` via a decreasing subsequence `H_i` of the `t^{(j)}` and increments `F_j=H_{j-1}−H_j+M^{(S_{j+1})}`, giving a sum of squares (p.23). **Lemma 3** (p.24, the QIP): `min_b A(b)=a·ℓ(ℓ−a)` at `b=a-1` or `a`. This yields Theorem 2's `λ`. **`θ`** (pp.25–27): **Lemma 4** bounds, **Lemma 5** gives `θ=a(ℓ−a)+1` by counting how the `T`-vectors distribute; explicit attaining charts `T_{s,k}` in Eqs (1)–(5) (pp.26–27).

[OBS, Codex correction] `θ` does NOT "count achieving charts"; per Def 1 (p.6) it is `max_u Card{j:(h_j+1)/(2k_j)=λ}` — the maximal number of critical divisors coinciding with `λ`-ratio at one point. (θ is out of scope for the engine; stated correctly here for the record.)

### 2.5 Analytic framework + bridge obligations
[CLAIM] The framework is **Watanabe's** `λ` = LCT = largest zeta pole (Def 1), read off the resolution by Hironaka's **change-of-variables equality** (§2, p.6). Her `λ` theorem consumes: Lemma 1 (ideal invariance), Theorem 3 (regular peel), Theorem 4 (deepest point), the §5 monomialization, Hironaka [15], and Lemma 3 (QIP). Bridge obligations to make it a two-sided equality: (i) the resolution is a genuine **proper log-principalization** (SNC + monomial pullback + a covering), (ii) the CoV transports the LCT **exactly** (both directions).

---

## 3. The two mint paths, priced (by hypothesis list)

**Decisive finding (verified in Lean, load-bearing):** the `≤`-half of the RLCT equality — **achiever divergence** `λ≤½·minAdm` — is **ALREADY PROVEN sorry-free for general `L`** (`routeMCore_box_diverges_achiever_full'`, `Validate/RouteMAchieverFullHNoFree.lean`, 0 sorry), and `r1_resolution_general` folds it with the finiteness half into the reduced-core value `= ofReal(lambdaCore M)`, **sorry-free, conditional ONLY on hbox**. The full headline `aoyagi_learning_coefficient_gen` (`Validate/HeadlineGenAssembly.lean:55`) is clean-three conditional SOLELY on `hbox=RouteMBoxThresholdFinite (H−r)` — it uses **NO** `cited_aoyagi_dln`, `monomial_rlct`, or `sorryAx`.

Consequence: **the ONLY open content standing between us and the unconditional, cite-free `λ`-equality is `hbox` = the finiteness (`≥`) direction = the coverage-hard side.** Discharging `hbox` and repointing the canonical `aoyagi_learning_coefficient` (`Skeleton.lean:1685`, still on the cite) to `_gen` DELETES `cited_aoyagi_dln`.

The inequality bookkeeping (Codex-confirmed) is why this is decisive:

| Claim | Meaning | Coverage (exhaustive atlas) needed? |
|---|---|---|
| `λ ≥ ½·minAdm` (= **hbox**) | integral finite for every `c'<½minAdm` | **YES** — miss one chart with a smaller ratio and finiteness is false |
| `λ ≤ ½·minAdm` (**banked**) | divergence at the attaining chart | NO — one chart/valuation suffices |

### Path A — engine → hbox → the proven assembly (the current default)
Hypotheses (what remains to build):
- `monomialization_terminates M` (`EngineObligations.lean`) — build the resolution tree into `CanonicalResolution` (the ONE structural hole; owns coverage `ChartBridge`, the step ledger `StepRel`, `IsFullMonomialization`, the exponent hooks).
- `region_glue M hbridge c' hrat` (`EngineObligations.lean`) — the ONE analytic hole: per-chart integration → box finiteness, via the Mathlib area formula on `chartMap=ψ∘β` (upper det bound) + banked monomial/radial atoms + the scaling bridge, glued over the finite subcover.
- Then `hbox` is discharged; `aoyagi_learning_coefficient_gen` (already proven) becomes unconditional.

Covered by banked substrate (survey-before-build; all sorry-free unless noted):
- QIP / `λ`-formula: `minAdm`,`Mval`,`Adm`,`admBound`,`lambdaCore`,`aoyagiLambda` (`Foundations/Lambda.lean`,`Validate/RouteMLayerSplit.lean`) — Aoyagi's `M_{s,k}`+Lemma 3, with build-time `#eval` ground-truth checks.
- The `≤`-half (achiever divergence): `routeMCore_box_diverges_achiever_full'`, folded by `r1_resolution_general` (both sorry-free).
- Deepest point (Theorem 4): `deepest_le_of_homogeneous_core` (`Validate/DeepestMinRlct.lean:157`, hypothesis-free).
- Regular peel / value side (Theorem 3 shift): `reg_shift_add_core_eq_aoyagiLambda`, `DeepestFrontGaugeGen`, `HeadlineRowColPermWLOG`, `D1Ge*` (all wired sorry-free in `_gen`).
- Terminal atoms + cover/null + transport families (`RouteMSJ*Atom/QBoxCore/ProductTube/Radial*`, `S1Cover`, `S1NonMPTransport`, `ParamsFlatLinear`).
- MP box-reduction `routeMCore_le_matBox` (S2-free).

Genuinely new Lean work: **coverage** (`ChartBridge`, in `monomialization_terminates`) + **`region_glue`** + the **construction tide** (the resolution-tree build: `stepUpdate`/`StepRel` ledger, μ-lex termination `conRel_wf` [done], the per-case descent, and the deferred `genDivExp` support redesign + full-`T` bookkeeping under the fork-10 reframe).

### Path B — transcribe her native `λ` theorem (candidate second path)
[CLAIM] Path B does **not** exist as a shorter route to the `λ`-equality. Her native equality *contains* Path A's hard finiteness/coverage content (Codex Q2): `λ≥C` needs coverage regardless of framing. What Path B would add over the *shared* mechanism is either (i) already banked (the `≤`/divergence half — `routeMCore_box_diverges_achiever_full'`) or (ii) explicitly out of scope (`θ`, the full `T`-vectors, the attaining-chart Eqs (1)–(5), Lemmas 4–5).

- EXTRA beyond the §5 mechanism: essentially nothing the engine doesn't already hold. B2 (the one-chart local divergence transport) — the only "new" analytic piece a from-scratch Path B would need — is **already discharged** in-tree. The zeta/pole apparatus is not needed (Def-1 `sup`-of-finiteness suffices, both directions already framed). Multiplicity `θ` is not needed for `λ`.
- SKIPS: nothing structural. It cannot skip coverage (the hard part). It could re-frame the box-threshold as a direct Hironaka read-off, but that is a presentation change, not a cost saving — the monomialization is shared and mandatory.
- Alternative cheaper `≤` (Codex Q2, for the record): prove `minAdm=codim` of a smooth stratum in the zero set, then Watanabe's universal `λ≤½·codim` gives the `≤` half without a chart. Our engine instead uses the achiever chart (already banked); the codim route is a NON-adopted alternative, and its `minAdm=codim` identification is itself nontrivial.

### Effort ranking of the new pieces (hardest named object first)
1. **HARD — the coverage / no-smaller-ratio theorem** (`ChartBridge` inside `monomialization_terminates`; landmark `coverage-theorem`). The **hardest named object** (binding rule): the *exhaustive proper log-principalization atlas* — that the enumerated charts COVER a neighbourhood of the zero locus AND that no untracked divisor gives a ratio `< minAdm`. Aoyagi ASSERTS "by a blow-up process" and never proves coverage as a theorem (Codex Q3); it is the irreducible new obligation, on either path, and holds a permanent lane. Kill-condition (compass): a decorrelated hunt for an untracked smaller-ratio divisor must come back empty (not "established" without it).
2. **HARD/MEDIUM — `region_glue`** (analytic hole): per-leaf area-formula integration (`ψ∘β`, upper det bound) + resRank/2 Morse-core threshold + scaling-bridge globalization + finite-subcover glue. Statement-soundness already twice repaired (resRank fold; bounded/measurable `srcBox`) — the compass's obligation-statement discipline applies.
3. **MEDIUM — the construction tide** (`monomialization_terminates` body): the resolution-tree build with the faithful `stepUpdate` ledger (rung 1, page-verified) + per-case μ-descent (rung 2B) + the deferred `genDivExp` support redesign and full-`T` bookkeeping (fork-10 un-deferrals). μ-lex termination `conRel_wf` is DONE.
4. **MECHANICAL — wiring**: repoint canonical `aoyagi_learning_coefficient`→`_gen`, delete `cited_aoyagi_dln`, once `hbox` lands.

---

## 4. Deltas against our current engine (fidelity flags for the fork-10 reframe)

[CLAIM] Well-matched (name = content):
- `divExp`↔`M_{s,k}`, `divTilde`↔`t̃_{s,k}`, `cleared`↔`J`, `layer`↔`S`, `bExp`/`bChain`↔the `b_i` divisibility chain. `stepUpdate` case clauses are page-pinned (1(1) p.16, 1(2) p.17, 2 p.20+p.21 `+=1`). `Mval`/`Adm`/`admBound` = Aoyagi's `M_{s,k}` + admissible cone (incl. the `j=1` block bound `min(M^{(1)},M^{(2)})`, p.8 Def 3).

[CLAIM] Genuine deltas (all already named as compass rungs, none new):
- **Full `T`-vector dropped to `t̃`.** Aoyagi carries `T_{s,k}=(t^{(1)},..,t^{(L)})`; the engine stores only the running-min `t̃` (+ `divExp`). Sound for `hbox`/finiteness (fork 9 — the certificate never reads full `T`), but the p.15 **minimality tie-break** (lex-min `T` per Def 4) and the **`J₁` gap condition** need the full vector; both are deliberately-uncaptured in `StepRel`'s docstring and are the construction tide's rung-3/4 burden (the divisor-chooser). This is the fork-10 fidelity gap — flagged, owned, on-path.
- **`support : Fin numGen → Finset` is a binary (nonzero-locus) approximation** of Aoyagi's sharing (the accumulating `b_i` products). Support propagation balloons across per-divisor re-indexing (STOP-AND-SURFACEd, rung 1); the named `gendivexp-support-redesign` rung restores multiplicity-valued fidelity. Guard: the exact `LeafPullback` identity, not propagation, breaks coupling for the certificate.
- **`resRank` Morse-core fold.** Aoyagi separates the regular peel (closed-form `[−r²+r(H^{(1)}+H^{(L+1)})]/2`) from the singular min; the engine's `terminalExponents` folds a `resRank` Morse residual into the same per-leaf threshold. Consistent (the `λ`-formula keeps the peel separate in `aoyagiLambda`; the fold is only local box-finiteness bookkeeping), but worth a bedrock note: `resRank≥minAdm` is a truth-witness the tide OWES (never assumed).
- **The regular peel (Theorem 3 block-diagonalization) is NOT itself formalized in the engine.** The engine starts from the corank-product `⟨∏C^{(s)}⟩` origin (`routeMCore = frobSq(prod M A)` at 0); the peel's `[−r²+..]/2` shift lives in the DOWNSTREAM value lane (`reg_shift_add_core_eq_aoyagiLambda`, `DeepestFrontGaugeGen`), which is banked sorry-free. So Theorem 3 is discharged by the assembly, not the engine — fine, but note it is NOT "her mechanism built in the engine"; a fully-faithful free-standing library (fork-10 spirit) would transcribe Lemma 2 + Theorem 3 as first-class objects. [Q] Is that in scope, or does the banked value lane satisfy the reframe? (recommend: value lane suffices for `λ`; Theorem 3 transcription is a distinct-bet, not critical-path.)

[CLAIM] No delta / engine is MORE uniform: Theorem 1 (L=2 base) is subsumed; the engine's single recursion covers all `L≥1`.

---

## 5. Recommended transcription roadmap (rung-sized; hard parts front-loaded)

Free-standing library = **the §5 mechanism as the shared core**, with `hbox` the thin adapter. Honors the operator's full-mechanism reframe: what her paper builds (the resolution), we build; the deferrals are un-deferred into the tide.

- **R0 (done/banked):** the `λ`-formula QIP (`minAdm`/`Mval`/`Adm`/`aoyagiLambda`), the `≤`-half (achiever divergence), the value lane + regular-peel shift, the deepest-point domination, μ-lex termination. Survey confirms: do NOT rebuild.
- **R1 — construction carrier + faithful ledger (medium):** `ResolutionTree`/`StepData`/`Edge` (done); `stepUpdate` faithful exponent/clearing ledger (rung 1, done); per-case μ-descent + KILL-condition (rung 2B). Front the full-`T`-vector carrier here (rung-3 divisor-chooser: minimality tie-break + `J₁` gap) — the fork-10 un-deferral.
- **R2 — coverage / no-smaller-ratio (HARD; the hardest named object — front-load, permanent lane):** prove `ChartBridge` for the built tree: image-cover of a zero-locus neighbourhood + a.e.-injective charts + `IsFullMonomialization`, WITHOUT `rlct=c*`. Gate: the exhaustiveness hunt (Tier B/C, decorrelated) returns no untracked smaller-ratio divisor. This is Aoyagi's implicit "by a blow-up process" made a theorem.
- **R3 — `region_glue` (hard/medium; analytic):** per-leaf area-formula integration on `ψ∘β` + resRank/2 Morse threshold + scaling-bridge globalization + finite-subcover glue → `hbox`. Prophylactic: the abstract-carrier-field pass (compass obligation-statement discipline) before the discharge lands.
- **R4 — `genDivExp` support redesign (medium; fidelity):** multiplicity-valued `genDivExp : Fin numGen → Fin numDiv → ℕ`, restoring sharing-propagation faithfulness. Kill-condition: `g-coupled-binding-334`/`g-delta-flatten` re-checked.
- **R5 — wiring (mechanical):** discharge `hbox`; repoint canonical headline → `_gen`; delete `cited_aoyagi_dln`.
- **R6 (distinct-bet, OPTIONAL, not critical-path):** transcribe Lemma 2 + Theorem 3 (the regular peel) as first-class library objects for full fidelity; and — separately — `θ` + Eqs (1)–(5) if the multiplicity ever comes into scope.

---

## Close (reflection)

- **Most likely to advance the expedition:** the decisive finding that the `≤`-half is banked and `_gen` is clean-three conditional solely on `hbox`. It collapses the "two mint paths" question: there is **one** critical path (build `hbox` = coverage + `region_glue`), and it simultaneously kills `cited_aoyagi_dln`. Path B is not a shorter alternative.
- **Most likely to break:** the **coverage / no-smaller-ratio** theorem — Aoyagi never proves it, and an untracked chart with a smaller ratio would falsify `hbox` as stated. The kill-condition (decorrelated exhaustiveness hunt) must stay armed; a monomial-only hunt passes vacuously.
- **Next computation that would clarify:** a small-`L` explicit chart-atlas closure check at a corank-2 instance (e.g. `M=(2,2,2)` or `(3,3,4)`) — enumerate the blow-up charts the construction emits and verify (a) they cover the zero-locus neighbourhood and (b) `min` of per-chart `½·M_{s,k}` equals `½·minAdm` with NO chart undershooting. This directly stress-tests R2's kill-condition against the banked `g-coverage-sharing-killcond` / `g-coupled-binding-334` witnesses and is the cheapest probe of the one thing most likely to break.

**Recommended bet: Path A.** One critical path (`hbox` = coverage + `region_glue`), cite dies for free via the already-proven `_gen` + banked divergence half; Path B adds only out-of-scope or already-banked content.

---
**DATED CORRECTION (2026-07-18, controller; source: cert-cov-rungs12 item 3 + page-pin-centers).**
§2.2's "Two charts: 1(1)/1(2)" reading is imprecise: 1(1)/1(2) are pivot TYPES of the ONE Case-1
blow-up (u-pivot vs d-entry-pivot), and the full chart family per node has d_center =
J₁·(M^(S+1)−J)+1 members (Aoyagi shows the corner d-pivot as REPRESENTATIVE; "by a blow-up
process" covers the rest). A two-edge-per-node emission is unsound for coverage at d_center ≥ 3
(the corner gap, kernel-witnessed by corner_chart_not_cover). Page-verified twice (page-pin-
centers.md; rev-cov independent read + Codex).
