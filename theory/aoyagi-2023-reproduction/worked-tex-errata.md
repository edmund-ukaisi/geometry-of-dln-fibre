# worked.tex errata — Aoyagi 2023 reproduction vs source PDF (image pass)

**Charge (task #63, amended):** a chunk-by-chunk cross-check of `aoyagi-2023-worked.tex` against the
**source PDF read as images** — `paper-sources/aoyagi-2023-consideration-of-learning-efficiency-of-dln/aoyagi-2023-neural-networks-preprint.pdf`
(31 pp., the canonical SSRN preprint). Per chunk: (i) UPLIFT — does worked.tex reproduce every formula,
hypothesis, index range, case boundary, and the **prose intent** faithfully? (ii) COVERAGE — tag the chunk
against its Lean render (feeds `threads/paper-coverage-audit.md`).

**ANCHOR-FREEZE (binding).** worked.tex line numbers are load-bearing (rulings §0–§11, certificates, lemma
docstrings all cite them). This file records findings; it does **not** authorise line-shifting edits to
worked.tex. Each item: source page + visual location · worked.tex line · discrepancy verbatim (both sides) ·
severity (MATH ERROR / omission / presentational) · downstream blast radius.

## Chunk map (progress tracker)

| Chunk | Source pp. | Content | worked.tex | Formula/index check | Prose-intent check |
|---|---|---|---|---|---|
| C0 | 1–4 | setup/notation: model `Y=∏A^(s)X`, loss, Kullback, free energy, sBIC; `H^(s)`, `M^(s)=H^(s)−r`, ∏ order | §0–1.1 | ☐ TODO | ☐ TODO |
| C1 | 5 | Def 1 (rlct/order) · Lemma 1 (ideal-inv) · Def 2 (‖C‖,⟨C⟩) | §1.2 | ✅ done | ✅ done |
| C2 | 6 | Hironaka monomial rule `λ=min min (h+1)/(2k)`, order `=max Card` | §1.3 | ✅ done | ✅ done |
| C3 | 6–7 | Thm 1 (RRR, L=2) + M-set (L=2) | §2.1 | ✅ done | ✅ done |
| C4 | 8 | Def 3 (general-L M-set) | §2.2 | ✅ done | ✅ done |
| C5 | 9 | Thm 2 (general-L λ, 3 forms) + order + equal-width example | §2.2 | ✅ done | ✅ done |
| C6 | 10–11 | Lemma 2 (block elimination) | §3.1 | ✅ done | ✅ done — faithful (see note) |
| C7 | 11–13 | Thm 3 (product reduction) | §3.2 | ✅ done | ✅ done — faithful (see note) |
| C8 | 14 | Thm 4 (deepest point) + inductive setup + Def 4 | §4 open | ✅ done | ☐ TODO |
| C9 | 15–22 | recursion: inductive invariant + `b_i` + Jacobian + Cases 1&2 + `M_{s,k}` | §4.recursion | prior pass | ☐ re-touch (highest blast: wall #38) |
| C10 | 23 | `M_{s,k}` completion-of-squares | §4.candidates | prior pass | ☐ TODO |
| C11 | 24 | Lemma 3 (within-set balance) | §4.lemma3 | prior pass | ☐ TODO |
| C12 | 25–27 | Lemmas 4–5 (order θ) + `t_{s,k}` construction | §4.order | prior pass | ☐ TODO |
| C13 | 27–31 | Conclusions + references | §6 | ✅ done | ✅ done |

Legend: ✅ done this pass (2026-07-23) · prior pass = image-verified by the earlier owed-math-audit
(`verify-owed-math-audit.md`), coverage-row only, no re-verification · ☐ TODO/re-touch. The full PDF pp.1–31
has been image-read once this pass; the ☐ items are the deeper **prose-intent** re-verification (her remarks
on why/when a step applies) not yet done — the C6/C9 recursion+Lemma-2 region is highest-blast (the wall #38
anchors to Lemma-2/merge-step semantics) and is next.

## Errata items

### E-1 — Lemma 1 inequality direction flipped (MATH ERROR; low blast; Lean unaffected)

- **Source:** p.5, Lemma 1 ([30,31,32]): *"We have `λ_{w*}(G₁²+⋯+G_m²) ≤ λ_{w*}(F₁²+⋯+F_n²)`, if
  `G₁,…,G_m ∈ J`."* (`≤`.)
- **worked.tex:** line 166: `$\rlct_{w^\ast}(G_1^2+\cdots+G_m^2)\ge\rlct_{w^\ast}(F_1^2+\cdots+F_n^2)$.` (`≥`.)
- **Discrepancy:** the inequality direction is reversed. Correct direction is `≤` (the source's):
  `G ∈ J ⟹ ∑G² ≤ c·∑F²` pointwise near `w*` (Cauchy–Schwarz on `G_i = ∑a_{ij}F_j`) ⟹ the `G`-integral is
  harder to converge ⟹ `rlct(∑G²) ≤ rlct(∑F²)`. Concrete: `F=x`, `G=x²∈⟨x⟩` ⟹ `rlct(x⁴)=¼ ≤ rlct(x²)=½`.
  The flip also contradicts worked.tex's **own** fnote (line 174: derives `∑G² ≤ c∑F²`).
- **Severity: MATH ERROR** (a wrong mathematical statement in the reference).
- **Blast radius: LOW.** The Lean object is correct (`Core.Aoyagi.IdealInvariance.rlctAt_sumSqFam_le_of_germRepresents`
  proves `≤`); Lemma 1's *usage* everywhere is the symmetric equality ("same ideal ⟹ same rlct"), which the
  flip does not corrupt. No ruling or lemma docstring anchors to line 166's inequality *direction* (they cite
  the equality). So this is a reference-doc statement-line typo, not a downstream hazard.
- **Correction — APPLIED (CLOSED).** `\ge` → `\le` on line 166, a single-token swap shifting no line
  numbers (anchors held). Landed by the controller at commit **e02610619**. Item retained here for the
  record; status CLOSED.

*(No other discrepancy found in the front-matter chunks C0–C8, C13.)*

### Prose-intent notes (no discrepancy — faithful)

- **C6 (Lemma 2) + C7 (Thm 3) — FAITHFUL, including the load-bearing intent.** worked.tex §3.1–3.2 carries
  Lemma 2's key point (Q₁,Q₂ *unipotent* ⟹ RLCT-preserving via Lemma 1, unit-Jacobian local iso; fnote
  :416–421) and Thm 3's induction. **Wall-relevant (highest-blast):** the accumulated recoord
  `A'^{(S+1)} = Q₂'⁻¹ A^{(S+1)}` (worked.tex:445) — the accumulated-`Q₂'⁻¹` current-chart semantics that
  this expedition's F₂ ruling (branch-(iii) input compensator + the §8(m) scope) is built on — is
  faithfully transcribed from source pp.11–13. No omission; nothing the wall #38 anchors to is dropped.
- **C9 (the recursion, pp.15–22) prose-intent re-touch — PARTIAL** (the merge region pp.15–18 done for the
  MergeBoostSplit check below; the rest — Case 2 pp.19–22, the `M_{s,k}` read-off — pending). Formulas were
  image-verified by the prior owed-math-audit (Cases-1/2 exponents, the (T-C)/(T-E)/(T-F) ledger).

### C9 finding — `MergeBoostSplit` predicate fidelity (folded from team-lead; on the wall's path, gates capstone review)

Checked the Lean predicate `MergeBoostSplit` (`lean/DLNFibre/DLN/Aoyagi/MergeBoostSplit.lean`) against
Aoyagi's separated normal form at the merge (source pp.15–18, image-read: the invariant
`diag(b)·[E_J|D_J]`, `b_i = (∏_{t̃_{s,k}=i−1} u_{s,k})·b_{i−1}`; Case 1(1), p.16). **VERDICT: FAITHFUL on
(a)/(b)/(c).**

- **(a) single reused pivot `e₂` — FAITHFUL.** Case 1(1) (p.16) factors the ENTIRE `J₁`-row equal-run block
  through a SINGLE exceptional `u_{s,k}` (`block = u_{s,k}·[d']`); the boost is `b'_i = u_{s,k}·b_i` on each
  run row, and one exceptional is absorbed per step (`#{u | t̃=J+J₁}` drops by one). The "multiple carried
  exceptionals" is the ACCUMULATED ledger `b_i = ∏u` (history across steps), NOT the per-step reuse — a
  case11 STEP reuses exactly one. `e₂ = canonPivotOf` (single) is the right generality for the case11 edge.
- **(b) center-ignoring coefficients — FAITHFUL.** After factoring `u_{s,k}=e₂` once, the residual quotients
  `d'_{ij}` are clean (do NOT re-carry `e₂`); the lower-exceptional monomials `b_i` and the clean `D_J`
  entries live in coordinates that are NEITHER `e₂` NOR the current partial block — so a `β` = (b-ratio
  `b_i/b_1`)·(clean `d'`) is continuous and center-ignoring, exactly the wall's "non-dominant b-chain
  coefficient" content. The `hex` guard (extra ∩ center = ∅; "e₂·(e₂+uᵢ) would fail IgnoresCoords") is the
  necessary and matching condition — Aoyagi's single-factoring respects it.
- **(c) per-slot pivot-XOR-free (no `e₂²`) — FAITHFUL.** The E_J/D_J separation puts the pivot in exactly one
  place: the boosted `b'_i = u_{s,k}·b_i` carries `e₂` to the FIRST power; the residual `d'` is clean of it;
  and `e₂ ∉ part`, `extra ∩ center = ∅` keep both summands `e₂`-degree ≤ 1. So each slot is degree-1 in `e₂`,
  no square — precisely the disjunction the consumers want.

**HONEST CHARACTERIZATION (not a defect):** the predicate is the *continuous-coefficient* consumer interface
(α/β continuous + center-ignoring), sufficient for the `Deg1SupportedOn` consumer; the *exact-monomial*
b-ledger is not asserted by the predicate — it is derived by the concrete content lemma
`foldResid_case11_mergeBoostSplit_canon` (LIVE frontier, canonFlatten-stated). So `MergeBoostSplit` faithfully
renders Aoyagi's normal form AT THE CONSUMER INTERFACE; the exact-monomial fidelity is deferred into the
content lemma (correctly — that is where the concrete `coreGen`-at-`canonFlatten` lives). The
`part = supportAt ∩ center` / `extra = supportAt ∖ center` partition matches her run-vs-rest `D_J` split. No
fidelity gap; the guards (`e₂ ∈ center`, `part ⊆ center`, `e₂ ∉ part`, `extra ∩ center = ∅`) are load-bearing
and all match her construction.
