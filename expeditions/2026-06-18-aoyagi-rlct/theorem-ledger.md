# theorem-ledger.md - source to Lean dependency ledger

This table is controller memory. Every source theorem or lemma that can affect
the final statement gets one row. Keep source references page-pinned; avoid
holding PDF line numbers only in context.

| Source item | Local claim | Source ref | Dependencies | Reproduction/status | Lean target/status | Review/status |
|---|---|---|---|---|---|---|
| RLCT definition and normal-crossing extraction | A0 | Aoyagi background, pages TBD | external analytic theorem | cite-interface check pending | interface TBD; open/Cited | pending |
| Theorem 1, cited three-layer formula | context/special case | PDF pp. 6-7 | prior result [12]; likely derivable from Theorem 2 at `L=2` | pending/optional | no Lean target yet | pending |
| Theorem 2 multi-layer main formula | A6 | PDF pp. 8-9 | A0-A5 | pending | final theorem TBD; open | pending |
| Lemma 2 block elimination | A1 | PDF pp. 10-11 | matrix rank/open block hypotheses | draft + partial check: `threads/03-block-product-reduction/reproduction-draft.md`, `threads/03-block-product-reduction/reproduction-check.md`; algebraic chart identities checked only | `schurComplement_leftBlockElim_fromBlocks`, `schurComplement_blockElim_fromBlocks`; proved in `lean/DLNFibre/DLN/Aoyagi/BlockElimination.lean`; rank formula still open | reviewed first tide; statement card `threads/03-block-product-reduction/statement-card-a1-block-identities.md` |
| Theorem 3 product reduction | A2 | PDF pp. 11-13 | A1, product/block notation, through-layer open-chart/basis lemma | draft + failed full check: `threads/03-block-product-reduction/reproduction-draft.md`, `threads/03-block-product-reduction/reproduction-check.md`; not formalisation-ready as stated | split algebraic induction target TBD; open | findings pending resolution |
| Theorem 4 deepest singular point | A3 | PDF p. 14 | A2, analytic/global comparison | scout report: `threads/02-analytic-interface/scout-report.md`; scope conflict under current citation rule | no Lean target until restricted proof/avoidance chosen | pending |
| Blow-up inductive statement | A4 | PDF pp. 14-15 | reduced product coordinates | draft reproduction + failed check: `threads/04-blow-up-certificate/reproduction-draft.md`, `threads/04-blow-up-certificate/reproduction-check.md`; width notation and invariant gaps block | invariant theorem TBD; blocked | failed check |
| Blow-up Case 1 | A4 | PDF pp. 15-18 | reduced product coordinates, inductive statement | draft reproduction + failed check: actual width `M^{(S+1)}` vs prefix minimum `M(S+1)` must be repaired; missing pivot charts unresolved | transition lemma TBD; blocked | failed check |
| Blow-up Case 2 | A4 | PDF pp. 19-22 | reduced product coordinates, inductive statement | draft reproduction + failed check: actual widths, pivot charts, regularity/divisibility, and boundary cases unresolved | transition lemma TBD; blocked | failed check |
| Terminal normal-crossing exponents | A4 | PDF p. 22 | Case 1/2 induction | draft reproduction + failed check: terminal exponent formula cannot be accepted until corrected transition system and termination proof exist | certificate theorem TBD; blocked | failed check |
| Quadratic exponent expression | A5 | PDF pp. 22-24 | terminal exponents | draft reproduction + failed check: promising algebra but candidate minimum must keep `\tilde t=0` restriction and feasibility hypotheses | arithmetic theorem TBD; blocked | failed check |
| Lemma 3 minimisation | A5 | PDF p. 24 | exponent vector definitions | draft reproduction + failed check: interior calculation mostly reproducible; endpoint split for `a=0`/`a=ell` required | endpoint arithmetic lemma TBD; blocked | failed check |
| Lemma 4 pole/order comparison | A5 | PDF p. 25 | Lemma 3 | draft reproduction + failed check: depends on fixed Lemma 3 and explicit `H_0`/`F_1` convention | arithmetic theorem TBD; blocked | failed check |
| Lemma 5 final order count | A5 | PDF pp. 25-27 | Lemmas 3-4 | draft reproduction + failed check: chart-family admissibility, coverage, exclusions, and exact equal-minimum count not reproduced | order-count theorem TBD; blocked | failed check |
| Notation translation to repo DLN dimensions | A6 | Aoyagi PDF pp. 8-9 | source inventory | pending | translation theorem TBD; open | pending |

## Ledger rules

- `Source ref` must eventually include PDF page numbers or stable local source
  anchors.
- `Lean target/status` records names only after the statement exists. Do not
  reserve impressive names before the statement is precise.
- `Reproduction/status` records the pen-and-paper derivation and independent
  check. A substantial calculation with this field pending is not
  formalisation-ready.
- `Review/status` is independent from build status. A theorem can be green and
  still fail fidelity or bedrock.
- Cited and deferred boundaries must appear in this table and in the matching
  claim card.
- Source references come from Aoyagi's PDF for this expedition. Do not fill
  ledger gaps from the quiver paper.
