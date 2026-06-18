# theorem-ledger.md - source to Lean dependency ledger

This table is controller memory. Every source theorem or lemma that can affect
the final statement gets one row. Keep source references page-pinned; avoid
holding PDF line numbers only in context.

| Source item | Local claim | Source ref | Dependencies | Reproduction/status | Lean target/status | Review/status |
|---|---|---|---|---|---|---|
| RLCT definition and normal-crossing extraction | A0 | Aoyagi background, pages TBD | external analytic theorem | cite-interface check pending | interface TBD; open/Cited | pending |
| Theorem 1, cited three-layer formula | context/special case | PDF pp. 6-7 | prior result [12]; likely derivable from Theorem 2 at `L=2` | pending/optional | no Lean target yet | pending |
| Theorem 2 multi-layer main formula | A6 | PDF pp. 8-9 | A0-A5 | pending | final theorem TBD; open | pending |
| Lemma 2 block elimination | A1 | PDF pp. 10-11 | matrix rank/open block hypotheses | draft reproduction: `threads/03-block-product-reduction/reproduction-draft.md`; check pending | TBD; open | pending |
| Theorem 3 product reduction | A2 | PDF pp. 11-13 | A1, product/block notation | draft reproduction: `threads/03-block-product-reduction/reproduction-draft.md`; check pending | TBD; open | pending |
| Theorem 4 deepest singular point | A3 | PDF p. 14 | A2, analytic/global comparison | scout report: `threads/02-analytic-interface/scout-report.md`; scope conflict under current citation rule | no Lean target until restricted proof/avoidance chosen | pending |
| Blow-up inductive statement | A4 | PDF pp. 14-15 | reduced product coordinates | pending | invariant theorem TBD; open | pending |
| Blow-up Case 1 | A4 | PDF pp. 15-18 | reduced product coordinates, inductive statement | pending | transition lemma TBD; open | pending |
| Blow-up Case 2 | A4 | PDF pp. 19-22 | reduced product coordinates, inductive statement | pending | transition lemma TBD; open | pending |
| Terminal normal-crossing exponents | A4 | PDF p. 22 | Case 1/2 induction | pending | certificate theorem TBD; open | pending |
| Quadratic exponent expression | A5 | PDF pp. 22-24 | terminal exponents | pending | arithmetic theorem TBD; open | pending |
| Lemma 3 minimisation | A5 | PDF p. 24 | exponent vector definitions | pending | arithmetic theorem TBD; open | pending |
| Lemma 4 pole/order comparison | A5 | PDF p. 25 | Lemma 3 | pending | arithmetic theorem TBD; open | pending |
| Lemma 5 final order count | A5 | PDF pp. 25-27 | Lemmas 3-4 | pending | arithmetic theorem TBD; open | pending |
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
