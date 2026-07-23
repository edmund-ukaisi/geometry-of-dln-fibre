# §-note: R3-flip merge-gate — Gröbner triple (#49) + reuse-node object identity (#50)

The ruling (§8, 62bfa334d) adopted **R3** (branch-ii recoord SIGN FLIP: `A_{S+1}·Q₁` = −γ, not the baked
`Q₁⁻¹`; direction from her text — my certificate's `Q₁⁻¹` was a conversion error) + **READING B** (clean-block
invariant: `b`'s in the external ledger, `foldResid` = the clean `D_J`). Elder MERGE GATE: "if the reuse node
is NOT clean under R3, RE-OPEN." This note is the compute half. Scripts (exact sympy + Gröbner, exit 0):
`verify/r3flip_ideal_triple.py` (#49, ed1), `verify/r3flip_reuse_node.py` (#50, reuse node). Decorrelated
Codex (xhigh, hypothesis withheld) on the object-identity criterion — folded in.

## Bottom line
**R3 CONFIRMS the ruling's central claim: it delivers a CLEAN `E_J` (cleared columns) where baked pollutes it.**
ONE item for the elder to check against worked.tex before merge: R3's `D_J` (residual column) picks up a
`u₀₀₁²` (degree-2 in the pivot-ROW coord), degree 5 vs baked's degree 4 — a consequence of leaving the pivot
ROW uncleared under the −γ flip. If the clean `D_J` tolerates `u₀₀₁²`, R3 passes clean; if `D_J` must be
degree-1 in each pivot-row coord, this is the re-open trigger.

## #49 — Gröbner triple on the R3-flip def (ed1, common ring; (2,2,2,2)/(2,3,2)/(2,3,2,2))
The leakage coefficient on `u₀₁₀·u₁ᵣ₁` in the cleared column (col-0), across the three variants:

    baked (+γ):   coeff 2   (the DOUBLING defect)
    honest(+γ,clr): coeff 1   (the recoordinatized coord w_{r,0})
    R3-flip (−γ):  coeff 0   (leakage CANCELS — col-0 = the clean deeper coord u₁ᵣ₀)

So honest is the midpoint; **the −γ flip drives the col-0 leakage to zero** (confirms seat-L4D's `[0][0]=u₁₀₀`).
- **(a) ideal-equality:** `⟨R3⟩ ≠ ⟨honest⟩` AND `⟨R3⟩ ≠ ⟨baked⟩` as ideals, both inclusions fail, all three
  witnesses. (Expected — R3, honest, baked are three different unipotent charts; ideal-equality is not the
  discriminator, per §7(1). honest_clear is object A / +γ, now retracted, so it is not the R3 reference.)
- **(b) block:** the R3 `A₀` block is still `[[1,u₀₀₁],[u₀₁₀,e₂]]` (NOT `diag(1,e₂)`) — R3 does NOT
  monomialise the BLOCK; the col-0 cleanliness is recoord-CANCELLATION in the product, a distinct phenomenon.
- **(c) M_{s,k}:** the R3 shear is `det J ≡ 1` AND structurally triangular ⟹ globally invertible ⟹
  M_{s,k}-safe / RLCT-safe, same as baked.

## #50 — reuse-node object identity (after ed1/ed2/ed3; (2,2,2,2) canonical + (2,3,2,2) wide)
Residual = the `[E_J | D_J]` block directly (at this node the row-gcd = 1 on both witnesses ⟹ no
row-scaling `b` spent yet ⟹ `foldResid` must BE the clean block; b's genuinely external — consistent with
Reading B). Split by output column:

| | col-0 = `E_J` (cleared) | col-1 = `D_J` (residual) |
|---|---|---|
| **baked (+γ)** | POLLUTED: `u₁ᵣ₀·u₂·· + 2·u₀₀₁·u₀₁₀·(…)` — deg 4, `u₀₀₁`-deg 1 | carries `u₀₁₁`; deg 4, `u₀₀₁`-deg 1 |
| **R3-flip (−γ)** | **CLEAN**: `u₁ᵣ₀·u₂··` exactly — deg 2, `u₀₀₁`-deg **0** | carries `u₀₁₁`; deg **5**, `u₀₀₁`-deg **2** |

- **E_J (col-0): R3 CLEAN, baked POLLUTED.** R3's cleared column is the pure deeper product with NO
  `u₀₀₁/u₀₁₀/u₀₁₁`; baked carries the `2·u₀₀₁·u₀₁₀` doubling. This is the ruling's "clean" and R3 delivers it.
- **D_J (col-1): both carry `u₀₁₁`** (the reused divisor's exceptional). Per decorrelated Codex, this is
  **legitimate** — `u₀₁₁` is a `D_J` block COORDINATE, not an external row-scaling `b`-factor; exceptional
  coordinates inside `D_J` are expected. So col-1 carrying `u₀₁₁` is NOT a re-open trigger.
- **THE ONE FLAG — R3 `D_J` degree.** R3's col-1 is degree 5, `u₀₀₁`-degree **2** (a genuine `u₀₀₁²` term:
  `2·u₀₀₁²·u₀₁₀·u₁₀₀·u₂₀₀ + …`), vs baked's degree-4 `u₀₀₁`-degree-1. Mechanism: the −γ flip cleans the pivot
  COLUMN direction (col-0) but the uncleared pivot ROW (`u₀₀₁` in `A₀[0][1]`) interacts with the flipped
  recoord to square `u₀₀₁` in col-1. This is the same "pivot row/col not cleared" residue as in §7 — R3 fixes
  the column half, the row half remains. **Elder check against worked.tex's `D_J`:** if the clean `D_J` is
  allowed degree-2 in a pivot-row coord, R3 passes; if `D_J` is degree-1 per pivot-row coord (multilinear-ish),
  the `u₀₀₁²` is a deviation.

## Decorrelated Codex (object-identity criterion)
Verbatim verdicts (xhigh, structure given, my leaning withheld): (1) clean `E_J` ⟹ **R3**, baked's
`2·u₀₀₁·u₀₁₀` is `E_J` pollution [logical necessity]; (2) `u₀₁₁` in col-1 does **NOT** disqualify clean `D_J`
— it's a `D_J` coordinate, not an external `b` [logical necessity]; (3) R3 consistent with "foldResid = clean
`D_J`, b's external"; "clean" does not require `D_J` exceptional-free [logical necessity]; (4) **R3 delivers
the paper's clean-block object; baked does not** [logical necessity]. (Codex did NOT see the `u₀₀₁²` — the
one flag above is outside its input.)

## Verdict on the gate
- **Clean-`E_J` sense (the ruling's mechanism): R3 PASSES, baked FAILS.** The reuse node IS clean under R3 in
  the `E_J`/cleared-column sense Codex + the ruling use. So the gate does not trip on the `E_J` criterion.
- **One residual flag** (the `u₀₀₁²` in R3's `D_J`) for the elder to reconcile against worked.tex's `D_J`
  degree before merge — the only place R3's clean-block claim is not unambiguous from my side.
- `M_{s,k}` / RLCT preserved (R3 unipotent). `⟨R3⟩ ≠ ⟨honest⟩` as ideals is expected (different charts), not a
  concern under §7(1) (RLCT-safe via invertibility; honest_clear object-A retracted).
