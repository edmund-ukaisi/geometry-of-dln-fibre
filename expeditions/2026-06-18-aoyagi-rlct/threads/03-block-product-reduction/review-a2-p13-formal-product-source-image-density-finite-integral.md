# Review - A2 p.13 formal-product source-image density finite integral

## Verdict

PASS.

The theorem is a consumer wrapper only.  Its name and statement match the
actual content: a supplied bounded-density identity between the p.13
formal-product chart-piece measure and the concrete passive-theta source-image
reference is converted into the readback hypotheses required by the existing
formal-product finite-integral socket.

## Checks

- The final handler asks for `chartPiece subset sourceChart '' V`, not direct
  p.13 support or direct readback/right-inverse hypotheses.
- p.13 support is derived from the returned local image-support theorem.
- the chart-piece readback/right-inverse condition is derived from the returned
  right inverse on `sourceChart '' V` and `V subset W`.
- the formal-product readback domination scalar is exactly the supplied density
  bound `D`.
- no inverse Haar scalar appears in the new wrapper; the original-prior bridge
  inside the existing formal-product readback socket is where the prior/Haar
  scalar bookkeeping belongs.
- the theorem keeps the formal-product/source-image identity and the a.e.
  density bound explicit.

## Verification

Passed locally:

```text
env LEAN_NUM_THREADS=3 lake env lean DLNFibre/DLN/Aoyagi/OriginalEdgeFamilyP13FormalProductSourceImageFiniteIntegral.lean
env LEAN_NUM_THREADS=3 lake build DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13FormalProductSourceImageFiniteIntegral
env LEAN_NUM_THREADS=3 lake build DLNFibre
lean/scripts/sorries
git diff --check
env LEAN_NUM_THREADS=3 lake env lean /tmp/aoyagi_formal_product_source_image_axioms.lean
```

The direct axiom probe reported only:

```text
[propext, Classical.choice, Quot.sound]
```

Imported-module linter warnings appeared during the focused module and full
library builds; no new failure was reported.

## Nonclaims

No formal-product/source-image density identity is proved.  No density bound is
proved.  No source-image coverage, source-rank coverage, Haar transport, scalar
normalization, normal crossings, pole order, or RLCT extraction is proved.
