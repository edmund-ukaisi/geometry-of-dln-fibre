# Thread-38 BLIND derivation of the per-step composition order (Aoyagi 2023)

Derived ONLY from the page images (PDF = printed page, offset 0), pp.14-20,
BEFORE reading the elder's ruling / journal 2026-07-21 / thread artifacts that
mention "the other order". Locked timestamp below.

## The objects (from pp.15-18, image-read)
- Inductive invariant (p.15): <∏ C^(s)> = <diag(b_1,...,b_{M(S)}) (E_J O; O D_J) ∏_{s>S} C^(s)>.
  D_J = (d_{ij}), J+1<=i<=M(S), J+1<=j<=M^(S+1).
- Case 1 (p.15-18): equal run b_{J+1}=...=b_{J+J_1}. Blow up
  {d_ij=0 (J<i<=J+J_1, J<j<=M^(S+1)), u_{s,k}=0}.

## The per-step atom, chart Case 1(2) (the J-advancing chart)
STEP A (p.16, p.17): the BLOW-UP substitution, introduced FIRST.
  d-block entries: d_ij = u_{S,J+1} * d'_ij   (the whole (M(S)-J)x(M^(S+1)-J) d-block
  factored by the pivot exceptional coordinate u_{S,J+1}; top-left of d' normalised to 1).
  Also u_{s,k} = u_{S,J+1} u'_{s,k}, and b'_i = u_{S,J+1} b_i.
  => PARENT coord d = u * (intermediate coord d').  This is B: parent = B(intermediate), B = "multiply block by pivot u".

STEP B (p.17-18): the unipotent SHEAR, introduced SECOND, acting on the POST-blow-up d'-block.
  Q (p.17) = I + (first row = -d'_{J+1,j}); post-mult clears the first ROW of the d'-block:
     D''_J = D'_J . Q.   [Q built from d'-entries = CHILD-frame coords.]
     Simultaneously C^(S+1) -> C'^(S+1) = Q^{-1} C^(S+1) (ideal-preserving insert of QQ^{-1}).
  P (p.18) = I + (first col = -(b'_i/b'_{J+1}) d''_{i,J+1}); pre-mult clears the first COLUMN:
     D'''_J = P . D''_J = (1 O; O D_{J+1}).
  So D'''_J = P D'_J Q = block-diag(1, D_{J+1}); the child block D_{J+1} is exposed.
  => intermediate d' = P^{-1} (1 (+) D_{J+1}) Q^{-1} = function of (child D_{J+1}, shear params).
     This is S: intermediate = S(child).

## Composition (resolution map g: child -> parent)
parent d = B(intermediate d'),  intermediate d' = S(child D_{J+1}).
Reversal rule: parent = B(x), x = S(child)  =>  atom = B ∘ S.

### VERDICT (blind): atom = B ∘ S  — BLOW-UP OUTERMOST, shear innermost.

Confirmed by the paper's own composite identity (p.18-19):
  P diag(b) D_J C^(S+1)
   = u_{S,J+1} diag(b') (P D'_J Q) C'^(S+1)      [factor pivot out FIRST, then Q,P]
   = u_{S,J+1} diag(b') D'''_J C'^(S+1)
   = u_{S,J+1} diag(b') (1 (+) D_{J+1}) C'^(S+1).
The pivot u_{S,J+1} is factored out ONCE, on the OUTSIDE, wrapping the entire
Q,P-sheared block. The shear matrices Q,P are built from d'-entries (child frame),
NOT from the parent d-entries.

## Why the order forces the divisibility (mechanism)
Every parent center coord d_ij = u_{S,J+1} * d'_ij, and d'_ij = [P^{-1}(1(+)D_{J+1})Q^{-1}]_ij.
Because B (multiply-by-pivot) is OUTERMOST it multiplies the ENTIRE sheared block,
so every parent center coord carries an explicit factor of the child pivot u_{S,J+1}:
the delta=1 division is STRUCTURAL, independent of what the (pivot-keeping) shear does.
Under S ∘ B (shear outermost) the shear would act on top of the u-scaled block and
could re-introduce u-free terms via shear parameters that live in the parent frame
-> division not guaranteed. (To be verified by exact algebra battery.)
