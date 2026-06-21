# Reproduction - Eq5 supplied endpoint coverage split

Date: 2026-06-21.

Scope: finite supplied-endpoint coverage bookkeeping for Aoyagi Lemma 5
equation `(5)`.  This does not construct Aoyagi's displayed source vectors,
prove source-label legality, terminal `tilde t=0`, chart coverage, pole order,
normal crossings, or RLCT extraction.

## Endpoint Deficit Input

The previous slice proved the endpoint-deficit split for the strict Eq5 offset
set `E_p` at coordinate `p`.

Outside the rising region:

```text
E_p = I_p \ {U_p}.
```

In the rising region `p<=a` and `p<=ell-a`:

```text
E_p = I_p \ {U_p,L_p}.
```

Here `I_p` is the same-coordinate interval value set, `U_p=Htilde'_p`, and
`L_p=Htilde_p`.

## Supplied Endpoints

Suppose a supplied upper endpoint branch has own-coordinate value

```text
Tupper(C.point p - 1) = U_p.
```

Then outside the rising region:

```text
insert Tupper E_p = insert U_p (I_p.erase U_p) = I_p.
```

Suppose additionally that, in the rising region, a supplied lower endpoint
branch has own-coordinate value

```text
Tlower(C.point p - 1) = L_p.
```

Then:

```text
insert Tupper (insert Tlower E_p)
  = insert U_p (insert L_p ((I_p.erase U_p).erase L_p))
  = I_p.
```

This is the generic endpoint form of the already proved Eq4-lower wrapper.  It
does not say Eq4, or any printed branch, supplies the lower endpoint.

## Unified Split

For each positive coordinate `p`, the supplied endpoint coverage theorem should
produce the disjunction:

```text
insert Tupper E_p = I_p
```

or

```text
p<=a and p<=ell-a and insert Tupper (insert Tlower E_p) = I_p.
```

The first branch is the non-rising case.  The second branch is the rising
case, where the lower endpoint is an additional explicit obligation.

## Formalisation Boundary

The Lean slice should add:

```text
aoyagiLemma5_suppliedUpperLower_Eq5_offsets_eq_intervalValueSetNat_of_le_min
aoyagiLemma5_suppliedEndpointCoverage_Eq5_offsets_split
```

The theorem names should make clear that endpoint values are supplied.  They
must not be described as source coverage, displayed-vector construction, or
the Lemma 5 order count.
