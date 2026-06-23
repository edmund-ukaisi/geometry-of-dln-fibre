# Statement card - A6 Definition 3 source-data ceiling

> **Claim.** Once Definition 3 selected cutpoints and `0 < ell` are supplied,
> the ceiling integer `M` and residue `a` used in Aoyagi Theorem 2 can be
> constructed by integer Euclidean division of the selected-width sum by `ell`.
>
> - **Lean:**
>   `DLNFibre.DLN.Aoyagi.AoyagiDefinition3CeilData.nonempty_of_ell_pos`,
>   `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData`, and
>   `DLNFibre.DLN.Aoyagi.AoyagiDefinition3SourceData.exists_ceilData`
>   (`lean/DLNFibre/DLN/Aoyagi/Definition3Bridge.lean`).
> - **Gloss.** For any integer selected-width family `m` and `0 < ell`,
>   Euclidean division of `sum_j m_j` by `ell` gives an integer `ceilWidth` and
>   natural residue `aParam` with
>   `sum_j m_j = ell*(ceilWidth-1)+aParam` and `0 < aParam <= ell`.
> - **Proved.** Generic finite ceiling/residue construction; source-data
>   wrapper carrying Definition 3's value-level selected dominance, selected
>   strict inequality, and value-level nonselected inequality; an existential
>   bridge from source data to `AoyagiDefinition3CeilData` plus the strict
>   selected inequality.
> - **Assumed.** The selected cutpoints and Definition 3 inequalities are
>   supplied as `AoyagiDefinition3SourceData`; in particular `0 < ell`.
> - **Cited.** None.
> - **Deferred.** Existence/uniqueness of selected cutpoints, source proof that
>   the selected set exists for arbitrary widths, later use of nonselected
>   inequalities, normal crossings, pole order, and RLCT extraction.
> - **Kill conditions.** Do not read this as selected-cutpoint construction.
>   The source-data wrapper is a formal package for supplied Definition 3 data,
>   not an existence theorem for that data.
