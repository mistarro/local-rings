# Local rings and algebras - an algorithmic characterization

Lean 4 formalization of the algorithmic characterization of local
`F`-algebras in:
  * M. Staromiejski, *Polynomial-time locality tests for finite rings*,
    J. Algebra, 379 (2013), pp. 441-452;
  * Z. Jelonek and M. Staromiejski, *A note on locality of algebras*,
    Journal of Algebra, 433 (2015), pp. 231-242.

## Main definitions

  * `isLocalElement`: an element `a` of an `F`-algebra `A` is *local* iff
    it belongs to a local `F`-subalgebra of `A`.
  * `localElements`: the set of all local elements in an `F`-algebra `A`.
  * `isLocallyGenerated`: an `F`-algebra `A` is *locally generated* if
    the local elements of `A` generate `A` as a vector space over `F`.
  * `absoluteTrace`: a non-trivial linear map `algebraicClosure F →ₗ[F] F`
    in characteristic `0`.

## Main results

  * `isLocalElement_integral`: if a local element `a` of an `F`-algebra `A` is
    integral then it belongs to a finite-dimensional local `F`-subalgebra of `A`.
  * `local_if_all_local`: if all elements of an `F`-algebra are local then
    the algebra is local.
  * `isLocalAlgebra_if_isLocallyGenerated`: generic theorem used to reduce: given
    * `hPQ`: proof that `P F A` implies `Q F K` given a surjective `f : A →ₐ[F] K`;
    * `hKK`: proof that `K₁ × K₂` cannot be locally generated if `Q F K₁` and `Q F K₂`;

    an `F`-algebra `A` satisfying `P A` is local if it is locally generated.
  * `isLocalRing_if_isLocallyGenerated_findim`: a finite-dimensional algebra is local
    if it is locally generated.
  * `isLocalRing_if_isLocallyGenerated_integral`: an integral (equivalently algebraic)
    algebra is local if it is locally generated.
