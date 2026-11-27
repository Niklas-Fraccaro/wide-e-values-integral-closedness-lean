import WideEIntegralClosed.Main
import WideEIntegralClosed.RetainedDenominators

/-! Integral closedness of the broad Siegel E-value ring. -/

noncomputable section

namespace WideEIntegralClosed

/-- The ring of broad Siegel E-values is integrally closed in its fraction field. -/
theorem isIntegrallyClosed_valueSubring : IsIntegrallyClosed WideE.valueSubring :=
  isIntegrallyClosed_valueSubring_of_broadArithmeticFrames broadArithmeticFrameExistence

/-- Every map to the value ring from a finitely presented algebra factors through a smooth
finite-type normal domain over the algebraic numbers. -/
theorem valueSubring_factors_of_finitePresentation {A : Type} [CommRing A]
    [Algebra WideE.AlgebraicComplex A] [Algebra.FinitePresentation WideE.AlgebraicComplex A]
    (φ : A →ₐ[WideE.AlgebraicComplex] WideE.valueSubring) :
    Nonempty (SmoothNormalFactorization φ) :=
  factors_of_hasSmoothNormalRelationLifts
    (hasSmoothNormalRelationLifts_of_realizedSmoothSpecializations evaluateAtOne wideParameter
      evaluateAtOne_surjective
      (divideAtOneInFunctionAlgebra (fun _ hf hz => WideE.wideEFunction_divAtOne hf hz))
      (realizedSmoothSpecializations_of_broadArithmeticFrames broadArithmeticFrameExistence)) φ

/-- A nonconstant polynomial over the algebraic numbers detects membership in the value ring. -/
theorem valueSubring_preimage_of_polynomial
    (p : Polynomial WideE.AlgebraicComplex) (hp : 0 < p.natDegree)
    (x : FractionRing WideE.valueSubring) (y : WideE.valueSubring)
    (hy : p.eval₂ ((algebraMap WideE.valueSubring (FractionRing WideE.valueSubring)).comp
      (algebraMap WideE.AlgebraicComplex WideE.valueSubring)) x =
        algebraMap WideE.valueSubring (FractionRing WideE.valueSubring) y) :
    ∃ a : WideE.valueSubring, algebraMap WideE.valueSubring (FractionRing WideE.valueSubring) a = x := by
  letI := isIntegrallyClosed_valueSubring
  exact exists_preimage_of_polynomial_value p hp x y hy

/-- An element of the fraction field with a positive power in the value ring is itself a value. -/
theorem valueSubring_preimage_of_pow {m : ℕ} (hm : 0 < m)
    (x : FractionRing WideE.valueSubring) (y : WideE.valueSubring)
    (hy : x ^ m = algebraMap WideE.valueSubring (FractionRing WideE.valueSubring) y) :
    ∃ a : WideE.valueSubring, algebraMap WideE.valueSubring (FractionRing WideE.valueSubring) a = x := by
  apply valueSubring_preimage_of_polynomial (Polynomial.X ^ m) (by simpa using hm) x y
  simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_X] using hy

end WideEIntegralClosed
