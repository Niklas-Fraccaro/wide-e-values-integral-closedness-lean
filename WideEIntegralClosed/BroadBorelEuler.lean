import WideEIntegralClosed.BroadBorelSelection
import WideEIntegralClosed.BroadLaurentForcing
import WideEIntegralClosed.BroadFilteredDenominators
import IntegralPolynomialForcingArithmetic
import OriginalSourceLaurentUnitPresentation
import FiniteSourceArithmeticFieldMap

/-! The selected broad Borel companion supplies the original regular Euler connection. -/

noncomputable section

open scoped NumberField Matrix
open StrictEUnit

namespace WideEIntegralClosed
namespace BroadBorelCompanion

variable {a : ℕ → WideE.AlgebraicComplex} (C : BroadBorelCompanion a)

/-- Subfactorial denominators for every fixed forcing extension of the selected source. -/
theorem finiteEuler_denominators (k : ℕ → ℤ) (s : ℕ) :
    let M := finiteLaurentOffset k s
    let n := C.rankMinusOne
    let t := C.clearingPolynomial
    let U := C.clearingMatrix
    HasSubfactorialEulerConnectionDenominators
      (finiteLaurentEulerMatrix (sourceLaurentEulerBase n t U M)
        (augmentedSourceEulerColumn n t) (M + (n + 1)) k s) := by
  let F := C.coefficientField
  letI : NumberField F := C.numberField
  let n := C.rankMinusOne
  let t := C.clearingPolynomial
  let U := C.clearingMatrix
  have hLaurent := broadLaurentDividedConnectionArithmetic_of_polynomial_clearing
    C.companionCoefficients C.denominator U C.denominator_ne_zero C.clears_companion C.subfactorial
  have hForcing := broadLaurentDividedConnectionArithmetic_finiteForcing _ _ hLaurent
    (sourcePolynomialForcingColumn_arithmetic (n + 1) C.denominator C.denominator_ne_zero) k s
  exact monomialEulerPresentation_subfactorial_arithmetic _ _ _
    (originalSource_finite_laurent_unit_euler_presentation n C.companionCoefficients t U
      C.denominator_ne_zero C.clears_companion C.regularClearing k s) hForcing

/-- The same integers work after extending the coefficient field of the selected source. -/
theorem finiteEuler_denominators_map {L : Type*} [Field L] [CharZero L]
    (φ : C.coefficientField →+* L) (k : ℕ → ℤ) (s : ℕ) :
    let M := finiteLaurentOffset k s
    let n := C.rankMinusOne
    let t := C.clearingPolynomial.map φ
    let U := fun i j => (C.clearingMatrix i j).map φ
    HasSubfactorialEulerConnectionDenominators
      (finiteLaurentEulerMatrix (sourceLaurentEulerBase n t U M)
        (augmentedSourceEulerColumn n t) (M + (n + 1)) k s) := by
  have h := (C.finiteEuler_denominators k s).field_map φ
  rwa [actualFiniteSourceMatrix_field_map φ C.rankMinusOne (finiteLaurentOffset k s)
    (finiteLaurentOffset k s + (C.rankMinusOne + 1)) s C.clearingPolynomial C.clearingMatrix
    C.denominator_ne_zero k] at h

/-- The homogeneous source is the forcing extension with no extra coordinates. -/
theorem sourceEuler_denominators_map {L : Type*} [Field L] [CharZero L]
    (φ : C.coefficientField →+* L) :
    HasSubfactorialEulerConnectionDenominators (sourceLaurentEulerBase C.rankMinusOne
      (C.clearingPolynomial.map φ) (fun i j => (C.clearingMatrix i j).map φ) 0) := by
  simpa only [finiteLaurentOffset, Finset.range_zero, Finset.sum_empty, finiteLaurentEulerMatrix]
    using C.finiteEuler_denominators_map φ (fun _ => 0) 0

end BroadBorelCompanion
end WideEIntegralClosed
