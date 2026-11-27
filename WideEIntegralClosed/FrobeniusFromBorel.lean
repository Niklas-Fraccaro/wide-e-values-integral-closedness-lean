import WideEIntegralClosed.BroadBorelSelection
import WideEIntegralClosed.BroadIndicialRationality
import WideEIntegralClosed.RetainedFourierFrobenius

/-! The broad Frobenius input reduces to denominator bounds for the exact Fourier amplitudes. -/

noncomputable section

set_option maxHeartbeats 400000

open StrictEUnit

namespace WideEIntegralClosed

/-- Every selected Borel companion supplies broad common denominators for the retained
log-free Fourier coefficients. -/
def HasBroadRetainedFourierDenominators : Prop :=
  ∀ {f : ℂ → ℂ} {a : ℕ → WideE.AlgebraicComplex} (C : BroadBorelCompanion a)
    (expansion : WideE.HasFactorialExpansion f a),
    let S := C.source expansion
    BroadRetainedFourierDenominators S.reciprocalArray S.fourier_equations.2.1

/-- The rationality theorem and the retained Fourier assembly construct the scalar
Frobenius basis of the exact nonzero Laurent operator selected from the original function. -/
theorem broadScalarFrobeniusExistence_of_retainedFourierDenominators
    (denominators : HasBroadRetainedFourierDenominators) : BroadScalarFrobeniusExistence := by
  intro f hf hne
  obtain ⟨a, expansion, ⟨C⟩⟩ := exists_broadBorelCompanion hf hne
  let S := C.source expansion
  let hF := S.fourier_equations.2.1
  have hroots : ∀ ξ : WideE.AlgebraicComplex,
      (sameFourierEulerCoefficientSymbols S.reciprocalArray hF 0).eval ξ = 0 →
      ∃ q : ℚ, algebraMap ℚ WideE.AlgebraicComplex q = ξ := by
    intro ξ hξ
    exact subfactorial_binomial_rational ξ (Algebra.IsIntegral.isIntegral ξ)
      (C.fourierRoot_binomialDenominators expansion hF ξ hξ)
  have hbasis := broadScalarFrobeniusBasis_of_retainedFourier_denominators
    S.reciprocalArray hF S.fourier_equations.2.2.1 (denominators C expansion) hroots
  exact ⟨S.fourierOrder, S.order, stage61_fourierCorner S.reciprocalArray, S.fourierOperator,
    S.fourier_equations.1, ⟨S.fourier_leading.1, S.fourier_leading.2, S.actual_equation hf⟩,
    hbasis⟩

/-- The last arithmetic step suffices to construct a common frame for every finite family. -/
theorem broadArithmeticFrameExistence_of_retainedFourierDenominators
    (denominators : HasBroadRetainedFourierDenominators) : BroadArithmeticFrameExistence :=
  broadArithmeticFrameExistence_of_scalarFrobenius
    (broadScalarFrobeniusExistence_of_retainedFourierDenominators denominators)

end WideEIntegralClosed
