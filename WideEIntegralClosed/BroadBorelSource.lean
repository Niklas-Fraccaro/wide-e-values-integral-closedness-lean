import WideE.Conjugates
import FocusedFourierNormalizationCore
import OrdinaryReflectionValuation
import Stage53FourierTupleNonzero
import ValuedReciprocalFourier

/-! The regular Borel equation and its Fourier transform retain the original coefficients. -/

noncomputable section

open scoped BigOperators
open StrictEUnit

namespace WideEIntegralClosed

/-- A regular ordinary Borel equation for the factorial coefficients of an actual function. -/
structure BroadBorelSource (f : ℂ → ℂ) where
  coefficients : ℕ → WideE.AlgebraicComplex
  expansion : WideE.HasFactorialExpansion f coefficients
  order : ℕ
  operator : Fin (order + 1) → Polynomial WideE.AlgebraicComplex
  leading_ne_zero : operator (Fin.last order) ≠ 0
  regular : ReciprocalRegularSingularBounds order operator
  equation : ∑ i, (operator i : PowerSeries WideE.AlgebraicComplex) *
    (PowerSeries.derivative WideE.AlgebraicComplex)^[i.val] (PowerSeries.mk coefficients) = 0

namespace BroadBorelSource

variable {f : ℂ → ℂ}

/-- The reciprocal source is constructed from the sign-reflected ordinary Borel equation. -/
def reflectedOperator (S : BroadBorelSource f) :=
  ordinaryReflectionTuple S.order S.operator

/-- The order of the resulting differential operator on the original factorial series. -/
def fourierOrder (S : BroadBorelSource f) :=
  reciprocalSourceDegree S.order (reciprocalCommonDegree S.order S.reflectedOperator)
    S.reflectedOperator

/-- The array to which the finite Fourier identities apply. -/
def reciprocalArray (S : BroadBorelSource f) :=
  reciprocalSourceArray S.order (reciprocalCommonDegree S.order S.reflectedOperator)
    S.reflectedOperator

/-- The polynomial coefficients of the resulting differential operator. -/
def fourierOperator (S : BroadBorelSource f) :=
  stage53_fourierCoeff S.reciprocalArray

/-- The Fourier operator has positive order and annihilates the original formal E-series.
The same reciprocal array also annihilates the signed Borel series. -/
theorem fourier_equations (S : BroadBorelSource f) :
    0 < S.fourierOrder ∧ Stage56FiniteFuchs S.reciprocalArray ∧
      S.reciprocalArray (Fin.last S.order) (Fin.last S.fourierOrder) ≠ 0 ∧
      signedLaplaceSourceAction S.reciprocalArray
        (HahnSeries.single (1 : ℤ) (1 : WideE.AlgebraicComplex) *
          HahnSeries.ofPowerSeries ℤ WideE.AlgebraicComplex
            (PowerSeries.mk (fun n => (-1 : WideE.AlgebraicComplex) ^ n * S.coefficients n))) = 0 ∧
      (∑ l, (stage53_fourierCoeff S.reciprocalArray l : PowerSeries WideE.AlgebraicComplex) *
        (PowerSeries.derivative WideE.AlgebraicComplex)^[l.val]
          (stage41_strictFormalSeries S.coefficients)) = 0 := by
  have reflected := (ordinaryReflectionTuple_last_and_valuation_iff
    S.order S.operator).mpr ⟨S.leading_ne_zero, S.regular⟩
  exact valued_signed_ordinary_original_factorial S.order S.reflectedOperator
    reflected.1 reflected.2 S.coefficients
    (ordinaryReflectionTuple_signed_mk S.coefficients S.order S.operator S.equation)

/-- The true leading polynomial of the Fourier operator is a nonzero monomial. -/
theorem fourier_leading (S : BroadBorelSource f) :
    stage61_fourierCorner S.reciprocalArray ≠ 0 ∧
      S.fourierOperator (Fin.last S.fourierOrder) =
        Polynomial.monomial S.order (stage61_fourierCorner S.reciprocalArray) := by
  classical
  refine ⟨stage61_fourierCorner_ne_zero _ S.fourier_equations.2.2.1, ?_⟩
  let A : Fin (S.order + 1) → Fin (S.fourierOrder + 1) → WideE.AlgebraicComplex :=
    S.reciprocalArray
  change stage53_fourierCoeff A (Fin.last S.fourierOrder) =
    Polynomial.monomial S.order (stage61_fourierCorner A)
  rw [stage53_fourierCoeff_of_columns_above_zero A (Fin.last S.fourierOrder)
    (fun i j hj => by simp only [Fin.val_last] at hj; omega)]
  rw [Finset.sum_eq_single (Fin.last S.order)]
  · simp only [Fin.val_last, stage61_fourierCorner]
    exact Polynomial.C_mul_X_pow_eq_monomial
  · intro i _ hne
    have hi : i.val < S.order := by
      have hle := Nat.le_of_lt_succ i.isLt
      have hn : i.val ≠ S.order := fun h => hne (Fin.ext h)
      omega
    rw [stage56_fuchs_topColumn A S.fourier_equations.2.1 i hi, mul_zero,
      Polynomial.C_0, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The chosen Fourier operator annihilates the original entire function. -/
theorem actual_equation (S : BroadBorelSource f) (hf : WideE.IsWideEFunction f) :
    ∀ z : ℂ, ∑ i, (S.fourierOperator i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
      iteratedDeriv i.val f z = 0 := by
  have ha := hf.arithmetic_of_expansion S.expansion
  have h := WideE.factorialSeries_polynomial_relation_of_formal
    ha S.fourierOrder S.fourierOperator S.fourier_equations.2.2.2.2
  have hrealize : WideE.factorialSeriesFunction S.coefficients = f :=
    funext (fun z => (ha.expansion z).unique (S.expansion z))
  simpa only [hrealize] using h

end BroadBorelSource

end WideEIntegralClosed
