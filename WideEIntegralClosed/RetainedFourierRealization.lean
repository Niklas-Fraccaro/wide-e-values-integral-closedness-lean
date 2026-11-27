import FiniteLogLaurentTranspose
import FourierNaturalResonanceBasis
import ActualResonanceAmplitudeFactorization
import Stage14ActualAnalyticODETransfer
import WideE.Conjugates
import WideEIntegralClosed.RetainedFourierArithmetic

/-! Entire realizations of the unchanged formal Fourier coefficients. -/

noncomputable section

open scoped BigOperators Classical
open StrictEUnit

namespace WideEIntegralClosed

local notation "k₀" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)

local instance : CommRing (subfieldEntireFunctionAlgebra k₀) :=
  (subfieldEntireFunctionAlgebra k₀).toCommRing

private theorem frobeniusCoefficient_laurentSupport
    (B : ℕ → Polynomial AlgebraicComplex) (rho : AlgebraicComplex)
    (u : Polynomial AlgebraicComplex) (j : ℕ) :
    HahnSeries.ofPowerSeries ℤ AlgebraicComplex (PowerSeries.mk (fun t =>
      ((polynomialLogFrobeniusAmplitude B rho u).coeff j).coeff (t : ℤ))) =
      (polynomialLogFrobeniusAmplitude B rho u).coeff j := by
  apply HahnSeries.ext
  funext t
  change ((PowerSeries.mk (fun n => ((polynomialLogFrobeniusAmplitude B rho u).coeff j).coeff
    (n : ℤ)) : PowerSeries AlgebraicComplex) : LaurentSeries AlgebraicComplex).coeff t = _
  rw [PowerSeries.coeff_coe]
  split_ifs with ht
  · unfold polynomialLogFrobeniusAmplitude
    rw [finiteLogLaurentTranspose_double_coeff _ _ (uniformLogBound_powerSeries_mk _ _
      (polynomialLogFrobeniusCoefficient_coeff_eq_zero B rho u))]
    rw [PowerSeries.coeff_coe, if_pos ht, Polynomial.coeff_zero]
  · rw [PowerSeries.coeff_mk, Int.natAbs_of_nonneg (by omega)]

private theorem retainedCoefficient_factorialSeries (P : Polynomial (LaurentSeries AlgebraicComplex))
    (j : ℕ) : stage41_strictFormalSeries (fun t => logAmplitudeFactorialCoefficient P j t) =
      PowerSeries.mk (fun t => (P.coeff j).coeff (t : ℤ)) := by
  apply PowerSeries.ext
  intro t
  rw [stage41_coeff_strictFormalSeries, PowerSeries.coeff_mk]
  unfold logAmplitudeFactorialCoefficient
  have hn : (t.factorial : AlgebraicComplex) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero t)
  field_simp

/-- A retained Fourier coefficient with broad arithmetic is realized by an entire broad
E-function if its formal Laurent series satisfies a polynomial differential equation. -/
theorem retainedFourierAmplitude_wideRealization {m n : ℕ}
    (A : Fin (m + 1) → Fin (n + 1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) (j : ℕ)
    (ha : WideE.HasWideEArithmetic (fun t =>
      logAmplitudeFactorialCoefficient (sameFourierTwistedAmplitude A hf i) j t))
    (hODE : HasPolynomialScalarDifferentialRelation (k := AlgebraicComplex)
      stage14_laurentAlgebraDerivation ((sameFourierTwistedAmplitude A hf i).coeff j)) :
    ∃ F : subfieldEntireFunctionAlgebra k₀, WideE.IsWideEFunction F.val.val ∧
      stage14_subfieldEntireLaurentAlgHom k₀ F = (sameFourierTwistedAmplitude A hf i).coeff j := by
  let a (t : ℕ) := logAmplitudeFactorialCoefficient (sameFourierTwistedAmplitude A hf i) j t
  let F : subfieldEntireFunctionAlgebra k₀ := WideE.wideSeriesRealization a ha
  have hLaurent : stage14_subfieldEntireLaurentAlgHom k₀ F =
      (sameFourierTwistedAmplitude A hf i).coeff j := by
    change stage14_subfieldEntireLaurentAlgHom k₀ (WideE.wideSeriesRealization a ha) = _
    rw [stage14_subfieldEntireLaurentAlgHom_apply, WideE.wideSeriesRealization_taylor,
      retainedCoefficient_factorialSeries]
    exact frobeniusCoefficient_laurentSupport _ _ _ j
  have hActual := (stage14_actualODE_iff_laurentODE k₀ F).mpr (by rwa [hLaurent])
  exact ⟨F, WideE.wideEFunction_of_expansion ha.differentiable_factorialSeries ha.expansion
    hActual ha, hLaurent⟩

/-- The natural resonance rows have exact entire broad log-free realizations for every
class representative, including the nonnegative integer shifts. -/
theorem retainedFourier_naturalLogFreeRow {m n : ℕ}
    (A : Fin (m + 1) → Fin (n + 1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last m) (Fin.last n) ≠ 0) (ha : BroadRetainedFourierArithmetic A hf)
    (hODE : ∀ i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0),
      HasPolynomialScalarDifferentialRelation (k := AlgebraicComplex)
        stage14_laurentAlgebraDerivation ((sameFourierTwistedAmplitude A hf i).coeff 0))
    (xi : AlgebraicComplex) :
    ∃ F : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0) →
        subfieldEntireFunctionAlgebra k₀,
      (∀ i, WideE.IsWideEFunction (F i).val.val) ∧
      ∀ i, stage14_subfieldEntireLaurentAlgHom k₀ (F i) =
        (naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi i).coeff 0 := by
  classical
  have hex (i : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0)) :
      ∃ F : subfieldEntireFunctionAlgebra k₀, WideE.IsWideEFunction F.val.val ∧
        stage14_subfieldEntireLaurentAlgHom k₀ F =
          (naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi i).coeff 0 := by
    let seed := naturalResonanceRootSeed _ xi (sameFourierEulerIndicial_ne_zero A hf hc) i
    obtain ⟨F, hF, hTaylor⟩ := retainedFourierAmplitude_wideRealization A hf seed 0
      (ha seed) (hODE seed)
    let s := i.1.val
    refine ⟨subfieldEntireCoordinate k₀ ^ s * F, ?_, ?_⟩
    · change WideE.IsWideEFunction (fun z => z ^ s * F.val.val z)
      suffices hshift : ∀ t : ℕ, WideE.IsWideEFunction (fun z => z ^ t * F.val.val z) from hshift s
      intro t
      induction t with
      | zero => simpa only [pow_zero, one_mul] using hF
      | succ t ih => simpa only [pow_succ', mul_assoc] using WideE.isWideEFunction_coordinate.mul ih
    · change _ = (frobeniusIntegerShift (s : ℤ) (sameFourierTwistedAmplitude A hf seed)).coeff 0
      rw [map_mul, map_pow, hTaylor, frobeniusIntegerShift, Polynomial.coeff_C_mul,
        stage14_subfieldEntireLaurentAlgHom_apply, subfieldEntireTaylorAlgHom_coordinate,
        HahnSeries.ofPowerSeries_X, HahnSeries.single_pow]
      simp only [nsmul_eq_mul, mul_one, one_pow]
      rfl
  choose F hF hTaylor using hex
  exact ⟨F, hF, hTaylor⟩

/-- The exact natural resonance amplitudes are recovered from the broad entire row by a
finite nilpotent logarithm factor of the same rank. -/
theorem retainedFourier_naturalLogFactorization {m n : ℕ}
    (A : Fin (m + 1) → Fin (n + 1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last m) (Fin.last n) ≠ 0) (ha : BroadRetainedFourierArithmetic A hf)
    (hODE : ∀ i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0),
      HasPolynomialScalarDifferentialRelation (k := AlgebraicComplex)
        stage14_laurentAlgebraDerivation ((sameFourierTwistedAmplitude A hf i).coeff 0))
    (xi : AlgebraicComplex) :
    let B := fun i : Fin (n + 1) => (stage61_fourierLift A hf).coeff i.val
    let hP := sameFourierEulerIndicial_ne_zero A hf hc
    let J := naturalResonanceLogMatrix n B xi hP
    ∃ F : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0) →
        subfieldEntireFunctionAlgebra k₀,
      (∀ i, WideE.IsWideEFunction (F i).val.val) ∧
      ∀ j, naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi j =
        ∑ i, Polynomial.C (show LaurentSeries AlgebraicComplex from
          stage14_subfieldEntireLaurentAlgHom k₀ (F i)) *
          Polynomial.map (algebraMap AlgebraicComplex (LaurentSeries AlgebraicComplex))
            ((finiteLogMatrixUnit J (naturalResonanceLogMatrix_isNilpotent n B xi hP)).val i j) := by
  dsimp only
  obtain ⟨F, hF, hTaylor⟩ := retainedFourier_naturalLogFreeRow A hf hc ha hODE xi
  refine ⟨F, hF, fun j => ?_⟩
  simp only [hTaylor]
  exact naturalResonanceFrobeniusAmplitude_square_factorization n
    (fun i => (stage61_fourierLift A hf).coeff i.val) xi
    (sameFourierEulerIndicial_ne_zero A hf hc) j

end WideEIntegralClosed
