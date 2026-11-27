import ActualRamifiedTaylor
import FixedExponentBaseRow
import RationalRamificationWeights
import WideEIntegralClosed.FourierResonanceAssembly
import WideEIntegralClosed.RetainedFourierCoefficientODE
import WideEIntegralClosed.RetainedFourierIndependence
import WideEIntegralClosed.RetainedFourierRealization
import WideEIntegralClosed.ScalarFrobenius

/-! The exact retained Fourier amplitudes give the scalar Frobenius basis once
their broad coefficient bounds and the rationality of the indicial roots are known.

This adapts the pinned `StrictEUnit` scalar normal-form assembly to broad arithmetic.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped BigOperators Classical
open StrictEUnit
open WideEIntegralClosed.FourierResonanceAssembly

namespace WideEIntegralClosed

section

variable {K I : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I]

omit [CharZero K] in
private theorem logRamification_constant_polynomial (N : ℕ) (hN : N ≠ 0)
    (p : Polynomial K) :
    stage38_logRamification N hN (Polynomial.map (algebraMap K (LaurentSeries K)) p) =
      Polynomial.map (algebraMap K (LaurentSeries K)) p := by
  apply Polynomial.ext
  intro i
  simp only [stage38_logRamification_coeff, Polynomial.coeff_map, AlgHom.commutes]

private theorem finiteLogMatrixExponential_map_series (J : Matrix I I K)
    (i j : I) :
    laurentLogToSeriesPolynomial (Polynomial.map (algebraMap K (LaurentPolynomial K))
      (finiteLogMatrixExponential J i j)) =
    Polynomial.map (algebraMap K (LaurentSeries K)) (finiteLogMatrixExponential J i j) := by
  apply Polynomial.ext
  intro n
  simp only [laurentLogToSeriesPolynomial, Polynomial.mapRingHom, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, Polynomial.coeff_map]
  change laurentPolynomialToSeries (algebraMap K (LaurentPolynomial K)
    ((finiteLogMatrixExponential J i j).coeff n)) = _
  exact laurentPolynomialToSeries.commutes _

private theorem fixedExponentBaseUnit_series_row (N : ℕ) (hN : N ≠ 0)
    (F : I → Polynomial (LaurentSeries K)) (p : Polynomial (LaurentSeries K))
    (m : ℤ) (J : Matrix I I K) (hJ : IsNilpotent J) (j : I)
    (hp : p = ∑ i, F i * Polynomial.map (algebraMap K (LaurentSeries K))
      (finiteLogMatrixExponential J i j)) :
    Polynomial.C (HahnSeries.single m (1 : K)) * stage38_logRamification N hN p =
      ∑ i, stage38_logRamification N hN (F i) *
        laurentLogToSeriesPolynomial ((fixedExponentBaseUnit m J hJ).val i j) := by
  rw [fixedExponentBaseUnit_row]
  have hm : laurentLogToSeriesPolynomial (Polynomial.C (LaurentPolynomial.T m)) =
      Polynomial.C (HahnSeries.single m (1 : K)) := by
    change Polynomial.map laurentPolynomialToSeries.toRingHom
      (Polynomial.C (LaurentPolynomial.T m)) = _
    rw [Polynomial.map_C]
    congr 1
    exact laurentPolynomialToSeries_single m (1 : K)
  rw [hm, hp, map_sum]
  simp_rw [map_mul, logRamification_constant_polynomial,
    finiteLogMatrixExponential_map_series]

variable (k : Subfield ℂ)
private theorem ramified_analytic_log_image (N : ℕ) (hN : N ≠ 0)
    (F : subfieldEntireFunctionAlgebra k) :
    stage38_logRamification N hN
      (Polynomial.C (stage14_subfieldEntireLaurentAlgHom k F)) =
    Polynomial.C (stage14_subfieldEntireLaurentAlgHom k
      (stage17_arithmeticPowerPullback k N hN F)) := by
  rw [actual_entireLaurent_powerPullback]
  change Polynomial.map (stage38_laurentRamification N hN).toRingHom
    (Polynomial.C (stage14_subfieldEntireLaurentAlgHom k F)) = _
  rw [Polynomial.map_C]
  rfl

end

private def fourierNaturalLogMatrix {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (xi : AlgebraicComplex) :
    Matrix (polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
      (polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
      AlgebraicComplex := by
  exact naturalResonanceLogMatrix nu (fun k => (stage61_fourierLift A hf).coeff k.val) xi
    (sameFourierEulerIndicial_ne_zero A hf hc)

private theorem fourierNaturalLogMatrix_nilpotent {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (xi : AlgebraicComplex) : IsNilpotent (fourierNaturalLogMatrix A hf hc xi) := by
  exact naturalResonanceLogMatrix_isNilpotent nu
    (fun k => (stage61_fourierLift A hf).coeff k.val) xi
    (sameFourierEulerIndicial_ne_zero A hf hc)

private theorem naturalAmplitude_retained_shift {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (xi : AlgebraicComplex)
    (i : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
    (j : Fin nu) (hj : j = e (naturalResonanceRootSeed _ xi
      (sameFourierEulerIndicial_ne_zero A hf hc) i)) :
    naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi i =
      frobeniusIntegerShift (i.1.1 : ℤ) (p j) := by
  rw [hj, hp, Equiv.symm_apply_apply]
  rfl

private theorem rational_of_integer_quotient {K : Type*} [Field K] [CharZero K]
    (m : ℤ) (N : ℕ) (x : K) (h : (m : K) / (N : K) = x) :
    ∃ q : ℚ, (q : K) = x := by
  refine ⟨(m : ℚ) / (N : ℚ), ?_⟩
  simpa using h

private theorem naturalRoot_retained_exponent {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex)
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (xi : AlgebraicComplex)
    (i : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
    (j : Fin nu) (hj : j = e (naturalResonanceRootSeed _ xi
      (sameFourierEulerIndicial_ne_zero A hf hc) i)) :
    rho j = xi + (i.1.1 : AlgebraicComplex) := by
  rw [hj, hrho, Equiv.symm_apply_apply]
  rfl

private theorem ramified_shift_quotient {K : Type*} [Field K] [CharZero K]
    (N : ℕ) (hN : N ≠ 0) (m : ℤ) (s : ℕ) (xi rho : K)
    (hm : (m : K) / (N : K) = xi) (hr : rho = xi + (s : K)) :
    ((m + (N : ℤ) * (s : ℤ) : ℤ) : K) / (N : K) = rho := by
  rw [hr, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
    add_div, hm]
  congr 1
  exact mul_div_cancel_left₀ (s : K) (Nat.cast_ne_zero.mpr hN)

private theorem scalarRow_as_logAmbient (k : Subfield ℂ)
    {I : Type*} [Fintype I] [DecidableEq I] (N : ℕ) (hN : N ≠ 0)
    (F : I → subfieldEntireFunctionAlgebra k)
    (Z : (Matrix I I (LaurentLogBase k))ˣ) (j : I) :
    stage33_scalarNormalFormRow k N hN F Z j =
      stage38_logAmbient (∑ i, Polynomial.C (stage14_subfieldEntireLaurentAlgHom k
        (stage17_arithmeticPowerPullback k N hN (F i))) *
        laurentLogToSeriesPolynomial (Z.val i j)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  rfl

private theorem broadFourier_global_base_unit {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex)
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      ∃ q : ℚ, algebraMap ℚ AlgebraicComplex q = x) :
    ∃ xi : ExponentClass rho → AlgebraicComplex, ∃ s : Fin nu → ℕ,
    ∃ E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
      (sameFourierEulerCoefficientSymbols A hf 0)) ≃ Fin nu,
      (∀ j, rho j = xi (exponentClassMap rho j) + (s j : AlgebraicComplex)) ∧
      (∀ i, E i = e (naturalResonanceRootSeed _ (xi i.1)
        (sameFourierEulerIndicial_ne_zero A hf hc) i.2)) ∧
      ∃ N : ℕ, 0 < N ∧ ∃ m : ExponentClass rho → ℤ,
      (∀ c, (m c : AlgebraicComplex) / (N : AlgebraicComplex) = xi c) ∧
      ∃ Z : (Matrix (Fin nu) (Fin nu) (LaurentLogBase AlgebraicComplex))ˣ,
      Z = @reindexedClassBaseUnit AlgebraicComplex (ExponentClass rho)
        (fun c => polynomialLogResonanceCoordinateIndex (xi c) (sameFourierEulerCoefficientSymbols A hf 0))
        (Fin nu) _ _ (Fintype.ofFinite _) _ _ _ _ _ m
        (fun c => fourierNaturalLogMatrix A hf hc (xi c))
        (fun c => fourierNaturalLogMatrix_nilpotent A hf hc (xi c)) E ∧
      matrixDerivative (manuscriptBaseDerivation N) Z.val =
        ramifiedConstantMatrix
          (@reindexedClassResidue AlgebraicComplex (ExponentClass rho)
            (fun c => polynomialLogResonanceCoordinateIndex (xi c) (sameFourierEulerCoefficientSymbols A hf 0))
            (Fin nu) _ (Fintype.ofFinite _) _ _ _ _ _ xi
            (fun c => fourierNaturalLogMatrix A hf hc (xi c)) E) * Z.val := by
  obtain ⟨xi,s,hs,hsep,E,hE,hcard⟩ := exists_disjoint_natural_resonance_equiv
    _ (sameFourierEulerIndicial_ne_zero A hf hc) e rho hrho
  have hr : ∀ j, ∃ q : ℚ, algebraMap ℚ AlgebraicComplex q = rho j := by
    intro j
    apply hroot
    rw [hrho j]
    exact frobeniusRootSeedExponent_isRoot _ (e.symm j)
  choose r hr using hr
  let q : ExponentClass rho → ℚ := fun c => r c.out - (s c.out : ℚ)
  have hq : ∀ c, (q c : AlgebraicComplex) = xi c := by
    intro c
    have hh := hs c.out
    have he : exponentClassMap rho c.out = c := Quotient.out_eq c
    rw [he, ← hr c.out] at hh
    dsimp [q]
    push_cast
    change algebraMap ℚ AlgebraicComplex (r c.out) - (s c.out : AlgebraicComplex) = xi c
    linear_combination hh
  letI : Fintype (ExponentClass rho) := Fintype.ofFinite _
  obtain ⟨N,hN,m,hm,_⟩ := rational_weights_common_denominator_field (k := AlgebraicComplex) q
  have hm' : ∀ c, (m c : AlgebraicComplex) / (N : AlgebraicComplex) = xi c :=
    fun c => (hm c).trans (hq c)
  let L := fun c => fourierNaturalLogMatrix A hf hc (xi c)
  let hL := fun c => fourierNaturalLogMatrix_nilpotent A hf hc (xi c)
  refine ⟨xi,s,E,hs,hE,N,hN,m,hm',reindexedClassBaseUnit m L hL E,rfl,?_⟩
  exact reindexedClassBaseUnit_equation N hN.ne' xi m hm' L hL E

private theorem broadFourier_ramified_analytic_block {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (ha : BroadRetainedFourierArithmetic A hf)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (xi : AlgebraicComplex) (N : ℕ) (hN : N ≠ 0) (m : ℤ) :
    ∃ F : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0) →
      subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
      (∀ i, WideE.IsWideEFunction (F i).val.val) ∧
      ∀ j, Polynomial.C (HahnSeries.single m (1 : AlgebraicComplex)) *
        stage38_logRamification N hN
          (naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi j) =
        ∑ i, Polynomial.C (show LaurentSeries AlgebraicComplex from stage14_subfieldEntireLaurentAlgHom
          (algebraicClosure ℚ ℂ).toSubfield
          (stage17_arithmeticPowerPullback (algebraicClosure ℚ ℂ).toSubfield N hN (F i))) *
          laurentLogToSeriesPolynomial
            ((fixedExponentBaseUnit m (fourierNaturalLogMatrix A hf hc xi)
              (fourierNaturalLogMatrix_nilpotent A hf hc xi)).val i j) := by
  obtain ⟨F, hs, he⟩ := retainedFourier_naturalLogFactorization A hf hc ha
    (fun i => retainedFourier_coefficient_ode A hf hc i 0) xi
  refine ⟨F,hs,?_⟩
  intro j
  have h := fixedExponentBaseUnit_series_row N hN
    (fun i => Polynomial.C (show LaurentSeries AlgebraicComplex from stage14_subfieldEntireLaurentAlgHom
      (algebraicClosure ℚ ℂ).toSubfield (F i)))
    (naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi j)
    m (fourierNaturalLogMatrix A hf hc xi)
    (fourierNaturalLogMatrix_nilpotent A hf hc xi) j (he j)
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun x => x * _)
  exact ramified_analytic_log_image (algebraicClosure ℚ ℂ).toSubfield N hN (F i)

private theorem broadFourier_global_ramified_row {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (ha : BroadRetainedFourierArithmetic A hf)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex) (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (xi : ExponentClass rho → AlgebraicComplex)
    (E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
      (sameFourierEulerCoefficientSymbols A hf 0)) ≃ Fin nu)
    (hE : ∀ i, E i = e (naturalResonanceRootSeed _ (xi i.1)
      (sameFourierEulerIndicial_ne_zero A hf hc) i.2))
    (N : ℕ) (hN : N ≠ 0) (m : ExponentClass rho → ℤ) :
    ∃ F : Fin nu → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
      (∀ i, WideE.IsWideEFunction (F i).val.val) ∧
      ∀ j, (∑ i : Fin nu, Polynomial.C (show LaurentSeries AlgebraicComplex from
        stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
          (stage17_arithmeticPowerPullback (algebraicClosure ℚ ℂ).toSubfield N hN (F i))) *
        laurentLogToSeriesPolynomial
          ((@reindexedClassBaseUnit AlgebraicComplex (ExponentClass rho)
            (fun c => polynomialLogResonanceCoordinateIndex (xi c) (sameFourierEulerCoefficientSymbols A hf 0))
            (Fin nu) _ _ (Fintype.ofFinite _) _ _ _ _ _ m
            (fun c => fourierNaturalLogMatrix A hf hc (xi c))
            (fun c => fourierNaturalLogMatrix_nilpotent A hf hc (xi c)) E).val i j)) =
        Polynomial.C (HahnSeries.single
          (m (E.symm j).1 + (N : ℤ) * ((E.symm j).2.1.1 : ℤ)) (1 : AlgebraicComplex)) *
          stage38_logRamification N hN (p j) := by
  letI : Fintype (ExponentClass rho) := Fintype.ofFinite _
  choose F hF hrow using fun c => broadFourier_ramified_analytic_block
    A hf ha hc (xi c) N hN (m c)
  refine ⟨fun j => F (E.symm j).1 (E.symm j).2, fun j => hF _ _, ?_⟩
  intro j
  have hg := mapped_reindexedBlockUnit_row laurentLogToSeriesPolynomial
    (fun c => fixedExponentBaseUnit (m c) (fourierNaturalLogMatrix A hf hc (xi c))
      (fourierNaturalLogMatrix_nilpotent A hf hc (xi c))) E
    (fun c i => Polynomial.C (show LaurentSeries AlgebraicComplex from
      stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (stage17_arithmeticPowerPullback (algebraicClosure ℚ ℂ).toSubfield N hN (F c i)))) j
  refine hg.trans ?_
  rw [← hrow (E.symm j).1 (E.symm j).2]
  have he := naturalAmplitude_retained_shift A hf hc e p hp
    (xi (E.symm j).1) (E.symm j).2 j
    ((E.apply_symm_apply j).symm.trans (hE (E.symm j)))
  rw [he, ramified_external_natural_shift]

private theorem broadFourier_scalarNormalForm {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (ha : BroadRetainedFourierArithmetic A hf)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex) (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      ∃ q : ℚ, algebraMap ℚ AlgebraicComplex q = x) :
    Nonempty (BroadScalarFrobeniusBasis nu (stage53_fourierCoeff A)) := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨xi,s,E,hs,hE,N,hN,m,hm,Z,hZ,hODE⟩ :=
    broadFourier_global_base_unit A hf hc e rho hrho hroot
  letI : Fintype (ExponentClass rho) := Fintype.ofFinite _
  obtain ⟨F,hF,hrow⟩ := broadFourier_global_ramified_row A hf ha hc e rho p hp
    xi E hE N hN.ne' m
  let M := reindexedClassResidue xi (fun c => fourierNaturalLogMatrix A hf hc (xi c)) E
  let w : Fin nu → ℤ := fun j => m (E.symm j).1 + (N : ℤ) * ((E.symm j).2.1.1 : ℤ)
  have hw : ∀ j, (w j : AlgebraicComplex) / (N : AlgebraicComplex) = rho j := by
    intro j
    exact ramified_shift_quotient N hN.ne' _ _ _ _ (hm (E.symm j).1)
      (naturalRoot_retained_exponent A hf hc e rho hrho _ _ j
        ((E.apply_symm_apply j).symm.trans (hE (E.symm j))))
  have hscalar : stage33_scalarNormalFormRow (algebraicClosure ℚ ℂ).toSubfield N hN.ne' F Z =
      fun j => stage38_logAmbient (Polynomial.C (HahnSeries.single (w j) (1 : AlgebraicComplex)) *
        stage38_logRamification N hN.ne' (p j)) := by
    funext j
    rw [scalarRow_as_logAmbient, hZ]
    exact congrArg stage38_logAmbient (hrow j)
  refine ⟨⟨N, hN.ne', F, M, Z, hF, ?_, hODE, ?_, ?_⟩⟩
  · intro a ha
    exact reindexedClassResidue_rational_spectrum xi
      (fun c => rational_of_integer_quotient (m c) N (xi c) (hm c))
      (fun c => fourierNaturalLogMatrix A hf hc (xi c))
      (fun c => fourierNaturalLogMatrix_nilpotent A hf hc (xi c)) E a ha
  · intro j
    rw [hscalar]
    have hh := retainedFourier_ramified_ambient_equation (algebraicClosure ℚ ℂ).toSubfield
      A hf hc (e.symm j) N hN.ne' (w j) ((hw j).trans (hrho j))
    simpa only [hp j] using hh
  · rw [hscalar]
    exact retainedFourier_ramified_ambient_independent A hf e rho p hrho hp N hN.ne' w hw

/-- Rational indicial roots and broad bounds for the exact retained log-free coefficients
supply the scalar Frobenius basis of the same Fourier equation. -/
theorem broadScalarFrobeniusBasis_of_retainedFourier {m n : ℕ}
    (A : Fin (m + 1) → Fin (n + 1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last m) (Fin.last n) ≠ 0) (ha : BroadRetainedFourierArithmetic A hf)
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      ∃ q : ℚ, algebraMap ℚ AlgebraicComplex q = x) :
    Nonempty (BroadScalarFrobeniusBasis n (stage53_fourierCoeff A)) := by
  classical
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  let e := Fintype.equivFinOfCardEq (sameFourierTwistedAmplitude_index_card A hf hc)
  exact broadFourier_scalarNormalForm A hf ha hc e
    (fun j => frobeniusRootSeedExponent _ (e.symm j))
    (fun j => sameFourierTwistedAmplitude A hf (e.symm j))
    (fun _ => rfl) (fun _ => rfl) hroot

/-- The arithmetic inputs for the chosen Fourier operator are rational indicial roots and
subfactorial prefix denominators of the retained log-free coefficients. -/
theorem broadScalarFrobeniusBasis_of_retainedFourier_denominators {m n : ℕ}
    (A : Fin (m + 1) → Fin (n + 1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last m) (Fin.last n) ≠ 0) (hd : BroadRetainedFourierDenominators A hf)
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      ∃ q : ℚ, algebraMap ℚ AlgebraicComplex q = x) :
    Nonempty (BroadScalarFrobeniusBasis n (stage53_fourierCoeff A)) :=
  broadScalarFrobeniusBasis_of_retainedFourier A hf hc
    ((broadRetainedFourierArithmetic_iff_denominators A hf hc).mpr hd) hroot

end WideEIntegralClosed
