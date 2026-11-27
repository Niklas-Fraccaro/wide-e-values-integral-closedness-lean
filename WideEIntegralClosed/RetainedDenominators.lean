import WideEIntegralClosed.BroadBorelEuler
import WideEIntegralClosed.BroadFactorialLogArithmetic
import WideEIntegralClosed.BroadPreimageArithmetic
import WideEIntegralClosed.FrobeniusFromBorel
import WideEIntegralClosed.RationalBinomialArithmetic
import RetainedSourceTower
import Stage38SourceDifferentialTransport
import ActualSourceTowerEquation
import ExtendedSourceCompanion

/-! Subfactorial denominators for the exact retained Fourier amplitudes of a broad E-function. -/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open scoped NumberField
open StrictEUnit

namespace WideEIntegralClosed

private theorem geometricBinomial_of_subfactorial
    {K : Type*} [Field K] [NumberField K] (ξ : K)
    (hξ : HasSubfactorialBinomialDenominators ξ) : BinomialPrefixDenominators ξ := by
  obtain ⟨q, hq⟩ := subfactorial_binomial_rational ξ (Algebra.IsIntegral.isIntegral ξ) hξ
  change (q : K) = ξ at hq
  rw [← hq]
  exact binomialPrefixDenominators_ratCast q

/-- The selected source and its finite Laurent forcing extensions supply the broad denominator
bound for the actual retained Fourier log-free coefficients. -/
theorem hasBroadRetainedFourierDenominators : HasBroadRetainedFourierDenominators := by
  classical
  intro f a C expansion
  let F := C.coefficientField
  letI : NumberField F := C.numberField
  letI : IsAlgClosed WideE.AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  let φ : F →+* WideE.AlgebraicComplex := algebraMap F WideE.AlgebraicComplex
  let n := C.rankMinusOne
  let t := C.clearingPolynomial
  let U := C.clearingMatrix
  let S := C.source expansion
  let A : Fin (S.order + 1) → Fin (S.fourierOrder + 1) → WideE.AlgebraicComplex := S.reciprocalArray
  let hf : Stage56FiniteFuchs A := S.fourier_equations.2.1
  have hc := S.fourier_equations.2.2.1
  let e := Fintype.equivFinOfCardEq (sameFourierTwistedAmplitude_index_card A hf hc)
  let ρ (j : Fin S.fourierOrder) := frobeniusRootSeedExponent _ (e.symm j)
  let p (j : Fin S.fourierOrder) := sameFourierTwistedAmplitude A hf (e.symm j)
  obtain ⟨E, hE, ψ, hTower, _, ρE, pE, _, hρE, hpE⟩ :=
    retainedFourierAmplitude_source_tower φ A hf e ρ p (fun _ => rfl) (fun _ => rfl)
  letI : FiniteDimensional ℚ E := hE
  letI : NumberField E := ⟨⟩
  let χ : E →+* WideE.AlgebraicComplex := algebraMap E WideE.AlgebraicComplex
  let tE := t.map ψ
  let UE := fun i j => (U i j).map ψ
  let qE := ordinaryReflectionTuple (n + 1) (sameCompanionScalarTuple (n + 1) (Nat.succ_pos n) tE UE)
  let AE := reciprocalSourceArray (n + 1) (reciprocalCommonDegree (n + 1) qE) qE
  have hODE (j : Fin S.fourierOrder) : actualTwistedStage53Action (ρE j) AE (pE j) = 0 := by
    apply actualRetained_source_tower_equation ψ χ φ hTower (n + 1) (Nat.succ_pos n) t U
      (ρE j) (ρ j) (hρE j) (pE j) (p j) (hpE j)
    exact sameFourierTwistedAmplitude_stage53 A hf hc (e.symm j)
  have hdenρ : JointBinomialPrefixDenominators ρE := by
    apply finite_binomialPrefixDenominators ρE
    intro j
    have hs : HasSubfactorialBinomialDenominators (ρ j) :=
      C.fourierRoot_binomialDenominators expansion hf (ρ j)
        (frobeniusRootSeedExponent_isRoot _ (e.symm j))
    obtain ⟨q, hq⟩ := subfactorial_binomial_rational (ρ j) (Algebra.IsIntegral.isIntegral _) hs
    have h : (q : E) = ρE j := by
      apply χ.injective
      rw [hρE j, map_ratCast]
      exact hq
    rw [← h]
    exact binomialPrefixDenominators_ratCast q
  have hdenρzero := jointBinomialPrefixDenominators_adjoin_zero ρE hdenρ
  have hTE : tE ≠ 0 := (Polynomial.map_ne_zero_iff ψ.injective).mpr C.denominator_ne_zero
  have hClearE := extendedSourceCompanion_clearing ψ n C.companionCoefficients t U
    C.denominator_ne_zero C.clears_companion
  have hVE := extendedSourceCompanion_valuation ψ n t U C.regularClearing
  have hSource := C.sourceEuler_denominators_map ψ
  have hForcing (d s : ℕ) := C.finiteEuler_denominators_map ψ (fun j => (d : ℤ) - (j : ℤ)) (s + 1)
  have hArithmetic (j : Fin S.fourierOrder) : HasSubfactorialFactorialLogDenominators (pE j) := by
    by_cases hni : ∀ z : ℤ, ρE j ≠ (z : E)
    · obtain ⟨u, hu, hdegree, hden⟩ := broad_actual_noninteger_preimage_arithmetic
        (fun ξ => geometricBinomial_of_subfactorial ξ) n (extendedSourceCompanion ψ n t U)
        tE UE hTE hClearE hVE hSource (ρE j) hni (pE j) (hODE j)
      exact factorialLog_subfactorial_of_preimage ρE hdenρ j
        (logMixing_noninteger_forward_nonzero (ρE j) hni) (pE j) u _ hu hdegree hden.natural_indices
    · push_neg at hni
      obtain ⟨z, hz⟩ := hni
      have hZero : actualTwistedStage53Action 0 AE (frobeniusIntegerShift z (pE j)) = 0 := by
        rw [actualTwistedStage53Action_integerGauge, zero_add, ← hz, hODE j]
        simp only [frobeniusIntegerShift, mul_zero]
      obtain ⟨u, hu, hdegree, hden⟩ := broad_actual_zero_preimage_arithmetic
        (fun ξ => geometricBinomial_of_subfactorial ξ) n (extendedSourceCompanion ψ n t U)
        tE UE hTE hClearE hVE hForcing (frobeniusIntegerShift z (pE j)) hZero
      have hShift := factorialLog_subfactorial_of_preimage (fun k : Option _ => k.elim 0 ρE)
        hdenρzero none logMixing_zero_forward_nonzero (frobeniusIntegerShift z (pE j)) u _
        hu hdegree hden.natural_indices
      have hBack := hShift.shift (-z)
      rw [frobeniusIntegerShift_add, neg_add_cancel] at hBack
      simpa only [frobeniusIntegerShift, HahnSeries.single_zero_one, map_one, one_mul] using hBack
  intro i ε hε
  have hMapped : HasSubfactorialFactorialLogDenominators (p (e i)) := by
    rw [← hpE (e i)]
    exact (hArithmetic (e i)).map χ
  obtain ⟨B, hB, hprefix⟩ := hMapped ε hε
  choose D hD hDB hCoeffs using hprefix
  refine ⟨B, hB, D, hD, hDB, fun m j hj => ?_⟩
  have hi := (hCoeffs m j hj 0).map (algebraicClosure ℚ ℂ).val.toIntAlgHom
  simpa only [p, Equiv.symm_apply_apply, logAmplitudeFactorialCoefficient, map_mul, map_natCast,
    RingHom.toIntAlgHom_apply, mul_assoc] using hi

/-- The broad arithmetic Frobenius frames of the paper exist for every finite family. -/
theorem broadArithmeticFrameExistence : BroadArithmeticFrameExistence :=
  broadArithmeticFrameExistence_of_retainedFourierDenominators hasBroadRetainedFourierDenominators

end WideEIntegralClosed
