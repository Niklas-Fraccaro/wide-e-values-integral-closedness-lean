import FrobeniusActualJetDeterminant
import Stage38SeriesCoefficientExtension
import WideEIntegralClosed.RetainedFourierRamifiedEquation

/-! Independence of the exact ramified Fourier solutions. -/

noncomputable section

attribute [-instance] Polynomial.module
attribute [-instance] Polynomial.commSemiring

open scoped BigOperators Classical
open StrictEUnit

namespace WideEIntegralClosed

section

variable {K : Type*} [Field K] [CharZero K]

private theorem retained_twistedJet_det_ne_zero [IsAlgClosed K] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν)
    (rho : Fin ν → K) (p : Fin ν → Polynomial (LaurentSeries K))
    (hrho : ∀ j,rho j=frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j,p j=sameFourierTwistedAmplitude A hf (e.symm j)) :
    (Matrix.of (fun i j : Fin ν =>(twistedLogPolynomialEuler (rho j))^[i.val] (p j))).det≠0 := by
  have he : (Matrix.of (fun i j : Fin ν =>(twistedLogPolynomialEuler (rho j))^[i.val] (p j)))=
      frobeniusActualJetMatrix (sameFourierEulerCoefficientSymbols A hf) e := by
    funext i j
    simp only [hrho,hp,frobeniusActualJetMatrix,sameFourierTwistedAmplitude,Matrix.of_apply]
  rw [he]
  exact frobeniusActualJetMatrix_det_ne_zero _ (IsAlgClosed.splits _) e

private theorem retained_ramifiedJet_det_ne_zero {n : ℕ}
    (N : ℕ) (hN : N ≠ 0) (m : Fin n → ℤ) (rho : Fin n → K)
    (hm : ∀ j, (m j : K) / (N : K) = rho j)
    (p : Fin n → Polynomial (LaurentSeries K))
    (hp : (Matrix.of (fun i j : Fin n =>
      (twistedLogPolynomialEuler (rho j))^[i.val] (p j))).det ≠ 0) :
    (Matrix.of (fun i j : Fin n => (stage38_sourceEuler N)^[i.val]
      (Polynomial.C (HahnSeries.single (m j) (1 : K)) *
        stage38_logRamification N hN (p j)))).det ≠ 0 := by
  let Y := Matrix.of (fun i j : Fin n =>
    (twistedLogPolynomialEuler (rho j))^[i.val] (p j))
  have hmat : Matrix.of (fun i j : Fin n => (stage38_sourceEuler N)^[i.val]
      (Polynomial.C (HahnSeries.single (m j) (1 : K)) *
        stage38_logRamification N hN (p j))) =
    Y.map (stage38_logRamification N hN) *
      Matrix.diagonal (fun j => Polynomial.C (HahnSeries.single (m j) (1 : K))) := by
    apply Matrix.ext
    intro i j
    simpa only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.map_apply, Y, mul_comm] using
      ramified_twistedEuler_iterate N hN (m j) (rho j) (hm j) (p j) i.val
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero
  · change ((stage38_logRamification N hN).toRingHom.mapMatrix Y).det ≠ 0
    rw [← RingHom.map_det (stage38_logRamification N hN).toRingHom]
    intro h
    apply hp
    exact stage38_logRamification_injective N hN (h.trans (map_zero _).symm)
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply Polynomial.C_ne_zero.mpr
    intro h
    have hh := congrArg (fun x : LaurentSeries K => x.coeff (m j)) h
    simpa using hh

end

section

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

private theorem retainedFourier_jet_det_ne_zero {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → K) (p : Fin nu → Polynomial (LaurentSeries K))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (N : ℕ) (hN : N ≠ 0) (m : Fin nu → ℤ)
    (hm : ∀ j, (m j : K) / (N : K) = rho j) :
    (Matrix.of (fun i j : Fin nu => (stage38_sourceEuler N)^[i.val]
      (Polynomial.C (HahnSeries.single (m j) (1 : K)) *
        stage38_logRamification N hN (p j)))).det ≠ 0 := by
  exact retained_ramifiedJet_det_ne_zero N hN m rho hm p
    (retained_twistedJet_det_ne_zero A hf e rho p hrho hp)

end

private theorem linearIndependent_of_jet_det
    {K R : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    {n : ℕ} (d : R →ₗ[K] R) (y : Fin n → R)
    (hy : (Matrix.of (fun i j : Fin n => d^[i.val] (y j))).det ≠ 0) :
    LinearIndependent K y := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hz : (Matrix.of (fun i j : Fin n => d^[i.val] (y j))).mulVec
      (fun j => algebraMap K R (c j)) = 0 := by
    funext i
    have h := congrArg (fun x => (d ^ i.val) x) hc
    simp only [map_sum, map_smul, map_zero, Module.End.pow_apply] at h
    simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.smul_def,
      mul_comm, Pi.zero_apply] using h
  have hj := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hy hz) j
  exact (algebraMap K R).injective (hj.trans (map_zero _).symm)

private theorem retainedFourier_scalar_independent {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → K) (p : Fin nu → Polynomial (LaurentSeries K))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (N : ℕ) (hN : N ≠ 0) (m : Fin nu → ℤ)
    (hm : ∀ j, (m j : K) / (N : K) = rho j) :
    LinearIndependent K (fun j => Polynomial.C (HahnSeries.single (m j) (1 : K)) *
      stage38_logRamification N hN (p j)) := by
  let d := (stage61_logEulerDerivation (K := K) N).toLinearMap
  have hd : (d : Polynomial (LaurentSeries K) → Polynomial (LaurentSeries K)) =
      stage38_sourceEuler N := rfl
  apply linearIndependent_of_jet_det d
  simp only [hd]
  exact retainedFourier_jet_det_ne_zero A hf e rho p hrho hp N hN m hm

/-- The exact basis with rationally ramified external powers is linearly independent. -/
theorem retainedFourier_ramified_ambient_independent {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → K) (p : Fin nu → Polynomial (LaurentSeries K))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (N : ℕ) (hN : N ≠ 0) (m : Fin nu → ℤ)
    (hm : ∀ j, (m j : K) / (N : K) = rho j) :
    LinearIndependent K (fun j => stage38_logAmbient
      (Polynomial.C (HahnSeries.single (m j) (1 : K)) *
        stage38_logRamification N hN (p j))) := by
  apply stage38_logAmbient_linearIndependent
  have h := retainedFourier_scalar_independent A hf e rho p hrho hp N hN m hm
  simpa only [stage38_logModule_eq] using h

end WideEIntegralClosed
