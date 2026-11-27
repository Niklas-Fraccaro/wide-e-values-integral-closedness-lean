import FourierIndicialTwistedAmplitudes
import FrobeniusIntegerShiftEquation
import Stage38OrdinarySourceTransport

/-! The exact retained Fourier equation after rational ramification. -/

noncomputable section

open scoped BigOperators
open StrictEUnit

namespace WideEIntegralClosed

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem twistedEuler_ring (rho : K) (p : Polynomial (LaurentSeries K)) :
    twistedLogPolynomialEuler rho p = logPolynomialEuler 1 p + Polynomial.C (HahnSeries.C rho) * p := by
  unfold twistedLogPolynomialEuler
  rw [Algebra.smul_def, Polynomial.algebraMap_apply, LaurentSeries.algebraMap_apply]

private theorem ramified_twistedEuler (N : ℕ) (hN : N ≠ 0)
    (m : ℤ) (rho : K) (hm : (m : K) / (N : K) = rho)
    (p : Polynomial (LaurentSeries K)) :
    stage38_sourceEuler N (Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN p) =
    Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN (twistedLogPolynomialEuler rho p) := by
  have hd : stage38_sourceEuler N (stage38_logRamification N hN p) =
      stage38_logRamification N hN (logPolynomialEuler 1 p) := by
    simpa [stage38_sourceEuler_apply] using
      stage38_logRamification_sourceEuler N hN 1 p
  rw [stage38_sourceEuler_mul, hd, stage61_logEuler_monomial, hm, mul_one,
    twistedEuler_ring, map_add, map_mul]
  change _ = Polynomial.C (HahnSeries.single m (1 : K)) *
    (stage38_logRamification N hN (logPolynomialEuler 1 p) +
      stage38_logRamification N hN (Polynomial.C (HahnSeries.single 0 rho)) *
        stage38_logRamification N hN p)
  rw [stage38_logRamification_constant]
  have hs : Polynomial.C (HahnSeries.single m rho) =
      Polynomial.C (HahnSeries.single m (1 : K)) *
        Polynomial.C (HahnSeries.single 0 rho) := by
    rw [← Polynomial.C_mul, HahnSeries.single_mul_single, add_zero, one_mul]
  rw [hs]
  ring

/-- The ramified Euler iterates preserve the exact twisted Laurent-log coefficients. -/
theorem ramified_twistedEuler_iterate (N : ℕ) (hN : N ≠ 0)
    (m : ℤ) (rho : K) (hm : (m : K) / (N : K) = rho)
    (p : Polynomial (LaurentSeries K)) (i : ℕ) :
    (stage38_sourceEuler N)^[i] (Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN p) =
    Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN ((twistedLogPolynomialEuler rho)^[i] p) := by
  induction i with
  | zero => rfl
  | succ i hi =>
    rw [Function.iterate_succ_apply', hi, ramified_twistedEuler N hN m rho hm,
      Function.iterate_succ_apply']

omit [CharZero K] in
private theorem ramifiedCoefficientMap (N : ℕ) (hN : N ≠ 0) (b : LaurentSeries K) :
    stage38_logRamification N hN (Polynomial.C b) = stage61_logCoefficientMap N hN b := by
  change Polynomial.map (stage38_laurentRamification N hN).toRingHom (Polynomial.C b) = _
  rw [Polynomial.map_C]
  rfl

private theorem ramified_twistedScalarEuler (N : ℕ) (hN : N ≠ 0)
    (m : ℤ) (rho : K) (hm : (m : K) / (N : K) = rho)
    (n : ℕ) (b : Polynomial (PowerSeries K)) (p : Polynomial (LaurentSeries K)) :
    stage61_logLeftEulerAction N hN n b
      (Polynomial.C (HahnSeries.single m (1 : K)) * stage38_logRamification N hN p) =
      Polynomial.C (HahnSeries.single m (1 : K)) * stage38_logRamification N hN
        (∑ i : Fin (n+1), Polynomial.C (HahnSeries.ofPowerSeries ℤ K (b.coeff i.val)) *
          (twistedLogPolynomialEuler rho)^[i.val] p) := by
  classical
  simp only [stage61_logLeftEulerAction, ramified_twistedEuler_iterate N hN m rho hm,
    map_sum, map_mul, ramifiedCoefficientMap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem retainedFourier_ramified_lift_equation {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0))
    (N : ℕ) (hN : N ≠ 0) (m : ℤ)
    (hm : (m : K) / (N : K) = frobeniusRootSeedExponent _ i) :
    stage61_logLeftEulerAction N hN nu (stage61_fourierLift A hf)
      (Polynomial.C (HahnSeries.single m (1 : K)) *
        stage38_logRamification N hN (sameFourierTwistedAmplitude A hf i)) = 0 := by
  rw [ramified_twistedScalarEuler N hN m _ hm]
  have he := sameFourierTwistedAmplitude_equation A hf hc i
  change (∑ k : Fin (nu+1), Polynomial.C (HahnSeries.ofPowerSeries ℤ K
    ((stage61_fourierLift A hf).coeff k.val)) *
    (twistedLogPolynomialEuler (frobeniusRootSeedExponent _ i))^[k.val]
      (sameFourierTwistedAmplitude A hf i)) = 0 at he
  rw [he, map_zero, mul_zero]

private theorem retainedFourier_ramified_ordinary_equation {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0))
    (N : ℕ) (hN : N ≠ 0) (m : ℤ)
    (hm : (m : K) / (N : K) = frobeniusRootSeedExponent _ i) :
    (∑ l : Fin (nu+1), Polynomial.aeval (stage38_sourceCoordinate (K := K) N)
      (stage53_fourierCoeff A l) * (stage38_sourceOrdinary N)^[l.val]
        (Polynomial.C (HahnSeries.single m (1 : K)) *
          stage38_logRamification N hN (sameFourierTwistedAmplitude A hf i))) = 0 := by
  apply (stage61_logMonic_same_normalOrder_annihilation N hN A hf hc _).mp
  rw [stage61_fourierMonic, stage61_logLeftEulerAction_C_mul,
    retainedFourier_ramified_lift_equation A hf hc i N hN m hm, mul_zero]

private theorem ramifiedIdentityEmbedding (k : Subfield ℂ)
    (p : Polynomial (LaurentSeries k)) :
    stage38_sourceEmbedding (RingHom.id k) p = stage38_logAmbient p := by
  change stage38_logAmbient (stage38_logMap (RingHom.id k) p) = _
  congr 1
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  simp [stage38_logMap_coeff, stage38_laurentMap_coeff]

/-- Every retained Fourier solution satisfies the exact original ordinary polynomial
operator in the ramified Laurent-log differential field. -/
theorem retainedFourier_ramified_ambient_equation (k : Subfield ℂ) {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → k) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0))
    (N : ℕ) (hN : N ≠ 0) (m : ℤ)
    (hm : (m : k) / (N : k) = frobeniusRootSeedExponent _ i) :
    ∑ l : Fin (nu+1), Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k))
      (stage53_fourierCoeff A l) *
      (stage32_ramifiedOrdinaryDerivation k N hN : RatFunc (LaurentSeries k) → _)^[l.val]
        (stage38_logAmbient (Polynomial.C (HahnSeries.single m (1 : k)) *
          stage38_logRamification N hN (sameFourierTwistedAmplitude A hf i))) = 0 := by
  have h := stage38_sourceEmbedding_ordinary_equation k (RingHom.id k) N hN nu
    (stage53_fourierCoeff A) _
    (retainedFourier_ramified_ordinary_equation A hf hc i N hN m hm)
  simpa only [Polynomial.map_id, ramifiedIdentityEmbedding] using h

end WideEIntegralClosed
