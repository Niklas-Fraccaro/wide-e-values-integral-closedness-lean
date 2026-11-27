import WideEIntegralClosed.BroadFilteredDenominators
import ActualFiniteLaurentScalarGauge
import ActualParallelPreimageExtraction
import Mathlib.Algebra.Field.NegOnePow

/-! Broad denominator arithmetic for the actual logarithmic Laplace preimages. -/

noncomputable section

open scoped BigOperators Matrix
open StrictEUnit

namespace WideEIntegralClosed

/-- Subfactorial denominators for the Laurent coefficients of a logarithmic solution. -/
def HasSubfactorialLogLaurentDenominators {K : Type*} [Field K] (u : LaurentSeries (Polynomial K)) : Prop :=
  HasSubfactorialPrefixDenominators fun N D =>
    ∀ m : ℤ, m ≤ (N : ℤ) → ∀ t, IsIntegral ℤ ((D : K) * (u.coeff m).coeff t)

/-- Restricting to nonnegative indices preserves the same bound and multipliers. -/
theorem HasSubfactorialLogLaurentDenominators.natural_indices {K : Type*} [Field K]
    {u : LaurentSeries (Polynomial K)} (hu : HasSubfactorialLogLaurentDenominators u) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ t, IsIntegral ℤ ((D : K) * (u.coeff (m : ℤ)).coeff t) := by
  intro ε hε
  obtain ⟨B, hB, hden⟩ := hu ε hε
  refine ⟨B, hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hden N
  exact ⟨D, hD, hDb, fun m hm t => hDi m (by exact_mod_cast hm) t⟩

/-- An integer Laurent monomial changes the required cutoff by a fixed amount. -/
theorem HasSubfactorialLogLaurentDenominators.monomial {K : Type*} [Field K] [CharZero K]
    {u : LaurentSeries (Polynomial K)} (hu : HasSubfactorialLogLaurentDenominators u) (k : ℤ) :
    HasSubfactorialLogLaurentDenominators (HahnSeries.single k (1 : Polynomial K) * u) := by
  let A := k.natAbs
  have hshift : -k ≤ (A : ℤ) := by simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -k))
  refine HasSubfactorialPrefixDenominators.affine hu (A + 1) (by omega) ?_
  intro N D hDi m hm t
  rw [logMonomial_one_mul_coeff]
  have hcutoff : N + A ≤ (A + 1) * (N + 1) := by nlinarith
  exact hDi (m - k) (by omega) t

private theorem subfactorial_reflection {K : Type*} [Field K]
    {u : LaurentSeries (Polynomial K)} (hu : HasSubfactorialLogLaurentDenominators u) :
    HasSubfactorialLogLaurentDenominators (logLaurentReflection u) := by
  intro ε hε
  obtain ⟨B, hB, hden⟩ := hu ε hε
  refine ⟨B, hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hden N
  refine ⟨D, hD, hDb, fun m hm t => ?_⟩
  change IsIntegral ℤ ((D : K) * (((-1 : K) ^ m) • u.coeff m).coeff t)
  rw [Polynomial.coeff_smul, smul_eq_mul]
  have hsign : IsIntegral ℤ ((-1 : K) ^ m) := by
    rw [← Int.cast_negOnePow]
    exact isIntegral_algebraMap
  convert hsign.mul (hDi m hm t) using 1
  ring

private theorem undo_reflected_gauge {K : Type*} [Field K] [CharZero K]
    (u : LaurentSeries (Polynomial K)) (k g : ℤ)
    (h : HasSubfactorialLogLaurentDenominators (HahnSeries.single k (1 : Polynomial K) *
      logLaurentReflection (HahnSeries.single g (1 : Polynomial K) * u))) :
    HasSubfactorialLogLaurentDenominators u := by
  have h1 := h.monomial (-k)
  simp only [← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
    HahnSeries.single_zero_one] at h1
  have h2 := subfactorial_reflection h1
  rw [logLaurentReflection_involutive] at h2
  have h3 := h2.monomial (-g)
  simpa only [← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, one_mul,
    HahnSeries.single_zero_one] using h3

private theorem subfactorial_logLaurent_component {K : Type*} [Field K] {r : ℕ}
    (u : Fin r → LaurentSeries (Polynomial K))
    (h : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m : ℤ, m ≤ (N : ℤ) → ∀ i t, IsIntegral ℤ ((D : K) * ((u i).coeff m).coeff t)) (i : Fin r) :
    HasSubfactorialLogLaurentDenominators (u i) := by
  intro ε hε
  obtain ⟨B, hB, hden⟩ := h ε hε
  refine ⟨B, hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hden N
  exact ⟨D, hD, hDb, fun m hm t => hDi m hm i t⟩

/-- For a noninteger exponent, the actual logarithmic Laplace preimage is an ordinary
homogeneous source solution. Its Laurent logarithmic coefficients inherit the broad bound. -/
theorem broad_actual_noninteger_preimage_arithmetic
    {K : Type u} [Field K] [NumberField K]
    (hbinomial : ∀ {L : Type u} [Field L] [NumberField L] (ξ : L),
      HasSubfactorialBinomialDenominators ξ → BinomialPrefixDenominators ξ)
    (n : ℕ) (c : Fin (n + 1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial K)) (hT : T ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * minimalDerivativeCompanion (n + 1) c i j)
    (hV : ∀ j, U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree + j.val ≤ (U (Fin.last n) j).natTrailingDegree + (n + 1))
    (hC : HasSubfactorialEulerConnectionDenominators (sourceLaurentEulerBase n T U 0))
    (rho : K) (hni : ∀ z : ℤ, rho ≠ (z : K)) (f : Polynomial (LaurentSeries K))
    (hf :
      let q := ordinaryReflectionTuple (n + 1) (sameCompanionScalarTuple (n + 1) (Nat.succ_pos n) T U)
      actualTwistedStage53Action rho (reciprocalSourceArray (n + 1) (reciprocalCommonDegree (n + 1) q) q) f = 0) :
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear rho (logMixing_noninteger_forward_nonzero rho hni) u =
        logPolynomialToCoefficientSeries f ∧
      (∀ m, (u.coeff m).natDegree ≤ f.natDegree) ∧ HasSubfactorialLogLaurentDenominators u := by
  obtain ⟨u, hu, hdeg, hsol⟩ := actualStage53_noninteger_original_euler_solution rho hni n c T U hT hclear hV f hf
  refine ⟨u, hu, hdeg, ?_⟩
  let x := fun i : Fin (n + 1) => HahnSeries.single ((T.natTrailingDegree + i.val : ℕ) : ℤ)
    (1 : Polynomial K) * generalizedLogOrdinaryJet rho n
      (logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ * u)) i
  let C := sourceLaurentEulerBase n T U 0
  have hx : ∀ i, twistedPolynomialCoefficientEuler rho (x i) =
      ∑ j, logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j)) * x j := by
    intro i
    rw [← twistedLogCoefficientEuler_eq]
    simpa only [actualPowerSeries_log_embedding] using hsol i
  obtain ⟨b, G, H, hb, _, hGH, hHG, hg⟩ := cyclicShape_exists_scalarGauge C (Nat.succ_pos n)
    (sourceLaurentEulerBase_cyclicShape n T U 0)
  have ha := regularScalarGauge_solution_common_subfactorial_denominators C (Nat.succ_pos n) hC
    b hb G H hGH hHG hg (fun ξ => hbinomial ξ) rho x hx
  have hi := subfactorial_logLaurent_component x ha 0
  dsimp [x, generalizedLogOrdinaryJet] at hi
  rw [logLaurentCoefficientMap_reciprocalZ] at hi
  exact undo_reflected_gauge u (T.natTrailingDegree : ℤ) (-1) hi

/-- The zero-exponent Laplace preimage is a solution of the finite Laurent forcing extension.
The broad arithmetic of that extension yields broad denominators for the preimage itself. -/
theorem broad_actual_zero_preimage_arithmetic
    {K : Type u} [Field K] [NumberField K]
    (hbinomial : ∀ {L : Type u} [Field L] [NumberField L] (ξ : L),
      HasSubfactorialBinomialDenominators ξ → BinomialPrefixDenominators ξ)
    (n : ℕ) (c : Fin (n + 1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial K)) (hT : T ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * minimalDerivativeCompanion (n + 1) c i j)
    (hV : ∀ j, U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree + j.val ≤ (U (Fin.last n) j).natTrailingDegree + (n + 1))
    (hEuler : ∀ d s : ℕ,
      let k := fun j : ℕ => (d : ℤ) - (j : ℤ)
      let M := finiteLaurentOffset k (s + 1)
      HasSubfactorialEulerConnectionDenominators (finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
        (augmentedSourceEulerColumn n T) (M + (n + 1)) k (s + 1)))
    (f : Polynomial (LaurentSeries K))
    (hf :
      let q := ordinaryReflectionTuple (n + 1) (sameCompanionScalarTuple (n + 1) (Nat.succ_pos n) T U)
      actualTwistedStage53Action 0 (reciprocalSourceArray (n + 1) (reciprocalCommonDegree (n + 1) q) q) f = 0) :
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u = logPolynomialToCoefficientSeries f ∧
      (∀ m, (u.coeff m).natDegree ≤ f.natDegree + 1) ∧ HasSubfactorialLogLaurentDenominators u := by
  obtain ⟨u, hu, hdeg, P, hsol⟩ := actualStage53_zero_original_euler_solution n c T U hT hclear hV f hf
  refine ⟨u, hu, hdeg, ?_⟩
  let q := ordinaryReflectionTuple (n + 1) (sameCompanionScalarTuple (n + 1) (Nat.succ_pos n) T U)
  let d := reciprocalCommonDegree (n + 1) q
  let k := fun j : ℕ => (d : ℤ) - (j : ℤ)
  let s := P.natDegree
  let M := finiteLaurentOffset k (s + 1)
  let w := fun i : Fin (n + 1) => M + T.natTrailingDegree + i.val
  let v := parallelForcingVector (generalizedLogOrdinaryJet 0 n
    (logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ * u))) (reflectedResidualConstant d P) (s + 1)
  let x := fun i => HahnSeries.single (finiteLaurentEulerWeights w (M + (n + 1)) k (s + 1) i : ℤ)
    (1 : Polynomial K) * v i
  let C := finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
    (augmentedSourceEulerColumn n T) (M + (n + 1)) k (s + 1)
  have hx : ∀ i, twistedPolynomialCoefficientEuler 0 (x i) =
      ∑ j, logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j)) * x j := by
    intro i
    rw [← twistedLogCoefficientEuler_eq]
    simpa only [actualPowerSeries_log_embedding] using hsol i
  have hinj : Function.Injective (fun j : Fin (s + 1) =>
      ((((M + (n + 1) : ℕ) : ℤ) + k j.val : ℤ) : K)) := by
    have h := shiftedResidualEigenvalues_injective (K := K) (s + 1) ((M + (n + 1) : ℕ) : ℤ) (d : ℤ)
    convert h using 1
    funext j
    dsimp [k]
    push_cast
    ring
  obtain ⟨b, G, H, hb, hGH, hHG, hg⟩ := actualFiniteLaurentSource_scalarGauge n s M (M + (n + 1)) T U hT k
    (by simpa only [Int.cast_add] using hinj)
  have ha := regularScalarGauge_solution_common_subfactorial_denominators C (by omega) (hEuler d s)
    b hb G H hGH hHG hg (fun ξ => hbinomial ξ) 0 x hx
  have hi := subfactorial_logLaurent_component x ha (parallelSourceIndex (0 : Fin (n + 1)) (s + 1))
  change HasSubfactorialLogLaurentDenominators
    (HahnSeries.single (finiteLaurentEulerWeights w (M + (n + 1)) k (s + 1) (parallelSourceIndex 0 (s + 1)) : ℤ)
      (1 : Polynomial K) * parallelForcingVector _ _ (s + 1) (parallelSourceIndex 0 (s + 1))) at hi
  rw [finiteLaurentEulerWeights_source, parallelForcingVector_source] at hi
  simp only [generalizedLogOrdinaryJet, Fin.val_zero, Function.iterate_zero, id_eq] at hi
  rw [logLaurentCoefficientMap_reciprocalZ] at hi
  exact undo_reflected_gauge u (w 0 : ℤ) (-1) hi

end WideEIntegralClosed
