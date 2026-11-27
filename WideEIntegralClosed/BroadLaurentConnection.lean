import WideE.ConnectionArithmetic
import WideEIntegralClosed.SubfactorialPrefixes
import SingularConnectionLaurentArithmetic
import RationalLaurentConnectionTransport

/-! Subfactorial arithmetic for the same divided connection in the Laurent field. -/

noncomputable section

open scoped BigOperators Matrix NumberField
open StrictEUnit

namespace WideEIntegralClosed

/-- An affine prefix cutoff and a geometric multiplier preserve subfactorial growth. -/
theorem HasSubfactorialPrefixDenominators.affine_mul {P Q R : ℕ → ℕ → Prop}
    (hP : HasSubfactorialPrefixDenominators P) {a : ℕ} (ha : 0 < a) (B : ℝ) (hB : 1 ≤ B)
    (hQ : ∀ N, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ B ^ (N + 1) ∧ Q N q)
    (transfer : ∀ N d q, P (a * (N + 1)) d → Q N q → R N (d * q)) :
    HasSubfactorialPrefixDenominators R := by
  intro ε hε
  let η : ℝ := ε / (2 * (a : ℝ))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hηmul : (a : ℝ) * η = ε / 2 := by
    dsimp only [η]
    field_simp [show (a : ℝ) ≠ 0 from by positivity]
    ring
  obtain ⟨C, hC, hPrefix⟩ := hP η hη
  obtain ⟨D, hD, hStretch⟩ := WideE.exists_affine_factorial_rpow_bound a η hη.le
  let H := D * B
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hD hB
  obtain ⟨E, hE, hGeom⟩ := WideE.exists_exp_pow_le_factorial_rpow H (ε / 2) hH (by positivity)
  refine ⟨C * H * E, one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC hH) hE,
    fun N => ?_⟩
  obtain ⟨d, hd, hdb, hInput⟩ := hPrefix (a * (N + 1))
  obtain ⟨q, hq, hqb, hqClear⟩ := hQ N
  refine ⟨d * q, Nat.mul_pos hd hq, ?_, transfer N d q hInput hqClear⟩
  have hs := hdb.trans (mul_le_mul_of_nonneg_left (hStretch N) (zero_le_one.trans hC))
  rw [hηmul] at hs
  have hFac : (N.factorial : ℝ) ^ (ε / 2) * (N.factorial : ℝ) ^ (ε / 2) =
      (N.factorial : ℝ) ^ ε := by
    rw [← Real.rpow_add (by positivity), add_halves]
  rw [Nat.cast_mul]
  calc
    (d : ℝ) * (q : ℝ) ≤ (C * (D ^ (N + 1) * (N.factorial : ℝ) ^ (ε / 2))) * B ^ (N + 1) :=
      mul_le_mul hs hqb (by positivity) (by positivity)
    _ = (C * H) * (H ^ N * (N.factorial : ℝ) ^ (ε / 2)) := by
      dsimp only [H]
      rw [pow_succ D, pow_succ B, mul_pow]
      ring
    _ ≤ (C * H) * ((E * (N.factorial : ℝ) ^ (ε / 2)) * (N.factorial : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hGeom N) (by positivity))
        (by positivity)
    _ = (C * H * E) * (N.factorial : ℝ) ^ ε := by
      rw [← hFac]
      ring

/-- Broad divided-connection arithmetic consists of a linear pole bound and
subfactorial common denominators for a joint prefix of derivatives and Laurent coefficients. -/
def BroadLaurentDividedConnectionArithmetic {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) : Prop :=
  ∃ P : ℕ,
    (∀ m i j l, l < -((P * m : ℕ) : ℤ) →
      (matrixConnectionSequence stage14_laurentAlgebraDerivation A m i j /
        (m.factorial : LaurentSeries K)).coeff l = 0) ∧
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ i j (l : ℤ), l ≤ (N : ℤ) → IsIntegral ℤ ((D : K) *
        (matrixConnectionSequence stage14_laurentAlgebraDerivation A m i j /
          (m.factorial : LaurentSeries K)).coeff l)

/-- The broad local quotient bound for a polynomial divided-connection numerator. -/
theorem poleClearedPolynomialQuotientGerm_subfactorial {K ι : Type*} [Field K] [NumberField K]
    (T : Polynomial (𝓞 K)) (H : ℕ → ι → Polynomial K)
    (hT : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (hden : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ i k, IsIntegral ℤ ((D : K) * (H m i).coeff k)) :
    let t := T.map (algebraMap (𝓞 K) K)
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m k, m + k ≤ N → ∀ i, IsIntegral ℤ ((D : K) *
        PowerSeries.coeff K k (poleClearedPolynomialQuotientGerm t (H m i) m)) := by
  intro t
  let v := T.coeff t.natTrailingDegree
  let τ := t.coeff t.natTrailingDegree
  let q := Int.natAbs (Algebra.norm ℤ v)
  have hvmap : (v : K) = τ := by
    dsimp only [v, τ, t]
    rw [Polynomial.coeff_map]
  have hτ : τ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hv : v ≠ 0 := by
    intro h
    apply hτ
    rw [← hvmap, h]
    rfl
  have hq : 0 < q := (ringOfIntegers_natAbs_norm_certificate v hv).1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt hq
  refine hden.affine_mul (a := 1) Nat.one_pos (q : ℝ) hq1
    (Q := fun N e => e = q ^ N) (fun N => ⟨q ^ N, pow_pos hq _, ?_, rfl⟩) ?_
  · rw [Nat.cast_pow]
    exact pow_le_pow_right₀ hq1 (Nat.le_succ _)
  intro N D e hint he m k hmk i
  subst e
  have hf (j : ℕ) : IsIntegral ℤ (PowerSeries.coeff K j (sameCompanionEulerDenominatorSeries t)) := by
    simp only [sameCompanionEulerDenominatorSeries, polynomialTailPowerSeries, PowerSeries.coeff_mk,
      t, Polynomial.coeff_map]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  have hi := powerSeries_cleared_mul_inverse_pow_integral
    (sameCompanionEulerDenominatorSeries t) (H m i : PowerSeries K) τ (D : K)
    (sameCompanionEulerDenominatorSeries_constantCoeff t) hτ hf
    (by intro j; simpa only [Polynomial.coeff_coe] using hint m (by omega) i j) m k
  apply integral_norm_clears_integral_power v hv D N (m + k) hmk
  simpa only [hvmap, poleClearedPolynomialQuotientGerm] using hi

/-- Restoring the coordinate pole costs only an affine enlargement of the prefix. -/
theorem bivariate_germ_subfactorial_laurent_prefix {K ι : Type*} [Field K]
    (g : ℕ → ι → PowerSeries K) (x : ℕ → ι → LaurentSeries K) (t : ℕ)
    (hidentity : ∀ m i, HahnSeries.ofPowerSeries ℤ K (g m i) =
      (HahnSeries.ofPowerSeries ℤ K PowerSeries.X) ^ (t * m) * x m i)
    (hden : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m l, m + l ≤ N → ∀ i, IsIntegral ℤ ((D : K) * PowerSeries.coeff K l (g m i))) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ k : ℤ, k ≤ N → ∀ i, IsIntegral ℤ ((D : K) * (x m i).coeff k) := by
  refine hden.affine_mul (a := t + 2) (by omega) 1 le_rfl
    (Q := fun _ q => q = 1) (fun _ => ⟨1, Nat.one_pos, by simp, rfl⟩) ?_
  intro N D q hint hq m hm k hk i
  subst q
  rw [Nat.mul_one, powerSeries_monomial_laurent_coefficient
    (g m i) (x m i) (t * m) (hidentity m i) k]
  split_ifs
  · apply hint m _ _ i
    have hcast : ((t * m : ℕ) : ℤ) + k ≤ ((t * m + N : ℕ) : ℤ) := by
      exact_mod_cast add_le_add_left hk ((t * m : ℕ) : ℤ)
    have hl : (((t * m : ℕ) : ℤ) + k).toNat ≤ t * m + N := by
      simpa only [Int.toNat_natCast] using Int.toNat_le_toNat hcast
    calc
      m + (((t * m : ℕ) : ℤ) + k).toNat ≤ N + (t * N + N) := by
        have hmul := Nat.mul_le_mul_left t hm
        omega
      _ = (t + 2) * N := by ring
      _ ≤ (t + 2) * (N + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  · rw [mul_zero]
    exact isIntegral_zero

/-- The same polynomial clearing controls the actual rational companion after Laurent expansion. -/
theorem broadLaurentDividedConnectionArithmetic_of_polynomial_clearing
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (c : Fin r → RatFunc K) (T : Polynomial (𝓞 K))
    (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hT : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K)) *
        minimalDerivativeCompanion r c i j)
    (hden : WideE.HasSubfactorialConnectionDenominators (T.map (algebraMap (𝓞 K) K)) U) :
    BroadLaurentDividedConnectionArithmetic
      (Matrix.map (minimalDerivativeCompanion r c) (algebraMap (RatFunc K) (LaurentSeries K))) := by
  let t := T.map (algebraMap (𝓞 K) K)
  let C : Matrix (Fin r) (Fin r) (RatFunc K) := minimalDerivativeCompanion r c
  let H (m : ℕ) (ij : Fin r × Fin r) :=
    dividedPolynomialConnectionSequence t U m ij.1 ij.2
  let g (m : ℕ) (ij : Fin r × Fin r) :=
    samePoleClearedDividedConnectionGerm t U m ij.1 ij.2
  let x (m : ℕ) (ij : Fin r × Fin r) :=
    algebraMap (RatFunc K) (LaurentSeries K) ((m.factorial : RatFunc K)⁻¹ *
      matrixConnectionSequence stage14_rationalOrdinaryDerivation C m ij.1 ij.2)
  have hid (m : ℕ) (ij : Fin r × Fin r) :=
    samePoleClearedDividedConnectionGerm_rational_identity C t U hT hclear m ij.1 ij.2
  have hH : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ ij k, IsIntegral ℤ ((D : K) * (H m ij).coeff k) := by
    intro ε hε
    obtain ⟨A, hA, hBound⟩ := hden ε hε
    refine ⟨A, hA, fun N => ?_⟩
    obtain ⟨D, hD, hDb, hDi⟩ := hBound N
    exact ⟨D, hD, hDb, fun m hm ij k => hDi m hm ij.1 ij.2 k⟩
  have hg := poleClearedPolynomialQuotientGerm_subfactorial T H hT hH
  have hLaurent := bivariate_germ_subfactorial_laurent_prefix g x t.natTrailingDegree hid hg
  refine ⟨t.natTrailingDegree, ?_, ?_⟩
  · intro m i j l hl
    rw [rational_laurent_divided_connection]
    change (x m (i, j)).coeff l = 0
    rw [powerSeries_monomial_laurent_coefficient (g m (i, j)) (x m (i, j))
      (t.natTrailingDegree * m) (hid m (i, j)) l, dif_neg (by omega)]
  · intro ε hε
    obtain ⟨A, hA, hBound⟩ := hLaurent ε hε
    refine ⟨A, hA, fun N => ?_⟩
    obtain ⟨D, hD, hDb, hDi⟩ := hBound N
    refine ⟨D, hD, hDb, fun m hm i j l hl => ?_⟩
    rw [rational_laurent_divided_connection]
    exact hDi m hm l hl (i, j)

end WideEIntegralClosed
