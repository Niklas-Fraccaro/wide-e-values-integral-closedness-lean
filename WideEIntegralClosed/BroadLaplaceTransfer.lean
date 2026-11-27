import FiniteLogMixingDenominatorTransfer
import WideEIntegralClosed.SubfactorialPrefixes

/-! The normalized logarithmic Laplace transform preserves broad prefix bounds. -/

noncomputable section

open StrictEUnit

namespace WideEIntegralClosed

private theorem subfactorial_shifted_prefix_product {P Q R : ℕ → ℕ → Prop}
    (hP : HasSubfactorialPrefixDenominators P) (C : ℝ) (hC : 1 ≤ C)
    (hQ : ∀ N, ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C ^ (N + 1) ∧ Q N q)
    (transfer : ∀ N d q, P (N + 1) d → Q N q → R N (d * q)) :
    HasSubfactorialPrefixDenominators R := by
  intro ε hε
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A, hA, hPrefix⟩ := hP η hη
  let B : ℝ := (2 : ℝ) ^ η
  have hB : 1 ≤ B := Real.one_le_rpow (by norm_num) hη.le
  have hBC : 1 ≤ B * C := one_le_mul_of_one_le_of_one_le hB hC
  obtain ⟨D, hD, hGeom⟩ := WideE.exists_exp_pow_le_factorial_rpow (B * C) η hBC hη
  refine ⟨A * C * D, one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hC) hD,
    fun N => ?_⟩
  obtain ⟨d, hd, hdb, hp⟩ := hPrefix (N + 1)
  obtain ⟨q, hq, hqb, hqClear⟩ := hQ N
  refine ⟨d * q, Nat.mul_pos hd hq, ?_, transfer N d q hp hqClear⟩
  have hShift : ((N + 1).factorial : ℝ) ^ η ≤ B ^ N * (N.factorial : ℝ) ^ η := by
    have hpow : (N + 1 : ℝ) ≤ (2 : ℝ) ^ N := by
      exact_mod_cast Nat.succ_le_of_lt (show N < 2 ^ N from Nat.lt_two_pow_self)
    have hcast : ((N + 1).factorial : ℝ) = (N + 1 : ℝ) * (N.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [hcast, Real.mul_rpow (by positivity) (by positivity)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      (N + 1 : ℝ) ^ η ≤ ((2 : ℝ) ^ N) ^ η :=
        Real.rpow_le_rpow (by positivity) hpow hη.le
      _ = B ^ N := by
        dsimp only [B]
        rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), mul_comm (N : ℝ)]
  have hFac : (N.factorial : ℝ) ^ η * (N.factorial : ℝ) ^ η = (N.factorial : ℝ) ^ ε := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    exact add_halves ε
  rw [Nat.cast_mul]
  calc
    (d : ℝ) * (q : ℝ) ≤ (A * (B ^ N * (N.factorial : ℝ) ^ η)) * C ^ (N + 1) :=
      mul_le_mul (hdb.trans (mul_le_mul_of_nonneg_left hShift (zero_le_one.trans hA)))
        hqb (by positivity) (by positivity)
    _ = (A * C) * ((B * C) ^ N * (N.factorial : ℝ) ^ η) := by
      rw [pow_succ C, mul_pow]
      ring
    _ ≤ (A * C) * ((D * (N.factorial : ℝ) ^ η) * (N.factorial : ℝ) ^ η) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hGeom N) (by positivity))
        (by positivity)
    _ = (A * C * D) * (N.factorial : ℝ) ^ ε := by
      rw [← hFac]
      ring

/-- The coefficients of the full mixed logarithmic Laplace image have subfactorial
denominators in factorial normalization. The finite mixing matrix retains its geometric bound. -/
theorem generalizedLogLaplace_hasSubfactorialDenominators
    {K : Type*} [Field K] [NumberField K]
    (ρ : K) (h : ∀ n : ℕ, ρ + (n + 1 : ℕ) ≠ 0)
    (u : LaurentSeries (Polynomial K)) (d : ℕ)
    (hdegree : ∀ n : ℕ, (u.coeff ((n : ℤ) + 1)).natDegree ≤ d)
    (hu : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ t, IsIntegral ℤ ((D : K) * (u.coeff (m : ℤ)).coeff t))
    (hmix : ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ C ^ (N + 1) ∧
      ∀ n ≤ N, ∀ j ≤ d, ∀ t,
        IsIntegral ℤ ((Q : K) * (factorialLogMixing ρ n (Polynomial.X ^ j)).coeff t)) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ n ≤ N, ∀ t, IsIntegral ℤ ((D : K) * (n.factorial : K) *
        ((generalizedLogLaplaceSeries ρ h u).coeff (n : ℤ)).coeff t) := by
  obtain ⟨C, hC, hMixing⟩ := hmix
  refine subfactorial_shifted_prefix_product hu C hC hMixing ?_
  intro N D Q hInput hMix n hn t
  have hInt (j : ℕ) : IsIntegral ℤ ((D : K) * (u.coeff ((n : ℤ) + 1)).coeff j) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hInput (n + 1) (by omega) j
  have hnorm := factorialLogMixing_denominator_transfer ρ h n d D Q
    (u.coeff ((n : ℤ) + 1)) (hdegree n) hInt (hMix n hn)
  have he := congrArg (fun p : Polynomial K => p.coeff t)
    (generalizedLogLaplaceSeries_factorial_log_coefficient ρ h u n)
  simp only [Polynomial.coeff_smul, smul_eq_mul] at he
  rw [mul_assoc, he]
  have hi : IsIntegral ℤ ((-1 : K) ^ n) := isIntegral_one.neg.pow n
  convert hi.mul (hnorm t) using 1
  ring

end WideEIntegralClosed
