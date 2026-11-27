import FinitePrimeRateBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Bounds on primes from broad binomial denominators

Subfactorial clearing denominators for the binomial coefficients of an exponent force a
small logarithmically weighted sum of the primes where its residue avoids the prime field.
-/

noncomputable section

open scoped BigOperators

namespace WideEIntegralClosed

private theorem half_div_le_nat_div {n p : ℕ} (hp : 0 < p) (hpn : p ≤ n) :
    (n : ℝ) / (2 * (p : ℝ)) ≤ ((n / p : ℕ) : ℝ) := by
  have hq : 1 ≤ n / p := Nat.div_pos hpn hp
  have hmod := Nat.mod_lt n hp
  have hdiv := Nat.div_add_mod n p
  have hmul := Nat.mul_le_mul_left p hq
  simp only [Nat.mul_one] at hmul
  have hle : n ≤ 2 * (p * (n / p)) := by omega
  have hle' : (n : ℝ) ≤ 2 * ((p : ℝ) * ((n / p : ℕ) : ℝ)) := by exact_mod_cast hle
  apply (div_le_iff₀ (by positivity : 0 < 2 * (p : ℝ))).2
  simpa only [mul_left_comm, mul_comm, mul_assoc] using hle'

/-- A clearing denominator for the `n`th binomial coefficient bounds the contribution
of any finite set of primes at most `n` that carry the indicated valuations. -/
theorem weighted_prime_sum_le_log_binomial_denominator
    {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]
    (a : K) (n d : ℕ) (hd : 0 < d) (S : Finset ℕ)
    (v : ℕ → Valuation K Γ₀)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ n)
    (hvp : ∀ p ∈ S, v p (p : K) < 1)
    (hu : ∀ p ∈ S, ∀ j : ℕ, j < n → v p (a - (j : K)) = 1)
    (hint : IsIntegral ℤ ((d : K) * ((descPochhammer K n).eval a / (n.factorial : K)))) :
    (n : ℝ) / 2 * (∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ)) ≤ Real.log (d : ℝ) := by
  let D : ℕ := ∏ p ∈ S, p ^ (n / p)
  have hDpos : 0 < D := Finset.prod_pos fun p hp => pow_pos (hS p hp).1.pos _
  have hDd : D ∣ d := StrictEUnit.binomial_denominator_prime_product_dvd a n d S
    (fun p => n / p) v (fun p hp => (hS p hp).1) hvp hu hint
    (fun p hp => StrictEUnit.prime_floor_power_dvd_factorial p n (hS p hp).1)
  have hle : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.le_of_dvd hd hDd
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hDpos) hle
  have hlogD : Real.log (D : ℝ) = ∑ p ∈ S, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    dsimp [D]
    rw [Nat.cast_prod, Real.log_prod]
    · simp only [Nat.cast_pow, Real.log_pow]
    · intro p hp
      exact_mod_cast (pow_ne_zero (n / p) (hS p hp).1.ne_zero)
  refine le_trans ?_ hlog
  rw [hlogD, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpos : (0 : ℝ) < p := Nat.cast_pos.mpr (hS p hp).1.pos
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hS p hp).1.one_lt.le)
  calc
    (n : ℝ) / 2 * (Real.log (p : ℝ) / (p : ℝ)) =
        ((n : ℝ) / (2 * (p : ℝ))) * Real.log (p : ℝ) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (half_div_le_nat_div (hS p hp).1.pos (hS p hp).2) hlogp

/-- Subfactorial binomial denominators force an arbitrarily small coefficient of
`log n` in the upper bound on the weighted sum of the certified primes at most `n`. -/
theorem weighted_prime_sum_le_of_subfactorial_binomial_denominators
    {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]
    (a : K) (v : ℕ → Valuation K Γ₀)
    (hD : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ,
      ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * (n.factorial : ℝ) ^ δ ∧
        IsIntegral ℤ ((d : K) * ((descPochhammer K n).eval a / (n.factorial : K)))) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ), 0 < n → ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime ∧ p ≤ n) →
      (∀ p ∈ S, v p (p : K) < 1) →
      (∀ p ∈ S, ∀ j : ℕ, j < n → v p (a - (j : K)) = 1) →
      (∑ p ∈ S, Real.log (p : ℝ) / (p : ℝ)) ≤ B + ε * Real.log (n : ℝ) := by
  intro ε hε
  obtain ⟨C, hC, hD⟩ := hD (ε / 2) (by positivity)
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hCLog := Real.log_nonneg hC
  refine ⟨2 * Real.log C, by positivity, ?_⟩
  intro n hn S hS hvp hu
  obtain ⟨d, hd, hdb, hdi⟩ := hD n
  have npos : 0 < (n : ℝ) := by exact_mod_cast hn
  have none : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have fpos : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hDf := weighted_prime_sum_le_log_binomial_denominator a n d hd S v hS hvp hu hdi
  have hdbLog := Real.log_le_log (Nat.cast_pos.mpr hd) hdb
  rw [Real.log_mul hCpos.ne' (Real.rpow_pos_of_pos fpos _).ne', Real.log_rpow fpos] at hdbLog
  have hfact : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  have hfl := Real.log_le_log fpos hfact
  rw [Real.log_pow] at hfl
  apply (mul_le_mul_left (by positivity : 0 < (n : ℝ) / 2)).1
  calc
    _ ≤ Real.log (d : ℝ) := hDf
    _ ≤ Real.log C + ε / 2 * Real.log (n.factorial : ℝ) := hdbLog
    _ ≤ Real.log C + ε / 2 * ((n : ℝ) * Real.log (n : ℝ)) := by gcongr
    _ ≤ (n : ℝ) / 2 * (2 * Real.log C + ε * Real.log (n : ℝ)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr none) hCLog]

end WideEIntegralClosed
