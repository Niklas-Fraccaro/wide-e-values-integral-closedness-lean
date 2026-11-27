import BinomialPrefixShiftClosure
import Mathlib.RingTheory.PowerSeries.Binomial

/-! Geometric common denominators for binomial coefficients at rational exponents. -/

noncomputable section

open scoped BigOperators
open Finset StrictEUnit

namespace WideEIntegralClosed

private theorem binomialSeries_nsmul_rat (x : ℚ) (d : ℕ) :
    PowerSeries.binomialSeries ℚ (d • x) = PowerSeries.binomialSeries ℚ x ^ d := by
  induction d with
  | zero =>
    ext n
    simp only [zero_nsmul, pow_zero, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
      PowerSeries.coeff_one, Ring.choose_zero_ite]
  | succ d ih =>
    rw [succ_nsmul, PowerSeries.binomialSeries_add, ih, pow_succ]

private theorem rat_choose_intCast (a : ℤ) (n : ℕ) :
    Ring.choose (a : ℚ) n = ((Ring.choose a n : ℤ) : ℚ) := by
  rw [field_choose_eq_descPochhammer_div, ← descPochhammer_eval_cast,
    Polynomial.eval_eq_smeval, Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast]
  field_simp

private theorem integral_coeff_pow_of_smaller {g : PowerSeries ℚ} {n j : ℕ}
    (hj : 2 ≤ j) (hzero : PowerSeries.coeff ℚ 0 g = 0)
    (hsmall : ∀ m < n, IsIntegral ℤ (PowerSeries.coeff ℚ m g)) :
    IsIntegral ℤ (PowerSeries.coeff ℚ n (g ^ j)) := by
  classical
  rw [PowerSeries.coeff_pow]
  apply IsIntegral.sum
  intro l hl
  by_cases hall : ∀ i ∈ Finset.range j, l i < n
  · apply IsIntegral.prod
    intro i hi
    exact hsmall (l i) (hall i hi)
  · push_neg at hall
    obtain ⟨i, hi, hni⟩ := hall
    have hsum : (∑ t ∈ Finset.range j, l t) = n := (Finset.mem_finsuppAntidiag.mp hl).1
    have hbound : l i ≤ n :=
      (Finset.single_le_sum (f := fun k => l k) (fun _ _ => Nat.zero_le _) hi).trans_eq hsum
    have heq : l i = n := le_antisymm hbound hni
    obtain ⟨k, hk, hki⟩ := Finset.exists_mem_ne (s := Finset.range j) (by simpa using hj) i
    have hK : l k ≤ ∑ t ∈ (Finset.range j).erase i, l t :=
      Finset.single_le_sum (f := fun u => l u) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hki, hk⟩)
    have hErase : (∑ t ∈ (Finset.range j).erase i, l t) + l i =
        ∑ t ∈ Finset.range j, l t := Finset.sum_erase_add (Finset.range j) (fun u => l u) hi
    have hkzero : l k = 0 := by omega
    rw [Finset.prod_eq_zero hk (by rw [hkzero, hzero])]
    exact isIntegral_zero

private def higherPowers (d : ℕ) (g : PowerSeries ℚ) : PowerSeries ℚ :=
  ∑ j ∈ Finset.range d,
    PowerSeries.C ℚ (((d + 1 : ℕ) : ℚ) ^ j * ((d + 1).choose (j + 2) : ℚ)) * g ^ (j + 2)

private theorem binomial_root_expansion (d : ℕ) (g : PowerSeries ℚ) :
    (1 + PowerSeries.C ℚ ((d + 1 : ℕ) : ℚ) * g) ^ (d + 1) =
      1 + PowerSeries.C ℚ (((d + 1 : ℕ) : ℚ) ^ 2) * (g + higherPowers d g) := by
  let c : PowerSeries ℚ := PowerSeries.C ℚ ((d + 1 : ℕ) : ℚ)
  change (1 + c * g) ^ (d + 1) = 1 + (PowerSeries.C ℚ _) * (g + higherPowers d g)
  rw [add_comm 1, add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [zero_add, pow_zero, pow_one, Nat.choose_zero_right, Nat.choose_one_right, one_pow,
    Nat.cast_one, mul_one]
  have hc : ((d + 1 : ℕ) : PowerSeries ℚ) = c := by simp [c]
  rw [hc, map_pow, mul_add, higherPowers, Finset.mul_sum]
  have hsum :
      ∑ j ∈ Finset.range d, (c * g) ^ (j + 1 + 1) * ((d + 1).choose (j + 1 + 1) : PowerSeries ℚ) =
      ∑ j ∈ Finset.range d, c ^ 2 *
        (PowerSeries.C ℚ (((d + 1 : ℕ) : ℚ) ^ j * ((d + 1).choose (j + 2) : ℚ)) * g ^ (j + 2)) := by
    apply Finset.sum_congr rfl
    intro j _
    change (c * g) ^ (j + 2) * ((d + 1).choose (j + 2) : PowerSeries ℚ) = _
    rw [map_mul, map_pow, map_natCast, mul_pow, pow_add c j 2]
    change _ = c ^ 2 * ((c ^ j * _) * g ^ (j + 2))
    simp only [map_natCast]
    ring
  rw [hsum]
  change _ = 1 + (c ^ 2 * g + _)
  ring

private theorem integral_coeff_of_binomial_root (d : ℕ) (g : PowerSeries ℚ)
    (hzero : PowerSeries.coeff ℚ 0 g = 0)
    (hdiv : ∀ n, 0 < n → IsIntegral ℤ
      (PowerSeries.coeff ℚ n ((1 + PowerSeries.C ℚ ((d + 1 : ℕ) : ℚ) * g) ^ (d + 1)) /
        (((d + 1 : ℕ) : ℚ) ^ 2))) :
    ∀ n, IsIntegral ℤ (PowerSeries.coeff ℚ n g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · rw [hn, hzero]
      exact isIntegral_zero
    have hrest : IsIntegral ℤ (PowerSeries.coeff ℚ n (higherPowers d g)) := by
      rw [higherPowers, map_sum]
      apply IsIntegral.sum
      intro j _
      rw [PowerSeries.coeff_C_mul]
      have hconstant : IsIntegral ℤ
          (((d + 1 : ℕ) : ℚ) ^ j * ((d + 1).choose (j + 2) : ℚ)) :=
        ((ordinaryJet_natCast_integral (K := ℚ) (d + 1)).pow j).mul
          (ordinaryJet_natCast_integral _)
      exact hconstant.mul (integral_coeff_pow_of_smaller (by omega) hzero ih)
    have hi := hdiv n (Nat.pos_of_ne_zero hn)
    rw [binomial_root_expansion, map_add, PowerSeries.coeff_one, if_neg hn, zero_add,
      PowerSeries.coeff_C_mul, map_add] at hi
    rw [mul_div_cancel_left₀ _ (pow_ne_zero _ (by positivity))] at hi
    simpa only [add_sub_cancel_right] using hi.sub hrest

private theorem rat_scaled_binomial_integral (x : ℚ) (m : ℕ) :
    IsIntegral ℤ ((x.den : ℚ) ^ (2 * m) * Ring.choose x m) := by
  let d := x.den - 1
  have hd : d + 1 = x.den := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr x.den_nz)
  let c : ℚ := (d + 1 : ℕ)
  have hc : c ≠ 0 := by dsimp [c]; positivity
  let f := PowerSeries.rescale (c ^ 2) (PowerSeries.binomialSeries ℚ x)
  let g := PowerSeries.C ℚ c⁻¹ * (f - 1)
  have hfg : 1 + PowerSeries.C ℚ c * g = f := by
    dsimp only [g]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
    ring
  have hzero : PowerSeries.coeff ℚ 0 g = 0 := by
    dsimp only [g, f]
    rw [PowerSeries.coeff_C_mul, map_sub, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff,
      PowerSeries.coeff_one, if_pos rfl, Ring.choose_zero_right]
    simp
  have hscaled : (d + 1) • x = (x.num : ℚ) := by
    rw [nsmul_eq_mul, hd, mul_comm]
    exact (eq_div_iff (Nat.cast_ne_zero.mpr x.den_nz)).mp x.num_div_den.symm
  have hdiv (n : ℕ) (hn : 0 < n) :
      IsIntegral ℤ (PowerSeries.coeff ℚ n ((1 + PowerSeries.C ℚ c * g) ^ (d + 1)) / c ^ 2) := by
    rw [hfg, ← map_pow, ← binomialSeries_nsmul_rat, hscaled, PowerSeries.coeff_rescale,
      PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one, rat_choose_intCast]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [pow_succ, mul_right_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hc)]
    have hChoose : IsIntegral ℤ ((Ring.choose x.num (k + 1) : ℤ) : ℚ) :=
      isIntegral_algebraMap (R := ℤ) (A := ℚ)
    exact ((ordinaryJet_natCast_integral (K := ℚ) (d + 1)).pow 2 |>.pow k).mul hChoose
  have hg := integral_coeff_of_binomial_root d g hzero hdiv m
  have hf : IsIntegral ℤ (PowerSeries.coeff ℚ m f) := by
    rw [← hfg, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_one]
    split_ifs
    · exact isIntegral_one.add ((ordinaryJet_natCast_integral (d + 1)).mul hg)
    · exact isIntegral_zero.add ((ordinaryJet_natCast_integral (d + 1)).mul hg)
  simpa only [f, PowerSeries.coeff_rescale, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
    c, hd, ← pow_mul] using hf

/-- Rational exponents have geometric common binomial denominators over any characteristic-zero
field. The multiplier at cutoff N is the rational denominator raised to 2N. -/
theorem binomialPrefixDenominators_ratCast {K : Type*} [Field K] [CharZero K] (x : ℚ) :
    BinomialPrefixDenominators (x : K) := by
  have hden : 0 < x.den := Nat.pos_of_ne_zero x.den_nz
  have hb : (1 : ℝ) ≤ x.den := by exact_mod_cast hden
  refine ⟨(x.den : ℝ) ^ 2, one_le_pow₀ hb, fun N => ⟨x.den ^ (2 * N),
    pow_pos hden _, ?_, ?_⟩⟩
  · rw [Nat.cast_pow, ← pow_mul]
    exact pow_le_pow_right₀ hb (Nat.mul_le_mul_left _ (Nat.le_succ _))
  · intro m hm
    have hle : 2 * m ≤ 2 * N := Nat.mul_le_mul_left _ hm
    have hi := (ordinaryJet_natCast_integral (x.den ^ (2 * N - 2 * m))).mul
      (rat_scaled_binomial_integral x m)
    rw [Nat.cast_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle,
      field_choose_eq_descPochhammer_div] at hi
    let φ : ℚ →+* K := algebraMap ℚ K
    have hEval : φ ((descPochhammer ℚ m).eval x) = (descPochhammer K m).eval (x : K) := by
      rw [← Polynomial.eval₂_at_apply φ, ← Polynomial.eval_map, descPochhammer_map]
      rfl
    have hiK := hi.map φ.toIntAlgHom
    simpa only [RingHom.toIntAlgHom_apply, map_mul, map_div₀, map_pow, map_natCast, hEval,
      Nat.cast_pow] using hiK

end WideEIntegralClosed
