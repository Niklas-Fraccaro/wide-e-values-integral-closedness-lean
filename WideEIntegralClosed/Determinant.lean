import WideE.Values
import Stage14OneSidedArithmeticRecovery
import Stage15TwoSidedDeterminantClassification

/-! The actual determinant and its inverse value in Section 2. -/

noncomputable section

namespace WideEIntegralClosed

open WideE StrictEUnit

/-- A broad E-function satisfies a quadratic exponential estimate after every positive
integer dilation. The prefactor may depend on the dilation. -/
theorem wideE_scaled_quadratic_bound {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((‖z‖ / (n : ℝ)) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := (hf.rescale (n : WideE.AlgebraicComplex)).quadratic_exp_bound
  refine ⟨C, hC, fun z => ?_⟩
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hcast : ((n : WideE.AlgebraicComplex) : ℂ) = (n : ℂ) :=
    map_natCast (algebraicClosure ℚ ℂ).val n
  simpa only [hcast, mul_div_cancel₀ z hnC, norm_div, Complex.norm_natCast]
    using hbound (z / (n : ℂ))

/-- Small quadratic type excludes a nonzero quadratic phase. Along a suitably
chosen ray, its leading real part is exactly the square of the real parameter. -/
private theorem quadratic_phase_eq_zero {f : ℂ → ℂ} {c a b : ℂ} {m : ℕ}
    (hc : c ≠ 0) (hform : ∀ z, f z = c * z ^ m * Complex.exp (a * z ^ 2 + b * z))
    (hbound : ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp ((‖z‖ / (n : ℝ)) ^ 2)) : a = 0 := by
  by_contra ha
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (n := 2) (by decide)
  have hunit : a * u ^ 2 = 1 := by rw [hu, mul_inv_cancel₀ ha]
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hunit
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (2 * ‖u‖))
  have hn1 : 1 < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hnR : 0 < (n : ℝ) := zero_lt_one.trans hn1
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hun : 2 * ‖u‖ < (n : ℝ) := (le_max_right _ _).trans_lt hn
  obtain ⟨C, hC, hCbound⟩ := hbound n hn0
  let K : ℝ := ‖c‖ * ‖u‖ ^ m
  have hK : 0 < K := mul_pos (norm_pos_iff.mpr hc) (pow_pos (norm_pos_iff.mpr hu0) _)
  let β : ℝ := (b * u).re
  let t : ℝ := max 1 (max (2 * |β|) (4 * (C / K)))
  have ht1 : 1 ≤ t := le_max_left _ _
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have htβ : 2 * |β| ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have htC : 4 * (C / K) ≤ t := (le_max_right _ _).trans (le_max_right _ _)
  let z : ℂ := (t : ℂ) * u
  have hnormz : ‖z‖ = t * ‖u‖ := by simp [z, norm_mul, abs_of_nonneg ht0]
  have hzrate : ‖z‖ / (n : ℝ) ≤ t / 2 := by
    apply (div_le_iff₀ hnR).mpr
    rw [hnormz]
    calc
      t * ‖u‖ ≤ t * ((n : ℝ) / 2) := mul_le_mul_of_nonneg_left (by linarith) ht0
      _ = (t / 2) * (n : ℝ) := by ring
  have hupper : ‖f z‖ ≤ C * Real.exp (t ^ 2 / 4) := by
    refine (hCbound z).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC.le)
    calc
      (‖z‖ / (n : ℝ)) ^ 2 ≤ (t / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hzrate 2
      _ = t ^ 2 / 4 := by ring
  have hphase : a * z ^ 2 + b * z = (t : ℂ) ^ 2 + (b * u) * (t : ℂ) := by
    calc
      a * z ^ 2 + b * z = a * u ^ 2 * (t : ℂ) ^ 2 + (b * u) * (t : ℂ) := by
        dsimp [z]
        ring
      _ = _ := by rw [hunit, one_mul]
  have hphaseRe : (a * z ^ 2 + b * z).re = t ^ 2 + β * t := by
    rw [hphase]
    simp only [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero, β]
  have hlower_exp : t ^ 2 / 2 ≤ t ^ 2 + β * t := by
    have hβt := mul_le_mul_of_nonneg_right (neg_abs_le β) ht0
    have htβt := mul_le_mul_of_nonneg_right htβ ht0
    nlinarith only [hβt, htβt]
  have hlower : K * Real.exp (t ^ 2 / 2) ≤ ‖f z‖ := by
    rw [hform, norm_mul, norm_mul, norm_pow, Complex.norm_exp, hnormz, hphaseRe, mul_pow]
    rw [show ‖c‖ * (t ^ m * ‖u‖ ^ m) = K * t ^ m by dsimp [K]; ring]
    calc
      K * Real.exp (t ^ 2 / 2) ≤ (K * t ^ m) * Real.exp (t ^ 2 / 2) := by
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hK.le (one_le_pow₀ ht1))
          (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlower_exp) (by positivity)
  have hratio : K * Real.exp (t ^ 2 / 4) ≤ C := by
    apply le_of_mul_le_mul_right _ (Real.exp_pos (t ^ 2 / 4))
    rw [mul_assoc, ← Real.exp_add, show t ^ 2 / 4 + t ^ 2 / 4 = t ^ 2 / 2 by ring]
    exact hlower.trans hupper
  have hexp : C / K < Real.exp (t ^ 2 / 4) := by
    nlinarith only [htC, Real.add_one_le_exp (t ^ 2 / 4),
      mul_nonneg (sub_nonneg.mpr ht1) ht0]
  exact (not_lt_of_ge hratio) (by simpa only [mul_comm] using (div_lt_iff₀ hK).mp hexp)

/-- A broad E-function with no zeros away from the origin has an algebraic
scalar times an integral power of the coordinate and a linear exponential. -/
theorem wideE_origin_only_zeros_exp_form {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (hnz : ∀ z : ℂ, z ≠ 0 → f z ≠ 0) :
    ∃ m : ℕ, ∃ c a : WideE.AlgebraicComplex,
      c ≠ 0 ∧ ∀ z : ℂ, f z = (c : ℂ) * z ^ m * Complex.exp ((a : ℂ) * z) := by
  obtain ⟨C, hC, hbound⟩ := hf.quadratic_exp_bound
  have hgrowth : HasPowerExponentialBound 2 f := by
    apply powerExponentialBound_of_separate_constants 2 0 id f C 1 hC (by norm_num)
    intro z _
    simpa using hbound z
  have hscaled := wideE_scaled_quadratic_bound hf
  obtain ⟨u, hdiff, hseries, _, _, _⟩ := hf
  obtain ⟨m, c, Q, _, hc, _, hQ0, hQdeg, hQform⟩ :=
    entire_eq_pow_subfield_exp_polynomial_of_one_sided_growth WideE.algebraicSubfield
      (N := 2) (by decide) hdiff hnz hgrowth (hseries.algebraic_coefficient hdiff)
  have hQsplit (z : ℂ) : (Q.map WideE.algebraicSubfield.subtype).eval z =
      (Q.coeff 2 : ℂ) * z ^ 2 + (Q.coeff 1 : ℂ) * z := by
    rw [Polynomial.eval_eq_sum_range' (p := Q.map WideE.algebraicSubfield.subtype) (n := 3) (by
      rw [Polynomial.natDegree_map_eq_of_injective WideE.algebraicSubfield.subtype.injective]
      omega)]
    simp [Finset.sum_range_succ, Polynomial.coeff_map, hQ0, add_comm]
    rfl
  have hform (z : ℂ) : f z = (c : ℂ) * z ^ m *
      Complex.exp ((Q.coeff 2 : ℂ) * z ^ 2 + (Q.coeff 1 : ℂ) * z) := by
    rw [hQform, hQsplit]
  have hzero := quadratic_phase_eq_zero
    (fun h => hc (Subtype.ext h)) hform hscaled
  refine ⟨m, c, Q.coeff 1, hc, fun z => ?_⟩
  simpa [hzero] using hform z

/-- The value at one of an origin-only-zero broad E-function has a broad
E-value as its reciprocal. -/
theorem wideE_at_one_unit_of_origin_only_zeros {f : ℂ → ℂ} (hf : IsWideEFunction f)
    (hnz : ∀ z : ℂ, z ≠ 0 → f z ≠ 0) : IsWideEValueUnit (f 1) := by
  obtain ⟨_, c, a, hc, hform⟩ := wideE_origin_only_zeros_exp_form hf hnz
  rw [hform]
  simpa using isWideEValueUnit_of_strict (algebraic_scalar_exp_isStrictEValueUnit c a hc)

/-- The determinant of a matrix of broad E-functions is a broad E-function. -/
theorem wideE_entireMatrix_det {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n entireFunctionAlgebra)
    (hwide : ∀ i j, IsWideEFunction (F i j).val) : IsWideEFunction F.det.val := by
  let R : Subring (ℂ → ℂ) :=
    { carrier := { f | IsWideEFunction f }
      zero_mem' := by simpa using isWideEFunction_const (0 : WideE.AlgebraicComplex)
      one_mem' := by simpa using isWideEFunction_const (1 : WideE.AlgebraicComplex)
      add_mem' := IsWideEFunction.add
      mul_mem' := IsWideEFunction.mul
      neg_mem' := IsWideEFunction.neg }
  let G : Matrix n n R := fun i j => ⟨(F i j).val, hwide i j⟩
  have he : (G.det : ℂ → ℂ) = F.det.val :=
    (RingHom.map_det R.subtype G).trans (RingHom.map_det entireFunctionAlgebra.val.toRingHom F).symm
  rw [← he]
  exact G.det.property

open scoped BigOperators in
/-- A denominator-cleared two-sided frame equation and one invertible frame
value give the determinant's reciprocal as a broad E-value. -/
theorem wideE_entireMatrix_two_sided_det_at_one_unit {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A C F : Matrix n n entireFunctionAlgebra)
    (hwide : ∀ i j, IsWideEFunction (F i j).val)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      (∑ k, (A i k).val z * (F k j).val z) - ∑ k, (F i k).val z * (C k j).val z)
    (hp : ∀ z : ℂ, z ≠ 0 → p.val z ≠ 0)
    (h1 : (F.map (entireEvaluation 1)).det ≠ 0) :
    IsWideEValueUnit ((F.map (entireEvaluation 1)).det) := by
  have hnz (z : ℂ) (hz : z ≠ 0) : F.det.val z ≠ 0 := by
    rw [entireMatrix_evaluation_det]
    exact entireMatrix_two_sided_determinant_nonzero_off_origin p A C F hF hp h1 z hz
  rw [← entireMatrix_evaluation_det]
  exact wideE_at_one_unit_of_origin_only_zeros (wideE_entireMatrix_det F hwide) hnz

end WideEIntegralClosed
