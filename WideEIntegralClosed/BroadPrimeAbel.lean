import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Reciprocal sums from logarithmically weighted prime bounds

Abel summation removes the logarithmic weight. A small coefficient of `log n`
in the original sum gives the same small coefficient of `log (log n)` in the
reciprocal sum.
-/

noncomputable section

open Finset MeasureTheory Set
open scoped Interval

namespace WideEIntegralClosed

/-- A logarithmic bound for the partial sums of `c` gives a double-logarithmic bound
after dividing its terms by `log n`. The sum starts at 2. -/
theorem sum_div_log_le_of_sum_le_log
    (c : ℕ → ℝ) (hc₀ : ∀ n, 0 ≤ c n) {B ε : ℝ} (hε : 0 ≤ ε)
    (hc : ∀ n : ℕ, 2 ≤ n → (∑ p ∈ Finset.Icc 0 n, c p) ≤ B + ε * Real.log (n : ℝ))
    (n : ℕ) (hn : 2 ≤ n) :
    ∑ p ∈ Finset.Icc 2 n, (Real.log (p : ℝ))⁻¹ * c p ≤
      (B + ε * Real.log 2) / Real.log 2 +
        ε * (Real.log (Real.log (n : ℝ)) - Real.log (Real.log 2)) := by
  let a : ℝ := 2
  let b : ℝ := n
  let f : ℝ → ℝ := fun x => (Real.log x)⁻¹
  let f' : ℝ → ℝ := fun x => -x⁻¹ / (Real.log x)^2
  let A : ℝ → ℝ := fun x => ∑ p ∈ Finset.Icc 0 ⌊x⌋₊, c p
  let G : ℝ → ℝ := fun x => B + ε * Real.log x
  let g : ℝ → ℝ := fun x => Real.log (Real.log x)
  have hab : a ≤ b := by
    change (2 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have ha : (1 : ℝ) < a := by norm_num [a]
  have hpositive {x : ℝ} (hx : x ∈ Set.Icc a b) : 0 < x := zero_lt_one.trans (ha.trans_le hx.1)
  have hlogpos {x : ℝ} (hx : x ∈ Set.Icc a b) : 0 < Real.log x := Real.log_pos (ha.trans_le hx.1)
  have hdf (x : ℝ) (hx : x ∈ Set.Icc a b) : HasDerivAt f (f' x) x :=
    (Real.hasDerivAt_log (hpositive hx).ne').inv (hlogpos hx).ne'
  have hf' : ContinuousOn f' (Set.Icc a b) := by
    apply ContinuousOn.div
    · exact (continuousOn_id.inv₀ fun x hx => (hpositive hx).ne').neg
    · apply ContinuousOn.pow
      exact Real.continuousOn_log.mono fun x hx => (hpositive hx).ne'
    · exact fun x hx => pow_ne_zero 2 (hlogpos hx).ne'
  have hlog : ContinuousOn Real.log (Set.Icc a b) :=
    Real.continuousOn_log.mono fun x hx => (hpositive hx).ne'
  have hG : ContinuousOn G (Set.Icc a b) := continuousOn_const.add (continuousOn_const.mul hlog)
  have hderiv : Set.EqOn (deriv f) f' (Set.Icc a b) := fun x hx => (hdf x hx).deriv
  have hint : IntegrableOn (deriv f) (Set.Icc a b) :=
    hf'.integrableOn_Icc.congr_fun (fun x hx => (hderiv hx).symm) measurableSet_Icc
  have hsub : ∑ p ∈ Finset.Ioc 2 n, f (p : ℝ) * c p =
      f b * A b - f a * A a - ∫ x in a..b, f' x * A x := by
    have h := sum_mul_eq_sub_sub_integral_mul' c hn
      (fun x hx => (hdf x hx).differentiableAt) hint
    change _ = _ - ∫ x in Set.Ioc a b, deriv f x * A x at h
    rw [← intervalIntegral.integral_of_le hab] at h
    have hi : (∫ x in a..b, deriv f x * A x) = ∫ x in a..b, f' x * A x :=
      intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le hab] at hx
      exact congrArg (fun y => y * A x) (hderiv hx)
    rw [hi] at h
    simpa [A, a, b] using h
  have hbound (x : ℝ) (hx : x ∈ Set.Icc a b) : A x ≤ G x := by
    have hfloor : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa [a] using hx.1)
    have hpos : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
    exact (hc _ hfloor).trans (add_le_add_left (mul_le_mul_of_nonneg_left
      (Real.log_le_log hpos (Nat.floor_le (hpositive hx).le)) hε) _)
  have hmain : (∫ x in a..b, f' x * G x) ≤ ∫ x in a..b, f' x * A x := by
    apply intervalIntegral.integral_mono_on hab
    · exact (hf'.mul hG).intervalIntegrable_of_Icc hab
    · have hi := integrableOn_mul_sum_Icc c (m := 0) (by norm_num [a] : 0 ≤ a)
        hf'.integrableOn_Icc
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hi
    · intro x hx
      apply mul_le_mul_of_nonpos_left (hbound x hx)
      dsimp [f']
      have h : 0 ≤ x⁻¹ := inv_nonneg.mpr (hpositive hx).le
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h) (sq_nonneg _)
  have hcalc : (∫ x in a..b, f' x * G x) =
      f b * G b - f a * G a - ε * (g b - g a) := by
    have hder (x : ℝ) (hx : x ∈ Set.Icc a b) :
        HasDerivAt (fun y => f y * G y - ε * g y) (f' x * G x) x := by
      have hG' : HasDerivAt G (ε * x⁻¹) x :=
        ((Real.hasDerivAt_log (hpositive hx).ne').const_mul ε).const_add B
      have hg' : HasDerivAt g ((Real.log x)⁻¹ * x⁻¹) x :=
        (Real.hasDerivAt_log (hlogpos hx).ne').comp x (Real.hasDerivAt_log (hpositive hx).ne')
      convert ((hdf x hx).mul hG').sub (hg'.const_mul ε) using 1
      dsimp [f]
      ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hder x (by rwa [uIcc_of_le hab] at hx))
      ((hf'.mul hG).intervalIntegrable_of_Icc hab)
    rw [h]
    ring
  have hcut : Finset.Icc 2 n = insert 2 (Finset.Ioc 2 n) := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hrest : 0 ≤ A a - c 2 := by
    dsimp [A, a]
    rw [show ⌊(2 : ℝ)⌋₊ = 2 by norm_num]
    exact sub_nonneg.mpr (Finset.single_le_sum (fun p _ => hc₀ p) (by simp))
  rw [hcut, Finset.sum_insert (by simp), hsub, div_eq_mul_inv]
  have hfa : 0 ≤ f a := inv_nonneg.mpr (by exact (Real.log_pos ha).le)
  have hfb : 0 ≤ f b := inv_nonneg.mpr (by exact (Real.log_pos (ha.trans_le hab)).le)
  have hb := mul_le_mul_of_nonneg_left (hbound b ⟨hab, le_rfl⟩) hfb
  have hl := mul_nonneg hfa hrest
  change f a * c 2 + (f b * A b - f a * A a - _) ≤ G a * f a + ε * (g b - g a)
  rw [hcalc] at hmain
  nlinarith

end WideEIntegralClosed
