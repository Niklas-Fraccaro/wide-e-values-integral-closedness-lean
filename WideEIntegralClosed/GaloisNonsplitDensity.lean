import RationalEulerLogComparison

/-!
# A lower bound for the nonsplit prime series

The simple poles of the rational zeta series and the number-field ideal series give
a quantitative logarithmic lower bound for the primes that fail to split completely.
-/

noncomputable section

set_option maxHeartbeats 1000000

open Finset Filter NumberField StrictEUnit
open scoped BigOperators Topology

namespace WideEIntegralClosed

private theorem split_prime_tsum_le
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [DecidablePred (GaloisCompletelySplitAt K)] :
    ∃ C Q : ℝ, 0 < C ∧ ∀ s : ℝ, 1 < s →
      (Module.finrank ℚ K : ℝ) *
        (∑' p : Nat.Primes, if GaloisCompletelySplitAt K (p : ℕ) then 1 / (p : ℝ)^s else 0) ≤
        Real.log (s * C / (s - 1)) + Q := by
  obtain ⟨C, hC, hbound⟩ := galois_split_prime_log_upper_constraint K
  let d : ℝ := Module.finrank ℚ K
  let Q : ℝ := (d^2 / 2) * ∑' n : ℕ, 1 / (n : ℝ)^2
  have hd : 0 ≤ d := Nat.cast_nonneg _
  refine ⟨C, Q, hC, fun s hs => ?_⟩
  let f : Nat.Primes → ℝ := fun p =>
    if GaloisCompletelySplitAt K (p : ℕ) then 1 / (p : ℝ)^s else 0
  have hf : Summable f := Summable.of_nonneg_of_le (g := f)
    (by intro p; dsimp [f]; split_ifs <;> positivity)
    (by intro p; dsimp [f]; split_ifs <;> first | rfl | positivity)
    (prime_reciprocal_rpow_summable hs)
  change d * (∑' p, f p) ≤ _
  rw [← tsum_mul_left]
  apply (hf.mul_left d).tsum_le_of_sum_le
  intro S
  let U := S.filter (fun p : Nat.Primes => GaloisCompletelySplitAt K (p : ℕ))
  let T := U.image (fun p : Nat.Primes => (p : ℕ))
  have hT (p : ℕ) (hp : p ∈ T) : p.Prime ∧ GaloisCompletelySplitAt K p := by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨q.prop, (Finset.mem_filter.mp hq).2⟩
  have hsums : (∑ p ∈ T, 1 / (p : ℝ)^s) = ∑ p ∈ S, f p := by
    dsimp only [T]
    rw [Finset.sum_image (f := fun p : ℕ => 1 / (p : ℝ)^s)
      (g := fun p : Nat.Primes => (p : ℕ))
      (fun p _ q _ h => Subtype.ext h)]
    simp only [U, f, Finset.sum_filter]
  have hlog := hbound s hs T (fun p hp => (hT p hp).1)
    (fun p hp => (hT p hp).2.1) (fun p hp => (hT p hp).2.2)
  have hquad := prime_quadratic_error_uniform d hd hs.le T
    (fun p hp => (hT p hp).1.one_lt.le)
  have hrew : (∑ p ∈ T, (d / (p : ℝ)^s - (d / (p : ℝ)^s)^2 / 2)) =
      d * (∑ p ∈ T, 1 / (p : ℝ)^s) - (∑ p ∈ T, (d / (p : ℝ)^s)^2 / 2) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    simp only [mul_one_div]
  change (∑ p ∈ T, (d / (p : ℝ)^s - (d / (p : ℝ)^s)^2 / 2)) ≤ _ at hlog
  rw [hrew, hsums] at hlog
  change (∑ p ∈ T, (d / (p : ℝ)^s)^2 / 2) ≤ Q at hquad
  rw [← Finset.mul_sum]
  linarith

/-- If the Galois field has degree greater than one, its nonsplit primes have a
positive logarithmic lower bound in the Dirichlet series near `s = 1`. -/
theorem galois_nonsplit_prime_log_lower
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [DecidablePred (GaloisCompletelySplitAt K)] (hd : 1 < Module.finrank ℚ K) :
    ∃ c B : ℝ, 0 < c ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      c * (-Real.log (s - 1)) - B ≤
        ∑' p : Nat.Primes, if GaloisCompletelySplitAt K (p : ℕ) then 0 else 1 / (p : ℝ)^s := by
  obtain ⟨C, Q, hC, hsplit⟩ := split_prime_tsum_le K
  let d : ℝ := Module.finrank ℚ K
  let A : ℝ := 2 * (∑' n : ℕ, 1 / (n : ℝ)^2)
  have hd' : 1 < d := by dsimp only [d]; exact_mod_cast hd
  have hd₀ : 0 < d := zero_lt_one.trans hd'
  refine ⟨(d - 1) / d, (Real.log (2*C) + Q) / d + A - Real.log (1/2),
    div_pos (sub_pos.mpr hd') hd₀, ?_⟩
  filter_upwards [rational_zeta_pole_lower, self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (1:ℝ) < 2)).filter_mono nhdsWithin_le_nhds] with s hz hs hs₂
  change 1 < s at hs
  have hp : 0 < s - 1 := sub_pos.mpr hs
  have hlower := Real.log_le_log (div_pos (by norm_num : (0:ℝ) < 1/2) hp) hz
  rw [Real.log_div (by norm_num : (1/2:ℝ) ≠ 0) hp.ne'] at hlower
  have hall := rational_zeta_log_le_prime_sum hs
  change Real.log (∑' n : ℕ, 1 / (n : ℝ)^s) ≤ _ + A at hall
  have hsplit := hsplit s hs
  have hlog := Real.log_le_log (div_pos (mul_pos (by linarith : 0 < s) hC) hp)
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs₂.le hC.le) hp.le)
  have hlogeq : Real.log (2*C/(s-1)) = Real.log (2*C) - Real.log (s-1) :=
    Real.log_div (mul_ne_zero (by norm_num) hC.ne') hp.ne'
  rw [hlogeq] at hlog
  let f : Nat.Primes → ℝ := fun p => 1 / (p : ℝ)^s
  let g : Nat.Primes → ℝ := fun p => if GaloisCompletelySplitAt K (p : ℕ) then f p else 0
  let h : Nat.Primes → ℝ := fun p => if GaloisCompletelySplitAt K (p : ℕ) then 0 else f p
  have hf : Summable f := prime_reciprocal_rpow_summable hs
  have hf₀ (p : Nat.Primes) : 0 ≤ f p := by dsimp [f]; positivity
  have hg : Summable g := Summable.of_nonneg_of_le (g := g)
    (fun p => by dsimp [g]; split_ifs <;> simp [hf₀])
    (fun p => by dsimp [g]; split_ifs <;> simp [hf₀]) hf
  have hh : Summable h := Summable.of_nonneg_of_le (g := h)
    (fun p => by dsimp [h]; split_ifs <;> simp [hf₀])
    (fun p => by dsimp [h]; split_ifs <;> simp [hf₀]) hf
  have hdecomp : (∑' p, f p) = (∑' p, g p) + (∑' p, h p) := by
    rw [← hg.tsum_add hh]
    apply tsum_congr
    intro p
    dsimp [g, h]
    split_ifs <;> simp
  change Real.log (∑' n : ℕ, 1 / (n : ℝ)^s) ≤ (∑' p, f p) + A at hall
  change d * (∑' p, g p) ≤ Real.log (s * C / (s-1)) + Q at hsplit
  rw [hdecomp] at hall
  have h₁ := hlower.trans hall
  have h₂ := hsplit.trans (add_le_add_right hlog Q)
  apply (mul_le_mul_left hd₀).mp
  change d * ((d - 1) / d * -Real.log (s - 1) -
      ((Real.log (2*C) + Q) / d + A - Real.log (1/2))) ≤ d * (∑' p, h p)
  have h₃ := mul_le_mul_of_nonneg_left h₁ hd₀.le
  rw [mul_sub, ← mul_assoc, show d * ((d - 1) / d) = d - 1 by field_simp,
    mul_sub, mul_add, show d * ((Real.log (2*C) + Q) / d) = Real.log (2*C) + Q by field_simp]
  nlinarith

end WideEIntegralClosed
