import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.PSeries

/-!
# Dirichlet series of sparse prime sets

A double-logarithmic upper bound on the partial reciprocal sums also bounds the
associated Dirichlet series near its boundary at 1.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace WideEIntegralClosed

/-- The logarithmic coefficient in the bound on the Dirichlet series can be made
arbitrarily small when this is possible for the partial reciprocal sums. -/
theorem reciprocal_dirichlet_upper_of_sum_le_log_log
    (P : ℕ → Prop) [DecidablePred P] (hP : ∀ p, P p → 2 ≤ p)
    {B ε : ℝ} (hε : 0 ≤ ε)
    (hpartial : ∀ n : ℕ, 2 ≤ n →
      (∑ p ∈ Finset.Icc 2 n, if P p then 1 / (p : ℝ) else 0) ≤
        B + ε * Real.log (Real.log (n : ℝ))) :
    ∀ᶠ s : ℝ in 𝓝[>] 1,
      (∑' p : ℕ, if P p then 1 / (p : ℝ)^s else 0) ≤
        B + 8 + 2 * ε * (-Real.log (s - 1)) := by
  let u : ℝ → ℝ := fun s => (s + 1) / 2
  have hucont : Continuous u := (continuous_id.add continuous_const).div_const 2
  have hut : Tendsto u (𝓝[>] 1) (𝓝[>] 1) := by
    have he : u 1 = 1 := by norm_num [u]
    have hm : Set.MapsTo u (Set.Ioi 1) (Set.Ioi (u 1)) := by
      intro s hs
      change 1 < s at hs
      change u 1 < u s
      dsimp [u]
      linarith
    simpa only [he] using (hucont.continuousWithinAt (x := 1) (s := Set.Ioi 1)).tendsto_nhdsWithin hm
  have hz := (tendsto_sub_mul_tsum_nat_rpow.comp hut).eventually
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
  filter_upwards [hz, self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds] with s hz hs hs₂
  change 1 < s at hs
  let t : ℝ := s - 1
  have ht : 0 < t := sub_pos.mpr hs
  have ht₁ : t < 1 := by dsimp [t]; linarith
  have hu : 1 < u s := by dsimp [u]; linarith
  have hs_eq : s = u s + t / 2 := by dsimp [u, t]; ring
  have hζ : (∑' p : ℕ, 1 / (p : ℝ) ^ u s) ≤ 4 / t := by
    change (u s - 1) * (∑' p : ℕ, 1 / (p : ℝ) ^ u s) < 2 at hz
    have h := (le_div_iff₀ ht).2 (show (∑' p : ℕ, 1 / (p : ℝ) ^ u s) * t ≤ 4 by
      have he : u s - 1 = t / 2 := by dsimp [u, t]; ring
      rw [he] at hz
      linarith)
    exact h
  let X : ℝ := Real.exp ((t⁻¹)^2)
  let n : ℕ := ⌊X⌋₊
  let S := Finset.Icc 2 n
  have hXpos : 0 < X := Real.exp_pos _
  have hti : 1 ≤ t⁻¹ := (one_le_inv₀ ht).2 ht₁.le
  have hX₂ : 2 ≤ X := by
    have h := Real.add_one_le_exp ((t⁻¹)^2)
    have hsq : 1 ≤ (t⁻¹)^2 := by nlinarith
    exact (by linarith : 2 ≤ (t⁻¹)^2 + 1).trans h
  have hn : 2 ≤ n := Nat.le_floor (by exact_mod_cast hX₂)
  have hlogn : Real.log (Real.log (n : ℝ)) ≤ 2 * (-Real.log t) := by
    have htwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnp : 1 < (n : ℝ) := (by norm_num : (1 : ℝ) < 2).trans_le htwo
    have h := Real.log_le_log (Real.log_pos hnp)
      (Real.log_le_log (zero_lt_one.trans hnp) (Nat.floor_le hXpos.le))
    dsimp [X] at h
    rw [Real.log_exp, Real.log_pow, Real.log_inv] at h
    simpa using h
  let f : ℕ → ℝ := fun p => if P p then 1 / (p : ℝ)^s else 0
  let g : ℕ → ℝ := fun p => if p ∈ S then 0 else f p
  have hf₀ (p : ℕ) : 0 ≤ f p := by dsimp [f]; split_ifs <;> positivity
  have hf : Summable f := Summable.of_nonneg_of_le hf₀
    (fun p => by dsimp [f]; split_ifs <;> first | rfl | positivity)
    (Real.summable_one_div_nat_rpow.mpr hs)
  have hg_bound (p : ℕ) : g p ≤ (2*t) * (1 / (p : ℝ)^u s) := by
    by_cases hp : P p
    · by_cases hpS : p ∈ S
      · rw [show g p = 0 from if_pos hpS]
        positivity
      have hnp : n < p := by
        change p ∉ Finset.Icc 2 n at hpS
        exact lt_of_not_ge (fun h => hpS (Finset.mem_Icc.mpr ⟨hP p hp, h⟩))
      have hXp : X < (p : ℝ) := lt_of_not_ge (fun h => (not_le_of_gt hnp) (Nat.le_floor h))
      have hp₀ : 0 < (p : ℝ) := hXpos.trans hXp
      have h := Real.log_le_log hXpos hXp.le
      dsimp only [X] at h
      rw [Real.log_exp] at h
      have hpw : 1 / (p : ℝ) ^ (t / 2) ≤ 2 * t := by
        apply (div_le_iff₀ (Real.rpow_pos_of_pos hp₀ _)).2
        rw [Real.rpow_def_of_pos hp₀, mul_comm (Real.log (p : ℝ))]
        have h₁ := Real.add_one_le_exp (t / 2 * Real.log (p : ℝ))
        have h₂ := mul_le_mul_of_nonneg_left h (show 0 ≤ t / 2 by positivity)
        have he : t / 2 * (t⁻¹)^2 = 1 / (2 * t) := by field_simp; ring
        rw [he] at h₂
        exact (div_le_iff₀ (by positivity : 0 < 2*t)).1
          (show 1 / (2*t) ≤ Real.exp (t / 2 * Real.log (p : ℝ)) by linarith) |>.trans_eq (mul_comm _ _)
      change (if p ∈ S then 0 else if P p then 1 / (p : ℝ)^s else 0) ≤ _
      rw [if_neg hpS, if_pos hp]
      nth_rewrite 1 [hs_eq]
      rw [Real.rpow_add hp₀, ← one_div_mul_one_div]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hpw (by positivity : 0 ≤ 1 / (p : ℝ)^u s)
    · have he : f p = 0 := if_neg hp
      simp only [g, he, ite_self]
      positivity
  have hsum : (∑' p : ℕ, f p) = (∑ p ∈ S, f p) + ∑' p : ℕ, g p := by
    have he := hf.sum_add_tsum_subtype_compl S
    rw [← he]
    congr 1
    change (∑' p : ↥((↑S : Set ℕ)ᶜ), f p) = ∑' p, g p
    rw [tsum_subtype]
    apply tsum_congr
    intro p
    simp only [g, Set.indicator, Set.mem_compl_iff, Finset.mem_coe, ite_not]
  have hg₀ (p : ℕ) : 0 ≤ g p := by dsimp [g]; split_ifs <;> simp [hf₀]
  have hzsum := (Real.summable_one_div_nat_rpow.mpr hu).mul_left (2*t)
  have hg := Summable.of_nonneg_of_le hg₀ hg_bound hzsum
  have htail := hg.tsum_le_tsum hg_bound hzsum
  rw [tsum_mul_left] at htail
  have htail' := htail.trans (mul_le_mul_of_nonneg_left hζ (by positivity : 0 ≤ 2*t))
  rw [show 2*t * (4/t) = 8 by field_simp; ring] at htail'
  have hsmall : (∑ p ∈ S, f p) ≤ B + ε * Real.log (Real.log (n : ℝ)) := by
    apply le_trans _ (hpartial n hn)
    apply Finset.sum_le_sum
    intro p hp
    dsimp [f]
    split_ifs with h
    · apply one_div_le_one_div_of_le
      · have hpos : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by have := hP p h; omega)
        exact hpos
      · have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by have := hP p h; omega)
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hp₁ hs.le
    · rfl
  change (∑' p : ℕ, f p) ≤ _
  rw [hsum]
  have hlog := mul_le_mul_of_nonneg_left hlogn hε
  linarith

end WideEIntegralClosed
