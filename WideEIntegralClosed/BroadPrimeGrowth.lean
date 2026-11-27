import WideEIntegralClosed.BroadPrimeAbel
import WideEIntegralClosed.BroadPrimeSmoothing

/-!
# Logarithmic density and weighted prime growth

A positive logarithmic lower bound for a prime set rules out arbitrarily small
growth of its logarithmically weighted partial sums.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace WideEIntegralClosed

/-- A set with positive logarithmic Dirichlet growth cannot have weighted partial
sums bounded by `B + ε * log n` for every positive `ε`. -/
theorem not_weighted_sum_le_log_of_positive_dirichlet_growth
    (P : ℕ → Prop) [DecidablePred P] (hP : ∀ p, P p → 2 ≤ p)
    (hlower : ∃ c A : ℝ, 0 < c ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      c * (-Real.log (s - 1)) - A ≤ ∑' p : ℕ, if P p then 1 / (p : ℝ)^s else 0) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ n : ℕ, 2 ≤ n →
      (∑ p ∈ Finset.Icc 0 n, if P p then Real.log (p : ℝ) / (p : ℝ) else 0) ≤
        B + ε * Real.log (n : ℝ)) := by
  rintro hub
  obtain ⟨c, A, hc, hlower⟩ := hlower
  let ε := c / 4
  have hε : 0 < ε := by positivity
  obtain ⟨B, hB⟩ := hub ε hε
  let w : ℕ → ℝ := fun p => if P p then Real.log (p : ℝ) / (p : ℝ) else 0
  have hw (p : ℕ) : 0 ≤ w p := by
    dsimp [w]
    split_ifs with hp
    · have hp₁ : 1 ≤ (p : ℝ) := by
        have hp₂ := hP p hp
        exact_mod_cast (show 1 ≤ p by omega)
      exact div_nonneg (Real.log_nonneg hp₁) (Nat.cast_nonneg p)
    · exact le_rfl
  let D := (B + ε * Real.log 2) / Real.log 2 - ε * Real.log (Real.log 2)
  have hd (n : ℕ) (hn : 2 ≤ n) :
      (∑ p ∈ Finset.Icc 2 n, if P p then 1 / (p : ℝ) else 0) ≤
        D + ε * Real.log (Real.log (n : ℝ)) := by
    have h := sum_div_log_le_of_sum_le_log w hw hε.le hB n hn
    have hterm (p : ℕ) : (Real.log (p : ℝ))⁻¹ * w p =
        if P p then 1 / (p : ℝ) else 0 := by
      dsimp [w]
      split_ifs with hp
      · have hp₁ : 1 < (p : ℝ) := by
          exact_mod_cast (show 1 < p from Nat.one_lt_two.trans_le (hP p hp))
        rw [← mul_div_assoc, inv_mul_cancel₀ (Real.log_pos hp₁).ne']
      · simp
    simp_rw [hterm] at h
    exact h.trans (by dsimp [D]; linarith)
  have hupper := reciprocal_dirichlet_upper_of_sum_le_log_log P hP hε.le hd
  have hlogbound : ∀ᶠ s : ℝ in 𝓝[>] 1,
      (c / 2) * (-Real.log (s - 1)) ≤ D + 8 + A := by
    filter_upwards [hlower, hupper] with s hs hu
    have h := hs.trans hu
    dsimp [ε] at h
    linarith
  have hcont : Continuous (fun s : ℝ => s - 1) := continuous_id.sub continuous_const
  have hsub : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    simpa using (hcont.continuousWithinAt (x := 1) (s := Set.Ioi 1)).tendsto_nhdsWithin
      (fun s hs => sub_pos.mpr hs)
  have hsmall := (Real.tendsto_log_nhdsGT_zero.comp hsub).eventually
    (eventually_lt_atBot (-(D + 8 + A + 1) / (c / 2)))
  obtain ⟨s, hs, hsmall⟩ := (hlogbound.and hsmall).exists
  have hs' := (lt_div_iff₀ (by positivity : 0 < c / 2)).mp hsmall
  simp only [Function.comp_apply] at hs'
  linarith

end WideEIntegralClosed
