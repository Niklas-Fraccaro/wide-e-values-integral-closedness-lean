import FourierUniformConjugateGrowth
import FourierIndicialTwistedAmplitudes
import Mathlib.FieldTheory.KrullTopology
import WideE.Basic
import WideE.Bounds

/-! The broad arithmetic of each retained Fourier coefficient reduces to its denominator bound. -/

noncomputable section

open StrictEUnit

namespace WideEIntegralClosed

/-- Broad arithmetic for the factorial coefficients of the constant log coefficient of each
retained formal amplitude. The finite log matrix determines the other log coefficients. -/
def BroadRetainedFourierArithmetic {m n : ℕ}
    (A : Fin (m + 1) → Fin (n + 1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A) : Prop :=
  ∀ i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0),
    WideE.HasWideEArithmetic (fun t =>
      logAmplitudeFactorialCoefficient (sameFourierTwistedAmplitude A hf i) 0 t)

/-- Subfactorial integral prefix denominators of the exact retained log-free coefficients. -/
def BroadRetainedFourierDenominators {m n : ℕ}
    (A : Fin (m + 1) → Fin (n + 1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A) : Prop :=
  ∀ i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0),
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 1 ≤ B ∧ ∃ d : ℕ → ℕ,
      (∀ t, 0 < d t) ∧ (∀ t, (d t : ℝ) ≤ B * (t.factorial : ℝ) ^ ε) ∧
      ∀ t j, j ≤ t → IsIntegral ℤ ((d t : ℂ) *
        (logAmplitudeFactorialCoefficient (sameFourierTwistedAmplitude A hf i) 0 j : ℂ))

/-- Uniform geometric bounds on conjugates supply the growth requirement of the broad class. -/
theorem broadRetainedFourierArithmetic_iff_denominators {m n : ℕ}
    (A : Fin (m + 1) → Fin (n + 1) → AlgebraicComplex) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last m) (Fin.last n) ≠ 0) :
    BroadRetainedFourierArithmetic A hf ↔ BroadRetainedFourierDenominators A hf := by
  constructor
  · intro h i ε hε
    obtain ⟨C, hC, _, hd⟩ := h i ε hε
    exact ⟨C, hC, hd⟩
  · classical
    intro h
    letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
    let e := Fintype.equivFinOfCardEq (sameFourierTwistedAmplitude_index_card A hf hc)
    obtain ⟨_, _, _, _, _, _, _, _, C, hC, _, hconj⟩ :=
      sameFourier_retained_uniform_conjugate_bound A hc ⊥
        (IntermediateField.finiteDimensional_bot ℚ AlgebraicComplex) hf e
        (fun j => frobeniusRootSeedExponent _ (e.symm j))
        (fun j => sameFourierTwistedAmplitude A hf (e.symm j)) (fun _ => rfl) (fun _ => rfl)
    intro i ε hε
    obtain ⟨B, hB, d, hd, hdb, hdi⟩ := h i ε hε
    obtain ⟨D, hD, hbound⟩ := WideE.exists_exp_pow_le_factorial_rpow C ε hC hε
    refine ⟨max B (C * D), hB.trans (le_max_left _ _), ?_, d, hd, ?_, hdi⟩
    · intro σ t
      have hgeometric := hconj σ (e i) 0 t
      rw [e.symm_apply_apply] at hgeometric
      exact hgeometric.trans (calc
        C ^ (t + 1) = C * C ^ t := pow_succ' _ _
        _ ≤ C * (D * (t.factorial : ℝ) ^ ε) := mul_le_mul_of_nonneg_left (hbound t) (by positivity)
        _ ≤ max B (C * D) * (t.factorial : ℝ) ^ ε := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    · exact fun t => (hdb t).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

end WideEIntegralClosed
