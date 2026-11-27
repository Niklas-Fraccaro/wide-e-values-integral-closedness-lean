import WideE.Bounds

namespace WideEIntegralClosed

/-- A positive integer clears each prefix, with a subfactorial bound on its size. -/
def HasSubfactorialPrefixDenominators (clears : ℕ → ℕ → Prop) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 1 ≤ A ∧ ∀ N : ℕ, ∃ D : ℕ,
    0 < D ∧ (D : ℝ) ≤ A * (N.factorial : ℝ) ^ ε ∧ clears N D

end WideEIntegralClosed
