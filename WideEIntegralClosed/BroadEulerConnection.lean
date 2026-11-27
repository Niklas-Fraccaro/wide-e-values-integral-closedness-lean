import WideEIntegralClosed.BroadLaurentConnection
import MonomialEulerPresentation

/-! Transport of broad divided-connection arithmetic to regular Euler presentations. -/

noncomputable section

open scoped BigOperators Matrix
open StrictEUnit

namespace WideEIntegralClosed

/-- An affine enlargement of the prefix preserves subfactorial clearing bounds. -/
theorem HasSubfactorialPrefixDenominators.affine {source target : ℕ → ℕ → Prop}
    (hsource : HasSubfactorialPrefixDenominators source) (a : ℕ) (ha : 0 < a)
    (hclear : ∀ N D, source (a * (N + 1)) D → target N D) :
    HasSubfactorialPrefixDenominators target := by
  refine hsource.affine_mul ha 1 le_rfl
    (Q := fun _ q => q = 1) (fun _ => ⟨1, Nat.one_pos, by simp, rfl⟩) ?_
  intro N D e hDi he
  simpa only [he, Nat.mul_one] using hclear N D hDi

/-- A monomial gauge preserves subfactorial connection denominators. Its coefficients add
integer binomial factors and require only a larger affine cutoff. -/
theorem laurent_diagonal_gauge_subfactorial_denominators {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (hA : BroadLaurentDividedConnectionArithmetic A) :
    BroadLaurentDividedConnectionArithmetic
      (diagonalGaugeConnection (stage14_laurentAlgebraDerivation (k := K)) A
        (fun i => laurentIntegerMonomial (w i : ℤ))) := by
  obtain ⟨P, hpole, hden⟩ := hA
  let W := Finset.univ.sup w
  have hw (i : Fin r) : w i ≤ W := Finset.le_sup (f := w) (Finset.mem_univ i)
  refine ⟨P + W + 1, ?_, ?_⟩
  · intro m i j l hl
    cases m with
    | zero =>
      have hln : l ≠ 0 := by omega
      simp only [matrixConnectionSequence, Nat.factorial_zero, Nat.cast_one, div_one, Matrix.one_apply]
      split <;> simp [HahnSeries.coeff_one, hln]
    | succ m =>
      rw [laurent_diagonal_gauge_divided_coefficient]
      apply Finset.sum_eq_zero
      rintro ⟨a, b⟩ hab
      have hab' := Finset.mem_antidiagonal.mp hab
      have hwM : W ≤ W * (m + 1) := by rw [Nat.mul_succ]; exact Nat.le_add_left _ _
      have hcutoff : P * b + (a + W) ≤ (P + W + 1) * (m + 1) := by
        calc
          _ ≤ P * (m + 1) + ((m + 1) + W * (m + 1)) :=
            Nat.add_le_add (Nat.mul_le_mul_left P (by omega)) (Nat.add_le_add (by omega) hwM)
          _ = _ := by ring
      have hcast : ((P * b : ℕ) : ℤ) + (a : ℤ) + (W : ℤ) ≤
          (((P + W + 1) * (m + 1) : ℕ) : ℤ) := by
        exact_mod_cast (show P * b + a + W ≤ (P + W + 1) * (m + 1) by omega)
      have hwi : (0 : ℤ) ≤ (w i : ℤ) := Int.natCast_nonneg _
      have hwj : (w j : ℤ) ≤ (W : ℤ) := by exact_mod_cast hw j
      rw [hpole b i j _ (by omega), mul_zero]
  refine hden.affine (W + 2) (by omega) ?_
  intro N D hDi m hm i j l hl
  have hcutoff : 2 * N + W ≤ (W + 2) * (N + 1) := by nlinarith
  rw [laurent_diagonal_gauge_divided_coefficient, Finset.mul_sum]
  apply IsIntegral.sum
  rintro ⟨a, b⟩ hab
  have hab' := Finset.mem_antidiagonal.mp hab
  have hb : b ≤ (W + 2) * (N + 1) := by omega
  have hcast : ((2 * N + W : ℕ) : ℤ) ≤ (((W + 2) * (N + 1) : ℕ) : ℤ) := by exact_mod_cast hcutoff
  have hwi : (0 : ℤ) ≤ (w i : ℤ) := Int.natCast_nonneg _
  have hwj : (w j : ℤ) ≤ (W : ℤ) := by exact_mod_cast hw j
  have ha : (a : ℤ) ≤ (N : ℤ) := by exact_mod_cast (show a ≤ N by omega)
  have hl' : l - (w i : ℤ) + (a : ℤ) + (w j : ℤ) ≤ (((W + 2) * (N + 1) : ℕ) : ℤ) := by
    push_cast at hcast ⊢
    omega
  have hc : IsIntegral ℤ (Nat.choose (w i) a : K) := ordinaryJet_natCast_integral _
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hc.mul (hDi b hb i j _ hl')

/-- The Euler divided connection has shared subfactorial denominators, for a rectangular
prefix of derivative orders and coefficient degrees. -/
def HasSubfactorialEulerConnectionDenominators {K : Type*} [Field K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) : Prop :=
  HasSubfactorialPrefixDenominators fun N D =>
    ∀ m, m ≤ N → ∀ l, l ≤ N → ∀ i j, IsIntegral ℤ ((D : K) *
      PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j))

/-- Passing from the ordinary Laurent connection to the regular Euler connection preserves
subfactorial denominators. The same clearing integer works at every cutoff. -/
theorem powerSeriesEulerDividedConnection_subfactorial_denominators
    {K : Type*} [Field K] [CharZero K] {r : ℕ} (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hA : BroadLaurentDividedConnectionArithmetic (powerSeriesEulerOrdinaryMatrix C)) :
    HasSubfactorialEulerConnectionDenominators C := by
  intro ε hε
  obtain ⟨_, _, hden⟩ := hA
  obtain ⟨B, hB, hden'⟩ := hden ε hε
  refine ⟨B, hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hden' N
  refine ⟨D, hD, hDb, ?_⟩
  intro m hm l hl i j
  have h := congrArg (fun f : LaurentSeries K => f.coeff (l : ℤ))
    (powerSeriesEulerDividedConnection_laurent C m i j)
  dsimp only at h
  rw [HahnSeries.ofPowerSeries_apply_coeff] at h
  have hx : (l : ℤ) = (l : ℤ) - (m : ℤ) + (m : ℤ) := by omega
  conv_rhs at h => arg 2; rw [hx]
  rw [laurentIntegerMonomial, HahnSeries.coeff_single_mul_add, one_mul] at h
  rw [h]
  exact hDi m hm i j _ ((sub_le_self _ (Int.natCast_nonneg m)).trans (by exact_mod_cast hl))

/-- The broad Laurent connection bound transfers to an identified monomial Euler presentation. -/
theorem monomialEulerPresentation_subfactorial_arithmetic {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hreal : monomialEulerConnection A w = C.map (HahnSeries.ofPowerSeries ℤ K))
    (hA : BroadLaurentDividedConnectionArithmetic A) : HasSubfactorialEulerConnectionDenominators C := by
  have hGauge := laurent_diagonal_gauge_subfactorial_denominators A w hA
  have he : diagonalGaugeConnection (stage14_laurentAlgebraDerivation (k := K)) A
      (fun i => laurentIntegerMonomial (w i : ℤ)) = powerSeriesEulerOrdinaryMatrix C := by
    rw [monomialEulerConnection_gauge, hreal]
    rfl
  rw [he] at hGauge
  exact powerSeriesEulerDividedConnection_subfactorial_denominators C hGauge

end WideEIntegralClosed
