import WideEIntegralClosed.BroadLaurentConnection
import FiniteLaurentForcingArithmetic

/-! Broad denominator bounds for the finite Laurent forcing extension. -/

noncomputable section

open StrictEUnit

namespace WideEIntegralClosed

/-- Adjoining a constant forcing coordinate preserves broad divided-connection arithmetic.
The forcing column has a geometric bound, which is absorbed by a smaller factorial exponent. -/
theorem broadLaurentDividedConnectionArithmetic_constantForcing {K : Type*} [Field K] [CharZero K]
    {r : ℕ} (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (hA : BroadLaurentDividedConnectionArithmetic A) (hb : LaurentForcingArithmetic b) :
    BroadLaurentDividedConnectionArithmetic (constantForcingConnection A b) := by
  obtain ⟨P, hAlow, hAden⟩ := hA
  obtain ⟨W, H, hH, hblow, hBden⟩ := hb
  let a := P + W + 3
  let C := H ^ (a + 1) * (16 : ℝ) ^ 2
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH) (by norm_num)
  refine ⟨P + W + 1, constantForcingConnection_linear_poles A b P W hAlow hblow, ?_⟩
  let clears (N q : ℕ) : Prop := ∃ DB : ℕ, q = DB * logJetLCM N ^ 2 ∧
    ∀ j l, l ≤ ((a * (N + 1) : ℕ) : ℤ) → IsIntegral ℤ ((DB : K) * (b j).coeff l)
  have hgeom (N : ℕ) : ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ C ^ (N + 1) ∧ clears N q := by
    obtain ⟨DB, hDB, hDBb, hDBi⟩ := hBden (a * (N + 1))
    refine ⟨DB * logJetLCM N ^ 2, Nat.mul_pos hDB (pow_pos (logJetLCM_pos N) _), ?_,
      ⟨DB, rfl, hDBi⟩⟩
    have hDb : (DB : ℝ) ≤ (H ^ (a + 1)) ^ (N + 1) := by
      apply hDBb.trans
      rw [← pow_mul]
      apply pow_le_pow_right₀ hH
      rw [show (a + 1) * (N + 1) = a * (N + 1) + (N + 1) by rw [Nat.add_mul, Nat.one_mul]]
      omega
    have hL : (logJetLCM N : ℝ) ^ 2 ≤ ((16 : ℝ) ^ 2) ^ (N + 1) := by
      calc
        _ ≤ ((16 : ℝ) ^ N) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (logJetLCM_real_le_sixteen_pow N) _
        _ = ((16 : ℝ) ^ 2) ^ N := by rw [← pow_mul, ← pow_mul, Nat.mul_comm N 2]
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    rw [Nat.cast_mul, Nat.cast_pow, show C = H ^ (a + 1) * (16 : ℝ) ^ 2 from rfl,
      mul_pow]
    exact mul_le_mul hDb hL (by positivity) (by positivity)
  refine hAden.affine_mul (a := a) (by dsimp [a]; omega) C hC hgeom ?_
  intro N DA q hDAi hQ
  obtain ⟨DB, rfl, hDBi⟩ := hQ
  have hcutoff : N ≤ a * (N + 1) := by
    dsimp only [a]
    nlinarith
  simpa only [Nat.mul_assoc] using
    constantForcingConnection_prefix_integral A b P W N DA DB
      (fun m _ => hAlow m) hblow (fun m hm i j l hl => hDAi m (hm.trans hcutoff) i j l hl) hDBi

/-- Every fixed finite Laurent forcing extension inherits broad arithmetic. -/
theorem broadLaurentDividedConnectionArithmetic_finiteForcing {K : Type*} [Field K] [CharZero K]
    {r : ℕ} (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (hA : BroadLaurentDividedConnectionArithmetic A) (hb : LaurentForcingArithmetic b)
    (k : ℕ → ℤ) (s : ℕ) :
    BroadLaurentDividedConnectionArithmetic (finiteLaurentForcingConnection A b k s) := by
  induction s with
  | zero => exact hA
  | succ s ih =>
    exact broadLaurentDividedConnectionArithmetic_constantForcing _ _ ih
      (laurentForcingArithmetic_integer_shift _ (zeroPaddedForcingColumn_arithmetic b hb s) (k s))

end WideEIntegralClosed
