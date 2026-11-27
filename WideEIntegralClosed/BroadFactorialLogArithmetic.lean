import WideEIntegralClosed.BroadLaplaceTransfer
import WideEIntegralClosed.BroadLaurentConnection
import NormalizedMixingMatrixBound
import FourierLaurentRealization

/-! Broad factorial-prefix arithmetic after the logarithmic Laplace transform. -/

noncomputable section

open StrictEUnit

namespace WideEIntegralClosed

/-- A fixed starting Laurent index can be removed from a broad prefix estimate. -/
theorem subfactorialLogPolynomial_tail_to_prefix
    {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    (f : ι → ℤ → Polynomial K) (L : ℤ)
    (hden : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ i t, IsIntegral ℤ ((D : K) * (f i ((m : ℤ) + L)).coeff t)) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ i t, IsIntegral ℤ ((D : K) * (f i (m : ℤ)).coeff t) := by
  classical
  obtain ⟨e, he, hIntegral⟩ := finitePolynomial_coeff_integral
    (fun z : ι × Fin L.toNat => f z.1 (z.2.val : ℤ))
  let A := (-L).toNat
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  refine hden.affine_mul (a := A + 1) (Nat.succ_pos _) (e : ℝ) he1
    (Q := fun _ q => q = e)
    (fun N => ⟨e, he, le_self_pow₀ he1 (Nat.succ_ne_zero N), rfl⟩) ?_
  intro N D q hint hq m hm i t
  subst q
  by_cases hml : (m : ℤ) < L
  · have hmt : m < L.toNat := by omega
    rw [Nat.cast_mul, mul_assoc]
    exact (ordinaryJet_natCast_integral D).mul (hIntegral (i, ⟨m, hmt⟩) t)
  · let j := ((m : ℤ) - L).toNat
    have hj : j ≤ N + A := by dsimp only [j, A]; omega
    have hcut : N + A ≤ (A + 1) * (N + 1) := by
      have hA : A ≤ A * (N + 1) := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left A (Nat.succ_pos N)
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have heq : (j : ℤ) + L = (m : ℤ) := by dsimp only [j]; omega
    have hi := hint j (hj.trans hcut) i t
    rw [heq] at hi
    rw [Nat.cast_mul, mul_comm (D : K) (e : K), mul_assoc]
    exact (ordinaryJet_natCast_integral e).mul hi

/-- Factorial-normalized common logarithmic coefficient denominators. -/
def HasSubfactorialFactorialLogDenominators {K : Type*} [Field K]
    (p : Polynomial (LaurentSeries K)) : Prop :=
  HasSubfactorialPrefixDenominators fun N D =>
    ∀ m ≤ N, ∀ t, IsIntegral ℤ ((D : K) * (m.factorial : K) * (p.coeff t).coeff (m : ℤ))

private theorem factorialLog_shift_one {K : Type*} [Field K] [NumberField K]
    (p : Polynomial (LaurentSeries K)) (hp : HasSubfactorialFactorialLogDenominators p) :
    HasSubfactorialFactorialLogDenominators (frobeniusIntegerShift 1 p) := by
  let f : Unit → ℤ → Polynomial K := fun _ z =>
    (z.toNat.factorial : K) • (logPolynomialToCoefficientSeries (frobeniusIntegerShift 1 p)).coeff z
  have ht : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ i t, IsIntegral ℤ ((D : K) * (f i ((m : ℤ) + 1)).coeff t) := by
    intro ε hε
    obtain ⟨B, hB, hBound⟩ := hp ε hε
    refine ⟨B, hB, fun N => ?_⟩
    obtain ⟨D, hD, hDb, hDi⟩ := hBound N
    refine ⟨D, hD, hDb, fun m hm i t => ?_⟩
    dsimp only [f]
    rw [Polynomial.coeff_smul, smul_eq_mul, logPolynomialToCoefficientSeries_double_coeff,
      frobeniusIntegerShift_coeff, add_sub_cancel_right]
    have he : ((m : ℤ) + 1).toNat = m + 1 := by omega
    rw [he, Nat.factorial_succ, Nat.cast_mul]
    convert (ordinaryJet_natCast_integral (K := K) (m + 1)).mul (hDi m hm t) using 1
    ring
  intro ε hε
  obtain ⟨B, hB, hBound⟩ := subfactorialLogPolynomial_tail_to_prefix f 1 ht ε hε
  refine ⟨B, hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hBound N
  refine ⟨D, hD, hDb, fun m hm t => ?_⟩
  simpa only [f, Int.toNat_natCast, Polynomial.coeff_smul, smul_eq_mul,
    logPolynomialToCoefficientSeries_double_coeff, mul_assoc] using hDi m hm () t

private theorem factorialLog_shift_neg_one {K : Type*} [Field K] [NumberField K]
    (p : Polynomial (LaurentSeries K)) (hp : HasSubfactorialFactorialLogDenominators p) :
    HasSubfactorialFactorialLogDenominators (frobeniusIntegerShift (-1) p) := by
  refine hp.affine_mul (a := 1) Nat.one_pos 16 (by norm_num)
    (Q := fun N Q => Q = logJetLCM (N + 1)) (fun N =>
      ⟨_, logJetLCM_pos _, logJetLCM_real_le_sixteen_pow (N + 1), rfl⟩) ?_
  intro N D Q hint hQ m hm t
  rw [frobeniusIntegerShift_coeff]
  have he : (m : ℤ) - (-1) = ((m + 1 : ℕ) : ℤ) := by omega
  rw [he]
  have hquot : IsIntegral ℤ ((Q : K) / (m + 1 : ℕ)) :=
    integral_nat_quotient_of_dvd Q (m + 1) (by omega)
      (by rw [hQ]; exact logJetLCM_dvd (N + 1) (m + 1) (by omega) (by omega))
  have hi := hquot.mul (hint (m + 1) (by omega) t)
  convert hi using 1
  rw [Nat.cast_mul, Nat.factorial_succ, Nat.cast_mul]
  have hsucc : (m : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  push_cast
  field_simp [hsucc]
  ring

/-- Undo or insert any fixed integer exponent gauge. -/
theorem HasSubfactorialFactorialLogDenominators.shift {K : Type*} [Field K] [NumberField K]
    {p : Polynomial (LaurentSeries K)} (hp : HasSubfactorialFactorialLogDenominators p) (z : ℤ) :
    HasSubfactorialFactorialLogDenominators (frobeniusIntegerShift z p) := by
  induction z using Int.induction_on with
  | hz => simpa [frobeniusIntegerShift] using hp
  | hp k ih =>
    have h := factorialLog_shift_one _ ih
    rw [frobeniusIntegerShift_add] at h
    simpa only [add_comm] using h
  | hn k ih =>
    have h := factorialLog_shift_neg_one _ ih
    rw [frobeniusIntegerShift_add] at h
    convert h using 1 <;> congr 1 <;> omega

/-- Factorial-prefix denominators are preserved by a coefficient field embedding. -/
theorem HasSubfactorialFactorialLogDenominators.map
    {K L : Type*} [Field K] [Field L] [CharZero K]
    {p : Polynomial (LaurentSeries K)} (hp : HasSubfactorialFactorialLogDenominators p)
    (φ : K →+* L) : HasSubfactorialFactorialLogDenominators (stage38_logMap φ p) := by
  intro ε hε
  obtain ⟨B, hB, hBound⟩ := hp ε hε
  refine ⟨B, hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hBound N
  refine ⟨D, hD, hDb, fun m hm t => ?_⟩
  have hi := (hDi m hm t).map φ.toIntAlgHom
  simpa only [RingHom.toIntAlgHom_apply, map_mul, map_natCast, stage38_logMap_coeff] using hi

/-- A broad preimage and the geometric bound on the finite mixing matrix suffice for
broad factorial-prefix arithmetic of the exact logarithmic amplitude. -/
theorem factorialLog_subfactorial_of_preimage
    {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
    (r : ι → K) (hr : JointBinomialPrefixDenominators r)
    (i : ι) (h : ∀ n : ℕ, r i + (n + 1 : ℕ) ≠ 0)
    (p : Polynomial (LaurentSeries K)) (u : LaurentSeries (Polynomial K)) (d : ℕ)
    (hu : generalizedLogLaplaceLinear (r i) h u = logPolynomialToCoefficientSeries p)
    (hd : ∀ m, (u.coeff m).natDegree ≤ d)
    (ha : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m ≤ N, ∀ t, IsIntegral ℤ ((D : K) * (u.coeff (m : ℤ)).coeff t)) :
    HasSubfactorialFactorialLogDenominators p := by
  obtain ⟨C, hC, hden⟩ := factorialLogMixing_shared_matrix_bound r hr d
  have hMix := generalizedLogLaplace_hasSubfactorialDenominators (r i) h u d
    (fun n => hd _) ha ⟨C, hC, fun N => by
      obtain ⟨Q, hQ, hQb, hQi⟩ := hden N
      exact ⟨Q, hQ, hQb, fun n hn j hj t => hQi i h n hn j hj t⟩⟩
  intro ε hε
  obtain ⟨B, hB, hBound⟩ := hMix ε hε
  refine ⟨B, hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hBound N
  refine ⟨D, hD, hDb, fun m hm t => ?_⟩
  have he : generalizedLogLaplaceSeries (r i) h u = logPolynomialToCoefficientSeries p := hu
  have hi := hDi m hm t
  rw [he, logPolynomialToCoefficientSeries_double_coeff] at hi
  exact hi

end WideEIntegralClosed
