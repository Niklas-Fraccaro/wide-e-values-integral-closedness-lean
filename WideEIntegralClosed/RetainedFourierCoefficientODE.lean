import FrobeniusIntegerShiftEquation
import DifferentialFiniteFiltration
import Stage14LaurentPolynomialODEClosure

/-! The formal Laurent ODE of every retained Fourier coefficient. -/

noncomputable section

set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 45000

open scoped BigOperators
open StrictEUnit

namespace WideEIntegralClosed

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
private theorem rationalLaurent_monomial (s : ℤ) (a : K) :
    algebraMap (RatFunc K) (LaurentSeries K) (RatFunc.C a * RatFunc.X ^ s) =
      HahnSeries.single s a := by
  let X : LaurentSeries K := HahnSeries.single (1 : ℤ) 1
  have hX : algebraMap (RatFunc K) (LaurentSeries K) RatFunc.X = X := RatFunc.coe_X
  have hinv : X⁻¹ = HahnSeries.single (-1 : ℤ) (1 : K) := by
    apply inv_eq_of_mul_eq_one_right
    simp [X, HahnSeries.single_mul_single]
  have hp (u : ℕ) : X ^ u = HahnSeries.single (u : ℤ) (1 : K) := by
    simp [X, HahnSeries.single_pow, nsmul_eq_mul]
  have hz : X ^ s = HahnSeries.single s (1 : K) := by
    cases s with
    | ofNat u => exact hp u
    | negSucc u =>
      rw [zpow_negSucc, ← inv_pow, hinv, HahnSeries.single_pow]
      congr 1
      · simp [nsmul_eq_mul, Int.negSucc_eq]
      · simp
  rw [map_mul, map_zpow₀, hX, hz]
  change (RatFunc.C a : LaurentSeries K) * _ = _
  rw [RatFunc.coe_C, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

omit [CharZero K] in
private theorem twistedEuler_coefficient (rho : K) (p : Polynomial (LaurentSeries K)) (j : ℕ) :
    (twistedLogPolynomialEuler rho p).coeff j =
      HahnSeries.single (1 : ℤ) (1 : K) * stage14_laurentAlgebraDerivation (p.coeff j) +
      HahnSeries.single (0 : ℤ) rho * p.coeff j +
      HahnSeries.single (0 : ℤ) ((j + 1 : ℕ) : K) * p.coeff (j + 1) := by
  apply HahnSeries.ext
  funext s
  rw [twistedLogPolynomialEuler_double_coeff, HahnSeries.coeff_add, HahnSeries.coeff_add]
  have h (t : ℤ) (a : K) (v : LaurentSeries K) :
      (HahnSeries.single t a * v).coeff s = a * v.coeff (s - t) := by
    conv_lhs => rw [show s = (s - t) + t by omega, HahnSeries.coeff_single_mul_add]
  repeat rw [h]
  rw [stage14_laurentAlgebraDerivation_apply, laurentOrdinaryDerivation_coeff]
  simp only [sub_zero, one_mul, sub_add_cancel]
  push_cast
  ring

omit [CharZero K] in
private theorem finiteTwistedEulerSystem_coefficient_ode
    {ι : Type*} [Fintype ι] (rho : K) (C : Matrix ι ι (RatFunc K))
    (y : ι → Polynomial (LaurentSeries K))
    (hy : ∀ i, twistedLogPolynomialEuler rho (y i) =
      ∑ j, Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (C i j)) * y j) :
    ∀ i j, HasPolynomialScalarDifferentialRelation (k := K) stage14_laurentAlgebraDerivation
      ((y i).coeff j) := by
  classical
  letI : SMul K (LaurentSeries K) := Algebra.toSMul
  letI : SMul K (RatFunc K) := Algebra.toSMul
  letI : Module K (LaurentSeries K) := Algebra.toModule
  letI : Module K (RatFunc K) := Algebra.toModule
  letI : IsScalarTower K (RatFunc K) (LaurentSeries K) := stage14_rationalLaurentScalarTower
  let d := Finset.univ.sup (fun i => (y i).natDegree)
  let M := Submodule.span (RatFunc K) (Set.range fun ij : ι × Fin (d + 1) => (y ij.1).coeff ij.2.val)
  have hmem (i : ι) (j : ℕ) : (y i).coeff j ∈ M := by
    by_cases hj : j < d + 1
    · exact Submodule.subset_span ⟨(i, ⟨j, hj⟩), rfl⟩
    · have hi : (y i).natDegree ≤ d := Finset.le_sup (f := fun k => (y k).natDegree) (Finset.mem_univ i)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Submodule.zero_mem _
  have hmul (s : ℤ) (a : K) (f : LaurentSeries K) (hf : f ∈ M) :
      HahnSeries.single s a * f ∈ M := by
    have hh := M.smul_mem (RatFunc.C a * RatFunc.X ^ s) hf
    simpa only [Algebra.smul_def, rationalLaurent_monomial] using hh
  have hstable : ∀ f ∈ M, stage14_laurentAlgebraDerivation f ∈ M := by
    apply differential_span_stable stage14_rationalOrdinaryDerivation stage14_laurentAlgebraDerivation
      (fun b => stage14_rationalLaurent_differential b)
    rintro f ⟨⟨i, j⟩, rfl⟩
    have he := congrArg (fun p : Polynomial (LaurentSeries K) => p.coeff j.val) (hy i)
    simp only [twistedEuler_coefficient, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul] at he
    have hrhs : (∑ l, algebraMap (RatFunc K) (LaurentSeries K) (C i l) * (y l).coeff j.val) ∈ M := by
      apply Submodule.sum_mem
      intro l _
      simpa only [Algebra.smul_def] using M.smul_mem (C i l) (hmem l j.val)
    have hEuler : HahnSeries.single (1 : ℤ) (1 : K) *
        stage14_laurentAlgebraDerivation ((y i).coeff j.val) ∈ M := by
      convert M.sub_mem (M.sub_mem hrhs (hmul 0 rho _ (hmem i j.val)))
        (hmul 0 ((j.val + 1 : ℕ) : K) _ (hmem i (j.val + 1))) using 1
      rw [← he]
      ring
    have ht := hmul (-1) 1 _ hEuler
    simpa only [← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one,
      HahnSeries.single_zero_one, one_mul] using ht
  intro i j
  exact finiteDifferentialSpan_polynomialScalarRelation _
    ⟨M, Submodule.fg_span (Set.finite_range _), hstable, hmem i j⟩

private theorem twistedEulerEquation_coefficient_ode (rho : K)
    (p : Polynomial (LaurentSeries K)) (n : ℕ)
    (q : Fin (n + 1) → RatFunc K) (hq : q (Fin.last n) ≠ 0)
    (he : ∑ i, Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q i)) *
      (twistedLogPolynomialEuler rho)^[i.val] p = 0) :
    ∀ j, HasPolynomialScalarDifferentialRelation (k := K) stage14_laurentAlgebraDerivation (p.coeff j) := by
  classical
  cases n with
  | zero =>
    have he' : Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q 0)) * p = 0 := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_zero, zero_add, Fin.val_last,
        Function.iterate_zero_apply] at he
      exact he
    have hp : p = 0 := (mul_eq_zero.mp he').resolve_left fun hz => hq (by
      apply (algebraMap (RatFunc K) (LaurentSeries K)).injective
      apply Polynomial.C_injective
      simpa only [map_zero] using hz)
    subst p
    intro j
    refine ⟨0, fun _ => 1, ⟨0, one_ne_zero⟩, ?_⟩
    simp
  | succ n =>
    rw [Fin.sum_univ_castSucc] at he
    let y (i : Fin (n + 1)) := (twistedLogPolynomialEuler rho)^[i.val] p
    let a (j : Fin (n + 1)) : RatFunc K := -(q (Fin.last (n + 1)))⁻¹ * q j.castSucc
    have htop : (twistedLogPolynomialEuler rho)^[n + 1] p =
        ∑ j, Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (a j)) * y j := by
      have hlast : Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q (Fin.last (n + 1)))) *
          (twistedLogPolynomialEuler rho)^[n + 1] p =
          -(∑ j : Fin (n + 1), Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q j.castSucc)) * y j) :=
        eq_neg_of_add_eq_zero_right he
      have h := congrArg (fun z : Polynomial (LaurentSeries K) =>
        Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) ((q (Fin.last (n + 1)))⁻¹)) * z) hlast
      simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul] at h
      rw [h]
      simp only [a, map_mul, map_neg, Finset.mul_sum, mul_neg, neg_mul, mul_assoc,
        ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    let C : Matrix (Fin (n + 1)) (Fin (n + 1)) (RatFunc K) := fun i j =>
      if i.val = n then a j else if j.val = i.val + 1 then 1 else 0
    have hy (i : Fin (n + 1)) : twistedLogPolynomialEuler rho (y i) =
        ∑ j, Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (C i j)) * y j := by
      by_cases hi : i.val = n
      · simpa only [y, C, hi, if_pos, ← Function.iterate_succ_apply'] using htop
      · let l : Fin (n + 1) := ⟨i.val + 1, by omega⟩
        have hl (j : Fin (n + 1)) : (j.val = i.val + 1) ↔ j = l :=
          ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
        rw [Finset.sum_eq_single l]
        · have hOne : C i l = 1 := by simp only [C, hi, if_false, hl, if_pos rfl, if_true]
          rw [hOne, map_one, map_one, one_mul]
          exact (Function.iterate_succ_apply' _ i.val p).symm
        · intro j _ hj
          have hZero : C i j = 0 := by simp only [C, hi, if_false, hl, hj]
          rw [hZero, map_zero, map_zero, zero_mul]
        · simp
    simpa only [y, Fin.val_zero, Function.iterate_zero_apply] using
      finiteTwistedEulerSystem_coefficient_ode rho C y hy (0 : Fin (n + 1))

/-- The retained twisted formal equation gives each of its Laurent coefficients an ordinary
polynomial differential equation. -/
theorem retainedFourier_coefficient_ode {m n : ℕ}
    (A : Fin (m + 1) → Fin (n + 1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last m) (Fin.last n) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0)) :
    ∀ j, HasPolynomialScalarDifferentialRelation (k := K) stage14_laurentAlgebraDerivation
      ((sameFourierTwistedAmplitude A hf i).coeff j) := by
  classical
  let q (k : Fin (n + 1)) : RatFunc K := ∑ u, ∑ v,
    RatFunc.C (((-1 : K) ^ v.val * A u v) * (stage61_shiftedDesc u.val v.val).coeff k.val) *
      RatFunc.X ^ stage57_exponent u v
  have hq (k : Fin (n + 1)) : algebraMap (RatFunc K) (LaurentSeries K) (q k) =
      HahnSeries.ofPowerSeries ℤ K ((stage61_fourierLift A hf).coeff k.val) := by
    simp only [q, map_sum, rationalLaurent_monomial, ← stage61_fourierEulerSymbol_coeff]
    rw [stage61_fourierLift, stage59_regularLift_map_coeff]
  have hne : q (Fin.last n) ≠ 0 := by
    intro h
    have h := hq (Fin.last n) ▸ congrArg (algebraMap (RatFunc K) (LaurentSeries K)) h
    rw [Fin.val_last, stage61_fourierLift_top, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, map_zero] at h
    exact stage61_fourierCorner_ne_zero A hc (by simpa using congrArg (HahnSeries.coeff · 0) h)
  apply twistedEulerEquation_coefficient_ode _ _ n q hne
  simp only [hq]
  exact sameFourierTwistedAmplitude_equation A hf hc i

end WideEIntegralClosed
