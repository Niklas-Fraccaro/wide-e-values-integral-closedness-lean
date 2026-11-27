import WideE.Bounds
import MappedIndicialBinomialArithmetic
import SelectedFourierIndicialFactor
import SelectedSourceRootBinomialArithmetic

/-! Subfactorial denominators for actual indicial binomials. -/

noncomputable section

open scoped BigOperators Matrix NumberField
open StrictEUnit

namespace WideEIntegralClosed

/-- Common subfactorial denominators for the binomials of a field element. -/
def HasSubfactorialBinomialDenominators {K : Type*} [Field K] [CharZero K] (x : K) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℕ,
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * (s.factorial : ℝ) ^ ε ∧
      ∀ m ≤ s, IsIntegral ℤ ((d : K) * ((descPochhammer K m).eval x / (m.factorial : K)))

theorem HasSubfactorialBinomialDenominators.natCast {K : Type*} [Field K] [CharZero K] (k : ℕ) :
    HasSubfactorialBinomialDenominators (k : K) := by
  intro ε hε
  refine ⟨1, le_rfl, fun s => ⟨1, Nat.zero_lt_one, ?_, ?_⟩⟩
  · simpa only [Nat.cast_one, one_mul] using
      Real.one_le_rpow (by exact_mod_cast Nat.factorial_pos s) hε.le
  · intro m _
    simpa only [Nat.cast_one, one_mul] using
      natCast_descPochhammer_div_factorial_integral (K := K) k m

/-- Subfactorial connection denominators give subfactorial binomial denominators for
every indicial root, including roots in an algebraic extension of the coefficient field.
The additional factors are a fixed eigenvector denominator and a power of the norm
of the trailing coefficient of the original clearing polynomial. -/
theorem hasSubfactorialBinomialDenominators_of_connection
    {K L : Type*} [Field K] [NumberField K] [Field L] [CharZero L] [Algebra.IsAlgebraic ℤ L]
    (φ : K →+* L) (n : ℕ) (c : Fin (n + 1) → RatFunc K) (T : Polynomial (𝓞 K))
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial K))
    (hT : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K)) *
        minimalDerivativeCompanion (n + 1) c i j)
    (hregular : ∀ j, U (Fin.last n) j ≠ 0 →
      (T.map (algebraMap (𝓞 K) K)).natTrailingDegree + j.val ≤
        (U (Fin.last n) j).natTrailingDegree + (n + 1))
    (hden : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℕ,
      ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * (s.factorial : ℝ) ^ ε ∧
        ∀ m ≤ s, ∀ i j : Fin (n + 1), ∀ l : ℕ,
          IsIntegral ℤ ((d : K) *
            (dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K)) U m i j).coeff l))
    (ξ : L) :
    let t := T.map (algebraMap (𝓞 K) K)
    (regularResidueIndicial n (φ (t.coeff t.natTrailingDegree))
      (fun j => φ (polynomialCompanionFace n 1 1 t U j))).eval ξ = 0 →
      HasSubfactorialBinomialDenominators ξ := by
  classical
  intro t hroot
  by_cases ht : t.natTrailingDegree = 0
  · rw [regularResidueIndicial_ordinary_eq_desc φ n t U ht] at hroot
    obtain ⟨k, _, rfl⟩ := (descPochhammer_eval_eq_zero_iff_natCast (n + 1) ξ).mp hroot
    exact HasSubfactorialBinomialDenominators.natCast k
  let τ := t.coeff t.natTrailingDegree
  let β := polynomialCompanionFace n 1 1 t U
  let v := T.coeff t.natTrailingDegree
  let q := Int.natAbs (Algebra.norm ℤ v)
  let e : Fin (n + 1) → L := fun j => (descPochhammer L j.val).eval ξ
  have hvmap : (v : K) = τ := by
    change algebraMap (𝓞 K) K (T.coeff t.natTrailingDegree) =
      (T.map (algebraMap (𝓞 K) K)).coeff t.natTrailingDegree
    rw [Polynomial.coeff_map]
  have hv : v ≠ 0 := by
    intro h
    have hτ : τ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
    apply hτ
    rw [← hvmap, h]
    rfl
  have hq : 0 < q := (ringOfIntegers_natAbs_norm_certificate v hv).1
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.succ_le_of_lt hq)
  obtain ⟨b, hb, hbe⟩ := exists_positive_nat_integral_algebraic_vector e
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (Nat.succ_le_of_lt hb)
  intro ε hε
  obtain ⟨C, hC, hprefix⟩ := hden (ε / 2) (by positivity)
  obtain ⟨D, hD, hpow⟩ := WideE.exists_exp_pow_le_factorial_rpow (q : ℝ)
    (ε / 2) hq1 (by positivity)
  refine ⟨(b : ℝ) * (C * D), one_le_mul_of_one_le_of_one_le hb1
    (one_le_mul_of_one_le_of_one_le hC hD), fun s => ?_⟩
  obtain ⟨d, hd, hdb, hint⟩ := hprefix s
  refine ⟨b * (d * q ^ s), Nat.mul_pos hb (Nat.mul_pos hd (pow_pos hq s)), ?_, ?_⟩
  · rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
    calc
      (b : ℝ) * ((d : ℝ) * (q : ℝ) ^ s) ≤
          (b : ℝ) * ((C * (s.factorial : ℝ) ^ (ε / 2)) * (D * (s.factorial : ℝ) ^ (ε / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hdb (hpow s) (by positivity) (by positivity))
          (by positivity)
      _ = (b : ℝ) * (C * D) * (s.factorial : ℝ) ^ ε := by
        have hp : (s.factorial : ℝ) ^ (ε / 2) * (s.factorial : ℝ) ^ (ε / 2) =
            (s.factorial : ℝ) ^ ε := by
          rw [← Real.rpow_add (by positivity : (0 : ℝ) < s.factorial), add_halves]
        rw [← hp]
        ring
  · intro m hm
    have hrow (j : Fin (n + 1)) :
        IsIntegral ℤ (((d * q ^ s : ℕ) : K) * regularResidueBinomialRow n τ β m j) := by
      let x := polynomialConnectionFaceRow n 1 1 t U m j
      have hx : IsIntegral ℤ ((d : K) * x / (m.factorial : K)) :=
        polynomialConnectionSequence_expanded_integral t U m d 1 Nat.one_pos 0 j
          (irregularPolynomialWeight 1 t.natTrailingDegree 1 m j.val) (hint m hm 0 j)
      have heq : ((d * q ^ s : ℕ) : K) * regularResidueBinomialRow n τ β m j =
          ((d * q ^ s : ℕ) : K) * (x / (m.factorial : K)) / (v : K) ^ m := by
        rw [regularResidueBinomialRow_eq_normalized_face n c t U hT hclear (Nat.pos_of_ne_zero ht)
          hregular m j, hvmap]
        change ((d * q ^ s : ℕ) : K) * (x / ((m.factorial : K) * τ ^ m)) =
          ((d * q ^ s : ℕ) : K) * (x / (m.factorial : K)) / τ ^ m
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [heq]
      exact ordinaryJet_norm_power_clearing v hv d s m hm (x / (m.factorial : K))
        (by simpa only [div_eq_mul_inv, mul_assoc] using hx)
    have hmapped (j : Fin (n + 1)) :
        IsIntegral ℤ (((d * q ^ s : ℕ) : L) *
          regularResidueBinomialRow n (φ τ) (fun l => φ (β l)) m j) := by
      simpa only [RingHom.toIntAlgHom_apply, map_mul, map_natCast, regularResidueBinomialRow_map]
        using (hrow j).map φ.toIntAlgHom
    rw [← regularResidueBinomialRow_indicial_pairing n (φ τ) (fun j => φ (β j)) ξ hroot m]
    change IsIntegral ℤ (((b * (d * q ^ s) : ℕ) : L) *
      ∑ j, regularResidueBinomialRow n (φ τ) (fun l => φ (β l)) m j * e j)
    rw [Finset.mul_sum]
    apply IsIntegral.sum
    intro j _
    convert (hmapped j).mul (hbe j) using 1
    simp only [Nat.cast_mul]
    ring

/-- The exact reflected Fourier tuple inherits subfactorial binomial denominators.
Its additional indicial roots are the natural roots of a descending Pochhammer factor. -/
theorem hasSubfactorialBinomialDenominators_of_reflected_fourier_root
    {K L : Type*} [Field K] [Field L] [CharZero L]
    (φ : K →+* L) (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial K)) (hT : T ≠ 0)
    (hregular : ReciprocalRegularSingularBounds (n + 1)
      (fun i => (sameCompanionScalarTuple (n + 1) (Nat.succ_pos n) T U i).map φ))
    (hsource : ∀ ξ : L, (regularResidueIndicial n (φ (T.coeff T.natTrailingDegree))
      (fun j => φ (polynomialCompanionFace n 1 1 T U j))).eval ξ = 0 →
      HasSubfactorialBinomialDenominators ξ) :
    let q := ordinaryReflectionTuple (n + 1)
      (fun i => (sameCompanionScalarTuple (n + 1) (Nat.succ_pos n) T U i).map φ)
    let A := reciprocalSourceArray (n + 1) (reciprocalCommonDegree (n + 1) q) q
    ∀ hf : Stage56FiniteFuchs A, ∀ ξ : L,
      (sameFourierEulerCoefficientSymbols A hf 0).eval ξ = 0 →
        HasSubfactorialBinomialDenominators ξ := by
  intro q A hf ξ hx
  have hfactor := sameCompanion_mapped_reflected_indicial_factor φ n T U hT hregular hf
  rw [hfactor, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C] at hx
  rcases mul_eq_zero.mp hx with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exfalso
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        ((map_ne_zero φ).mpr (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT)) h
    · obtain ⟨k, _, rfl⟩ := (descPochhammer_eval_eq_zero_iff_natCast _ ξ).mp h
      exact HasSubfactorialBinomialDenominators.natCast k
  · exact hsource ξ h

end WideEIntegralClosed
