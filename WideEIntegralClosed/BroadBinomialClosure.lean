import BinomialPrefixShiftClosure
import BinomialPrimitiveCombination
import Mathlib.FieldTheory.SplittingField.Construction
import WideEIntegralClosed.BroadResidueArithmetic

/-!
# Broad binomial denominator bounds under field operations

The denominator bounds are preserved under embeddings, addition, and natural
scaling. Consequently an exponent with these bounds supplies an integral
primitive element of its normal closure with the same kind of bounds.
-/

noncomputable section

open IntermediateField Polynomial StrictEUnit
open scoped BigOperators NumberField

namespace WideEIntegralClosed

namespace HasSubfactorialBinomialDenominators

variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

theorem map_iff (f : K →+* L) (a : K) :
    HasSubfactorialBinomialDenominators (f a) ↔ HasSubfactorialBinomialDenominators a := by
  have h (d m : ℕ) : IsIntegral ℤ ((d : L) * ((descPochhammer L m).eval (f a) / (m.factorial : L))) ↔
      IsIntegral ℤ ((d : K) * ((descPochhammer K m).eval a / (m.factorial : K))) := by
    have he : f ((d : K) * ((descPochhammer K m).eval a / (m.factorial : K))) =
        (d : L) * ((descPochhammer L m).eval (f a) / (m.factorial : L)) := by
      rw [map_mul, map_natCast, map_div₀, map_natCast, ← eval₂_at_apply,
        eval₂_eq_eval_map, descPochhammer_map]
    rw [← he]
    exact isIntegral_algHom_iff f.toIntAlgHom f.injective
  constructor <;> intro hp ε hε
  · obtain ⟨C, hC, hd⟩ := hp ε hε
    refine ⟨C, hC, fun n => ?_⟩
    obtain ⟨d, hd₀, hdb, hi⟩ := hd n
    exact ⟨d, hd₀, hdb, fun m hm => (h d m).1 (hi m hm)⟩
  · obtain ⟨C, hC, hd⟩ := hp ε hε
    refine ⟨C, hC, fun n => ?_⟩
    obtain ⟨d, hd₀, hdb, hi⟩ := hd n
    exact ⟨d, hd₀, hdb, fun m hm => (h d m).2 (hi m hm)⟩

/-- The Vandermonde identity gives a product clearing denominator for a sum. -/
theorem add {a b : K} (ha : HasSubfactorialBinomialDenominators a)
    (hb : HasSubfactorialBinomialDenominators b) :
    HasSubfactorialBinomialDenominators (a + b) := by
  intro ε hε
  obtain ⟨A, hA, hda⟩ := ha (ε / 2) (by positivity)
  obtain ⟨B, hB, hdb⟩ := hb (ε / 2) (by positivity)
  refine ⟨A * B, one_le_mul_of_one_le_of_one_le hA hB, fun n => ?_⟩
  obtain ⟨d, hd, hAd, hid⟩ := hda n
  obtain ⟨e, he, hBe, hie⟩ := hdb n
  refine ⟨d * e, Nat.mul_pos hd he, ?_, ?_⟩
  · rw [Nat.cast_mul]
    calc
      (d : ℝ) * (e : ℝ) ≤ (A * (n.factorial : ℝ)^(ε/2)) * (B * (n.factorial : ℝ)^(ε/2)) :=
        mul_le_mul hAd hBe (Nat.cast_nonneg _) (mul_nonneg (zero_le_one.trans hA) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ = (A * B) * (n.factorial : ℝ)^ε := by
        have he : (n.factorial : ℝ)^(ε/2) * (n.factorial : ℝ)^(ε/2) = (n.factorial : ℝ)^ε := by
          rw [← Real.rpow_add (Nat.cast_pos.mpr (Nat.factorial_pos n)), show ε / 2 + ε / 2 = ε by ring]
        rw [mul_mul_mul_comm, he]
  · intro m hm
    rw [← field_choose_eq_descPochhammer_div, Ring.add_choose_eq m (Commute.all a b), Finset.mul_sum]
    apply IsIntegral.sum
    intro ij hij
    have hi := (hid ij.1 ((Finset.antidiagonal.fst_le hij).trans hm)).mul
      (hie ij.2 ((Finset.antidiagonal.snd_le hij).trans hm))
    rw [← field_choose_eq_descPochhammer_div, ← field_choose_eq_descPochhammer_div] at hi
    convert hi using 1
    push_cast
    ring

theorem nat_mul {a : K} (ha : HasSubfactorialBinomialDenominators a) (n : ℕ) :
    HasSubfactorialBinomialDenominators ((n : K) * a) := by
  induction n with
  | zero => simpa using (natCast (K := K) 0)
  | succ n ih => simpa [Nat.cast_add, add_mul] using ih.add ha

theorem exists_integral_multiple {a : K} (ha : HasSubfactorialBinomialDenominators a) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : K) * a) ∧
      HasSubfactorialBinomialDenominators ((n : K) * a) := by
  obtain ⟨C, hC, hd⟩ := ha 1 zero_lt_one
  obtain ⟨n, hn, _, hi⟩ := hd 1
  refine ⟨n, hn, ?_, ha.nat_mul n⟩
  have h := hi 1 le_rfl
  rwa [← field_choose_eq_descPochhammer_div, Ring.choose_one_right] at h

end HasSubfactorialBinomialDenominators

private theorem subfactorial_primitive_finite_family
    (K : Type*) [Field K] [NumberField K] (S : Finset K)
    (hS : ∀ a ∈ S, HasSubfactorialBinomialDenominators a) :
    ∃ c : K, IntermediateField.adjoin ℚ (S : Set K) = ℚ⟮c⟯ ∧
      HasSubfactorialBinomialDenominators c := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨0, by simp, by simpa using HasSubfactorialBinomialDenominators.natCast (K := K) 0⟩
  | insert a S ha ih =>
    obtain ⟨b, hb, hbin⟩ := ih (fun x hx => hS x (Finset.mem_insert_of_mem hx))
    obtain ⟨n, hn⟩ := exists_nat_primitive_pair K a b
    refine ⟨a + (n : K) * b, ?_, (hS a (Finset.mem_insert_self a S)).add (hbin.nat_mul n)⟩
    rw [Finset.coe_insert, ← Set.singleton_union, IntermediateField.adjoin_union,
      hb, ← IntermediateField.adjoin_union]
    exact hn

/-- An algebraic element with broad binomial denominator bounds has a normal closure
with an integral primitive generator satisfying the same kind of bounds. -/
theorem subfactorial_binomial_normal_closure
    {K : Type*} [Field K] [CharZero K] (a : K) (hi : IsIntegral ℚ a)
    (ha : HasSubfactorialBinomialDenominators a) :
    NumberField (minpoly ℚ a).SplittingField ∧ IsGalois ℚ (minpoly ℚ a).SplittingField ∧
    ∃ c : (minpoly ℚ a).SplittingField,
      ℚ⟮c⟯ = ⊤ ∧ IsIntegral ℤ c ∧ HasSubfactorialBinomialDenominators c := by
  classical
  let L := (minpoly ℚ a).SplittingField
  letI : NumberField L := ⟨⟩
  have hg : IsGalois ℚ L := IsGalois.of_separable_splitting_field
    (minpoly.irreducible hi).separable
  let S := ((minpoly ℚ a).aroots L).toFinset
  have hS : ∀ b ∈ S, HasSubfactorialBinomialDenominators b := by
    intro b hb
    have hb' : b ∈ (minpoly ℚ a).aroots L := Multiset.mem_toFinset.mp hb
    let f := (algHomAdjoinIntegralEquiv ℚ hi).symm ⟨b,hb'⟩
    let g := AdjoinSimple.gen ℚ a
    have hg : HasSubfactorialBinomialDenominators g := by
      apply (HasSubfactorialBinomialDenominators.map_iff (algebraMap ℚ⟮a⟯ K) g).mp
      simpa only [g, AdjoinSimple.algebraMap_gen] using ha
    have h := (HasSubfactorialBinomialDenominators.map_iff f.toRingHom g).mpr hg
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, f, g,
      algHomAdjoinIntegralEquiv_symm_apply_gen] using h
  obtain ⟨b, hb, hbin⟩ := subfactorial_primitive_finite_family L S hS
  have hgen : ℚ⟮b⟯ = ⊤ := hb.symm.trans ((isSplittingField_iff_intermediateField.mp
    (inferInstance : IsSplittingField ℚ L (minpoly ℚ a))).2)
  obtain ⟨n, hn, hint, hbin⟩ := hbin.exists_integral_multiple
  refine ⟨inferInstance, hg, (n : L) * b, ?_, hint, hbin⟩
  apply top_unique
  rw [← hgen, adjoin_simple_le_iff]
  have hmem := ℚ⟮(n : L)*b⟯.smul_mem (mem_adjoin_simple_self ℚ ((n : L)*b)) (x := (n : ℚ)⁻¹)
  have hnL : (n : L) ≠ 0 := by exact_mod_cast hn.ne'
  simpa only [Algebra.smul_def, map_inv₀, map_natCast, ← mul_assoc,
    inv_mul_cancel₀ hnL, one_mul] using hmem

end WideEIntegralClosed
