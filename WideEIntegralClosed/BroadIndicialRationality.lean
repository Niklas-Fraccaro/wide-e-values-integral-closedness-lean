import WideEIntegralClosed.BroadBinomialClosure
import WideEIntegralClosed.BroadIndicialPrimeBounds
import WideEIntegralClosed.BroadPrimeGrowth
import WideEIntegralClosed.GaloisNonsplitDensity
import GaloisNonsplitPlaceCertificates

/-!
# Rationality from broad binomial denominator bounds

Prime valuations force logarithmically weighted growth for the clearing integer
of a binomial coefficient whenever its exponent generates a nontrivial Galois
extension. The bound for primes outside a finite exceptional set contradicts
subfactorial growth. Passing to the normal closure proves rationality.
-/

noncomputable section

set_option maxHeartbeats 400000

open Filter IntermediateField Polynomial StrictEUnit
open scoped BigOperators NumberField Topology

namespace WideEIntegralClosed

private theorem galois_nonsplit_prime_log_lower_except
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    [DecidablePred (GaloisCompletelySplitAt K)] (hd : 1 < Module.finrank ℚ K) (T : Finset ℕ) :
    ∃ c B : ℝ, 0 < c ∧ ∀ᶠ s : ℝ in 𝓝[>] 1,
      c * (-Real.log (s - 1)) - B ≤
        ∑' p : ℕ, if p.Prime ∧ ¬GaloisCompletelySplitAt K p ∧ p ∉ T then 1 / (p : ℝ)^s else 0 := by
  obtain ⟨c, A, hc, hbound⟩ := galois_nonsplit_prime_log_lower K hd
  refine ⟨c, A + T.card, hc, ?_⟩
  filter_upwards [hbound, self_mem_nhdsWithin] with s hbound hs
  change 1 < s at hs
  let P : ℕ → Prop := fun p => p.Prime ∧ ¬GaloisCompletelySplitAt K p
  let f : ℕ → ℝ := fun p => if P p then 1 / (p : ℝ)^s else 0
  let g : ℕ → ℝ := fun p => if p.Prime ∧ ¬GaloisCompletelySplitAt K p ∧ p ∉ T then 1 / (p : ℝ)^s else 0
  let e : ℕ → ℝ := fun p => if p ∈ T then 1 else 0
  have hconvert : (∑' p : Nat.Primes, if GaloisCompletelySplitAt K (p : ℕ) then 0 else 1 / (p : ℝ)^s) =
      ∑' p, f p := by
    let k : ℕ → ℝ := fun p => if GaloisCompletelySplitAt K p then 0 else 1 / (p : ℝ)^s
    change (∑' p : ↥{p : ℕ | p.Prime}, k p) = _
    rw [tsum_subtype]
    apply tsum_congr
    intro p
    by_cases hp : p.Prime <;> by_cases hT : GaloisCompletelySplitAt K p
      <;> simp [Set.indicator, P, f, k, hp, hT]
  have hz := Real.summable_one_div_nat_rpow.mpr hs
  have hf : Summable f := Summable.of_nonneg_of_le
    (fun p => by dsimp [f]; split_ifs <;> positivity)
    (fun p => by dsimp [f]; split_ifs <;> first | rfl | positivity) hz
  have hg : Summable g := Summable.of_nonneg_of_le
    (fun p => by dsimp [g]; split_ifs <;> positivity)
    (fun p => by dsimp [g]; split_ifs <;> first | rfl | positivity) hz
  have he : Summable e := summable_of_ne_finset_zero (s := T) (by intro p hp; simp [e, hp])
  have he' : (∑' p, e p) = (T.card : ℝ) := by
    rw [tsum_eq_sum (s := T) (fun p hp => by simp [e, hp])]
    simp [e]
  have hle (p : ℕ) : f p ≤ g p + e p := by
    have heq : g p = if P p ∧ p ∉ T then 1 / (p : ℝ)^s else 0 := by
      simp only [g, P, and_assoc]
    rw [heq]
    by_cases hp : P p
    · by_cases hT : p ∈ T
      · simp only [f, e, hp, hT, not_true_eq_false, and_false, if_true, if_false, zero_add]
        have hp₁ : (1 : ℝ) ≤ p := by
          exact_mod_cast (show 1 ≤ p from hp.1.one_lt.le)
        have hpow := Real.one_le_rpow hp₁ (zero_le_one.trans hs.le)
        exact (div_le_iff₀ (zero_lt_one.trans_le hpow)).mpr (by simpa using hpow)
      · simp [f, e, hp, hT]
    · simp only [f, hp, false_and, if_false, zero_add]
      dsimp [e]
      split_ifs <;> positivity
  have h := hf.tsum_le_tsum hle (hg.add he)
  rw [hg.tsum_add he, he'] at h
  rw [hconvert] at hbound
  change c * (-Real.log (s-1)) - (A + ↑T.card) ≤ ∑' p, g p
  linarith

/-- Broad binomial bounds on a primitive algebraic integer force its Galois field
to have degree one. -/
theorem subfactorial_binomial_galois_degree_one
    {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (a : K) (hgen : ℚ⟮a⟯ = ⊤) (hi : IsIntegral ℤ a)
    (ha : HasSubfactorialBinomialDenominators a) : Module.finrank ℚ K = 1 := by
  classical
  by_contra hne
  have hd : 1 < Module.finrank ℚ K := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    omega
  let B := (IntermediateField.adjoin.powerBasis (IsIntegral.of_finite ℚ a)).map
    ((IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv)
  obtain ⟨T, hT⟩ := galois_nonsplit_powerBasis_place_certificates (⟨a, hi⟩ : 𝓞 K) B rfl
  let P : ℕ → Prop := fun p => p.Prime ∧ ¬GaloisCompletelySplitAt K p ∧ p ∉ T
  have hp (p : ℕ) (h : P p) : p.Prime := h.1
  have hP (p : ℕ) (h : P p) : 2 ≤ p := (hp p h).two_le
  have hw : ∀ p : Subtype P, ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      w.valuation K (p.val : K) < 1 ∧
      ∀ j : ℕ, w.valuation K (a - (j : K)) = 1 :=
    fun p => hT p p.property.1 p.property.2.2 p.property.2.1
  choose w hwv hwu using hw
  let v := fun p : ℕ => if h : P p then (w ⟨p,h⟩).valuation K
    else (numberField_exists_prime_place K 2 Nat.prime_two).choose
  have ha' : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ,
      ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * (n.factorial : ℝ)^ε ∧
        IsIntegral ℤ ((d : K) * ((descPochhammer K n).eval a / (n.factorial : K))) := by
    intro ε hε
    obtain ⟨C, hC, hbound⟩ := ha ε hε
    refine ⟨C, hC, fun n => ?_⟩
    obtain ⟨d, hd, hdb, hdi⟩ := hbound n
    exact ⟨d, hd, hdb, hdi n le_rfl⟩
  have hupper := weighted_prime_sum_le_of_subfactorial_binomial_denominators a v ha'
  apply (not_weighted_sum_le_log_of_positive_dirichlet_growth P hP
    (galois_nonsplit_prime_log_lower_except K hd T))
  intro ε hε
  obtain ⟨C, _, hC⟩ := hupper ε hε
  refine ⟨C, fun n hn => ?_⟩
  rw [← Finset.sum_filter]
  apply hC n (by omega)
  · intro p h
    obtain ⟨hpn, hpP⟩ := Finset.mem_filter.mp h
    exact ⟨hp p hpP, (Finset.mem_Icc.mp hpn).2⟩
  · intro p h
    have hh := (Finset.mem_filter.mp h).2
    simpa only [v, dif_pos hh] using hwv ⟨p,hh⟩
  · intro p h j _
    have hh := (Finset.mem_filter.mp h).2
    simpa only [v, dif_pos hh] using hwu ⟨p,hh⟩ j

/-- Subfactorial clearing denominators for the binomial coefficients of an
algebraic exponent force it to be rational. -/
theorem subfactorial_binomial_rational {K : Type*} [Field K] [CharZero K]
    (a : K) (hi : IsIntegral ℚ a) (ha : HasSubfactorialBinomialDenominators a) :
    ∃ q : ℚ, algebraMap ℚ K q = a := by
  let L := (minpoly ℚ a).SplittingField
  obtain ⟨hN, hG, c, hc, hci, hcd⟩ := subfactorial_binomial_normal_closure a hi ha
  letI : NumberField L := hN
  letI : IsGalois ℚ L := hG
  have hd : Module.finrank ℚ L = 1 := subfactorial_binomial_galois_degree_one c hc hci hcd
  obtain ⟨b, hb⟩ := Polynomial.exists_root_of_splits (algebraMap ℚ L)
    (Polynomial.SplittingField.splits (minpoly ℚ a)) (ne_of_gt (minpoly.degree_pos hi))
  have hb' : b ∈ (minpoly ℚ a).aroots L := by
    rw [Polynomial.mem_aroots]
    exact ⟨minpoly.ne_zero hi, hb⟩
  let f := (algHomAdjoinIntegralEquiv ℚ hi).symm ⟨b,hb'⟩
  letI : FiniteDimensional ℚ ℚ⟮a⟯ := IntermediateField.adjoin.finiteDimensional hi
  have hle : Module.finrank ℚ ℚ⟮a⟯ ≤ Module.finrank ℚ L :=
    LinearMap.finrank_le_finrank_of_injective f.injective
  have hpos := Module.finrank_pos (R := ℚ) (M := ℚ⟮a⟯)
  have heq : Module.finrank ℚ ℚ⟮a⟯ = 1 := by omega
  exact (IntermediateField.mem_bot).mp
    (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp heq)

end WideEIntegralClosed
