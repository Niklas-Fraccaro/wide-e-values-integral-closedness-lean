import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! The algebraic descent in Section 5, over an arbitrary base algebra. -/

noncomputable section

open scoped BigOperators Polynomial
open Polynomial

namespace WideEIntegralClosed

/-- A simultaneous lift of specified polynomial relations through a normal domain. -/
structure NormalRelationLift (k S : Type) [CommRing k] [CommRing S] [Algebra k S]
    {ι : Type} (x : ι → S) (relations : Finset (MvPolynomial ι k)) where
  carrier : Type
  [commRing : CommRing carrier]
  [algebra : Algebra k carrier]
  [domain : IsDomain carrier]
  [integrallyClosed : IsIntegrallyClosed carrier]
  specialize : carrier →ₐ[k] S
  generators : ι → carrier
  specialize_generators : ∀ i, specialize (generators i) = x i
  vanishes : ∀ q ∈ relations, MvPolynomial.aeval generators q = 0

/-- The relation-lifting property needed for algebraic descent. -/
def HasNormalRelationLifts (k S : Type) [CommRing k] [CommRing S] [Algebra k S] : Prop :=
  ∀ {ι : Type} [Finite ι] (x : ι → S) (relations : Finset (MvPolynomial ι k)),
    (∀ q ∈ relations, MvPolynomial.aeval x q = 0) → Nonempty (NormalRelationLift k S x relations)

private def monicPolynomial {R : Type} [CommRing R] {n : ℕ} (c : Fin n → R) : R[X] :=
  X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)

private theorem monicPolynomial_monic {R : Type} [CommRing R] [Nontrivial R] {n : ℕ}
    (c : Fin n → R) : (monicPolynomial c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt _)

private theorem map_monicPolynomial {R S : Type} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (c : Fin n → R) :
    (monicPolynomial c).map f = monicPolynomial (f ∘ c) := by
  simp [monicPolynomial, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_pow]

private theorem monicPolynomial_coeff {R : Type} [CommRing R] {p : R[X]} (hp : p.Monic) :
    monicPolynomial (fun i : Fin p.natDegree => p.coeff i) = p := by
  unfold monicPolynomial
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => C (p.coeff i) * X ^ i)]
  exact hp.as_sum.symm

private abbrev Variables (n : ℕ) := Fin n ⊕ Bool

/-- The equation obtained by clearing the denominator in a monic degree `n` equation. -/
private def denominatorRelation (k : Type) [CommRing k] (n : ℕ) : MvPolynomial (Variables n) k :=
  ((monicPolynomial (MvPolynomial.X ∘ Sum.inl)).scaleRoots (MvPolynomial.X (.inr false))).eval
    (MvPolynomial.X (.inr true))

private theorem eval_denominatorRelation {k S : Type} [CommRing k] [Nontrivial k]
    [CommRing S] [Nontrivial S] [Algebra k S] {n : ℕ} (x : Variables n → S) :
    MvPolynomial.aeval x (denominatorRelation k n) =
      ((monicPolynomial (x ∘ Sum.inl)).scaleRoots (x (.inr false))).eval (x (.inr true)) := by
  let f : MvPolynomial (Variables n) k →+* S := (MvPolynomial.aeval x).toRingHom
  let p : (MvPolynomial (Variables n) k)[X] := monicPolynomial (MvPolynomial.X ∘ Sum.inl)
  have hp := monicPolynomial_monic (MvPolynomial.X ∘ (Sum.inl : Fin n → Variables n) :
    Fin n → MvPolynomial (Variables n) k)
  have hlead : f p.leadingCoeff ≠ 0 := by
    rw [show p.leadingCoeff = 1 from hp.leadingCoeff, map_one]
    exact one_ne_zero
  change f ((p.scaleRoots _).eval _) = _
  rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_eq_eval_map, Polynomial.map_scaleRoots _ _ _ hlead]
  simp [p, f, map_monicPolynomial, Function.comp_def]

/-- An algebra admitting simultaneous lifts of its finite relations to normal domains is
integrally closed in its fraction field. -/
theorem isIntegrallyClosed_of_hasNormalRelationLifts {k S : Type} [CommRing k] [Nontrivial k]
    [CommRing S] [IsDomain S] [Algebra k S] (lift : HasNormalRelationLifts k S) :
    IsIntegrallyClosed S := by
  classical
  rw [isIntegrallyClosed_iff (FractionRing S)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  obtain ⟨p, hp, hroot⟩ := hx
  let input : Variables p.natDegree → S := Sum.elim (fun i => p.coeff i) (fun t => if t then a else b)
  let q := denominatorRelation k p.natDegree
  have hq : MvPolynomial.aeval input q = 0 := by
    rw [eval_denominatorRelation]
    have hclear := scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero
      (IsFractionRing.injective S (FractionRing S)) hroot hb
    apply IsFractionRing.injective S (FractionRing S)
    simpa [input, Function.comp_def, monicPolynomial_coeff hp,
      aeval_algebraMap_apply_eq_algebraMap_eval] using hclear
  obtain ⟨data⟩ := lift input {q} (by simpa using hq)
  let B := data.carrier
  letI : CommRing B := data.commRing
  letI : Algebra k B := data.algebra
  letI : IsDomain B := data.domain
  letI : IsIntegrallyClosed B := data.integrallyClosed
  let a' : B := data.generators (.inr true)
  let b' : B := data.generators (.inr false)
  have ha' : data.specialize a' = a := by simpa [a', input] using data.specialize_generators (.inr true)
  have hb' : data.specialize b' = b := by simpa [b', input] using data.specialize_generators (.inr false)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb'0 : b' ≠ 0 := by
    intro h
    exact hb0 (by simpa [h] using hb'.symm)
  let p' := monicPolynomial (data.generators ∘ Sum.inl)
  have hclear : (p'.scaleRoots b').eval a' = 0 := by
    simpa only [q, eval_denominatorRelation, p', b', a'] using data.vanishes q (by simp)
  let K := FractionRing B
  let i : B →+* K := algebraMap B K
  have hi : i b' ≠ 0 := by
    intro h
    exact hb'0 (IsFractionRing.injective B K (h.trans (map_zero i).symm))
  have hscale := scaleRoots_eval₂_mul (p := p') i (i a' / i b') b'
  rw [mul_div_cancel₀ _ hi] at hscale
  have hleft : (p'.scaleRoots b').eval₂ i (i a') = 0 := by
    rw [Polynomial.eval₂_at_apply, hclear, map_zero]
  have hz : aeval (i a' / i b') p' = 0 := by
    rw [aeval_def]
    exact (mul_eq_zero.mp (hscale.symm.trans hleft)).resolve_left (pow_ne_zero _ hi)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (show IsIntegral B (i a' / i b') from ⟨p', monicPolynomial_monic _, hz⟩)
  have hmul : b' * y = a' := by
    apply IsFractionRing.injective B K
    change i (b' * y) = i a'
    rw [map_mul, show i y = _ from hy, mul_div_cancel₀ _ hi]
  have hout := congrArg data.specialize hmul
  rw [map_mul, hb', ha'] at hout
  refine ⟨data.specialize y, ?_⟩
  have hbn : algebraMap S (FractionRing S) b ≠ 0 := by
    intro h
    exact hb0 (IsFractionRing.injective S _ (h.trans (map_zero _).symm))
  apply (eq_div_iff hbn).2
  rw [mul_comm, ← map_mul, hout]

/-- The polynomial-value corollary in Section 5. A nonconstant polynomial over the
coefficient field detects membership in an integrally closed value ring. -/
theorem exists_preimage_of_polynomial_value {k S : Type} [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] [IsIntegrallyClosed S] (p : k[X]) (hp : 0 < p.natDegree)
    (x : FractionRing S) (y : S)
    (hy : p.eval₂ ((algebraMap S (FractionRing S)).comp (algebraMap k S)) x =
      algebraMap S (FractionRing S) y) :
    ∃ a : S, algebraMap S (FractionRing S) a = x := by
  let f := algebraMap k S
  let g := algebraMap S (FractionRing S)
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hp
  have hdeg : degree (C y) < degree (p.map f) := by
    rw [degree_map_eq_of_injective f.injective, degree_eq_natDegree hp0]
    exact lt_of_le_of_lt degree_C_le (WithBot.coe_lt_coe.mpr hp)
  let q := p.map f - C y
  have hlead : q.leadingCoeff = f p.leadingCoeff := by
    rw [show q = p.map f - C y from rfl, leadingCoeff_sub_of_degree_lt hdeg,
      leadingCoeff_map' f.injective]
  have hunit : f (p.leadingCoeff⁻¹) * q.leadingCoeff = 1 := by
    rw [hlead, ← map_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hp0), map_one]
  have hq : q.eval₂ g x = 0 := by
    change (p.map f - C y).eval₂ g x = 0
    rw [eval₂_sub, eval₂_map, eval₂_C, show p.eval₂ (g.comp f) x = g y from hy, sub_self]
  exact IsIntegrallyClosed.isIntegral_iff.mp
    ⟨C (f (p.leadingCoeff⁻¹)) * q, monic_C_mul_of_mul_leadingCoeff_eq_one hunit, by
      rw [eval₂_mul, hq, mul_zero]⟩

end WideEIntegralClosed
