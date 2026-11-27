import WideEIntegralClosed.Normalization
import WideEIntegralClosed.Fiber
import WideE.HopfConnectedDomain
import Mathlib.RingTheory.Localization.InvSubmonoid

/-! Normality of affine algebraic groups with integral coordinate rings. -/

noncomputable section

open scoped nonZeroDivisors
open StrictEUnit WideE

namespace WideEIntegralClosed

section IntegralHopf

variable {k H : Type*} [Field k] [IsAlgClosed k] [CommRing H] [IsDomain H]

private theorem exists_algebraic_point_not_vanish [Algebra k H] [Algebra.FiniteType k H]
    (d : H) (hd : d ≠ 0) :
    ∃ r : H →ₐ[k] k, r d ≠ 0 := by
  let T := Localization.Away d
  have hpowers : Submonoid.powers d ≤ H⁰ := by
    rintro _ ⟨n, rfl⟩
    exact pow_mem (mem_nonZeroDivisors_iff_ne_zero.mpr hd) n
  letI : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors H (S := T) hpowers
  letI : Algebra.FiniteType H T := IsLocalization.finiteType_of_monoid_fg
    (Submonoid.powers d) T
  letI : Algebra.FiniteType k T :=
    (inferInstance : Algebra.FiniteType k H).trans (inferInstance : Algebra.FiniteType H T)
  obtain ⟨r⟩ := nonempty_algebraic_point (k := k) (S := T)
  refine ⟨r.comp (IsScalarTower.toAlgHom k H T), ?_⟩
  change r (algebraMap H T d) ≠ 0
  exact ((IsLocalization.map_units T ⟨d, Submonoid.mem_powers d⟩).map r).ne_zero

/-- The coordinate ring of an integral affine algebraic group over an algebraically closed
field of characteristic zero is integrally closed in its fraction field. -/
theorem hopf_isIntegrallyClosed [CharZero k] [HopfAlgebra k H] [Algebra.FiniteType k H] :
    IsIntegrallyClosed H := by
  let K := FractionRing H
  letI : Module.Finite H (integralClosure H K) := finite_normalization_of_finiteType k
  obtain ⟨d, hd, hclear⟩ := exists_normalization_denominator (A := H) (K := K)
  obtain ⟨r, hr⟩ := exists_algebraic_point_not_vanish (k := k) d hd
  apply isIntegrallyClosed_of_normalization_denominator_translates d hclear
  intro m hm
  letI := hm
  let p := maximalIdealPoint (k := k) m
  let e : H ≃ₐ[k] H := (hopfTranslation r).trans (hopfTranslation p).symm
  refine ⟨e.toRingEquiv, ?_⟩
  rw [← maximalIdealPoint_ker (k := k) m, RingHom.mem_ker]
  change p ((hopfTranslation p).symm (hopfTranslation r d)) ≠ 0
  rw [← hopfTranslation_counit p ((hopfTranslation p).symm (hopfTranslation r d)),
    AlgEquiv.apply_symm_apply, hopfTranslation_counit]
  exact hr

end IntegralHopf

private theorem isIntegrallyClosed_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [IsIntegrallyClosed B] (e : A ≃+* B) : IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  let E : FractionRing A ≃+* FractionRing B := IsFractionRing.ringEquivOfRingEquiv e
  have hcomp : (algebraMap B (FractionRing B)).comp e.toRingHom =
      E.toRingHom.comp (algebraMap A (FractionRing A)) := by
    ext a
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap e a).symm
  have hi : IsIntegral B (E x) := IsIntegral.map_of_comp_eq e.toRingHom E.toRingHom hcomp hx
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  use e.symm b
  apply E.injective
  rw [show E = IsFractionRing.ringEquivOfRingEquiv e from rfl,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap, e.apply_symm_apply]
  exact hb

section Components

open Set TopologicalSpace

universe u

variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] (P : ComponentHopfPresentation k H)

omit [IsAlgClosed k] [Algebra.FiniteType k H] in
private theorem basicOpen_eq_connectedComponent_of_point (i : P.Index) (p : H →ₐ[k] k)
    (hp : p (P.idempotent i) = 1) :
    (PrimeSpectrum.basicOpen (P.idempotent i) : Set (PrimeSpectrum H)) =
      connectedComponent (hopfPointPrime p) := by
  letI := P.index_finite
  letI := P.connected i
  let e := P.idempotent i
  have he : IsIdempotentElem e := P.complete.idem i
  have hx : hopfPointPrime p ∈ PrimeSpectrum.basicOpen e := by
    change ¬p e = 0
    rw [hp]
    exact one_ne_zero
  have hc : IsPreconnected (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum H)) := by
    rw [← quotientComponent_range H he]
    exact isPreconnected_range
      (PrimeSpectrum.comap (algebraMap H (QuotientComponent H e))).continuous
  have hclopen : IsClopen (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum H)) :=
    PrimeSpectrum.isClopen_basicOpen_of_mul_add e (1 - e)
      (by rw [mul_sub, mul_one, he.eq, sub_self]) (by ring)
  exact (hc.subset_connectedComponent hx).antisymm (hclopen.connectedComponent_subset hx)

private theorem component_exists_point (i : P.Index) :
    ∃ p : H →ₐ[k] k, p (P.idempotent i) = 1 := by
  letI := P.index_finite
  letI := P.connected i
  let e := P.idempotent i
  let I : Ideal H := Ideal.span {1 - e}
  let C := QuotientComponent H e
  letI : Nontrivial C := by
    let x : PrimeSpectrum C := Classical.choice (inferInstance : Nonempty (PrimeSpectrum C))
    exact nontrivial_of_ne 0 1 fun h => x.isPrime.ne_top
      ((Ideal.eq_top_iff_one _).mpr (h ▸ x.asIdeal.zero_mem))
  letI : Algebra.FiniteType k C :=
    (inferInstance : Algebra.FiniteType k H).of_surjective (Ideal.Quotient.mkₐ k I)
      Ideal.Quotient.mk_surjective
  obtain ⟨p⟩ := nonempty_algebraic_point (k := k) (S := C)
  refine ⟨p.comp (Ideal.Quotient.mkₐ k I), ?_⟩
  have hzero : (Ideal.Quotient.mkₐ k I) (1 - e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton (1 - e)))
  have h := congrArg p hzero
  simp only [map_sub, map_one, map_zero] at h
  exact (sub_eq_zero.mp h).symm

/-- Translation identifies every connected component of the group with the identity component. -/
theorem nonempty_componentEquivIdentity (i : P.Index) :
    Nonempty (QuotientComponent H (P.idempotent i) ≃ₐ[k] P.IdentityComponent) := by
  letI := P.index_finite
  obtain ⟨p, hp⟩ := component_exists_point P i
  let ε := Bialgebra.counitAlgHom k H
  let e := hopfTranslation p
  let T := (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm
  have hT : T (hopfPointPrime ε) = hopfPointPrime p := by
    apply PrimeSpectrum.ext
    ext a
    change ε (e a) = 0 ↔ p a = 0
    rw [hopfTranslation_counit]
  have he : e (P.idempotent i) = P.idempotent P.identityIndex := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem ((P.complete.idem i).map e)
      (P.complete.idem P.identityIndex)
    apply SetLike.ext
    intro x
    change T x ∈ (PrimeSpectrum.basicOpen (P.idempotent i) : Set (PrimeSpectrum H)) ↔
      x ∈ (PrimeSpectrum.basicOpen (P.idempotent P.identityIndex) : Set (PrimeSpectrum H))
    rw [basicOpen_eq_connectedComponent_of_point P i p hp,
      basicOpen_eq_connectedComponent_of_point P P.identityIndex ε P.identityIndex_counit]
    constructor
    · intro hx
      have hi := T.symm.continuous.image_connectedComponent_subset (hopfPointPrime p)
        (show x ∈ T.symm '' connectedComponent (hopfPointPrime p) from
          ⟨T x, hx, T.symm_apply_apply x⟩)
      simpa only [← hT, T.symm_apply_apply] using hi
    · intro hx
      rw [← hT]
      exact T.continuous.image_connectedComponent_subset (hopfPointPrime ε) ⟨x, hx, rfl⟩
  refine ⟨Ideal.quotientEquivAlg _ _ e ?_⟩
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {1 - P.idempotent P.identityIndex} =
    Ideal.span {e (1 - P.idempotent i)}
  rw [map_sub, map_one, he]

/-- All component quotients of a reduced affine algebraic group are normal domains. -/
theorem component_isDomain_and_isIntegrallyClosed [CharZero k] [IsReduced H] (i : P.Index) :
    IsDomain (QuotientComponent H (P.idempotent i)) ∧
      IsIntegrallyClosed (QuotientComponent H (P.idempotent i)) := by
  letI := P.identityHopf
  letI : Algebra.FiniteType k P.IdentityComponent := P.identityComponent_finiteType
  letI : IsDomain P.IdentityComponent := P.identityComponent_isDomain
  letI : IsIntegrallyClosed P.IdentityComponent := hopf_isIntegrallyClosed (k := k)
  obtain ⟨e⟩ := nonempty_componentEquivIdentity P i
  letI : IsDomain (QuotientComponent H (P.idempotent i)) :=
    Equiv.isDomain e.toRingEquiv
  exact ⟨inferInstance, isIntegrallyClosed_of_ringEquiv e.toRingEquiv⟩

end Components

/-- A fiber identified with an affine Hopf algebra admits specialization through a normal
component. The fiber map is required to kill the specialization parameter. -/
theorem normalSpecialization_of_hopfFiberMap {k A S H ι : Type} [Field k] [CharZero k]
    [IsAlgClosed k] [CommRing A] [Algebra k A] [CommRing S] [IsDomain S] [Algebra k S]
    [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
    (functions : Subalgebra k A) (parameter : A) (hparameter : parameter ∈ functions)
    (f : ι → A) (hf : ∀ i, f i ∈ functions) (x : ι → S)
    (toFiber : functions →ₐ[k] H) (eval : H →ₐ[k] S)
    (hzero : toFiber ⟨parameter, hparameter⟩ = 0)
    (heval : ∀ i, eval (toFiber ⟨f i, hf i⟩) = x i)
    (inversion : H →ₐ[k] H) (hinversion : inversion.toLinearMap = HopfAlgebra.antipode (R := k)) :
    Nonempty (NormalSpecialization (k := k) parameter f x) := by
  obtain ⟨P⟩ := nonempty_componentHopfPresentation inversion hinversion
  letI := P.index_finite
  exact normalSpecialization_of_fiberMap functions parameter hparameter f hf x toFiber eval
    hzero heval P.idempotent P.complete
    (fun i => (component_isDomain_and_isIntegrallyClosed P i).1)
    (fun i => (component_isDomain_and_isIntegrallyClosed P i).2)

end WideEIntegralClosed
