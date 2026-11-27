import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-! A finite normalization agrees with the original domain on a nonempty principal open. -/

noncomputable section

open scoped nonZeroDivisors

namespace WideEIntegralClosed

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- One nonzero denominator suffices for the normalization when it is finite as a module. -/
theorem exists_normalization_denominator [Module.Finite A (integralClosure A K)] :
    ∃ d : A, d ≠ 0 ∧ ∀ x : K, IsIntegral A x →
      ∃ a : A, algebraMap A K a = algebraMap A K d * x := by
  classical
  let C := integralClosure A K
  have finiteC : Module.Finite A C := ‹Module.Finite A (integralClosure A K)›
  obtain ⟨⟨s, hs⟩⟩ := finiteC
  let values : Finset K := s.image Subtype.val
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset A⁰ values
  refine ⟨(d : A), nonZeroDivisors.ne_zero d.property, ?_⟩
  let multiply : C →ₗ[A] K := (d : A) • C.val.toLinearMap
  let image : Submodule A K := LinearMap.range (Algebra.linearMap A K)
  have hspan : (⊤ : Submodule A C) ≤ image.comap multiply := by
    rw [← hs, Submodule.span_le]
    intro c hc
    exact hd c.val (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  intro x hx
  have hmem : (⟨x, hx⟩ : C) ∈ image.comap multiply := hspan (Submodule.mem_top : _ ∈ ⊤)
  change ∃ a, (Algebra.linearMap A K) a = multiply ⟨x, hx⟩ at hmem
  simpa [multiply, Algebra.smul_def] using hmem

omit [IsDomain A] [IsFractionRing A K] in
/-- Inverting a common denominator for the normalization yields an integrally closed ring. -/
theorem isIntegrallyClosed_of_normalization_denominator {L : Type*} [CommRing L]
    [Algebra A L] [Algebra L K] [IsScalarTower A L K] [IsFractionRing L K] (M : Submonoid A)
    [IsLocalization M L] (d : M)
    (hd : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = algebraMap A K (d : A) * x) :
    IsIntegrallyClosed L := by
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M x hx
  obtain ⟨a, ha⟩ := hd _ hm
  let s : M := d * m
  refine ⟨IsLocalization.mk' L a s, ?_⟩
  have hunit : IsUnit (algebraMap A K (s : A)) := by
    rw [IsScalarTower.algebraMap_apply A L K]
    exact (IsLocalization.map_units L s).map (algebraMap L K)
  apply mul_right_cancel₀ hunit.ne_zero
  rw [IsScalarTower.algebraMap_apply A L K, ← map_mul, IsLocalization.mk'_spec,
    ← IsScalarTower.algebraMap_apply A L K, ha, Submonoid.smul_def, Algebra.smul_def]
  rw [show (s : A) = (d : A) * (m : A) from rfl]
  simp only [map_mul, ← IsScalarTower.algebraMap_apply A L K]
  ring

omit [IsDomain A] in
private theorem finite_normalization_of_finite {P : Type*} [CommRing P] [IsDomain P]
    [IsNoetherianRing P] [IsIntegrallyClosed P] [CharZero P]
    [Algebra P A] [Algebra P K] [IsScalarTower P A K] [FaithfulSMul P K] [Module.Finite P A] :
    Module.Finite A (integralClosure A K) := by
  classical
  let Q := FractionRing P
  letI : Algebra Q K := FractionRing.liftAlgebra P K
  letI : IsScalarTower P Q K := FractionRing.isScalarTower_liftAlgebra P K
  obtain ⟨⟨s, hs⟩⟩ := (inferInstance : Module.Finite P A)
  let t : Finset K := s.image (algebraMap A K)
  let D : IntermediateField Q K := IntermediateField.adjoin Q (t : Set K)
  letI : FiniteDimensional Q D := IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact (Algebra.IsIntegral.isIntegral (R := P) a).algebraMap.tower_top
  let f : A →ₗ[P] K := (IsScalarTower.toAlgHom P A K).toLinearMap
  let V : Submodule P K := D.toSubalgebra.toSubmodule.restrictScalars P
  have hV : (⊤ : Submodule P A) ≤ V.comap f := by
    rw [← hs, Submodule.span_le]
    intro a ha
    change algebraMap A K a ∈ D
    exact IntermediateField.subset_adjoin Q (t : Set K) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  have hall (a : A) : algebraMap A K a ∈ D := hV (Submodule.mem_top : a ∈ ⊤)
  have hsurj : Function.Surjective D.val := by
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    exact ⟨⟨_, D.div_mem (hall a) (hall b)⟩, rfl⟩
  letI : FiniteDimensional Q K := FiniteDimensional.of_surjective D.val.toLinearMap hsurj
  let C := integralClosure A K
  letI : Algebra P C := ((algebraMap A C).comp (algebraMap P A)).toAlgebra
  letI : IsScalarTower P A C := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower P C K := IsScalarTower.of_algebraMap_eq fun p => by
    change algebraMap P K p = algebraMap A K (algebraMap P A p)
    exact IsScalarTower.algebraMap_apply P A K p
  letI : IsIntegralClosure C P K := {
    algebraMap_injective' := Subtype.val_injective
    isIntegral_iff := by
      intro x
      constructor
      · intro hx
        exact ⟨⟨x, hx.tower_top⟩, rfl⟩
      · rintro ⟨⟨x, hx⟩, rfl⟩
        exact isIntegral_trans x hx }
  letI : Module.Finite P C := IsIntegralClosure.finite P Q K C
  exact Module.Finite.of_restrictScalars_finite P A C

/-- The normalization of a finite-type domain over a characteristic-zero field is finite. -/
theorem finite_normalization_of_finiteType (k : Type*) [Field k] [CharZero k] [Algebra k A]
    [Algebra.FiniteType k A] : Module.Finite A (integralClosure A K) := by
  obtain ⟨n, f, hinj, hfinite⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  letI : CharZero P := charZero_of_injective_ringHom
    (MvPolynomial.C_injective (Fin n) k)
  letI : GCDMonoid P := UniqueFactorizationMonoid.toGCDMonoid P
  letI : IsIntegrallyClosed P := GCDMonoid.toIsIntegrallyClosed
  letI : Algebra P A := f.toRingHom.toAlgebra
  letI : Algebra P K := ((algebraMap A K).comp f.toRingHom).toAlgebra
  letI : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq' rfl
  letI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr
    ((IsFractionRing.injective A K).comp hinj)
  letI : Module.Finite P A := hfinite
  exact finite_normalization_of_finite (P := P)

omit [IsDomain A] in
/-- If translates of a common normalization denominator avoid every maximal ideal, each
integral fraction has denominator ideal equal to the unit ideal. -/
theorem isIntegrallyClosed_of_normalization_denominator_translates (d : A)
    (hd : ∀ x : K, IsIntegral A x → ∃ a : A, algebraMap A K a = algebraMap A K d * x)
    (hcover : ∀ m : Ideal A, m.IsMaximal → ∃ e : A ≃+* A, e d ∉ m) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff K]
  intro x hx
  let multiply : A →ₗ[A] K :=
    { toFun := fun a => algebraMap A K a * x
      map_add' := fun a b => by rw [map_add, add_mul]
      map_smul' := fun a b => by simp [Algebra.smul_def, mul_assoc] }
  let I : Ideal A := (LinearMap.range (Algebra.linearMap A K)).comap multiply
  have htranslate (e : A ≃+* A) : e d ∈ I := by
    let E : K ≃+* K := IsFractionRing.ringEquivOfRingEquiv e
    have hcomp : (algebraMap A K).comp e.symm.toRingHom =
        E.symm.toRingHom.comp (algebraMap A K) := by
      ext a
      change algebraMap A K (e.symm a) = E.symm (algebraMap A K a)
      rw [show E.symm = IsFractionRing.ringEquivOfRingEquiv e.symm from rfl,
        IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    have hx' : IsIntegral A (E.symm x) :=
      IsIntegral.map_of_comp_eq e.symm.toRingHom E.symm.toRingHom hcomp hx
    obtain ⟨a, ha⟩ := hd (E.symm x) hx'
    use e a
    change algebraMap A K (e a) = algebraMap A K (e d) * x
    simpa only [map_mul, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      RingEquiv.apply_symm_apply, E] using congrArg E ha
  have hI : I = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hmI⟩ := Ideal.exists_le_maximal I h
    obtain ⟨e, he⟩ := hcover m hm
    exact he (hmI (htranslate e))
  have h : (1 : A) ∈ I := hI.symm ▸ Submodule.mem_top
  change ∃ a, algebraMap A K a = algebraMap A K 1 * x at h
  simpa only [map_one, one_mul] using h

end WideEIntegralClosed
