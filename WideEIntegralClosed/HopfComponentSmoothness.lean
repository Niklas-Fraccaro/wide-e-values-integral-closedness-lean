import WideEIntegralClosed.HopfNormality
import WideEIntegralClosed.Factorization
import WideE.HopfSmoothLocus

/-! Smoothness and finite type for the Hopf components used in specialization. -/

namespace WideEIntegralClosed

open WideE

variable {k H : Type} [Field k] [CharZero k] [IsAlgClosed k] [CommRing H]
  [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
  (P : ComponentHopfPresentation k H)

/-- Each component is a smooth algebra of finite type over the coefficient field. -/
theorem hopfComponent_finiteType_and_smooth (i : P.Index) :
    Algebra.FiniteType k (QuotientComponent H (P.idempotent i)) ∧
      Algebra.Smooth k (QuotientComponent H (P.idempotent i)) := by
  letI := P.index_finite
  letI : Algebra.Smooth k H := hopfSmooth_of_isReduced
  exact ⟨Algebra.FiniteType.of_surjective inferInstance
    (Ideal.Quotient.mkₐ k (Ideal.span {1 - P.idempotent i})) Ideal.Quotient.mk_surjective,
    smooth_quotient_idempotent (P.complete.idem i)⟩

/-- Evaluation in a domain selects a unique smooth, normal component of finite type. -/
theorem existsUnique_smooth_normal_hopfComponent_at_evaluation {S : Type}
    [CommRing S] [IsDomain S] [Algebra k S] (eval : H →ₐ[k] S) :
    ∃! i : P.Index, eval (P.idempotent i) = 1 ∧
      Algebra.FiniteType k (QuotientComponent H (P.idempotent i)) ∧
      Algebra.Smooth k (QuotientComponent H (P.idempotent i)) ∧
      IsDomain (QuotientComponent H (P.idempotent i)) ∧
      IsIntegrallyClosed (QuotientComponent H (P.idempotent i)) := by
  letI := P.index_finite
  obtain ⟨i, hi, hUnique⟩ := existsUnique_component_at_evaluation
    (k := k) (A := H) (S := S) (ι := P.Index) (e := P.idempotent) eval P.complete
  obtain ⟨hFinite, hSmooth⟩ := hopfComponent_finiteType_and_smooth P i
  exact ⟨i, ⟨hi, hFinite, hSmooth, component_isDomain_and_isIntegrallyClosed P i⟩,
    fun j hj => hUnique j hj.1⟩

/-- A specialization whose selected carrier is also smooth and of finite type. -/
structure SmoothNormalSpecialization {k A S ι : Type} [CommRing k] [CommRing A] [Algebra k A]
    [CommRing S] [Algebra k S] (parameter : A) (f : ι → A) (x : ι → S)
    extends NormalSpecialization (k := k) parameter f x where
  [finiteType : Algebra.FiniteType k carrier]
  [smooth : Algebra.Smooth k carrier]

/-- Specialization through the selected Hopf component retains its smooth finite-type carrier. -/
theorem smoothNormalSpecialization_of_hopfFiberMap {k A S H ι : Type} [Field k] [CharZero k]
    [IsAlgClosed k] [CommRing A] [Algebra k A] [CommRing S] [IsDomain S] [Algebra k S]
    [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
    (functions : Subalgebra k A) (parameter : A) (hparameter : parameter ∈ functions)
    (f : ι → A) (hf : ∀ i, f i ∈ functions) (x : ι → S)
    (toFiber : functions →ₐ[k] H) (eval : H →ₐ[k] S)
    (hzero : toFiber ⟨parameter, hparameter⟩ = 0)
    (heval : ∀ i, eval (toFiber ⟨f i, hf i⟩) = x i)
    (inversion : H →ₐ[k] H) (hinversion : inversion.toLinearMap = HopfAlgebra.antipode (R := k)) :
    Nonempty (SmoothNormalSpecialization (k := k) parameter f x) := by
  obtain ⟨P⟩ := nonempty_componentHopfPresentation inversion hinversion
  obtain ⟨i, ⟨hi, hFinite, hSmooth, hDomain, hNormal⟩, _⟩ :=
    existsUnique_smooth_normal_hopfComponent_at_evaluation P eval
  let C := QuotientComponent H (P.idempotent i)
  letI : IsDomain C := hDomain
  letI : IsIntegrallyClosed C := hNormal
  let q : H →ₐ[k] C := Ideal.Quotient.mkₐ k _
  let data : NormalSpecialization (k := k) parameter f x :=
    { functions := functions
      contains := hf
      parameter_mem := hparameter
      carrier := C
      fiberMap := q.comp toFiber
      eval := componentEvaluation eval (P.idempotent i) hi
      kills_parameter := by
        change q (toFiber ⟨parameter, hparameter⟩) = 0
        rw [hzero, map_zero]
      eval_lift := by
        intro j
        exact (componentEvaluation_mk eval (P.idempotent i) hi _).trans (heval j) }
  exact ⟨{ toNormalSpecialization := data, finiteType := hFinite, smooth := hSmooth }⟩

section Factorization

variable {k W A S : Type} [CommRing k] [CommRing W] [Algebra k W]
  [CommRing A] [Algebra k A] [CommRing S] [Algebra k S]

/-- A smooth normal specialization whose realization can depend on the finite family. -/
structure RealizedSmoothNormalSpecialization {ι : Type} (eval : W →ₐ[k] S)
    (parameter : W) (family : ι → W) where
  ambient : Type
  [commRing : CommRing ambient]
  [algebra : Algebra k ambient]
  realize : W →ₐ[k] ambient
  specialization : SmoothNormalSpecialization (k := k)
    (realize parameter) (realize ∘ family) (eval ∘ family)

/-- Simultaneous lifts with the original smooth finite-type carrier. -/
structure SmoothNormalRelationLift (k S : Type) [CommRing k] [CommRing S] [Algebra k S]
    {ι : Type} (x : ι → S) (relations : Finset (MvPolynomial ι k))
    extends NormalRelationLift k S x relations where
  [finiteType : Algebra.FiniteType k carrier]
  [smooth : Algebra.Smooth k carrier]

/-- Every prescribed finite list of polynomial relations lifts to a smooth normal domain. -/
def HasSmoothNormalRelationLifts (k S : Type) [CommRing k] [CommRing S] [Algebra k S] : Prop :=
  ∀ {ι : Type} [Finite ι] (x : ι → S) (relations : Finset (MvPolynomial ι k)),
    (∀ q ∈ relations, MvPolynomial.aeval x q = 0) →
    Nonempty (SmoothNormalRelationLift k S x relations)

/-- Division at the fiber parameter gives simultaneous lifts in the chosen smooth component. -/
theorem hasSmoothNormalRelationLifts_of_realizedSmoothSpecializations (eval : W →ₐ[k] S)
    (parameter : W) (surj : Function.Surjective eval)
    (divide : ∀ w : W, eval w = 0 → ∃ g : W, parameter * g = w)
    (specialize : ∀ {ι : Type} [Finite ι] (f : ι → W),
      Nonempty (RealizedSmoothNormalSpecialization eval parameter f)) :
    HasSmoothNormalRelationLifts k S := by
  classical
  intro ι _ x relations hx
  choose f hf using fun i => surj (x i)
  have vanishes (q : relations) : eval (MvPolynomial.aeval f q.val) = 0 := by
    rw [MvPolynomial.comp_aeval_apply]
    simpa only [hf] using hx q.val q.property
  choose g hg using fun q => divide (MvPolynomial.aeval f q.val) (vanishes q)
  obtain ⟨R⟩ := specialize (Sum.elim f g)
  letI : CommRing R.ambient := R.commRing
  letI : Algebra k R.ambient := R.algebra
  let data := R.specialization
  let B := data.carrier
  letI : CommRing B := data.commRing
  letI : Algebra k B := data.algebra
  letI : IsDomain B := data.domain
  letI : IsIntegrallyClosed B := data.integrallyClosed
  let included (i : ι ⊕ relations) : data.functions :=
    ⟨R.realize (Sum.elim f g i), data.contains i⟩
  let generators (i : ι) := data.fiberMap (included (.inl i))
  refine ⟨{
    toNormalRelationLift := ⟨B, data.eval, generators, ?_, ?_⟩
    finiteType := data.finiteType
    smooth := data.smooth }⟩
  · intro i
    exact (data.eval_lift (.inl i)).trans (hf i)
  · intro q hq
    let j : relations := ⟨q, hq⟩
    have lifted : MvPolynomial.aeval (fun i => included (.inl i)) q =
        (⟨R.realize parameter, data.parameter_mem⟩ : data.functions) * included (.inr j) := by
      apply Subtype.ext
      change data.functions.val (MvPolynomial.aeval (fun i => included (.inl i)) q) =
        R.realize parameter * R.realize (g j)
      rw [← map_mul, hg j, MvPolynomial.comp_aeval_apply]
      change MvPolynomial.aeval (fun i => R.realize (f i)) q = R.realize (MvPolynomial.aeval f q)
      rw [MvPolynomial.comp_aeval_apply]
    change MvPolynomial.aeval (fun i => data.fiberMap (included (.inl i))) q = 0
    rw [← MvPolynomial.comp_aeval_apply, lifted, map_mul, data.kills_parameter, zero_mul]

/-- A factorization through a smooth normal domain of finite type. -/
structure SmoothNormalFactorization (φ : A →ₐ[k] S) extends NormalFactorization φ where
  [finiteType : Algebra.FiniteType k carrier]
  [smooth : Algebra.Smooth k carrier]

/-- Simultaneous smooth lifts factor a morphism out of a finitely presented algebra. -/
theorem factors_of_hasSmoothNormalRelationLifts [Algebra.FinitePresentation k A]
    (h : HasSmoothNormalRelationLifts k S) (φ : A →ₐ[k] S) :
    Nonempty (SmoothNormalFactorization φ) := by
  classical
  obtain ⟨ι, hι, q, onto, relations, hrelations⟩ := Algebra.FinitePresentation.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FinitePresentation k A)
  letI := hι
  let x (i : ι) := φ (q (MvPolynomial.X i))
  have hx : MvPolynomial.aeval x = φ.comp q := MvPolynomial.algHom_ext (by simp [x])
  obtain ⟨data⟩ := h x relations (by
    intro r hr
    have hker : r ∈ RingHom.ker q.toRingHom := hrelations ▸ Ideal.subset_span hr
    have hz : q r = 0 := hker
    simp [hx, hz])
  let B := data.carrier
  letI : CommRing B := data.commRing
  letI : Algebra k B := data.algebra
  letI : IsDomain B := data.domain
  letI : IsIntegrallyClosed B := data.integrallyClosed
  let eval : MvPolynomial ι k →ₐ[k] B := MvPolynomial.aeval data.generators
  let I := RingHom.ker q.toRingHom
  have hker : I ≤ RingHom.ker eval.toRingHom := by
    change RingHom.ker q.toRingHom ≤ _
    rw [← hrelations]
    exact Ideal.span_le.mpr data.vanishes
  let e := Ideal.quotientKerAlgEquivOfSurjective onto
  let f : A →ₐ[k] B := (Ideal.Quotient.liftₐ I eval hker).comp e.symm.toAlgHom
  have heval : data.specialize.comp eval = φ.comp q := by
    apply MvPolynomial.algHom_ext
    intro i
    change data.specialize (MvPolynomial.aeval data.generators (MvPolynomial.X i)) = x i
    rw [MvPolynomial.aeval_X]
    exact data.specialize_generators i
  refine ⟨{
    toNormalFactorization := ⟨B, f, data.specialize, ?_⟩
    finiteType := data.finiteType
    smooth := data.smooth }⟩
  ext a
  obtain ⟨r, rfl⟩ := onto a
  change data.specialize (Ideal.Quotient.liftₐ I eval hker
    (e.symm (e (Ideal.Quotient.mk I r)))) = φ (q r)
  rw [AlgEquiv.symm_apply_apply]
  exact DFunLike.congr_fun heval r

end Factorization

end WideEIntegralClosed
