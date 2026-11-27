import WideEIntegralClosed.AlgebraicDescent
import Mathlib.RingTheory.FinitePresentation

/-! Factoring maps from finitely presented algebras through normal domains. -/

noncomputable section

namespace WideEIntegralClosed

variable {k A S : Type} [CommRing k] [CommRing A] [CommRing S] [Algebra k A] [Algebra k S]

/-- A factorization of an algebra map through an integrally closed domain. -/
structure NormalFactorization (φ : A →ₐ[k] S) where
  carrier : Type
  [commRing : CommRing carrier]
  [algebra : Algebra k carrier]
  [domain : IsDomain carrier]
  [integrallyClosed : IsIntegrallyClosed carrier]
  lift : A →ₐ[k] carrier
  specialize : carrier →ₐ[k] S
  commutes : specialize.comp lift = φ

/-- Simultaneous lifts of finite relations factor maps from finitely presented algebras. -/
theorem factors_of_hasNormalRelationLifts [Algebra.FinitePresentation k A]
    (h : HasNormalRelationLifts k S) (φ : A →ₐ[k] S) : Nonempty (NormalFactorization φ) := by
  classical
  obtain ⟨ι, hι, q, onto, hfg⟩ := Algebra.FinitePresentation.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FinitePresentation k A)
  letI := hι
  obtain ⟨relations, hrelations⟩ := hfg
  let x (i : ι) := φ (q (MvPolynomial.X i))
  have eval_eq : MvPolynomial.aeval x = φ.comp q := MvPolynomial.algHom_ext (by simp [x])
  have hx : ∀ r ∈ relations, MvPolynomial.aeval x r = 0 := by
    intro r hr
    have hr' : r ∈ RingHom.ker q.toRingHom :=
      hrelations ▸ Ideal.subset_span hr
    have hzero : q r = 0 := hr'
    simp [eval_eq, hzero]
  obtain ⟨data⟩ := h x relations hx
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
    exact Ideal.span_le.mpr fun r hr => data.vanishes r hr
  let e := Ideal.quotientKerAlgEquivOfSurjective onto
  let f : A →ₐ[k] B := (Ideal.Quotient.liftₐ I eval hker).comp e.symm.toAlgHom
  have hf (r : MvPolynomial ι k) : f (q r) = eval r := by
    change Ideal.Quotient.liftₐ I eval hker (e.symm (e (Ideal.Quotient.mk I r))) = eval r
    rw [AlgEquiv.symm_apply_apply]
    rfl
  refine ⟨⟨B, f, data.specialize, ?_⟩⟩
  ext a
  obtain ⟨r, rfl⟩ := onto a
  have heval : data.specialize.comp eval = φ.comp q := by
    rw [← eval_eq]
    apply MvPolynomial.algHom_ext
    intro i
    calc
      (data.specialize.comp eval) (MvPolynomial.X i) = data.specialize (data.generators i) :=
        congrArg data.specialize (MvPolynomial.aeval_X data.generators i)
      _ = x i := data.specialize_generators i
      _ = MvPolynomial.aeval x (MvPolynomial.X i) := (MvPolynomial.aeval_X x i).symm
  change data.specialize (f (q r)) = φ (q r)
  rw [hf]
  exact DFunLike.congr_fun heval r

end WideEIntegralClosed
