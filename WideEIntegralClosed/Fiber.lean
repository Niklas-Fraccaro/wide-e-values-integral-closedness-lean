import WideEIntegralClosed.Components
import WideEIntegralClosed.Specialization

/-! Factoring function evaluation through the selected normal component of the fiber. -/

noncomputable section

namespace WideEIntegralClosed

variable {k A S : Type} [CommRing k] [CommRing A] [Algebra k A]
  [CommRing S] [Algebra k S]

/-- Evaluation on the quotient by the fiber parameter. -/
def fiberEvaluation (eval : A →ₐ[k] S) (t : A) (ht : eval t = 0) :
    (A ⧸ Ideal.span {t}) →ₐ[k] S :=
  Ideal.Quotient.liftₐ _ eval (by
    have h : Ideal.span {t} ≤ RingHom.ker eval.toRingHom :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht)
    exact fun _ ha => h ha)

@[simp]
theorem fiberEvaluation_mk (eval : A →ₐ[k] S) (t : A) (ht : eval t = 0) (a : A) :
    fiberEvaluation eval t ht (Ideal.Quotient.mkₐ k _ a) = eval a := by
  simp [fiberEvaluation]

/-- Select the normal component of any algebraic fiber on which the parameter vanishes. -/
theorem normalSpecialization_of_fiberMap [IsDomain S] {ι J B : Type} [Fintype J]
    [CommRing B] [Algebra k B] (functions : Subalgebra k A)
    (parameter : A) (hparameter : parameter ∈ functions) (f : ι → A)
    (hf : ∀ i, f i ∈ functions) (x : ι → S) (toFiber : functions →ₐ[k] B)
    (eval : B →ₐ[k] S) (hzero : toFiber ⟨parameter, hparameter⟩ = 0)
    (heval : ∀ i, eval (toFiber ⟨f i, hf i⟩) = x i)
    (e : J → B) (he : CompleteOrthogonalIdempotents e)
    (hdom : ∀ j, IsDomain (B ⧸ Ideal.span {1 - e j}))
    (hnormal : ∀ j, IsIntegrallyClosed (B ⧸ Ideal.span {1 - e j})) :
    Nonempty (NormalSpecialization (k := k) parameter f x) := by
  obtain ⟨j, hj, _⟩ := existsUnique_component_at_evaluation eval he
  let component := B ⧸ Ideal.span {1 - e j}
  letI : IsDomain component := hdom j
  letI : IsIntegrallyClosed component := hnormal j
  let q : B →ₐ[k] component := Ideal.Quotient.mkₐ k _
  refine ⟨{
    functions := functions
    contains := hf
    parameter_mem := hparameter
    carrier := component
    fiberMap := q.comp toFiber
    eval := componentEvaluation eval (e j) hj
    kills_parameter := ?_
    eval_lift := ?_ }⟩
  · change q (toFiber ⟨parameter, hparameter⟩) = 0
    rw [hzero, map_zero]
  · intro i
    change componentEvaluation eval (e j) hj (q (toFiber ⟨f i, hf i⟩)) = x i
    rw [show q = Ideal.Quotient.mkₐ k _ from rfl, componentEvaluation_mk]
    exact heval i

/-- A common function algebra with a fiber that is a finite product of normal domains
provides the specialization needed for finite relation lifting. -/
theorem normalSpecialization_of_fiber [IsDomain S] {ι J : Type} [Fintype J]
    (functions : Subalgebra k A)
    (parameter : A) (hparameter : parameter ∈ functions) (f : ι → A)
    (hf : ∀ i, f i ∈ functions) (x : ι → S) (eval : functions →ₐ[k] S)
    (hzero : eval ⟨parameter, hparameter⟩ = 0) (heval : ∀ i, eval ⟨f i, hf i⟩ = x i)
    (e : J → (functions ⧸ Ideal.span {(⟨parameter, hparameter⟩ : functions)}))
    (he : CompleteOrthogonalIdempotents e)
    (hdom : ∀ j, IsDomain ((functions ⧸ Ideal.span {(⟨parameter, hparameter⟩ : functions)}) ⧸
      Ideal.span {1 - e j}))
    (hnormal : ∀ j, IsIntegrallyClosed ((functions ⧸ Ideal.span {(⟨parameter, hparameter⟩ : functions)}) ⧸
      Ideal.span {1 - e j})) :
    Nonempty (NormalSpecialization (k := k) parameter f x) := by
  let t : functions := ⟨parameter, hparameter⟩
  let fiber := functions ⧸ Ideal.span {t}
  let evFiber : fiber →ₐ[k] S := fiberEvaluation eval t hzero
  let frameToFiber : functions →ₐ[k] fiber := Ideal.Quotient.mkₐ k _
  refine normalSpecialization_of_fiberMap functions parameter hparameter f hf x frameToFiber
    evFiber ?_ ?_ e he hdom hnormal
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton t))
  · intro i
    exact (fiberEvaluation_mk eval t hzero _).trans (heval i)

end WideEIntegralClosed
