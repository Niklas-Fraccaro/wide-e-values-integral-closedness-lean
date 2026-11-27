import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Specialization to a domain selects a factor of a finite idempotent decomposition. -/

noncomputable section

open scoped BigOperators

namespace WideEIntegralClosed

variable {k A S ι : Type} [CommRing k] [CommRing A] [Algebra k A]
  [CommRing S] [Algebra k S] [Fintype ι]

/-- Exactly one component idempotent specializes to one under an algebra map to a domain. -/
theorem existsUnique_component_at_evaluation [IsDomain S] (eval : A →ₐ[k] S) {e : ι → A}
    (he : CompleteOrthogonalIdempotents e) : ∃! i, eval (e i) = 1 := by
  classical
  have hsum : ∑ i, eval (e i) = 1 := by rw [← map_sum, he.complete, map_one]
  have hnonzero : ∃ i, eval (e i) ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  obtain ⟨i, hi⟩ := hnonzero
  have hmul : eval (e i) * eval (e i) = eval (e i) := by
    rw [← map_mul]
    exact congrArg eval (he.idem i).eq
  have hmul' : eval (e i) * (eval (e i) - 1) = 0 := by
    rw [mul_sub, mul_one, hmul, sub_self]
  have hi1 : eval (e i) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hmul').resolve_left hi)
  refine ⟨i, hi1, ?_⟩
  intro j hj
  by_contra hji
  have hz : eval (e j) * eval (e i) = 0 := by rw [← map_mul, he.ortho hji, map_zero]
  simp [hj, hi1] at hz

/-- The evaluation factors through the component quotient selected by its idempotent. -/
def componentEvaluation (eval : A →ₐ[k] S) (e : A) (h : eval e = 1) :
    (A ⧸ Ideal.span {1 - e}) →ₐ[k] S :=
  Ideal.Quotient.liftₐ _ eval (by
    have hle : Ideal.span {1 - e} ≤ RingHom.ker eval.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ (rfl : _ = _)
      change eval (1 - e) = 0
      rw [map_sub, map_one, h, sub_self]
    exact fun _ ha => hle ha)

@[simp]
theorem componentEvaluation_mk (eval : A →ₐ[k] S) (e : A) (h : eval e = 1) (a : A) :
    componentEvaluation eval e h (Ideal.Quotient.mkₐ k _ a) = eval a := by
  simp [componentEvaluation]

end WideEIntegralClosed
