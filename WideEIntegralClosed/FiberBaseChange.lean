import Mathlib.RingTheory.TensorProduct.Quotient

/-! The principal-ideal quotient and tensor-product descriptions of the same fiber. -/

noncomputable section

open scoped TensorProduct

namespace WideEIntegralClosed

variable {k R A : Type} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Algebra R A] [IsScalarTower k R A]
  [Algebra R k] [IsScalarTower k R k]

/-- Quotienting by the extended ideal of a base point is the same as base change. -/
def quotientFiberEquiv (I : Ideal R) (residue : (R ⧸ I) ≃ₐ[R] k) :
    (A ⧸ I.map (algebraMap R A)) ≃ₐ[k] (k ⊗[R] A) := by
  let quotientToTensor := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).restrictScalars k
  let changeResidue := Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A)) residue
  exact quotientToTensor.trans ((changeResidue.trans (Algebra.TensorProduct.comm R A k)).restrictScalars k)

end WideEIntegralClosed
