import WideE.Values
import WideEIntegralClosed.Specialization

/-! The algebra and evaluation of actual broad Siegel E-functions. -/

noncomputable section

namespace WideEIntegralClosed

open WideE

local notation "k" => WideE.AlgebraicComplex

/-- Broad Siegel E-functions, with the algebraic complex numbers as scalars. -/
def wideFunctions : Subalgebra k (ℂ → ℂ) where
  carrier := { f | IsWideEFunction f }
  add_mem' := fun hf hg => IsWideEFunction.add hf hg
  mul_mem' := fun hf hg => IsWideEFunction.mul hf hg
  algebraMap_mem' a := isWideEFunction_const a

/-- The algebraic numbers are values of constant broad E-functions. -/
def valueConstants : k →+* valueSubring where
  toFun a := ⟨(a : ℂ), algebraic_isWideEValue a⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

instance : Algebra k valueSubring := valueConstants.toAlgebra

/-- Evaluation at one with the codomain restricted to the existing value ring. -/
def evaluateAtOne : wideFunctions →ₐ[k] valueSubring where
  toFun f := ⟨f.val 1, ⟨f.val, f.property, rfl⟩⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

theorem evaluateAtOne_surjective : Function.Surjective evaluateAtOne := by
  intro x
  obtain ⟨f, hf, hx⟩ := x.property
  exact ⟨⟨f, hf⟩, Subtype.ext hx⟩

/-- The ordinary fiber parameter as an element of the broad function algebra. -/
def wideParameter : wideFunctions :=
  ⟨fun z => z - 1, isWideEFunction_coordinate.sub (isWideEFunction_const 1)⟩

/-- Division at a vanishing value, in the form provided by `WideE.wideEFunction_divAtOne`. -/
def HasWideDivisionAtOne : Prop :=
  ∀ f : ℂ → ℂ, IsWideEFunction f → f 1 = 0 →
    ∃ g : ℂ → ℂ, IsWideEFunction g ∧ ∀ z, (z - 1) * g z = f z

theorem divideAtOneInFunctionAlgebra (division : HasWideDivisionAtOne)
    (f : wideFunctions) (h : evaluateAtOne f = 0) :
    ∃ g : wideFunctions, wideParameter * g = f := by
  have hzero : f.val 1 = 0 := congrArg Subtype.val h
  obtain ⟨g, hg, heq⟩ := division f.val f.property hzero
  exact ⟨⟨g, hg⟩, Subtype.ext (funext heq)⟩

/-- A common specialization can use a ramification specific to the finite family. -/
def HasRealizedWideSpecializations : Prop :=
  ∀ {ι : Type} [Finite ι] (f : ι → wideFunctions),
    Nonempty (RealizedNormalSpecialization evaluateAtOne wideParameter f)

theorem isIntegrallyClosed_valueSubring_of_realizedSpecializations
    (division : HasWideDivisionAtOne) (h : HasRealizedWideSpecializations) :
    IsIntegrallyClosed valueSubring :=
  isIntegrallyClosed_of_hasNormalRelationLifts
    (hasNormalRelationLifts_of_realizedSpecializations evaluateAtOne wideParameter
      evaluateAtOne_surjective (divideAtOneInFunctionAlgebra division) h)

end WideEIntegralClosed
