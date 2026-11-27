import WideEIntegralClosed.ValueSpecialization
import WideE.Taylor
import Stage17RamifiedLaurentCoefficients

/-! Algebraic Taylor realization for the broad function algebra, including ramification. -/

noncomputable section

namespace WideEIntegralClosed

open StrictEUnit

local notation "k" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)

private def entireRepresentative (f : wideFunctions) : subfieldEntireFunctionAlgebra k :=
  ⟨⟨f.val, WideE.IsWideEFunction.differentiable f.property⟩,
    (mem_subfieldEntireFunctionAlgebra _ _).mpr fun n => by
      obtain ⟨a, hf, hs, _⟩ := f.property
      exact hs.algebraic_coefficient hf n⟩

/-- Realization of a broad E-function as an entire function with algebraic Taylor coefficients. -/
def arithmeticRealization : wideFunctions →ₐ[k] subfieldEntireFunctionAlgebra k where
  toFun := entireRepresentative
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)
  commutes' _ := Subtype.ext (Subtype.ext rfl)

@[simp]
theorem arithmeticRealization_apply (f : wideFunctions) (z : ℂ) :
    (arithmeticRealization f).val.val z = f.val z := rfl

/-- The Taylor realization after the substitution `z = t^N`. -/
def ramifiedRealization (N : ℕ) (hN : N ≠ 0) : wideFunctions →ₐ[k] RatFunc (LaurentSeries k) :=
  (stage17_ramifiedEntireFormalAlgHom k N hN).comp arithmeticRealization

/-- The function `z - 1` maps to the corresponding Laurent expression in the ramified base. -/
theorem ramifiedRealization_parameter (N : ℕ) (hN : N ≠ 0) :
    ramifiedRealization N hN wideParameter =
      stage17_laurentAmbientPullback k N (LaurentPolynomial.T 1 - 1) := by
  let coordinate : wideFunctions := ⟨fun z => z, WideE.isWideEFunction_coordinate⟩
  have hparameter : wideParameter = coordinate - 1 := Subtype.ext rfl
  rw [hparameter, map_sub, map_one, map_sub, map_one,
    stage17_laurentAmbientPullback_coordinate k N hN]
  rfl

end WideEIntegralClosed
