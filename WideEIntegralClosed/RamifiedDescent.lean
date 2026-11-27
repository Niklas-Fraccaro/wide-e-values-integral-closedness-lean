import WideEIntegralClosed.ArithmeticRealization
import WideEIntegralClosed.BroadFrobenius
import WideEIntegralClosed.Determinant
import WideEIntegralClosed.PicardVessiotFiber
import LaurentLogBasePointKernel

/-! Descent from actual broad arithmetic frames through ramified Picard–Vessiot fibers. -/

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

open scoped BigOperators Matrix TensorProduct
open StrictEUnit

namespace WideEIntegralClosed

local notation "k" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)
local notation "R" => LaurentLogBase k
local notation "L" => RatFunc (LaurentSeries k)

attribute [local instance] StrictEUnit.formalAmbientBaseAlgebra
attribute [local instance] StrictEUnit.formalAmbientBaseTower
attribute [local instance] StrictEUnit.laurentLogPointAlgebra
attribute [local instance] StrictEUnit.laurentLogPointTower

local instance : Algebra k WideE.valueSubring :=
  (inferInstance : Algebra WideE.AlgebraicComplex WideE.valueSubring)

private def residueEquiv : (R ⧸ laurentLogBasePointIdeal k) ≃ₐ[R] k where
  toRingEquiv := (laurentLogBasePointQuotientEquiv k).toRingEquiv
  commutes' p := laurentLogBasePointQuotientEquiv_mk k p

private theorem parameter_mem_pointIdeal (N : ℕ) :
    stage17_laurentBasePullback k N (LaurentPolynomial.T 1 - 1) ∈ laurentLogBasePointIdeal k := by
  have hone : laurentLogBasePoint k (stage17_laurentBasePullback k N (LaurentPolynomial.T 1)) = 1 := by
    change laurentLogBasePoint k (Polynomial.C
      (LaurentPolynomial.eval₂ LaurentPolynomial.C (stage17_laurentCoordinateUnit k ^ N)
        (LaurentPolynomial.T (1 : ℤ)))) = 1
    rw [laurentLogBasePoint_C, show (1 : ℤ) = (1 : ℕ) by rfl, LaurentPolynomial.eval₂_T_n,
      pow_one, Units.val_pow_eq_pow_val, stage17_laurentCoordinateUnit_val, map_pow,
      laurentEvaluateOne_T, one_pow]
  rw [← laurentLogBasePoint_kernel]
  change laurentLogBasePoint k (stage17_laurentBasePullback k N (LaurentPolynomial.T 1 - 1)) = 0
  simp only [map_sub, map_one, hone, sub_self]

namespace RamifiedFundamental

variable {n : Type} [Fintype n] [DecidableEq n]
  {frame : BroadArithmeticFrame n} {solutions : Matrix n n (subfieldEntireFunctionAlgebra k)}

local instance (F : RamifiedFundamental frame solutions) : CommRing F.candidate :=
  F.candidate.toCommRing

local instance (F : RamifiedFundamental frame solutions) : AddCommGroup F.candidate :=
  F.candidate.toCommRing.toAddCommGroup

private theorem amplitude_inverse_wide : WideE.IsWideEValue
    (frame.amplitudes.map (stage14_subfieldEntireEvaluation k 1)).det⁻¹ := by
  let B := frame.amplitudes.map (subfieldEntireFunctionAlgebra k).val
  have nonzero (z : ℂ) (hz : z ≠ 0) : B.det.val z ≠ 0 := by
    rw [entireMatrix_evaluation_det]
    exact stage23_arithmeticFrame_det_nonzero_off_origin k frame.system frame.residue
      frame.amplitudes frame.frame_equation frame.invertible_at_one z hz
  have h := wideE_at_one_unit_of_origin_only_zeros (wideE_entireMatrix_det B frame.broad) nonzero
  rw [entireMatrix_evaluation_det] at h
  exact h.2.2

private theorem wide_value_of_candidate (F : RamifiedFundamental frame solutions)
    (u : F.candidate) : WideE.IsWideEValue (F.evaluateAtOne u) := by
  let good : Subalgebra R F.candidate := {
    carrier := {a | WideE.IsWideEValue (F.evaluateAtOne a)}
    add_mem' := by
      intro a b ha hb
      change WideE.IsWideEValue (F.evaluateAtOne (a + b))
      rw [show F.evaluateAtOne (a + b) = F.evaluateAtOne a + F.evaluateAtOne b from
        F.evaluateAtOne.map_add' a b]
      exact WideE.IsWideEValue.add ha hb
    mul_mem' := by
      intro a b ha hb
      change WideE.IsWideEValue (F.evaluateAtOne (a * b))
      rw [show F.evaluateAtOne (a * b) = F.evaluateAtOne a * F.evaluateAtOne b from
        F.evaluateAtOne.map_mul' a b]
      exact WideE.IsWideEValue.mul ha hb
    algebraMap_mem' := by
      intro b
      change WideE.IsWideEValue (F.evaluateAtOne (algebraMap R F.candidate b))
      rw [F.evaluateAtOne_base]
      exact WideE.algebraic_isWideEValue (laurentLogBasePoint k b) }
  have hle : F.candidate ≤ good.map F.candidate.val := by
    refine (le_of_eq F.candidate_eq_amplitudes).trans ?_
    apply (matrixGeneratedAlgebra_le_iff _ _).mpr
    refine ⟨⟨F.amplitudeDeterminantInverse, ?_, rfl⟩, fun i j =>
      ⟨F.amplitudeInCandidate i j, ?_, rfl⟩⟩
    · change WideE.IsWideEValue (F.evaluateAtOne F.amplitudeDeterminantInverse)
      rw [F.evaluateAtOne_determinantInverse]
      exact amplitude_inverse_wide (frame := frame)
    · change WideE.IsWideEValue (F.evaluateAtOne (F.amplitudeInCandidate i j))
      rw [F.evaluateAtOne_amplitude]
      exact ⟨_, frame.broad i j, rfl⟩
  obtain ⟨v, hv, heq⟩ := hle u.property
  have hu : v = u := Subtype.ext heq
  exact hu ▸ hv

/-- The numerical evaluation of the ramified PV candidate takes values in the broad ring. -/
def evaluateWide (F : RamifiedFundamental frame solutions) : F.candidate →ₐ[k] WideE.valueSubring where
  toFun a := ⟨F.evaluateAtOne a, F.wide_value_of_candidate a⟩
  map_zero' := Subtype.ext F.evaluateAtOne.map_zero'
  map_one' := Subtype.ext F.evaluateAtOne.map_one'
  map_add' _ _ := Subtype.ext (F.evaluateAtOne.map_add' _ _)
  map_mul' _ _ := Subtype.ext (F.evaluateAtOne.map_mul' _ _)
  commutes' a := Subtype.ext (F.evaluateAtOne.commutes a)

private theorem evaluateWide_of_mem_pointIdeal (F : RamifiedFundamental frame solutions)
    (a : R) (ha : a ∈ laurentLogBasePointIdeal k) :
    F.evaluateWide (algebraMap R F.candidate a) = 0 := by
  rw [← laurentLogBasePoint_kernel] at ha
  change laurentLogBasePoint k a = 0 at ha
  apply Subtype.ext
  change F.evaluateAtOne (algebraMap R F.candidate a) = 0
  simp only [F.evaluateAtOne_base, ha, Subfield.coe_zero]

end RamifiedFundamental

/-- Each finite family specializes through the actual smooth normal component of its fiber. -/
theorem realizedSmoothSpecializations_of_broadArithmeticFrames
    (frames : BroadArithmeticFrameExistence) :
    ∀ {ι : Type} [Finite ι] (f : ι → wideFunctions),
      Nonempty (RealizedSmoothNormalSpecialization evaluateAtOne wideParameter f) := by
  intro ι _ f
  obtain ⟨d, frame, solutions, hsolutions, entries⟩ := frames (fun i => (f i).val) (fun i => (f i).property)
  obtain ⟨F⟩ := frame.exists_ramifiedFundamental solutions hsolutions
  choose row col hentries using entries
  letI : IsAlgClosed k := stage17_algebraicTaylorField_isAlgClosed
  letI : IsNoetherianRing R := laurentLogBase_isNoetherianRing k
  letI : IsDomain R := laurentLogBase_isDomain k
  letI : CharZero R := Algebra.charZero_of_charZero k R
  let δ := manuscriptBaseDerivation («k» := k) F.degree
  let D := formalAmbientDerivation («k» := k) F.degree F.positive
  let M := frame.system.map (stage17_laurentBasePullback k F.degree)
  let U := stage17_formalFundamental k F.degree F.positive frame.amplitudes F.factor
  have hbase : ∀ a, D (algebraMap R L a) = algebraMap R L (δ a) :=
    formalBaseEmbedding_differential F.degree F.positive
  have hode : ∀ i j, D (U i j) = ∑ l, algebraMap R L (M i l) * U l j := by
    intro i j
    have h := congrFun (congrFun F.equation i) j
    simpa only [matrixDerivative_apply, Matrix.mul_apply, Matrix.map_apply] using h
  have hu : U.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det U).mp F.invertible)
  have simple := manuscriptBase_stable_ideal_eq_top («k» := k) F.degree F.positive
  have constants : ∀ a, D a = 0 → ∃ c : k, algebraMap k L c = a :=
    fun a => (formalAmbientDerivation_constants F.degree F.positive a).mp
  let realize := ramifiedRealization F.degree F.positive
  let t := stage17_laurentBasePullback k F.degree (LaurentPolynomial.T 1 - 1)
  have ht : realize wideParameter = algebraMap R L t := ramifiedRealization_parameter _ _
  have he (i : ι) : arithmeticRealization (f i) = solutions (row i) (col i) :=
    Subtype.ext (Subtype.ext (hentries i).symm)
  have hf (i : ι) : realize (f i) ∈ F.candidate := by
    change stage17_ramifiedEntireFormalAlgHom k F.degree F.positive (arithmeticRealization (f i)) ∈ _
    rw [he i]
    exact F.solution_mem_candidate (row i) (col i)
  have heval (i : ι) : F.evaluateWide ⟨realize (f i), hf i⟩ = evaluateAtOne (f i) := by
    have hrep : (⟨realize (f i), hf i⟩ : F.candidate) = F.solutionInCandidate (row i) (col i) :=
      Subtype.ext (congrArg (stage17_ramifiedEntireFormalAlgHom k F.degree F.positive) (he i))
    rw [hrep]
    apply Subtype.ext
    change F.evaluateAtOne (F.solutionInCandidate (row i) (col i)) = (f i).val 1
    rw [F.evaluateAtOne_solution, hentries i]
  have specialization : Nonempty (SmoothNormalSpecialization («k» := ↥k)
      (realize wideParameter) (realize ∘ f) (evaluateAtOne ∘ f)) := by
    rw [ht]
    exact smoothNormalSpecialization_of_matrixPVFiber δ D M U hbase hode hu simple constants
      formalBaseEmbedding_injective (laurentLogBasePointIdeal k) residueEquiv
      t (parameter_mem_pointIdeal F.degree) (realize ∘ f) hf (evaluateAtOne ∘ f)
      F.evaluateWide F.evaluateWide_of_mem_pointIdeal heval
  obtain ⟨data⟩ := specialization
  letI : Algebra WideE.AlgebraicComplex L := (inferInstance : Algebra ↥k L)
  exact ⟨⟨L, realize, data⟩⟩

/-- Sections 1–5 under the arithmetic Frobenius-frame existence statement from the paper. -/
theorem isIntegrallyClosed_valueSubring_of_broadArithmeticFrames_and_division
    (frames : BroadArithmeticFrameExistence) (division : HasWideDivisionAtOne) :
    IsIntegrallyClosed WideE.valueSubring := by
  apply isIntegrallyClosed_valueSubring_of_realizedSpecializations division
  intro ι _ f
  obtain ⟨data⟩ := realizedSmoothSpecializations_of_broadArithmeticFrames frames f
  letI := data.commRing
  letI := data.algebra
  exact ⟨⟨data.ambient, data.realize, data.specialization.toNormalSpecialization⟩⟩

end WideEIntegralClosed
