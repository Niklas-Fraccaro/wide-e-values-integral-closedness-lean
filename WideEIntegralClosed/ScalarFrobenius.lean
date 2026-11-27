import Stage33FormalCompanion
import Stage33ShiftedFormalUnit
import Stage29InitialNondegeneracy
import WideEIntegralClosed.ArithmeticRealization
import WideEIntegralClosed.FrameAssembly

/-! Passage from scalar broad Frobenius data to the actual arithmetic frame. -/

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 40000

attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring

open scoped BigOperators Matrix
open StrictEUnit

namespace WideEIntegralClosed

local notation "k₀" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)
local notation "A" => subfieldEntireFunctionAlgebra k₀

local instance (F : Subfield ℂ) : CommRing (subfieldEntireFunctionAlgebra F) :=
  (subfieldEntireFunctionAlgebra F).toCommRing

/-- A full scalar Frobenius row for a specific polynomial differential operator. -/
structure BroadScalarFrobeniusBasis (m : ℕ) (p : Fin (m + 1) → Polynomial k₀) where
  degree : ℕ
  degree_ne_zero : degree ≠ 0
  amplitudes : Fin m → A
  residue : Matrix (Fin m) (Fin m) k₀
  factor : (Matrix (Fin m) (Fin m) (LaurentLogBase k₀))ˣ
  broad : ∀ j, WideE.IsWideEFunction (amplitudes j).val.val
  rational_spectrum : ∀ a : k₀, (minpoly k₀ residue).IsRoot a → ∃ q : ℚ, (q : k₀) = a
  factor_equation : matrixDerivative (manuscriptBaseDerivation (k := k₀) degree) factor.val =
    ramifiedConstantMatrix residue * factor.val
  scalar_equation : ∀ j, ∑ l,
    Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k₀ degree degree_ne_zero (subfieldEntireCoordinate k₀))
      (p l) *
      ((stage32_ramifiedOrdinaryDerivation k₀ degree degree_ne_zero) :
        RatFunc (LaurentSeries k₀) → RatFunc (LaurentSeries k₀))^[l.val]
          (stage33_scalarNormalFormRow k₀ degree degree_ne_zero amplitudes factor j) = 0
  independent : LinearIndependent k₀
    (stage33_scalarNormalFormRow k₀ degree degree_ne_zero amplitudes factor)

private theorem entireJetRow_broad {n : Type*} [Fintype n] [DecidableEq n]
    (e : n → A) (M : Matrix n n k₀) (he : ∀ j, WideE.IsWideEFunction (e j).val.val)
    (i : ℕ) (j : n) : WideE.IsWideEFunction (stage33_entireJetRow k₀ e M i j).val.val := by
  induction i generalizing j with
  | zero => exact he j
  | succ i ih =>
    change stage33_entireFunctionValue k₀ (_ + _) ∈ wideFunctions
    have hsum (g : n → A) : stage33_entireFunctionValue k₀ (∑ l, g l) =
        ∑ l, stage33_entireFunctionValue k₀ (g l) :=
      map_sum (stage33_entireFunctionValue k₀).toAddMonoidHom g Finset.univ
    rw [(stage33_entireFunctionValue k₀).map_add, hsum]
    apply wideFunctions.add_mem
    · exact WideE.isWideEFunction_coordinate.mul (ih j).derivative
    · apply wideFunctions.sum_mem
      intro l _
      rw [(stage33_entireFunctionValue k₀).map_mul]
      exact (ih l).mul (WideE.isWideEFunction_const _)

private theorem entireJetFrame_broad (m : ℕ) (e : Fin m → A) (M : Matrix (Fin m) (Fin m) k₀)
    (he : ∀ j, WideE.IsWideEFunction (e j).val.val) (i j : Fin m) :
    WideE.IsWideEFunction (stage33_entireJetFrame k₀ m e M i j).val.val := by
  change stage33_entireFunctionValue k₀ (_ ^ _ * _) ∈ wideFunctions
  rw [(stage33_entireFunctionValue k₀).map_mul, (stage33_entireFunctionValue k₀).map_pow]
  apply wideFunctions.mul_mem
  · exact wideFunctions.pow_mem WideE.isWideEFunction_coordinate _
  · exact entireJetRow_broad e M he i.val j

namespace BroadScalarFrobeniusBasis

variable {m r : ℕ} {c : k₀} {p : Fin (m + 1) → Polynomial k₀}
  (S : BroadScalarFrobeniusBasis m p) (hc : c ≠ 0)
  (hp : p (Fin.last m) = Polynomial.monomial r c)

include hc hp

private theorem frame_relation :
    Stage17ActualEulerFrameRelation k₀ (stage28_laurentCompanion k₀ m r c p)
      (stage33_shiftedResidue k₀ S.residue (m - 1))
      (stage33_entireJetFrame k₀ m S.amplitudes S.residue) := by
  apply stage32_actualEulerFrame_of_formalFrame_ode k₀ S.degree S.degree_ne_zero
  apply stage33_frame_ode_of_factorization _ _ _ _
    (stage33_shiftedFormalBaseUnit k₀ S.degree S.degree_ne_zero (m - 1) S.factor)
  · rw [← stage33_scalarNormalFormJet_factorization k₀ S.degree S.degree_ne_zero
      m S.amplitudes S.residue S.factor S.factor_equation]
    exact stage33_formal_scalarJet_ode k₀ S.degree S.degree_ne_zero m r c p hc hp
      (stage33_scalarNormalFormRow k₀ S.degree S.degree_ne_zero S.amplitudes S.factor) S.scalar_equation
  · exact stage33_shiftedFormalBaseUnit_ode k₀ S.degree S.degree_ne_zero (m - 1)
      S.residue S.factor S.factor_equation

private theorem det_at_one (hm : 0 < m) :
    ((stage33_entireJetFrame k₀ m S.amplitudes S.residue).map
      (stage14_subfieldEntireEvaluation k₀ 1)).det ≠ 0 := by
  apply (stage29_arithmeticFrame_formal_det_ne_zero_iff_at_one k₀ S.degree S.degree_ne_zero
    (stage28_laurentCompanion k₀ m r c p) (stage33_shiftedResidue k₀ S.residue (m - 1))
    (stage33_entireJetFrame k₀ m S.amplitudes S.residue) (S.frame_relation hc hp)).mp
  have hj : (stage33_scalarNormalFormJet k₀ S.degree S.degree_ne_zero m S.amplitudes S.factor).det ≠ 0 :=
    stage30_scaled_formal_jet_det_ne_zero S.degree S.degree_ne_zero
      (stage17_ramifiedEntireFormalAlgHom k₀ S.degree S.degree_ne_zero (subfieldEntireCoordinate k₀))⁻¹
      (inv_ne_zero (stage17_ramifiedEntireFormal_coordinate_ne_zero k₀ S.degree S.degree_ne_zero))
      m hm (fun l => Polynomial.aeval
        (stage17_ramifiedEntireFormalAlgHom k₀ S.degree S.degree_ne_zero (subfieldEntireCoordinate k₀))
        (p l)) (stage33_formal_leading_ne_zero k₀ S.degree S.degree_ne_zero m r c p hc hp)
      (stage33_scalarNormalFormRow k₀ S.degree S.degree_ne_zero S.amplitudes S.factor)
      S.scalar_equation S.independent
  rw [stage33_scalarNormalFormJet_factorization k₀ S.degree S.degree_ne_zero
    m S.amplitudes S.residue S.factor S.factor_equation, Matrix.det_mul] at hj
  exact fun h => hj (by rw [h, zero_mul])

/-- Construct the pole-cleared frame of the exact ordinary derivative companion. -/
def arithmeticFrame (hm : 0 < m) : BroadArithmeticFrame (Fin m) where
  system := stage28_laurentCompanion k₀ m r c p
  residue := stage33_shiftedResidue k₀ S.residue (m - 1)
  amplitudes := stage33_entireJetFrame k₀ m S.amplitudes S.residue
  broad := entireJetFrame_broad m S.amplitudes S.residue S.broad
  rational_spectrum := stage33_shiftedResidue_rational k₀ S.residue (m - 1) S.rational_spectrum
  frame_equation := S.frame_relation hc hp
  invertible_at_one := S.det_at_one hc hp hm

end BroadScalarFrobeniusBasis

/-- The scalar existence claim for each nonzero broad E-function. -/
def BroadScalarFrobeniusExistence : Prop :=
  ∀ f : ℂ → ℂ, WideE.IsWideEFunction f → f ≠ (fun _ => 0) →
    ∃ m r : ℕ, ∃ c : k₀, ∃ p : Fin (m + 1) → Polynomial k₀,
      0 < m ∧ Stage28MonomialLeadingODE k₀ m r c p f ∧ Nonempty (BroadScalarFrobeniusBasis m p)

private def trivialFrame : BroadArithmeticFrame (Fin 1) where
  system := (stage27_trivialFrame k₀).B
  residue := (stage27_trivialFrame k₀).M
  amplitudes := (stage27_trivialFrame k₀).F
  broad i j := WideE.isWideEFunction_of_strict ((stage27_trivialFrame k₀).strict i j)
  rational_spectrum := (stage27_trivialFrame k₀).rational
  frame_equation := (stage27_trivialFrame k₀).relation
  invertible_at_one := (stage27_trivialFrame k₀).invertible_at_one

/-- The scalar claim suffices for the single-function arithmetic frame, including the original
solution as the zeroth component of the ordinary derivative jet. -/
theorem broadSingleArithmeticFrameExistence_of_scalarFrobenius
    (h : BroadScalarFrobeniusExistence) : BroadSingleArithmeticFrameExistence := by
  intro f hf
  by_cases hne : f = fun _ => 0
  · subst f
    exact ⟨1, trivialFrame, 0, by intro z i j; simp [trivialFrame, stage27_trivialFrame], 0, 0, rfl⟩
  obtain ⟨m, r, c, p, hm, hode, ⟨S⟩⟩ := h f hf hne
  let U : Matrix (Fin m) (Fin m) A := fun i _ =>
    arithmeticRealization ⟨stage28_derivativeJet m f i, hf.iteratedDeriv i.val⟩
  refine ⟨m, S.arithmeticFrame hode.coefficient_ne_zero hode.leading hm, U,
    ?_, ⟨0, hm⟩, ⟨0, hm⟩, stage28_derivativeJet_zero m hm f⟩
  intro z i j
  simpa [BroadScalarFrobeniusBasis.arithmeticFrame, U, arithmeticRealization] using
    stage28_derivativeJet_solution k₀ m r c p f hode z i

/-- The scalar claim suffices for a common arithmetic frame of any finite family. -/
theorem broadArithmeticFrameExistence_of_scalarFrobenius
    (h : BroadScalarFrobeniusExistence) : BroadArithmeticFrameExistence :=
  broadArithmeticFrameExistence_of_single (broadSingleArithmeticFrameExistence_of_scalarFrobenius h)

end WideEIntegralClosed
