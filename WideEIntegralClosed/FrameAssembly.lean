import Stage27ActualFrameAssembly
import WideEIntegralClosed.BroadFrobenius

/-! Assembly of a common broad arithmetic frame from individual frames. -/

noncomputable section

open StrictEUnit

namespace WideEIntegralClosed

local notation "k" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)
local notation "A" => subfieldEntireFunctionAlgebra k

/-- The arithmetic existence input for one broad E-function and one original solution entry. -/
def BroadSingleArithmeticFrameExistence : Prop :=
  ∀ f : ℂ → ℂ, WideE.IsWideEFunction f →
    ∃ d : ℕ, ∃ frame : BroadArithmeticFrame (Fin d), ∃ solutions : Matrix (Fin d) (Fin d) A,
      Stage17ActualEulerFrameRelation k frame.system 0 solutions ∧
      ∃ r c : Fin d, (solutions r c).val.val = f

private def emptyFrame : BroadArithmeticFrame (Fin 0) where
  system := 0
  residue := 0
  amplitudes := 0
  broad i _ := Fin.elim0 i
  rational_spectrum a ha := by
    rw [minpoly.subsingleton k (0 : Matrix (Fin 0) (Fin 0) k)] at ha
    simp [Polynomial.IsRoot] at ha
  frame_equation := fun _ i => Fin.elim0 i
  invertible_at_one := by rw [Matrix.det_isEmpty]; exact one_ne_zero

private def blockFrame {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (F : BroadArithmeticFrame n) (G : BroadArithmeticFrame m) : BroadArithmeticFrame (n ⊕ m) where
  system := Matrix.fromBlocks F.system 0 0 G.system
  residue := Matrix.fromBlocks F.residue 0 0 G.residue
  amplitudes := Matrix.fromBlocks F.amplitudes 0 0 G.amplitudes
  broad := by
    have hz : WideE.IsWideEFunction (fun _ : ℂ => (0 : ℂ)) := by
      simpa using WideE.isWideEFunction_const (0 : WideE.AlgebraicComplex)
    intro i j
    cases i <;> cases j
    · exact F.broad _ _
    · exact hz
    · exact hz
    · exact G.broad _ _
  rational_spectrum := stage27_blockDiagonal_rational_spectrum F.residue G.residue
    F.rational_spectrum G.rational_spectrum
  frame_equation := stage27_actualEulerFrame_blockDiagonal k F.system G.system F.residue G.residue
    F.amplitudes G.amplitudes F.frame_equation G.frame_equation
  invertible_at_one := stage27_blockDiagonal_det_ne_zero k F.amplitudes G.amplitudes
    F.invertible_at_one G.invertible_at_one

private def reindexFrame {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (e : n ≃ m) (F : BroadArithmeticFrame n) : BroadArithmeticFrame m where
  system := Matrix.reindex e e F.system
  residue := Matrix.reindex e e F.residue
  amplitudes := Matrix.reindex e e F.amplitudes
  broad i j := F.broad (e.symm i) (e.symm j)
  rational_spectrum a ha := F.rational_spectrum a (by rwa [stage27_reindex_minpoly] at ha)
  frame_equation := stage27_actualEulerFrame_reindex k e F.system F.residue F.amplitudes
    F.frame_equation
  invertible_at_one := stage27_reindex_det_ne_zero k e F.amplitudes F.invertible_at_one

/-- Individual arithmetic frames suffice for every finite family, by block-diagonal assembly. -/
theorem broadArithmeticFrameExistence_of_single (h : BroadSingleArithmeticFrameExistence) :
    BroadArithmeticFrameExistence := by
  classical
  intro ι hι f hf
  letI := Fintype.ofFinite ι
  suffices hcover : ∀ s : Finset ι, ∃ d : ℕ, ∃ frame : BroadArithmeticFrame (Fin d),
      ∃ solutions : Matrix (Fin d) (Fin d) A,
        Stage17ActualEulerFrameRelation k frame.system 0 solutions ∧
        ∀ i ∈ s, ∃ r c : Fin d, (solutions r c).val.val = f i by
    obtain ⟨d, frame, solutions, hsolve, entries⟩ := hcover Finset.univ
    exact ⟨d, frame, solutions, hsolve, fun i => entries i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, emptyFrame, 0, fun _ i => Fin.elim0 i, fun _ hi => (Finset.not_mem_empty _ hi).elim⟩
  | @insert a s _ ih =>
    obtain ⟨n, F, U, hU, r, c, ha⟩ := h (f a) (hf a)
    obtain ⟨m, G, V, hV, hentries⟩ := ih
    let e : (Fin n ⊕ Fin m) ≃ Fin (n + m) := finSumFinEquiv
    let W := Matrix.fromBlocks U 0 0 V
    have hblock : Stage17ActualEulerFrameRelation k (blockFrame F G).system 0 W := by
      simpa only [Matrix.fromBlocks_zero] using stage27_actualEulerFrame_blockDiagonal k
        F.system G.system 0 0 U V hU hV
    have hzero : Matrix.reindex e e (0 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) k) = 0 := by
      ext i j
      rfl
    have hW : Stage17ActualEulerFrameRelation k (reindexFrame e (blockFrame F G)).system 0
        (Matrix.reindex e e W) := by
      simpa only [hzero] using
        stage27_actualEulerFrame_reindex k e (blockFrame F G).system 0 W hblock
    refine ⟨n + m, reindexFrame e (blockFrame F G), Matrix.reindex e e W, hW, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact ⟨e (.inl r), e (.inl c), by simpa [W, Matrix.reindex_apply] using ha⟩
    · obtain ⟨r', c', hi'⟩ := hentries i hi
      exact ⟨e (.inr r'), e (.inr c'), by simpa [W, Matrix.reindex_apply] using hi'⟩

/-- The arithmetic existence statements for one function and for finite families are equivalent. -/
theorem broadArithmeticFrameExistence_iff_single :
    BroadArithmeticFrameExistence ↔ BroadSingleArithmeticFrameExistence := by
  refine ⟨?_, broadArithmeticFrameExistence_of_single⟩
  intro h f hf
  obtain ⟨d, frame, solutions, hsolve, entries⟩ := h (fun _ : Unit => f) (fun _ => hf)
  exact ⟨d, frame, solutions, hsolve, entries ()⟩

end WideEIntegralClosed
