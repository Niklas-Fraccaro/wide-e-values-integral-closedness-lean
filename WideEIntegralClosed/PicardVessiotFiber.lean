import WideEIntegralClosed.FiberBaseChange
import WideEIntegralClosed.HopfComponentSmoothness
import AlgebraicFiber
import CandidateFaithfullyFlat
import MatrixCandidateTorsorCriterion
import PVConstantHopfAlgebra
import WideE.HopfAntipode
import WideE.HopfSmoothness

/-! The quotient fiber of a matrix-generated Picard–Vessiot algebra. -/

noncomputable section

open scoped Matrix TensorProduct
open StrictEUnit

namespace WideEIntegralClosed

variable {k R L n : Type} [Field k] [CommRing R] [Field L] [Fintype n] [DecidableEq n]
  [Algebra k R] [Algebra k L] [Algebra R L] [IsScalarTower k R L]
  (dR : Derivation k R R) (dL : Derivation k L L) (M : Matrix n n R) (U : Matrix n n L)
  (hbase : ∀ a, dL (algebraMap R L a) = algebraMap R L (dR a))
  (hode : ∀ i j, dL (U i j) = ∑ l, algebraMap R L (M i l) * U l j)

local notation "P" => matrixGeneratedAlgebra (B := R) U
local notation "dP" => candidateKDerivation dR dL U M hbase hode
local notation "hP" => candidateKDerivation_base dR dL U M hbase hode

/-- The coordinate algebra of the differential Galois group of the chosen matrix. -/
abbrev matrixPVGroup := pvConstantAlgebra dR dP hP

variable [IsNoetherianRing R] (hdet : U.det ≠ 0)
  (simple : ∀ I : Ideal R, (∀ a ∈ I, dR a ∈ I) → I ≠ ⊥ → I = ⊤)
  (constants : ∀ a, dL a = 0 → ∃ c : k, algebraMap k L c = a)

/-- The constants give the Hopf structure on the matrix PV group. -/
def matrixPVHopf : HopfAlgebra k (matrixPVGroup dR dL M U hbase hode) := by
  letI : Module.FaithfullyFlat R P :=
    matrixGeneratedAlgebra_faithfullyFlat dR dL U M hdet hbase hode simple
  refine pvConstantHopfAlgebra dR dP hP
    (candidateConstantMultiplication_bijective dR dL U M hdet hbase hode constants) ?_
  intro a ha
  obtain ⟨c, hc⟩ := constants a.val (congrArg Subtype.val ha)
  exact ⟨c, Subtype.ext hc⟩

variable [IsAlgClosed k] [Algebra R k] [IsScalarTower k R k]

/-- The ordinary quotient fiber is a torsor trivialized by an algebraic point. -/
def matrixPVFiberEquiv (I : Ideal R) (residue : (R ⧸ I) ≃ₐ[R] k) :
    (P ⧸ I.map (algebraMap R P)) ≃ₐ[k] (matrixPVGroup dR dL M U hbase hode) := by
  letI : Module.FaithfullyFlat R P :=
    matrixGeneratedAlgebra_faithfullyFlat dR dL U M hdet hbase hode simple
  letI : Algebra.FiniteType R P := candidate_finiteType (B := R) U
  let chart := candidateConstantMultiplicationEquiv dR dL U M hdet hbase hode constants
  exact (quotientFiberEquiv I residue).trans (algebraicFiberTrivialization (k := k) chart)

include hdet simple constants in
/-- The PV group is of finite type, as is the fiber that trivializes it. -/
theorem matrixPVGroup_finiteType (I : Ideal R) (residue : (R ⧸ I) ≃ₐ[R] k) :
    Algebra.FiniteType k (matrixPVGroup dR dL M U hbase hode) := by
  letI : Algebra.FiniteType R P := candidate_finiteType (B := R) U
  letI : Algebra.FiniteType k (k ⊗[R] P) := algebraicFiber_finiteType (k := k) (B := R)
  exact (inferInstance : Algebra.FiniteType k (k ⊗[R] P)).equiv
    ((quotientFiberEquiv I residue).symm.trans
      (matrixPVFiberEquiv dR dL M U hbase hode hdet simple constants I residue))

omit [IsAlgClosed k] [Algebra R k] [IsScalarTower k R k] in
include hdet simple in
/-- The matrix PV group is reduced because its coordinate algebra embeds in the flat
relative tensor product of the candidate with itself. -/
theorem matrixPVGroup_isReduced [IsDomain R] [CharZero R]
    (hinjective : Function.Injective (algebraMap R L)) :
    IsReduced (matrixPVGroup dR dL M U hbase hode) := by
  letI : Module.FaithfullyFlat R P :=
    matrixGeneratedAlgebra_faithfullyFlat dR dL U M hdet hbase hode simple
  letI : Algebra.FiniteType R P := candidate_finiteType (B := R) U
  letI : IsReduced (P ⊗[R] P) :=
    WideE.flatDomainTensor_isReduced (fun _ _ h => hinjective (congrArg Subtype.val h))
  exact isReduced_of_injective (matrixPVGroup dR dL M U hbase hode).val Subtype.val_injective

set_option maxRecDepth 1500 in
include M hbase hode hdet simple constants in
/-- Specialization through the actual smooth normal component selected by evaluation. -/
theorem smoothNormalSpecialization_of_matrixPVFiber [IsDomain R] [CharZero R] [CharZero k]
    {S ι : Type} [CommRing S] [IsDomain S] [Algebra k S]
    (hinjective : Function.Injective (algebraMap R L))
    (I : Ideal R) (residue : (R ⧸ I) ≃ₐ[R] k)
    (t : R) (ht : t ∈ I) (f : ι → L) (hf : ∀ i, f i ∈ P) (x : ι → S)
    (eval : P →ₐ[k] S) (hvanishes : ∀ a ∈ I, eval (algebraMap R P a) = 0)
    (heval : ∀ i, eval ⟨f i, hf i⟩ = x i) :
    Nonempty (SmoothNormalSpecialization (k := k) (algebraMap R L t) f x) := by
  let functions := P
  let H := matrixPVGroup dR dL M U hbase hode
  letI : HopfAlgebra k H := matrixPVHopf dR dL M U hbase hode hdet simple constants
  letI : Algebra.FiniteType k H :=
    matrixPVGroup_finiteType dR dL M U hbase hode hdet simple constants I residue
  letI : IsReduced H := matrixPVGroup_isReduced dR dL M U hbase hode hdet simple hinjective
  let J := I.map (algebraMap R P)
  let q : P →ₐ[k] (P ⧸ J) := Ideal.Quotient.mkₐ k J
  let e := matrixPVFiberEquiv dR dL M U hbase hode hdet simple constants I residue
  let quotientEval : (P ⧸ J) →ₐ[k] S := Ideal.Quotient.liftₐ J eval (by
    have hj : J ≤ RingHom.ker eval.toRingHom := Ideal.map_le_iff_le_comap.mpr hvanishes
    exact fun _ ha => hj ha)
  let inversion : H →ₐ[k] H := WideE.hopfAntipodeAlgHom k H
  refine smoothNormalSpecialization_of_hopfFiberMap (functions.restrictScalars k) (algebraMap R L t)
    (functions.algebraMap_mem t) f hf x (e.toAlgHom.comp q) (quotientEval.comp e.symm.toAlgHom)
    ?_ ?_ inversion WideE.hopfAntipodeAlgHom_toLinearMap
  · have hq : q (algebraMap R P t) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ht)
    change e (q (algebraMap R P t)) = 0
    rw [hq, map_zero]
  · intro i
    let a : P := ⟨f i, hf i⟩
    have h : e.symm.toAlgHom (e.toAlgHom (q a)) = q a := e.symm_apply_apply (q a)
    exact (congrArg quotientEval h).trans (heval i)

include M hbase hode hdet simple constants in
/-- The smooth specialization supplies the normal-domain data used in descent. -/
theorem normalSpecialization_of_matrixPVFiber [IsDomain R] [CharZero R] [CharZero k]
    {S ι : Type} [CommRing S] [IsDomain S] [Algebra k S]
    (hinjective : Function.Injective (algebraMap R L))
    (I : Ideal R) (residue : (R ⧸ I) ≃ₐ[R] k)
    (t : R) (ht : t ∈ I) (f : ι → L) (hf : ∀ i, f i ∈ P) (x : ι → S)
    (eval : P →ₐ[k] S) (hvanishes : ∀ a ∈ I, eval (algebraMap R P a) = 0)
    (heval : ∀ i, eval ⟨f i, hf i⟩ = x i) :
    Nonempty (NormalSpecialization (k := k) (algebraMap R L t) f x) := by
  obtain ⟨data⟩ := smoothNormalSpecialization_of_matrixPVFiber
    dR dL M U hbase hode hdet simple constants hinjective I residue t ht f hf x eval hvanishes heval
  exact ⟨data.toNormalSpecialization⟩

end WideEIntegralClosed
