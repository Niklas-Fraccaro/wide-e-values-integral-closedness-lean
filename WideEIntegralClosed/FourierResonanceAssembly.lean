import FourierNaturalResonanceBasis
import FiniteLogBaseIdentification
import FrobeniusIntegerShiftEquation
import Stage38OrdinarySourceTransport
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Assembly of scalar Fourier resonance blocks over the Laurent-log base.

The generic resonance and block-matrix lemmas adapt the pinned `StrictEUnit` source
to a dependency chain that is independent of the strict arithmetic estimates.
-/

noncomputable section

open scoped BigOperators Classical
open StrictEUnit

namespace WideEIntegralClosed.FourierResonanceAssembly

section

variable {K : Type*} [Field K] [CharZero K]

def IntegerExponentRelated (rho sigma : K) : Prop :=
  ∃ z : ℤ,rho-sigma=(z : K)

omit [CharZero K] in
theorem integerExponentRelated_equivalence :
    Equivalence (IntegerExponentRelated (K:=K)) := by
  refine ⟨?_,?_,?_⟩
  · intro rho
    exact ⟨0,by simp⟩
  · rintro rho sigma ⟨z,hz⟩
    refine ⟨-z,?_⟩
    rw [Int.cast_neg,← hz]
    ring
  · rintro rho sigma tau ⟨a,ha⟩ ⟨b,hb⟩
    refine ⟨a+b,?_⟩
    rw [Int.cast_add,← ha,← hb]
    ring

end

section

variable {K : Type*} [Field K] [CharZero K] {r : ℕ}

def exponentClassSetoid (rho : Fin r → K) : Setoid (Fin r) where
  r s t := IntegerExponentRelated (rho s) (rho t)
  iseqv := ⟨fun _ => integerExponentRelated_equivalence.refl _,
    fun h => integerExponentRelated_equivalence.symm h,
    fun h g => integerExponentRelated_equivalence.trans h g⟩

abbrev ExponentClass (rho : Fin r → K) := Quotient (exponentClassSetoid rho)
def exponentClassMap (rho : Fin r → K) (s : Fin r) : ExponentClass rho :=
  Quotient.mk _ s

/-- A lower representative for each disjoint class makes every original shift natural.
The representatives need not themselves occur in the tuple. -/
theorem exists_disjoint_natural_exponent_classes (rho : Fin r → K) :
    ∃ xi : ExponentClass rho → K, ∃ shift : Fin r → ℕ,
      (∀ s, rho s = xi (exponentClassMap rho s) + (shift s : K)) ∧
      (∀ c d, c ≠ d → ∀ z : ℤ, xi c - xi d ≠ (z : K)) := by
  classical
  let q := exponentClassMap rho
  have hr : ∀ s, IntegerExponentRelated (rho s) (rho (q s).out) := by
    intro s
    exact Quotient.exact (Quotient.out_eq (q s)).symm
  choose a ha using hr
  let B : ℕ := ∑ s, (a s).natAbs
  have hB : ∀ s, -(B : ℤ) ≤ a s := by
    intro s
    have h : (a s).natAbs ≤ B := Finset.single_le_sum (fun i _ => Nat.zero_le ((a i).natAbs)) (Finset.mem_univ s)
    have h' : ((a s).natAbs : ℤ) ≤ (B : ℤ) := by exact_mod_cast h
    have h'' := Int.natAbs_eq (a s)
    omega
  refine ⟨fun c => rho c.out - (B : K), fun s => (a s + B).toNat, ?_, ?_⟩
  · intro s
    have hn : 0 ≤ a s + (B : ℤ) := by have := hB s; omega
    have he : (((a s + B).toNat : ℕ) : K) = (a s : K) + (B : K) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, Int.cast_add, Int.cast_natCast]
    rw [he]
    have := ha s
    dsimp [q] at *
    linear_combination this
  · intro c d hcd z hz
    apply hcd
    have hrel : IntegerExponentRelated (rho c.out) (rho d.out) := by
      refine ⟨z, ?_⟩
      linear_combination hz
    have he : (Quotient.mk (exponentClassSetoid rho) c.out) =
        Quotient.mk (exponentClassSetoid rho) d.out := Quotient.sound hrel
    simpa only [Quotient.out_eq] using he

end

section

variable {K : Type*} [Field K] [CharZero K] {r : ℕ}

/-- The actual root-seed map of all disjoint lower classes is bijective.
This retains root multiplicities, not merely the set of distinct exponents. -/
theorem disjointNaturalResonanceSeed_bijective
    (P : Polynomial K) (hP : P ≠ 0) (e : frobeniusRootSeedIndex P ≃ Fin r)
    (rho : Fin r → K) (hrho : ∀ j, rho j = frobeniusRootSeedExponent P (e.symm j))
    (xi : ExponentClass rho → K) (s : Fin r → ℕ)
    (hs : ∀ j, rho j = xi (exponentClassMap rho j) + (s j : K))
    (hsep : ∀ c d, c ≠ d → ∀ z : ℤ, xi c - xi d ≠ (z : K)) :
    Function.Bijective (fun i : Σ c, polynomialLogResonanceCoordinateIndex (xi c) P =>
      naturalResonanceRootSeed P (xi i.1) hP i.2) := by
  classical
  constructor
  · intro i j he
    have hx : xi i.1 + (i.2.1.1 : K) = xi j.1 + (j.2.1.1 : K) :=
      congrArg (fun a : frobeniusRootSeedIndex P => a.1.1) he
    have hc : i.1 = j.1 := by
      by_contra hn
      apply hsep i.1 j.1 hn ((j.2.1.1 : ℤ) - (i.2.1.1 : ℤ))
      push_cast
      linear_combination hx
    cases i with | mk c i =>
      cases j with | mk d j =>
        dsimp only at hc
        subst d
        have hn : i.1.1 = j.1.1 := by
          have hn' : (i.1.1 : K) = (j.1.1 : K) := add_left_cancel hx
          exact_mod_cast hn'
        have hnsub : i.1 = j.1 := Subtype.ext hn
        have hi : i = j := by
          apply Sigma.ext hnsub
          apply (Fin.heq_ext_iff (by congr 1)).mpr
          exact congrArg (fun a : frobeniusRootSeedIndex P => a.2.1) he
        cases hi
        rfl
  · intro a
    let j := e a
    have hj : rho j = a.1.1 := by simpa [j, frobeniusRootSeedExponent] using hrho j
    have hx : xi (exponentClassMap rho j) + (s j : K) = a.1.1 := (hs j).symm.trans hj
    have hm : s j ∈ polynomialResonanceIndices (xi (exponentClassMap rho j)) P := by
      apply (polynomialResonanceIndices_mem_iff_eval_zero _ P hP _).mpr
      rw [hx]
      exact (Polynomial.mem_roots hP).mp (Multiset.mem_toFinset.mp a.1.2)
    have hmult : polynomialResonanceMultiplicity (xi (exponentClassMap rho j)) P (s j) =
        P.rootMultiplicity a.1.1 := by
      unfold polynomialResonanceMultiplicity
      rw [hx]
    let i : polynomialLogResonanceCoordinateIndex (xi (exponentClassMap rho j)) P :=
      ⟨⟨s j, hm⟩, ⟨a.2.1, by rw [hmult]; exact a.2.2⟩⟩
    refine ⟨⟨exponentClassMap rho j, i⟩, ?_⟩
    apply Sigma.ext (Subtype.ext hx)
    apply (Fin.heq_ext_iff (by congr 1)).mpr
    rfl

/-- Global natural-resonance indexing has exactly the original scalar rank. -/
theorem exists_disjoint_natural_resonance_equiv
    (P : Polynomial K) (hP : P ≠ 0) (e : frobeniusRootSeedIndex P ≃ Fin r)
    (rho : Fin r → K) (hrho : ∀ j, rho j = frobeniusRootSeedExponent P (e.symm j)) :
    ∃ xi : ExponentClass rho → K, ∃ s : Fin r → ℕ,
      (∀ j, rho j = xi (exponentClassMap rho j) + (s j : K)) ∧
      (∀ c d, c ≠ d → ∀ z : ℤ, xi c - xi d ≠ (z : K)) ∧
      ∃ E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c) P) ≃ Fin r,
        (∀ i, E i = e (naturalResonanceRootSeed P (xi i.1) hP i.2)) ∧
        Nat.card (Σ c, polynomialLogResonanceCoordinateIndex (xi c) P) = r := by
  classical
  obtain ⟨xi, s, hs, hsep⟩ := exists_disjoint_natural_exponent_classes rho
  let f := fun i : Σ c, polynomialLogResonanceCoordinateIndex (xi c) P =>
    naturalResonanceRootSeed P (xi i.1) hP i.2
  let E := (Equiv.ofBijective f
    (disjointNaturalResonanceSeed_bijective P hP e rho hrho xi s hs hsep)).trans e
  refine ⟨xi, s, hs, hsep, E, fun _ => rfl, ?_⟩
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_fin]

end

section

variable {C : Type*} {I : C →Type*} {R : Type*}
  [Fintype C] [DecidableEq C] [∀ c,Fintype (I c)] [∀ c,DecidableEq (I c)] [CommRing R]

/-- Block units combine into an actual square unit on the dependent disjoint union. -/
def finiteBlockUnit (Z : ∀ c,(Matrix (I c) (I c) R)ˣ) :
    (Matrix (Σ c,I c) (Σ c,I c) R)ˣ where
  val := Matrix.blockDiagonal' (fun c =>(Z c).val)
  inv := Matrix.blockDiagonal' (fun c =>((Z c)⁻¹).val)
  val_inv := by
    rw [← Matrix.blockDiagonal'_mul]
    have he : (fun c =>(Z c).val*((Z c)⁻¹).val)=(1 : ∀ c,Matrix (I c) (I c) R) := by
      funext c;exact (Z c).val_inv
    rw [he,Matrix.blockDiagonal'_one]
  inv_val := by
    rw [← Matrix.blockDiagonal'_mul]
    have he : (fun c =>((Z c)⁻¹).val*(Z c).val)=(1 : ∀ c,Matrix (I c) (I c) R) := by
      funext c;exact (Z c).inv_val
    rw [he,Matrix.blockDiagonal'_one]

end

section

variable {C : Type*} {I : C → Type*} {J R : Type*}
  [Fintype C] [DecidableEq C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
  [Fintype J] [DecidableEq J] [CommRing R]

def reindexedBlockUnit (Z : ∀ c, (Matrix (I c) (I c) R)ˣ)
    (e : (Σ c, I c) ≃ J) : (Matrix J J R)ˣ :=
  Units.map (Matrix.reindexAlgEquiv R R e).toMonoidHom (finiteBlockUnit Z)

end

section

variable {K C : Type*} {I : C → Type*} {J : Type*}
  [Field K] [Fintype C] [DecidableEq C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
  [Fintype J] [DecidableEq J]

omit [Fintype C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)] in
theorem matrixDerivative_blockDiagonal
    (d : Derivation K (LaurentLogBase K) (LaurentLogBase K))
    (A : ∀ c, Matrix (I c) (I c) (LaurentLogBase K)) :
    matrixDerivative d (Matrix.blockDiagonal' A) =
      Matrix.blockDiagonal' (fun c => matrixDerivative d (A c)) := by
  ext ⟨c,i⟩ ⟨b,j⟩
  by_cases h : c = b
  · subst b
    simp [matrixDerivative, Matrix.blockDiagonal'_apply_eq]
  · simp [matrixDerivative, Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- Exact differential equation survives actual dependent block gluing and
reindexing to the original rank. -/
theorem reindexedBlockUnit_equation
    (d : Derivation K (LaurentLogBase K) (LaurentLogBase K))
    (M : ∀ c, Matrix (I c) (I c) (LaurentLogBase K))
    (Z : ∀ c, (Matrix (I c) (I c) (LaurentLogBase K))ˣ)
    (hZ : ∀ c, matrixDerivative d (Z c).val = M c * (Z c).val)
    (e : (Σ c, I c) ≃ J) :
    matrixDerivative d (reindexedBlockUnit Z e).val =
      (Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e
        (Matrix.blockDiagonal' M)) * (reindexedBlockUnit Z e).val := by
  have hb : matrixDerivative d (finiteBlockUnit Z).val =
      Matrix.blockDiagonal' M * (finiteBlockUnit Z).val := by
    change matrixDerivative d (Matrix.blockDiagonal' (fun c => (Z c).val)) =
      Matrix.blockDiagonal' M * Matrix.blockDiagonal' (fun c => (Z c).val)
    rw [matrixDerivative_blockDiagonal]
    simp only [hZ, Matrix.blockDiagonal'_mul]
  change matrixDerivative d
      (Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e (finiteBlockUnit Z).val) =
      (Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e (Matrix.blockDiagonal' M)) *
      (Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e (finiteBlockUnit Z).val)
  rw [← map_mul]
  rw [← hb]
  rfl

end

section

variable {K C : Type*} {I : C → Type*} {J : Type*}
  [Field K] [CharZero K] [Fintype C] [DecidableEq C]
  [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)] [Fintype J] [DecidableEq J]

def reindexedClassResidue (xi : C → K) (L : ∀ c, Matrix (I c) (I c) K)
    (e : (Σ c, I c) ≃ J) : Matrix J J K :=
  Matrix.reindexAlgEquiv K K e
    (Matrix.blockDiagonal' (fun c => Matrix.diagonal (fun _ => xi c) + L c))

def reindexedClassBaseUnit (m : C → ℤ) (L : ∀ c, Matrix (I c) (I c) K)
    (hL : ∀ c, IsNilpotent (L c)) (e : (Σ c, I c) ≃ J) :
    (Matrix J J (LaurentLogBase K))ˣ :=
  reindexedBlockUnit (fun c => fixedExponentBaseUnit (m c) (L c) (hL c)) e

theorem reindexedClassBaseUnit_equation
    (N : ℕ) (hN : N ≠ 0) (xi : C → K) (m : C → ℤ)
    (hm : ∀ c, (m c : K) / (N : K) = xi c)
    (L : ∀ c, Matrix (I c) (I c) K) (hL : ∀ c, IsNilpotent (L c))
    (e : (Σ c, I c) ≃ J) :
    matrixDerivative (manuscriptBaseDerivation N) (reindexedClassBaseUnit m L hL e).val =
      ramifiedConstantMatrix (reindexedClassResidue xi L e) *
        (reindexedClassBaseUnit m L hL e).val := by
  have hh := reindexedBlockUnit_equation (manuscriptBaseDerivation (k := K) N)
    (fun c => ramifiedConstantMatrix (Matrix.diagonal (fun _ : I c => xi c) + L c))
    (fun c => fixedExponentBaseUnit (m c) (L c) (hL c))
    (fun c => fixedExponentBaseUnit_equation N hN (m c) (xi c) (hm c) (L c) (hL c)) e
  have he : Matrix.reindexAlgEquiv (LaurentLogBase K) (LaurentLogBase K) e
      (Matrix.blockDiagonal' (fun c => ramifiedConstantMatrix
        (Matrix.diagonal (fun _ : I c => xi c) + L c))) =
      ramifiedConstantMatrix (reindexedClassResidue xi L e) := by
    apply Matrix.ext
    intro i j
    change Matrix.blockDiagonal' (fun c => ramifiedConstantMatrix
        (Matrix.diagonal (fun _ : I c => xi c) + L c)) (e.symm i) (e.symm j) =
      algebraMap K (LaurentLogBase K) (Matrix.blockDiagonal'
        (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c) (e.symm i) (e.symm j))
    obtain ⟨c,a⟩ := e.symm i
    obtain ⟨b,d⟩ := e.symm j
    by_cases h : c = b
    · subst b
      simp [Matrix.blockDiagonal'_apply_eq, ramifiedConstantMatrix]
    · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h]
  rw [he] at hh
  exact hh

end

open Polynomial

section

variable {K C : Type*} {I : C → Type*} {J : Type*}
  [Field K] [CharZero K] [Fintype C] [DecidableEq C]
  [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)] [Fintype J] [DecidableEq J]

def classBlockAlgHom : (∀ c, Matrix (I c) (I c) K) →ₐ[K]
    Matrix (Σ c, I c) (Σ c, I c) K :=
  { Matrix.blockDiagonal'RingHom I K with
    commutes' := by
      intro x
      change Matrix.blockDiagonal' (fun c => Matrix.diagonal (fun _ : I c => x)) = Matrix.diagonal (fun _ => x)
      apply Matrix.ext
      intro ⟨c,i⟩ ⟨b,j⟩
      by_cases h : c = b
      · subst b
        simp [Matrix.blockDiagonal'_apply_eq, Matrix.diagonal]
      · simp [Matrix.blockDiagonal'_apply_ne _ _ _ h, Matrix.diagonal, h] }

omit [CharZero K] in
theorem reindexedClassResidue_root
    (xi : C → K) (L : ∀ c, Matrix (I c) (I c) K)
    (hL : ∀ c, IsNilpotent (L c)) (e : (Σ c, I c) ≃ J)
    (a : K) (ha : (minpoly K (reindexedClassResidue xi L e)).IsRoot a) :
    ∃ c, a = xi c := by
  choose n hn using hL
  let f : C → K[X] := fun c => (X - Polynomial.C (xi c)) ^ n c
  let p : K[X] := ∏ c, f c
  have hf : ∀ c, aeval (Matrix.diagonal (fun _ : I c => xi c) + L c) (f c) = 0 := by
    intro c
    simpa [f, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def, add_sub_cancel_left] using hn c
  have hp : ∀ c, aeval (Matrix.diagonal (fun _ : I c => xi c) + L c) p = 0 := by
    intro c
    have hd : f c ∣ p := Finset.dvd_prod_of_mem f (Finset.mem_univ c)
    obtain ⟨q,hq⟩ := hd
    rw [hq, map_mul, hf c, zero_mul]
  have hpPi : aeval (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c) p = 0 := by
    funext c
    exact (aeval_pi_apply₂ _ _ c).trans (hp c)
  have hpB : aeval (Matrix.blockDiagonal' (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c)) p = 0 := by
    rw [show Matrix.blockDiagonal' (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c) =
      classBlockAlgHom (fun c => Matrix.diagonal (fun _ : I c => xi c) + L c) from rfl,
      aeval_algHom_apply, hpPi, map_zero]
  have hpM : aeval (reindexedClassResidue xi L e) p = 0 := by
    rw [reindexedClassResidue, aeval_algHom_apply, hpB, map_zero]
  have hd := minpoly.dvd K (reindexedClassResidue xi L e) hpM
  have hpa : p.IsRoot a := eval_eq_zero_of_dvd_of_eval_eq_zero hd ha
  obtain ⟨c,_,hc⟩ := (isRoot_prod Finset.univ f a).mp hpa
  refine ⟨c, ?_⟩
  have hz : (a - xi c) ^ n c = 0 := by simpa [IsRoot, f] using hc
  exact sub_eq_zero.mp (pow_eq_zero hz)

theorem reindexedClassResidue_rational_spectrum
    (xi : C → K) (hxi : ∀ c, ∃ q : ℚ, (q : K) = xi c)
    (L : ∀ c, Matrix (I c) (I c) K) (hL : ∀ c, IsNilpotent (L c))
    (e : (Σ c, I c) ≃ J) (a : K)
    (ha : (minpoly K (reindexedClassResidue xi L e)).IsRoot a) :
    ∃ q : ℚ, (q : K) = a := by
  obtain ⟨c,rfl⟩ := reindexedClassResidue_root xi L hL e a ha
  exact hxi c

end

section

variable {C : Type*} {I : C → Type*} {J R S : Type*}
  [Fintype C] [DecidableEq C] [∀ c, Fintype (I c)] [∀ c, DecidableEq (I c)]
  [Fintype J] [DecidableEq J] [CommRing R] [CommRing S]

theorem mapped_reindexedBlockUnit_row (g : R →+* S)
    (Z : ∀ c, (Matrix (I c) (I c) R)ˣ) (e : (Σ c, I c) ≃ J)
    (f : ∀ c, I c → S) (j : J) :
    (∑ i : J, f (e.symm i).1 (e.symm i).2 * g ((reindexedBlockUnit Z e).val i j)) =
      ∑ i : I (e.symm j).1, f (e.symm j).1 i * g ((Z (e.symm j).1).val i (e.symm j).2) := by
  change (∑ i : J, f (e.symm i).1 (e.symm i).2 *
    g ((finiteBlockUnit Z).val (e.symm i) (e.symm j))) = _
  rw [e.symm.sum_comp (fun i => f i.1 i.2 * g ((finiteBlockUnit Z).val i (e.symm j)))]
  obtain ⟨c,j⟩ := e.symm j
  rw [Fintype.sum_sigma, Finset.sum_eq_single c]
  · simp only [finiteBlockUnit, Matrix.blockDiagonal'_apply_eq]
  · intro b hb hbc
    simp only [finiteBlockUnit, Matrix.blockDiagonal'_apply_ne _ _ _ hbc, map_zero,
      mul_zero, Finset.sum_const_zero]
  · intro hc
    exact (hc (Finset.mem_univ c)).elim

theorem ramified_external_natural_shift {K : Type*} [Field K]
    (N : ℕ) (hN : N ≠ 0) (m s : ℤ) (p : Polynomial (LaurentSeries K)) :
    Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN (frobeniusIntegerShift s p) =
    Polynomial.C (HahnSeries.single (m + (N : ℤ) * s) (1 : K)) *
      stage38_logRamification N hN p := by
  rw [frobeniusIntegerShift, map_mul, stage38_logRamification_monomial,
    ← mul_assoc, ← Polynomial.C_mul, HahnSeries.single_mul_single, one_mul]

end

end WideEIntegralClosed.FourierResonanceAssembly
