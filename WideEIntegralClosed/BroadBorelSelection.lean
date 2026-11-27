import WideEIntegralClosed.BroadBorelSource
import WideEIntegralClosed.BroadResidueArithmetic
import WideE.ConnectionArithmetic
import OrdinaryBorelMinimalCyclic

/-! Selecting a regular Borel equation from the defining coefficients of a broad E-function. -/

noncomputable section

open scoped BigOperators Matrix NumberField
open StrictEUnit

namespace WideEIntegralClosed

/-- The minimal Borel companion with its original number field and its subfactorial bounds.
The same clearing polynomials are retained for the arithmetic study of the indicial roots. -/
structure BroadBorelCompanion (a : ℕ → WideE.AlgebraicComplex) where
  coefficientField : IntermediateField ℚ WideE.AlgebraicComplex
  coefficients_mem : ∀ n, a n ∈ coefficientField
  [numberField : NumberField coefficientField]
  rankMinusOne : ℕ
  companionCoefficients : Fin (rankMinusOne + 1) → RatFunc coefficientField
  minimal : OrdinaryBorelMinimalCyclicData
    (HahnSeries.ofPowerSeries ℤ coefficientField
      (PowerSeries.mk (ordinaryBorelFieldCoefficient coefficientField a coefficients_mem)))
    (rankMinusOne + 1) companionCoefficients
  denominator : Polynomial (𝓞 coefficientField)
  numerator : Matrix (Fin (rankMinusOne + 1)) (Fin (rankMinusOne + 1))
    (Polynomial (𝓞 coefficientField))
  denominator_ne_zero : denominator.map (algebraMap (𝓞 coefficientField) coefficientField) ≠ 0
  clears_companion : ∀ i j,
    algebraMap (Polynomial coefficientField) (RatFunc coefficientField)
      ((numerator i j).map (algebraMap (𝓞 coefficientField) coefficientField)) =
      algebraMap (Polynomial coefficientField) (RatFunc coefficientField)
        (denominator.map (algebraMap (𝓞 coefficientField) coefficientField)) *
        minimalDerivativeCompanion (rankMinusOne + 1) companionCoefficients i j
  subfactorial : WideE.HasSubfactorialConnectionDenominators
    (denominator.map (algebraMap (𝓞 coefficientField) coefficientField))
    (Matrix.of fun i j => (numerator i j).map (algebraMap (𝓞 coefficientField) coefficientField))

/-- The wide connection arithmetic selects the same Borel companion that supplies the Laurent
operator. Keeping its minimality and clearing data allows further conclusions at singularities. -/
theorem exists_broadBorelCompanion {f : ℂ → ℂ} (hf : WideE.IsWideEFunction f) (hfne : f ≠ 0) :
    ∃ a : ℕ → WideE.AlgebraicComplex,
      WideE.HasFactorialExpansion f a ∧ Nonempty (BroadBorelCompanion a) := by
  classical
  obtain ⟨a, hd, hs, hODE, ha, _⟩ := hf
  have hne : ∃ n, a n ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hfne
    funext z
    have hz : HasSum (fun _ : ℕ => (0 : ℂ)) (f z) := by simpa [hn] using hs z
    exact hz.unique hasSum_zero
  obtain ⟨m, p, hp, hFormal⟩ := WideE.formal_polynomial_ode hd hs hODE
  rw [WideE.taylorRealization_factorialSeries hd hs] at hFormal
  obtain ⟨u, Q, hQ, hRec⟩ := factorialSeries_ode_original_coefficients_recurrence a m p hp hFormal
  obtain ⟨v, q, hq, hOrd⟩ := polynomial_recurrence_ordinary_series_ode a u Q hQ hRec
  obtain ⟨F, hF, haF, hqF⟩ := stage26_formal_ode_finite_coefficient_field v q (PowerSeries.mk a) hq hOrd
  letI : FiniteDimensional ℚ F := hF
  letI : NumberField F := ⟨⟩
  have hmem (n : ℕ) : a n ∈ F := by simpa only [PowerSeries.coeff_mk] using haF n
  obtain ⟨qF, _, hqFn, hqFO⟩ := ordinaryBorel_equation_descends F a hmem v q hqF hq hOrd
  let aF := ordinaryBorelFieldCoefficient F a hmem
  let G := PowerSeries.mk aF
  have haFne : ∃ n, aF n ≠ 0 := by
    obtain ⟨n, hn⟩ := hne
    exact ⟨n, fun hz => hn (congrArg (fun x : F => (x : WideE.AlgebraicComplex)) hz)⟩
  obtain ⟨r, hr, c, hCyclic⟩ := ordinaryBorel_exists_minimal_cyclic (HahnSeries.ofPowerSeries ℤ F G)
    (ordinaryBorel_laurent_mk_ne_zero aF haFne)
    (ordinaryBorel_laurent_scalar_relation G v qF hqFn hqFO)
  cases r with
  | zero => omega
  | succ n =>
    let A := minimalDerivativeCompanion (n + 1) c
    obtain ⟨_, _, _, _, _, _, T, UI, _, _, _, hT, hclear⟩ :=
      exists_integral_polynomial_matrix_clearing F (n + 1) A
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) (Polynomial F) :=
      Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 F) F))
    obtain ⟨hli, hSystem⟩ := minimal_companion_powerSeries_clearing G (n + 1) c hCyclic
      (T.map (algebraMap (𝓞 F) F)) U hclear
    have hPrefix := WideE.ordinaryBorel_hasSubfactorialIntegralPrefixes F a ha hmem (n + 1)
    have hden := WideE.hasSubfactorialConnectionDenominators_of_integralPrefixes hr T U A
      (ordinaryDerivativePrefix (n + 1) G) hT hclear hli hSystem hPrefix
    exact ⟨a, hs, ⟨{
      coefficientField := F
      coefficients_mem := hmem
      rankMinusOne := n
      companionCoefficients := c
      minimal := hCyclic
      denominator := T
      numerator := UI
      denominator_ne_zero := hT
      clears_companion := hclear
      subfactorial := hden }⟩⟩

namespace BroadBorelCompanion

variable {a : ℕ → WideE.AlgebraicComplex} (C : BroadBorelCompanion a)

/-- The integral clearing polynomial viewed over the selected coefficient field. -/
def clearingPolynomial : Polynomial C.coefficientField :=
  C.denominator.map (algebraMap (𝓞 C.coefficientField) C.coefficientField)

/-- The cleared connection matrix over the selected coefficient field. -/
def clearingMatrix : Matrix (Fin (C.rankMinusOne + 1)) (Fin (C.rankMinusOne + 1))
    (Polynomial C.coefficientField) :=
  Matrix.of fun i j => (C.numerator i j).map (algebraMap (𝓞 C.coefficientField) C.coefficientField)

private def scalarTuple : Fin (C.rankMinusOne + 1 + 1) → Polynomial C.coefficientField :=
  sameCompanionScalarTuple (C.rankMinusOne + 1) (Nat.succ_pos _)
    C.clearingPolynomial C.clearingMatrix

private theorem regularScalarTuple :
    ReciprocalRegularSingularBounds (C.rankMinusOne + 1) C.scalarTuple := by
  letI : NumberField C.coefficientField := C.numberField
  exact C.subfactorial.reciprocalRegularSingularBounds C.rankMinusOne
    C.companionCoefficients C.clearingPolynomial C.clearingMatrix
    C.denominator_ne_zero C.clears_companion

/-- The original cleared last row satisfies the regular singular inequalities. -/
theorem regularClearing (j : Fin (C.rankMinusOne + 1))
    (hj : C.clearingMatrix (Fin.last C.rankMinusOne) j ≠ 0) :
    C.clearingPolynomial.natTrailingDegree + j.val ≤
      (C.clearingMatrix (Fin.last C.rankMinusOne) j).natTrailingDegree + (C.rankMinusOne + 1) := by
  let n := C.rankMinusOne
  have hidx : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    simp
  have hnonzero : C.scalarTuple j.castSucc ≠ 0 := by
    simpa only [scalarTuple, sameCompanionScalarTuple, Fin.lastCases_castSucc, hidx, neg_ne_zero]
      using hj
  have h := C.regularScalarTuple j.castSucc hnonzero
  simpa only [scalarTuple, sameCompanionScalarTuple, Fin.lastCases_last, Fin.lastCases_castSucc,
    hidx, Polynomial.natTrailingDegree_neg, Fin.coe_castSucc] using h

private theorem mappedScalarTuple_spec :
    let p := fun i => (C.scalarTuple i).map (algebraMap C.coefficientField WideE.AlgebraicComplex)
    p (Fin.last (C.rankMinusOne + 1)) ≠ 0 ∧
      ReciprocalRegularSingularBounds (C.rankMinusOne + 1) p ∧
      (∑ i, (p i : PowerSeries WideE.AlgebraicComplex) *
        (PowerSeries.derivative WideE.AlgebraicComplex)^[i.val] (PowerSeries.mk a)) = 0 := by
  let F := C.coefficientField
  let G := PowerSeries.mk (ordinaryBorelFieldCoefficient F a C.coefficients_mem)
  let r := C.rankMinusOne + 1
  obtain ⟨_, htop, hL, _⟩ := sameCompanionScalarTuple_spec (HahnSeries.ofPowerSeries ℤ F G)
    r (Nat.succ_pos _) C.companionCoefficients C.minimal C.clearingPolynomial C.clearingMatrix
    C.denominator_ne_zero C.clears_companion
  have hPower := powerSeries_equation_of_laurent_scalar_equation G r C.scalarTuple hL
  exact ordinaryFieldTuple_map F a C.coefficients_mem r C.scalarTuple
    htop C.regularScalarTuple hPower

/-- The Borel source and exact Fourier transform are attached to the selected companion. -/
def source {f : ℂ → ℂ} (expansion : WideE.HasFactorialExpansion f a) : BroadBorelSource f where
  coefficients := a
  expansion := expansion
  order := C.rankMinusOne + 1
  operator := fun i => (C.scalarTuple i).map (algebraMap C.coefficientField WideE.AlgebraicComplex)
  leading_ne_zero := C.mappedScalarTuple_spec.1
  regular := C.mappedScalarTuple_spec.2.1
  equation := C.mappedScalarTuple_spec.2.2

/-- The exact Fourier roots inherit subfactorial binomial denominators from the original
connection, using the regularity proved for this very same clearing. -/
theorem fourierRoot_binomialDenominators {f : ℂ → ℂ}
    (expansion : WideE.HasFactorialExpansion f a) :
    let S := C.source expansion
    ∀ hf : Stage56FiniteFuchs S.reciprocalArray, ∀ ξ : WideE.AlgebraicComplex,
      (sameFourierEulerCoefficientSymbols S.reciprocalArray hf 0).eval ξ = 0 →
        HasSubfactorialBinomialDenominators ξ := by
  let F := C.coefficientField
  letI : NumberField F := C.numberField
  letI : Algebra.IsAlgebraic ℤ WideE.AlgebraicComplex :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := WideE.AlgebraicComplex)).mpr
      (inferInstance : Algebra.IsAlgebraic ℚ WideE.AlgebraicComplex)
  let φ : F →+* WideE.AlgebraicComplex := algebraMap F WideE.AlgebraicComplex
  apply hasSubfactorialBinomialDenominators_of_reflected_fourier_root φ C.rankMinusOne
    C.clearingPolynomial C.clearingMatrix C.denominator_ne_zero C.mappedScalarTuple_spec.2.1
  exact hasSubfactorialBinomialDenominators_of_connection φ C.rankMinusOne C.companionCoefficients
    C.denominator C.clearingMatrix C.denominator_ne_zero C.clears_companion C.regularClearing
    C.subfactorial

end BroadBorelCompanion

end WideEIntegralClosed
