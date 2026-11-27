import WideEIntegralClosed.BroadEulerConnection
import WideEIntegralClosed.BroadResidueArithmetic
import ActualEulerFieldMap
import ActualLogFrameSpanning
import IntegerClassShiftedFrame

/-! Subfactorial denominator estimates for the finite-jet Frobenius filters.

The integrality calculations at a fixed cutoff are independent of the growth class.
The broad estimate uses a smaller factorial exponent for the enlarged connection prefix.
-/

noncomputable section

open scoped BigOperators Matrix
open StrictEUnit

namespace WideEIntegralClosed

/-- Extension of the coefficient field leaves the common clearing integers and bounds intact. -/
theorem HasSubfactorialEulerConnectionDenominators.field_map
    {K L : Type*} [Field K] [Field L] {r : ℕ}
    {C : Matrix (Fin r) (Fin r) (PowerSeries K)}
    (hC : HasSubfactorialEulerConnectionDenominators C) (phi : K →+* L) :
    HasSubfactorialEulerConnectionDenominators (C.map (PowerSeries.map phi)) := by
  intro ε hε
  obtain ⟨B, hB, hden⟩ := hC ε hε
  refine ⟨B, hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hden N
  refine ⟨D, hD, hDb, fun m hm l hl i j => ?_⟩
  have h := (hDi m hm l hl i j).map phi.toIntAlgHom
  have he := congrFun (congrFun (powerSeriesEulerDividedConnection_field_map phi C m) i) j
  rw [← he]
  simpa only [Matrix.map_apply, PowerSeries.coeff_map, RingHom.toIntAlgHom_apply,
    map_mul, map_natCast] using h

/-- A residue eigenvalue inherits subfactorial binomial denominators from its actual connection. -/
theorem HasSubfactorialEulerConnectionDenominators.eigenvalue
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    {C : Matrix (Fin r) (Fin r) (PowerSeries K)} (hC : HasSubfactorialEulerConnectionDenominators C)
    (xi : K) (v : Fin r → K) (hv : (C.map (PowerSeries.constantCoeff K)) *ᵥ v = xi • v)
    (k : Fin r) (hk : v k ≠ 0) : HasSubfactorialBinomialDenominators xi := by
  let M := C.map (PowerSeries.constantCoeff K)
  let w : Fin r → K := (v k)⁻¹ • v
  have hwk : w k = 1 := by simp [w, Pi.smul_apply, smul_eq_mul, hk]
  have hw : M *ᵥ w = xi • w := by
    change M *ᵥ ((v k)⁻¹ • v) = xi • ((v k)⁻¹ • v)
    rw [Matrix.mulVec_smul, hv, smul_smul, smul_smul, mul_comm]
  have hp (m : ℕ) : (∑ j, (matrixFallingProduct M m k j / (m.factorial : K)) * w j) =
      (descPochhammer K m).eval xi / (m.factorial : K) := by
    have h := congrFun (matrixFallingProduct_mulVec_eigenvector M w xi hw m) k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hwk, mul_one] at h
    calc
      _ = (∑ j, matrixFallingProduct M m k j * w j) / (m.factorial : K) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [h]
  obtain ⟨b, hb, hbi⟩ := exists_positive_nat_integral_vector w
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  intro ε hε
  obtain ⟨B, hB, hden⟩ := hC ε hε
  refine ⟨(b : ℝ) * B, one_le_mul_of_one_le_of_one_le hb1 hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hden N
  refine ⟨b * D, Nat.mul_pos hb hD, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hDb (Nat.cast_nonneg b)
  · intro m hm
    rw [← hp m, Finset.mul_sum]
    apply IsIntegral.sum
    intro j _
    have h : IsIntegral ℤ ((D : K) * (matrixFallingProduct M m k j / (m.factorial : K))) := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
        powerSeriesEulerDividedConnection_constantCoeff, M] using hDi m hm 0 (Nat.zero_le N) k j
    convert h.mul (hbi j) using 1
    push_cast
    ring

/-- A scalar indicial root inherits the residue estimate through the actual regular gauge. -/
theorem HasSubfactorialEulerConnectionDenominators.indicial_binomial
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    {C : Matrix (Fin r) (Fin r) (PowerSeries K)} (hC : HasSubfactorialEulerConnectionDenominators C)
    (hr : 0 < r) (b : Fin (r + 1) → PowerSeries K) (hb : b (Fin.last r) = 1)
    (G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (hGH : G * H = 1) (hHG : H * G = 1)
    (hc : Matrix.of (fun i j => powerSeriesEuler (G i j)) + G * C = scalarEulerPowerSeriesCompanion r b * G)
    (xi : K) (hxi : (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0).eval xi = 0) :
    HasSubfactorialBinomialDenominators xi := by
  let C₀ := C.map (PowerSeries.constantCoeff K)
  let B₀ := (scalarEulerPowerSeriesCompanion r b).map (PowerSeries.constantCoeff K)
  let G₀ := G.map (PowerSeries.constantCoeff K)
  let H₀ := H.map (PowerSeries.constantCoeff K)
  have hGH₀ : G₀ * H₀ = 1 := by
    change (PowerSeries.constantCoeff K).mapMatrix G * (PowerSeries.constantCoeff K).mapMatrix H = 1
    rw [← map_mul, hGH, map_one]
  have hHG₀ : H₀ * G₀ = 1 := by
    change (PowerSeries.constantCoeff K).mapMatrix H * (PowerSeries.constantCoeff K).mapMatrix G = 1
    rw [← map_mul, hHG, map_one]
  have hc₀ : G₀ * C₀ = B₀ * G₀ := regularScalarGauge_residue_intertwining C _ G hc
  have hCH : C₀ * H₀ = H₀ * B₀ := by
    calc
      _ = H₀ * (G₀ * C₀) * H₀ := by rw [← mul_assoc, hHG₀, one_mul]
      _ = H₀ * (B₀ * G₀) * H₀ := by rw [hc₀]
      _ = H₀ * B₀ := by simp [mul_assoc, hGH₀]
  let w : Fin r → K := fun i => xi ^ i.val
  let v := H₀ *ᵥ w
  have hw : B₀ *ᵥ w = xi • w := monicScalarIndicial_root_eigenvector b hb xi hxi
  have hv : C₀ *ᵥ v = xi • v := by
    change C₀ *ᵥ (H₀ *ᵥ w) = _
    rw [Matrix.mulVec_mulVec, hCH, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul]
  have hGv : G₀ *ᵥ v = w := by
    change G₀ *ᵥ (H₀ *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, hGH₀, Matrix.one_mulVec]
  have hn : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : v = 0 := funext h
    have he := congrFun hGv ⟨0, hr⟩
    rw [hz, Matrix.mulVec_zero] at he
    simp [w] at he
  obtain ⟨k, hk⟩ := hn
  exact hC.eigenvalue xi v hv k hk

/-- The simultaneous connection denominator for the Frobenius filters is subfactorial whenever
the divided connection prefix denominators are subfactorial. -/
theorem allClassPrefixFilter_subfactorial_connection_denominators
    {K : Type*} [Field K] [CharZero K] {r q : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hden : HasSubfactorialEulerConnectionDenominators C)
    (rho : Fin q → K) (hrho : JointBinomialPrefixDenominators rho) (L : ℤ) (d : ℕ) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m, m ≤ N → ∀ l, l ≤ N → ∀ i j, IsIntegral ℤ ((D : K) * PowerSeries.coeff K l
        (powerSeriesEulerPolynomialConnection C (allClassPrefixFilter rho L m d) i j)) := by
  let R := q * (d + 1)
  obtain ⟨H, hH, hneg⟩ := jointBinomialPrefixDenominators_neg _
    (jointBinomialPrefixDenominators_integer_shift rho hrho L)
  let binomialClears (N e : ℕ) := ∀ m, m ≤ N → ∀ j, IsIntegral ℤ
    ((e : K) * ((descPochhammer K m).eval (-(rho j + (L : K))) / (m.factorial : K)))
  refine HasSubfactorialPrefixDenominators.affine_mul hden (a := R + 1) (by omega)
    (H ^ R) (one_le_pow₀ hH) (Q := fun N u => ∃ e, binomialClears N e ∧ u = e ^ R) ?_ ?_
  · intro N
    obtain ⟨e, he, heb, hei⟩ := hneg N
    refine ⟨e ^ R, pow_pos he R, ?_, e, hei, rfl⟩
    rw [Nat.cast_pow]
    calc
      _ ≤ (H ^ (N + 1)) ^ R := pow_le_pow_left₀ (Nat.cast_nonneg e) heb R
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm (N + 1) R]
  rintro N D u hDi ⟨e, hei, rfl⟩ m hm l hl i j
  have hbound : R * N ≤ (R + 1) * (N + 1) := by nlinarith
  have hl' : l ≤ (R + 1) * (N + 1) := hl.trans (by nlinarith)
  have hv : ∀ n : ℕ, IsIntegral ℤ ((e : K) ^ R * (allClassPrefixFilter rho L m d).eval (n : K)) := by
    intro n
    have h := (fallingCompositeSymbol_eval_integral (fun i => rho i + (L : K)) id (fun _ => m)
      N (fun _ => hm) (e : K)
      (by intro j hj v; rw [field_choose_eq_descPochhammer_div]; exact hei j hj v) n).pow (d+1)
    simpa only [mul_pow, ← pow_mul, allClassPrefixFilter, Polynomial.eval_pow, R] using h
  have h := powerSeriesEulerPolynomialConnection_integral C (allClassPrefixFilter rho L m d)
    (R * N) l ((allClassPrefixFilter_natDegree_le rho L m d).trans (Nat.mul_le_mul_left R hm))
    (D : K) ((e : K) ^ R) (fun j hj i k => hDi j (hj.trans hbound) l hl' i k)
    (fun n _ => hv n) i j
  simpa only [Nat.cast_mul, Nat.cast_pow] using h

private theorem logFrame_filtered_subfactorial_of_bounds
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hden : HasSubfactorialEulerConnectionDenominators C)
    (rho : Fin r → K) (hrho : JointBinomialPrefixDenominators rho)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i, twistedLogPolynomialEuler (rho j) (Y i j) =
      ∑ l, logPowerSeriesEmbedding (C i l) * Y l j) (hdet : Y.det ≠ 0)
    (L : ℤ) (d : ℕ)
    (hYlow : ∀ i j a, a < L → (logPolynomialToCoefficientSeries (Y i j)).coeff a = 0)
    (hYdeg : ∀ i j a, ((logPolynomialToCoefficientSeries (Y i j)).coeff a).natDegree ≤ d) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m, m ≤ N → ∀ s i t, IsIntegral ℤ ((D : K) *
        ((literalLogPolynomialFilter (rho s) (allClassPrefixFilter rho L m d) (Y i s)).coeff t).coeff
          ((m : ℤ) + L)) := by
  obtain ⟨J, W, hJ, _, hJlow⟩ := logFrame_exists_inverse_with_fixed_pole_bound C rho Y hY hdet
  obtain ⟨e, he, hei⟩ := logSolution_fixed_jet_common_denominator Y L (W : ℤ) d hYlow hYdeg
  have hconnection := allClassPrefixFilter_subfactorial_connection_denominators C hden rho hrho L d
  intro ε hε
  obtain ⟨E, hE, hED⟩ := hconnection ε hε
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  refine ⟨E * (e : ℝ), one_le_mul_of_one_le_of_one_le hE he1, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hED N
  refine ⟨D * e, Nat.mul_pos hD he, ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hDb (Nat.cast_nonneg e)).trans (le_of_eq (by ring))
  · intro m hm s i t
    have h := allClassPrefixFilter_solution_finite_jet_integral C rho Y J hY hJ L (W : ℤ) d
      hYlow hYdeg hJlow s m (D : K) (e : K)
      (fun i j l hl => hDi m hm l (hl.trans hm) i j)
      (fun j t l hl => hei j s t l hl) i t
    simpa only [Nat.cast_mul] using h

/-- The actual logarithmic frame has a common subfactorial denominator for the coefficients of
the Frobenius filters. One additional fixed integer clears the initial finite jet. -/
theorem logFrame_filtered_solution_common_subfactorial_denominators
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hden : HasSubfactorialEulerConnectionDenominators C)
    (rho : Fin r → K) (hrho : JointBinomialPrefixDenominators rho)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i, twistedLogPolynomialEuler (rho j) (Y i j) =
      ∑ l, logPowerSeriesEmbedding (C i l) * Y l j) (hdet : Y.det ≠ 0) :
    ∃ L : ℤ, ∃ d : ℕ, HasSubfactorialPrefixDenominators fun N D =>
      ∀ m, m ≤ N → ∀ s i t, IsIntegral ℤ ((D : K) *
        ((literalLogPolynomialFilter (rho s) (allClassPrefixFilter rho L m d) (Y i s)).coeff t).coeff
          ((m : ℤ) + L)) := by
  obtain ⟨L, d, hYlow, hYdeg⟩ := logFrame_exists_uniform_bounds Y
  exact ⟨L, d, logFrame_filtered_subfactorial_of_bounds C hden rho hrho Y hY hdet L d hYlow hYdeg⟩

private theorem aligned_logFrame_subfactorial_of_bounds
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hden : HasSubfactorialEulerConnectionDenominators C)
    (rho : Fin r → K) (hrho : JointBinomialPrefixDenominators rho)
    (halign : ∀ s t, rho s = rho t ∨ ∀ z : ℤ, rho s - rho t ≠ (z : K))
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i, twistedLogPolynomialEuler (rho j) (Y i j) =
      ∑ l, logPowerSeriesEmbedding (C i l) * Y l j) (hdet : Y.det ≠ 0)
    (L : ℤ) (d : ℕ)
    (hYlow : ∀ i j a, a < L → (logPolynomialToCoefficientSeries (Y i j)).coeff a = 0)
    (hYdeg : ∀ i j a, ((logPolynomialToCoefficientSeries (Y i j)).coeff a).natDegree ≤ d) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m, m ≤ N → ∀ s i t, IsIntegral ℤ ((D : K) * ((Y i s).coeff t).coeff ((m : ℤ) + L)) := by
  have hfiltered := logFrame_filtered_subfactorial_of_bounds C hden rho hrho Y hY hdet L d hYlow hYdeg
  obtain ⟨H, hH, hnormal⟩ := allClassPrefixFilter_shared_log_normalization rho hrho L d
  refine hfiltered.affine_mul (a := 1) Nat.one_pos H hH hnormal ?_
  intro N D e hDi hei m hm s i t
  have hs : rho s + (((m : ℤ) + L : ℤ) : K) = rho s + (L : K) + (m : K) := by
    push_cast
    ring
  have hp := alignedClassPrefixFilter_boundary_nonzero rho halign L m d s
  have h := hei s m hm hp (D : K) ((logPolynomialToCoefficientSeries (Y i s)).coeff ((m : ℤ) + L))
    (hYdeg i s _) (by
      intro j
      simpa only [literalLogPolynomialFilter_double_coefficient, hs] using hDi m (by omega) s i j) t
  simpa only [Nat.cast_mul, mul_comm (D : K) (e : K),
    logPolynomialToCoefficientSeries_double_coeff] using h

/-- A frame for a regular Euler system inherits common subfactorial denominators from its divided
connection coefficients. Aligning integer exponent classes removes collisions in the Frobenius
filters. The integer column shifts change the required cutoff by a fixed amount. -/
theorem logFrame_solution_common_subfactorial_denominators
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hden : HasSubfactorialEulerConnectionDenominators C)
    (rho : Fin r → K) (hrho : JointBinomialPrefixDenominators rho)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i, twistedLogPolynomialEuler (rho j) (Y i j) =
      ∑ l, logPowerSeriesEmbedding (C i l) * Y l j) (hdet : Y.det ≠ 0) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m : ℤ, m ≤ (N : ℤ) → ∀ s i t, IsIntegral ℤ ((D : K) * ((Y i s).coeff t).coeff m) := by
  obtain ⟨rep, shift, hs, halign⟩ := exists_integerClass_aligned_representatives rho
  let Y' := Matrix.of fun i j => frobeniusIntegerShift (shift j) (Y i j)
  have hY' := integerShift_logFrame_equation C rho (rho ∘ rep) shift hs Y hY
  have hdet' := integerShift_logFrame_det_nonzero shift Y hdet
  obtain ⟨L, d, hYlow, hYdeg⟩ := logFrame_exists_uniform_bounds Y'
  have hsource := aligned_logFrame_subfactorial_of_bounds C hden (rho ∘ rep) (hrho.comp rep)
    halign Y' hY' hdet' L d hYlow hYdeg
  let A : ℕ := ∑ s, (shift s - L).toNat
  refine hsource.affine (A + 1) (by omega) ?_
  intro N D hDi m hm s i t
  have hcoeff : ((Y' i s).coeff t).coeff (m + shift s) = ((Y i s).coeff t).coeff m := by
    change ((frobeniusIntegerShift (shift s) (Y i s)).coeff t).coeff _ = _
    rw [frobeniusIntegerShift_coeff, add_sub_cancel_right]
  rw [← hcoeff]
  by_cases hlow : m + shift s < L
  · rw [← logPolynomialToCoefficientSeries_double_coeff, hYlow i s _ hlow, Polynomial.coeff_zero, mul_zero]
    exact isIntegral_zero
  · let j : ℕ := (m + shift s - L).toNat
    have hj : (j : ℤ) = m + shift s - L := Int.toNat_of_nonneg (by omega)
    have ha : (shift s - L).toNat ≤ A :=
      Finset.single_le_sum (f := fun s => (shift s - L).toNat) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s)
    have hsA : shift s - L ≤ (A : ℤ) := (Int.self_le_toNat _).trans (by exact_mod_cast ha)
    have hj' : j ≤ (A + 1) * (N + 1) := by
      have hjA : j ≤ N + A := by omega
      exact hjA.trans (by nlinarith)
    have he : (j : ℤ) + L = m + shift s := by omega
    simpa only [he] using hDi j hj' s i t

/-- A regular Euler solution inherits subfactorial denominators from a full logarithmic frame.
Spanning expresses it as a finite sum of integer shifts with fixed field coefficients. -/
theorem actualLogFrame_solution_common_subfactorial_denominators
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (hY : ∀ j i, twistedLogPolynomialEuler (rho j) (Y i j) =
      ∑ l, logPowerSeriesEmbedding (C i l) * Y l j) (hdet : Y.det ≠ 0)
    (hden : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m : ℤ, m ≤ (N : ℤ) → ∀ s i t, IsIntegral ℤ ((D : K) * ((Y i s).coeff t).coeff m))
    (xi : K) (u : Fin r → LaurentSeries (Polynomial K))
    (hu : ∀ i, twistedPolynomialCoefficientEuler xi (u i) =
      ∑ j, logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j)) * u j) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m : ℤ, m ≤ (N : ℤ) → ∀ i t, IsIntegral ℤ ((D : K) * ((u i).coeff m).coeff t) := by
  obtain ⟨n, c, _, hs⟩ := actualLogFrame_spanning C rho Y hY hdet xi u hu
  obtain ⟨e, he, hc⟩ := logJet_finite_family_integral c
  let A : ℕ := ∑ j, (n j).natAbs
  have hshift (j : Fin r) : -(n j) ≤ (A : ℤ) := by
    have haj : (n j).natAbs ≤ A :=
      Finset.single_le_sum (f := fun j => (n j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hn := (Int.le_natAbs (a := -(n j)))
    rw [Int.natAbs_neg] at hn
    exact hn.trans (by exact_mod_cast haj)
  have hpadded : HasSubfactorialPrefixDenominators fun N D =>
      ∀ m : ℤ, m ≤ (N : ℤ) → ∀ j i t, IsIntegral ℤ ((D : K) * ((Y i j).coeff t).coeff (m - n j)) := by
    refine hden.affine (A + 1) (by omega) ?_
    intro N D hDi m hm j i t
    apply hDi (m - n j) ?_ j i t
    have hcutoff : N + A ≤ (A + 1) * (N + 1) := by nlinarith
    have hj := hshift j
    omega
  intro ε hε
  obtain ⟨B, hB, hden'⟩ := hpadded ε hε
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  refine ⟨(e : ℝ) * B, one_le_mul_of_one_le_of_one_le he1 hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hden' N
  refine ⟨e * D, Nat.mul_pos he hD, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hDb (Nat.cast_nonneg e)
  · intro m hm i t
    have hsum : ((u i).coeff m).coeff t = ∑ j, c j * ((Y i j).coeff t).coeff (m - n j) := by
      rw [hs i, HahnSeries.coeff_sum, Polynomial.finset_sum_coeff]
      apply Finset.sum_congr rfl
      intro j _
      conv_lhs =>
        rw [mul_comm, show m = m - n j + n j by omega, HahnSeries.coeff_single_mul_add,
          Polynomial.coeff_C_mul, logPolynomialToCoefficientSeries_double_coeff]
    rw [hsum, Finset.mul_sum]
    apply IsIntegral.sum
    intro j _
    convert (hc j).mul (hDi m hm j i t) using 1
    push_cast
    ring

/-- A splitting scalar equation supplies a full frame for the actual regular Euler system. -/
theorem regularScalarGauge_constructed_subfactorial_frame
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hr : 0 < r)
    (hC : HasSubfactorialEulerConnectionDenominators C)
    (b : Fin (r + 1) → PowerSeries K) (hb : b (Fin.last r) = 1)
    (G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (hGH : G * H = 1) (hHG : H * G = 1)
    (hc : Matrix.of (fun i j => powerSeriesEuler (G i j)) + G * C = scalarEulerPowerSeriesCompanion r b * G)
    (hsplit : (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K))
    (hbinomial : ∀ ξ : K, HasSubfactorialBinomialDenominators ξ → BinomialPrefixDenominators ξ) :
    ∃ rho : Fin r → K, ∃ Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)),
      Y.det ≠ 0 ∧ (∀ j i, twistedLogPolynomialEuler (rho j) (Y i j) =
        ∑ l, logPowerSeriesEmbedding (C i l) * Y l j) ∧
      HasSubfactorialPrefixDenominators fun N D =>
        ∀ m : ℤ, m ≤ (N : ℤ) → ∀ s i t, IsIntegral ℤ ((D : K) * ((Y i s).coeff t).coeff m) := by
  have htop : PowerSeries.constantCoeff K (b (Fin.last r)) ≠ 0 := by rw [hb, map_one]; exact one_ne_zero
  let B := scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))
  let e := scalarEulerFrobeniusIndexEquiv r b htop hsplit
  let rho : Fin r → K := fun j => frobeniusRootSeedExponent (B 0) (e.symm j)
  let Z := frobeniusActualJetMatrix B e
  obtain ⟨hdet, hZ, _⟩ := scalarEuler_constructed_frobenius_frame r b htop hsplit
  obtain ⟨hYdet, hY⟩ := regularEuler_log_frame_pullback C _ G H hGH hHG hc rho Z hZ hdet
  have hJoint : JointBinomialPrefixDenominators rho := by
    apply finite_binomialPrefixDenominators rho
    intro j
    refine hbinomial (rho j) (hC.indicial_binomial hr b hb G H hGH hHG hc (rho j) ?_)
    exact frobeniusRootSeedExponent_isRoot (B 0) (e.symm j)
  exact ⟨rho, H.map logPowerSeriesEmbedding * Z, hYdet, hY,
    logFrame_solution_common_subfactorial_denominators C hC rho hJoint _ hY hYdet⟩

/-- An actual solution of a broad regular Euler system with a monic scalar gauge has subfactorial
denominators. Its frame is constructed over a finite splitting field, and the estimates descend. -/
theorem regularScalarGauge_solution_common_subfactorial_denominators
    {K : Type u} [Field K] [NumberField K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hr : 0 < r)
    (hC : HasSubfactorialEulerConnectionDenominators C)
    (b : Fin (r + 1) → PowerSeries K) (hb : b (Fin.last r) = 1)
    (G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (hGH : G * H = 1) (hHG : H * G = 1)
    (hg : Matrix.of (fun i j => powerSeriesEuler (G i j)) + G * C = scalarEulerPowerSeriesCompanion r b * G)
    (hbinomial : ∀ {L : Type u} [Field L] [NumberField L] (ξ : L),
      HasSubfactorialBinomialDenominators ξ → BinomialPrefixDenominators ξ)
    (xi : K) (u : Fin r → LaurentSeries (Polynomial K))
    (hu : ∀ i, twistedPolynomialCoefficientEuler xi (u i) =
      ∑ j, logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j)) * u j) :
    HasSubfactorialPrefixDenominators fun N D =>
      ∀ m : ℤ, m ≤ (N : ℤ) → ∀ i t, IsIntegral ℤ ((D : K) * ((u i).coeff m).coeff t) := by
  let P := scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0
  let L := P.SplittingField
  obtain ⟨hNF, hsplit⟩ := scalarIndicial_finite_splitting_field b
  letI : NumberField L := hNF
  let phi : K →+* L := algebraMap K L
  have hb' : PowerSeries.map phi (b (Fin.last r)) = 1 := by rw [hb, map_one]
  obtain ⟨hGH', hHG', hg'⟩ := monicScalarGauge_field_map phi C G H b hb hGH hHG hg
  obtain ⟨rho, Y, hdet, hY, hYden⟩ := regularScalarGauge_constructed_subfactorial_frame
    (C.map (PowerSeries.map phi)) hr (hC.field_map phi) (fun i => PowerSeries.map phi (b i)) hb'
    (G.map (PowerSeries.map phi)) (H.map (PowerSeries.map phi)) hGH' hHG' hg' hsplit
    (fun ξ => hbinomial ξ)
  have hu' := actualEuler_solution_field_map phi C xi u hu
  have hden := actualLogFrame_solution_common_subfactorial_denominators _ rho Y hY hdet hYden (phi xi)
    (fun i => logCoefficientFieldHom phi (u i)) hu'
  intro ε hε
  obtain ⟨B, hB, hprefix⟩ := hden ε hε
  refine ⟨B, hB, fun N => ?_⟩
  obtain ⟨D, hD, hDb, hDi⟩ := hprefix N
  refine ⟨D, hD, hDb, fun m hm i t => ?_⟩
  apply (isIntegral_algHom_iff phi.toIntAlgHom phi.injective).mp
  have h := hDi m hm i t
  change IsIntegral ℤ ((D : L) * (((u i).coeff m).map phi).coeff t) at h
  simpa only [Polynomial.coeff_map, RingHom.toIntAlgHom_apply, map_mul, map_natCast] using h

end WideEIntegralClosed
