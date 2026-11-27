import WideEIntegralClosed.AlgebraicDescent

/-! Lifting finite relations by division and a common specialization, as in Section 4. -/

noncomputable section

namespace WideEIntegralClosed

variable {k F S : Type} [CommRing k] [CommRing F] [Algebra k F]
  [CommRing S] [Algebra k S]

/-- A ring of functions containing a specified family and a specialization through a normal
domain. The specialization kills the fiber parameter and agrees with evaluation on the family. -/
structure NormalSpecialization {ι : Type} (parameter : F) (f : ι → F) (x : ι → S) where
  functions : Subalgebra k F
  contains : ∀ i, f i ∈ functions
  parameter_mem : parameter ∈ functions
  carrier : Type
  [commRing : CommRing carrier]
  [algebra : Algebra k carrier]
  [domain : IsDomain carrier]
  [integrallyClosed : IsIntegrallyClosed carrier]
  fiberMap : functions →ₐ[k] carrier
  eval : carrier →ₐ[k] S
  kills_parameter : fiberMap ⟨parameter, parameter_mem⟩ = 0
  eval_lift : ∀ i, eval (fiberMap ⟨f i, contains i⟩) = x i

variable {W : Type} [CommRing W] [Algebra k W]

private theorem lift_of_divided_relations {ι : Type} (x : ι → S)
    (relations : Finset (MvPolynomial ι k)) (realize : W →ₐ[k] F) (eval : W →ₐ[k] S)
    (parameter : F) (f : ι → W) (g : relations → W)
    (hf : ∀ i, eval (f i) = x i)
    (hg : ∀ q : relations, parameter * realize (g q) = realize (MvPolynomial.aeval f q.val))
    (data : NormalSpecialization (k := k) parameter (realize ∘ Sum.elim f g)
      (eval ∘ Sum.elim f g)) : Nonempty (NormalRelationLift k S x relations) := by
  let B := data.carrier
  letI : CommRing B := data.commRing
  letI : Algebra k B := data.algebra
  letI : IsDomain B := data.domain
  letI : IsIntegrallyClosed B := data.integrallyClosed
  let included (i : ι ⊕ relations) : data.functions := ⟨realize (Sum.elim f g i), data.contains i⟩
  let generators (i : ι) := data.fiberMap (included (.inl i))
  refine ⟨⟨B, data.eval, generators, ?_, ?_⟩⟩
  · intro i
    exact (data.eval_lift (.inl i)).trans (hf i)
  · intro q hq
    let j : relations := ⟨q, hq⟩
    have lift_eq : MvPolynomial.aeval (fun i => included (.inl i)) q =
        (⟨parameter, data.parameter_mem⟩ : data.functions) * included (.inr j) := by
      apply Subtype.ext
      change data.functions.val (MvPolynomial.aeval (fun i => included (.inl i)) q) =
        parameter * realize (g j)
      rw [MvPolynomial.comp_aeval_apply, hg j]
      change MvPolynomial.aeval (fun i => realize (f i)) q = realize (MvPolynomial.aeval f q)
      rw [MvPolynomial.comp_aeval_apply]
    change MvPolynomial.aeval (fun i => data.fiberMap (included (.inl i))) q = 0
    rw [← MvPolynomial.comp_aeval_apply, lift_eq, map_mul, data.kills_parameter, zero_mul]

/-- If functions can be divided by the fiber parameter at a vanishing value, then a common
normal specialization for each finite family lifts arbitrary finite relations between values. -/
theorem hasNormalRelationLifts_of_specializations (realize : W →ₐ[k] F) (eval : W →ₐ[k] S)
    (parameter : F) (surj : Function.Surjective eval)
    (divide : ∀ w : W, eval w = 0 → ∃ g : W, parameter * realize g = realize w)
    (specialize : ∀ {ι : Type} [Finite ι] (f : ι → W),
      Nonempty (NormalSpecialization (k := k) parameter (realize ∘ f) (eval ∘ f))) :
    HasNormalRelationLifts k S := by
  classical
  intro ι _ x relations hx
  choose f hf using fun i => surj (x i)
  have vanishes (q : relations) : eval (MvPolynomial.aeval f q.val) = 0 := by
    rw [MvPolynomial.comp_aeval_apply]
    simpa only [hf] using hx q.val q.property
  choose g hg using fun q => divide (MvPolynomial.aeval f q.val) (vanishes q)
  obtain ⟨data⟩ := specialize (Sum.elim f g)
  exact lift_of_divided_relations x relations realize eval parameter f g hf hg data

/-- A normal specialization with an ambient realization chosen for the finite family.
For example, the ambient ring can use a common ramification depending on the family. -/
structure RealizedNormalSpecialization {ι : Type} (eval : W →ₐ[k] S)
    (parameter : W) (family : ι → W) where
  ambient : Type
  [commRing : CommRing ambient]
  [algebra : Algebra k ambient]
  realize : W →ₐ[k] ambient
  specialization : NormalSpecialization (k := k) (realize parameter) (realize ∘ family) (eval ∘ family)

/-- Finite relation lifting with a realization chosen only after fixing the division witnesses. -/
theorem hasNormalRelationLifts_of_realizedSpecializations (eval : W →ₐ[k] S) (parameter : W)
    (surj : Function.Surjective eval)
    (divide : ∀ w : W, eval w = 0 → ∃ g : W, parameter * g = w)
    (specialize : ∀ {ι : Type} [Finite ι] (f : ι → W),
      Nonempty (RealizedNormalSpecialization eval parameter f)) : HasNormalRelationLifts k S := by
  classical
  intro ι _ x relations hx
  choose f hf using fun i => surj (x i)
  have vanishes (q : relations) : eval (MvPolynomial.aeval f q.val) = 0 := by
    rw [MvPolynomial.comp_aeval_apply]
    simpa only [hf] using hx q.val q.property
  choose g hg using fun q => divide (MvPolynomial.aeval f q.val) (vanishes q)
  obtain ⟨data⟩ := specialize (Sum.elim f g)
  letI : CommRing data.ambient := data.commRing
  letI : Algebra k data.ambient := data.algebra
  have h (q : relations) : data.realize parameter * data.realize (g q) =
      data.realize (MvPolynomial.aeval f q.val) := by
    rw [← map_mul, hg q]
  exact lift_of_divided_relations x relations data.realize eval _ f g hf h data.specialization

end WideEIntegralClosed
