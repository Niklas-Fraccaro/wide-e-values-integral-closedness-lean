import WideEIntegralClosed
import Lean.Util.CollectAxioms

/-! An axiom audit for the checked proof endpoints. -/

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let endpoints := #[
    ``WideEIntegralClosed.isIntegrallyClosed_of_hasNormalRelationLifts,
    ``WideEIntegralClosed.exists_preimage_of_polynomial_value,
    ``WideEIntegralClosed.factors_of_hasNormalRelationLifts,
    ``WideEIntegralClosed.normalSpecialization_of_fiber,
    ``WideEIntegralClosed.hasNormalRelationLifts_of_realizedSpecializations,
    ``WideEIntegralClosed.broadArithmeticFrameExistence_iff_single,
    ``WideEIntegralClosed.wideE_entireMatrix_two_sided_det_at_one_unit,
    ``WideEIntegralClosed.normalSpecialization_of_hopfFiberMap,
    ``WideEIntegralClosed.normalSpecialization_of_matrixPVFiber,
    ``WideEIntegralClosed.isIntegrallyClosed_valueSubring_of_broadArithmeticFrames_and_division]
  for endpoint in endpoints do
    let axioms ← collectAxioms endpoint
    let extra := axioms.filter fun name => !allowed.contains name
    unless extra.isEmpty do
      throwError m!"{endpoint} depends on unexpected axioms {extra.toList}"
  logInfo m!"Checked the axioms of {endpoints.size} declarations."
