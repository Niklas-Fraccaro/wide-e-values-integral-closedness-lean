import WideEIntegralClosed.IntegralClosedness
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let endpoints := #[
    ``WideEIntegralClosed.subfactorial_binomial_rational,
    ``WideEIntegralClosed.binomialPrefixDenominators_ratCast,
    ``WideEIntegralClosed.hasBroadRetainedFourierDenominators,
    ``WideEIntegralClosed.broadArithmeticFrameExistence,
    ``WideEIntegralClosed.isIntegrallyClosed_valueSubring,
    ``WideEIntegralClosed.valueSubring_factors_of_finitePresentation,
    ``WideEIntegralClosed.valueSubring_preimage_of_polynomial,
    ``WideEIntegralClosed.valueSubring_preimage_of_pow]
  for endpoint in endpoints do
    let axioms ← collectAxioms endpoint
    let extra := axioms.filter fun name => !allowed.contains name
    unless extra.isEmpty do
      throwError m!"{endpoint} depends on unexpected axioms {extra.toList}"
  logInfo m!"Checked the axioms of {endpoints.size} declarations in the unconditional proof."
