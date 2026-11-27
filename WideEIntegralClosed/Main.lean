import WideE.LaurentExistence
import WideEIntegralClosed.RamifiedDescent

/-! The integral closedness theorem relative to the arithmetic Frobenius input. -/

namespace WideEIntegralClosed

/-- The ring of broad Siegel E-values is integrally closed if the broad arithmetic
Frobenius frames used in the paper exist. Division is supplied by `WideE`. -/
theorem isIntegrallyClosed_valueSubring_of_broadArithmeticFrames
    (frames : BroadArithmeticFrameExistence) : IsIntegrallyClosed WideE.valueSubring :=
  isIntegrallyClosed_valueSubring_of_broadArithmeticFrames_and_division frames
    (fun _ hf hz => WideE.wideEFunction_divAtOne hf hz)

end WideEIntegralClosed
