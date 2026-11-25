import NlsGge.Schur.FourierMultiplier

set_option autoImplicit false
open MeasureTheory

namespace NlsGge.Schur

/-- The actual doubled-circle Haar measure is a probability measure. This
public fact lets downstream representatives install the pinned finiteness
instance without relying on a file-local instance. -/
theorem spectralHaar_isProbabilityMeasure : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

end NlsGge.Schur
