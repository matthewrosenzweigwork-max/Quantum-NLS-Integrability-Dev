import NlsGge.Schur.ActualSchurQVDCompositionDerivativeMinimumV5_33
set_option autoImplicit false
noncomputable section
namespace NlsGge.Schur
/-- Isolate the module-parent identity needed to transfer the concrete
QVD derivative between the canonical CLM API and the normed-ring calculus. -/
theorem rootSchurDerivative_moduleParentCoherence36V1 (n : ℤ) :
    let E := ParityPair n →L[ℂ] ParityPair n
    let m : Module ℂ E := inferInstance
    let ns : NormedSpace ℂ E := ContinuousLinearMap.toNormedSpace
    ns.toModule = m := by
  rfl
/-- The operator-norm topology is the canonical continuous-linear-map
operator topology; this is a parent-data identity, not a spectral assumption. -/
theorem rootSchurDerivative_topologyParentCoherence36V1 (n : ℤ) :
    let E := ParityPair n →L[ℂ] ParityPair n
    let t : TopologicalSpace E := inferInstance
    let ng : NormedAddCommGroup E := ContinuousLinearMap.toNormedAddCommGroup
    ng.toUniformSpace.toTopologicalSpace = t := by
  rfl
end NlsGge.Schur
end
