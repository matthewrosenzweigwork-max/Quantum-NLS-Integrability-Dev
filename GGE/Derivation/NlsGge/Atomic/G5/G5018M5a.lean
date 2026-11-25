import Mathlib
import NlsGge.Atomic.G5.G5018M5Ep
import NlsGge.Atomic.G3.G3031All

/- G5-018 M5a `G5018M5a` (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5018M5a.lean, namespace NlsGge.GKDefinitionDesign.
   Head `g5018_diagonal_local_lift` VERBATIM from Pro round 13 section 6 (M5a): the worker-lane-tested
   `g5018_diagonal_local_lift_of_beta` (G5018M5Ep) applied to landed `betaSum_analyticOnNhd_sourceBetaW`
   (G3031All; inline closure exceeds worker-lane memory, so this file needs a main-lane check by root). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38


namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5018_diagonal_local_lift
    (u : PhysicalL2) (n : ℤ)
    (hn : gamma2 (realSlice u) n ≠ 0) :
    ∃ (V : Set PotPair) (e : PotPair → ℂ),
      IsOpen V ∧ realSlice u ∈ V ∧
      V ⊆ sourceBetaW \ collapsedSet n ∧
      AnalyticOnNhd ℂ e V ∧
      (∀ φ ∈ V, ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        Complex.exp (Complex.I * e φ) = s * etaExponential n φ) ∧
      ∀ φ ∈ V,
        angleDerivative n φ - fderiv ℂ (betaSum n) φ = fderiv ℂ e φ :=
  g5018_diagonal_local_lift_of_beta u n hn (betaSum_analyticOnNhd_sourceBetaW n)

end
end NlsGge.GKDefinitionDesign
