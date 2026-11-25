import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS003Host
import NlsGge.ThirdConsultation.KSPS.KSPS003Support2

/- KSPS-003 PRODUCTION02 (proof development, AUTHOR; not reviewed; target NlsGge/Atomic/KSPS/KSPS003.lean).
   Head verbatim from Pro round 6 (c5547100) section 10A (round 10 leaves it unchanged), with the lexical
   repair `open scoped Matrix.Norms.L2Operator` (the house L2 operator norm, = the source's Euclidean operator norm).
   Proof: entrywise bounds of KSPS003Support2 (scalar IBP argument in KSPS003Support1). -/
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem second_volterra_remainder_bound :
  ∃ C : ℝ, 0 < C ∧ ∀ (φ : SobolevC 1)
    (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 →
    ∀ lam : ℂ, lam ≠ 0 →
      ‖secondVolterraRemainder φ x lam‖ ≤
        C * Real.exp (|lam.im| * x) * sobolevNorm 1 φ ^ 2 / ‖lam‖ ^ 2 := by
  refine ⟨(‖NlsGge.GKDefinitionDesign.iotaCLM‖ + ‖NlsGge.GKDefinitionDesign.derivCLM‖) ^ 2 + 1,
    by positivity, fun φ x hx lam hlam => ?_⟩
  exact NlsGge.ThirdConsultation.KSPS003Support2.remainder_matrix_bound φ hx hlam

end
end NlsGge.ThirdConsultation.KSPS
