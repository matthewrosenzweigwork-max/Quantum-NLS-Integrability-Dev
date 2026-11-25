import Mathlib
import NlsGge.Atomic.M.M016ChartFinal
import NlsGge.Atomic.M.M052
import NlsGge.ThirdConsultation.M.FiniteGapPair

/- M016CHARTFINALHEAD PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target NlsGge/Atomic/M/M016ChartFinalHead.lean.
   Needs ROOT MAIN PROBE (imports M052, FiniteGapPair host). Pro R16 §1.1 head VERBATIM (L49-58).
   Proof: the R14 bodies are definitionally the unfolded statement of
   `finitegap_pair_primitive_meromorphic_infinity_unfolded`; if the M-052 host bodies differ from R14
   (`ExteriorPrimitiveRepresentative φ R F := 0 < R ∧ ∀ z, R < ‖z‖ → ∃ hz, F z = primitive ⟨(φ, z), hz⟩`,
   `finiteGapPair φ := {n | gap φ n ≠ 0}.Finite`), this term must be adjusted. -/
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem finitegap_pair_primitive_meromorphic_infinity
    (φ : PotPair) (hW : φ ∈ gkW) (hfg : finiteGapPair φ) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      ExteriorPrimitiveRepresentative φ R F ∧
      MPrimitive.ExteriorHolomorphic F ∧
      AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z) ∧
      MPrimitive.HasValueAtInfinity (fun z : ℂ => F z + Complex.I * z) 0 :=
  finitegap_pair_primitive_meromorphic_infinity_unfolded φ hW hfg

end NlsGge.ThirdConsultation.M
