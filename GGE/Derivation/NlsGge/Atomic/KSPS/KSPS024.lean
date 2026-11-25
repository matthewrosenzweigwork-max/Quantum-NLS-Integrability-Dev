import Mathlib
import NlsGge.Atomic.KSPS.KSPS017
import NlsGge.Atomic.KSPS.KSPS019
import NlsGge.ThirdConsultation.KSPS.KSPS024Support

/- KSPS-024 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/KSPS/KSPS024.lean.
   Head: followup12 STATEMENTS/KSPS.md "KSPS-024 -- critical spectral expansion" (Pro round 14 Cluster 1 audit-F2 row:
   "KSPS-024 ... unchanged with their hN/reality/normalization"), theorem `critical_spectral_expansion`, VERBATIM.
   Proof: KSPS024W.crit_localization_of turns the landed KSPS-019 head into |lamDot_n - n pi| <= a / indexWeight n for
   all n; the landed KSPS-017 head at xi = criticalEigenvalue discharges the explicit hypothesis of
   KSPS024W.critical_spectral_expansion_of (KSPS-022 content enters through KSPS023T, the landed native re-proof of
   the private landed `ksps022_consistent`). No hypothesis added. NOT COMPILED IN THE WORKER LANE (closure exceeds the
   lane memory cap): READY FOR ROOT MAIN PROBE; the identical term is compiled against the landed head TYPES in
   KSPS024_GLUETEST01. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem critical_spectral_expansion
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) :
  WeightedL2Error (N+1)
    (fun n => criticalEigenvalue φ n - spectralPolynomial φ n) := by
  obtain ⟨a, ha, hxi⟩ :=
    NlsGge.ThirdConsultation.KSPS024W.crit_localization_of rough_boundary_roots hN φ
  exact NlsGge.ThirdConsultation.KSPS024W.critical_spectral_expansion_of N hN φ a ha hxi
    (discriminant_derivative_WKB N hN φ (criticalEigenvalue φ) ⟨a, ha, hxi⟩)

end
end NlsGge.ThirdConsultation.KSPS
