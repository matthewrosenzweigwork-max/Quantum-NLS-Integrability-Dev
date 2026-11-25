import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.Atomic.M.M049Core
import NlsGge.Atomic.M.M049Coef
import NlsGge.ThirdConsultation.M.BirkhoffInverseHost

/- BIRKHOFF INVERSE POLY PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/ThirdConsultation/PDE/BirkhoffInversePoly.lean. Needs ROOT MAIN PROBE. Imports the topological core
   (PDE/BirkhoffTop: actualBirkhoffTop38, actualBirkhoffTop38_TinvC) and NOT the completed BirkhoffInput38 (r16 L1452
   acyclic order). `actualBirkhoffTop38_inverse_polynomial_of`: the r16 L619-626 conclusion VERBATIM
   (∃ C, 0 < C ∧ ∀ z, ‖TinvC m z‖ ≤ C (1+‖z‖)^(4m−2)), from `h49` = EXACTLY the M-049 MAIN head body (not the coarse
   existential-degree corollary), with C = 2D: TinvC m = actualTinvC38 m is the isometric Fourier image of
   birkhoffInverse m z; both inclusions have norm ≤ 1 (M049Aux.incl_norm_le); a + (1+b)^p c ≤ 2(1+a)^{p+1}. -/

set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.PDE

theorem actualBirkhoffTop38_inverse_polynomial_of
    (m : ℕ) (hm : 1 ≤ m)
    (h49 : ∃ D : ℝ, 0 < D ∧ ∀ z : NlsGge.ThirdConsultation.M.RealSobolevSequence m,
      ‖NlsGge.ThirdConsultation.M.birkhoffInverse m z‖ ≤
        D * (‖z‖ +
          (1 + ‖NlsGge.Birkhoff.carrierIncl38
            (r := 1) (s := (m : ℝ)) (by exact_mod_cast hm) z‖) ^ (4 * m - 3) *
            ‖NlsGge.Birkhoff.carrierIncl38
              (r := 0) (s := (m : ℝ)) (by positivity) z‖)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : NlsGge.Sobolev38.SobolevCarrier38 (m : ℝ),
        ‖actualBirkhoffTop38.TinvC m z‖ ≤
          C * (1 + ‖z‖) ^ (4 * m - 2) := by
  obtain ⟨D, hD, hb⟩ := h49
  refine ⟨2 * D, by positivity, fun z => ?_⟩
  have hT : ‖actualBirkhoffTop38.TinvC m z‖ = ‖NlsGge.ThirdConsultation.M.birkhoffInverse m z‖ := by
    rw [actualBirkhoffTop38_TinvC]
    exact (physicalSobolevFourierEquiv38 (m : ℝ)).norm_map _
  rw [hT]
  have h1 := NlsGge.ThirdConsultation.M049Aux.incl_norm_le (r := 1) (s := (m : ℝ))
    (by exact_mod_cast hm) z
  have h0 := NlsGge.ThirdConsultation.M049Aux.incl_norm_le (r := 0) (s := (m : ℝ))
    (by positivity) z
  have hp := NlsGge.ThirdConsultation.M049Aux.poly_alg ‖z‖ _ _ (4 * m - 3)
    (norm_nonneg _) (norm_nonneg _) h1 h0
  rw [show 4 * m - 3 + 1 = 4 * m - 2 by omega] at hp
  calc _ ≤ _ := hb z
    _ ≤ D * (2 * (1 + ‖z‖) ^ (4 * m - 2)) := mul_le_mul_of_nonneg_left hp hD.le
    _ = 2 * D * (1 + ‖z‖) ^ (4 * m - 2) := by ring

end NlsGge.ThirdConsultation.PDE
