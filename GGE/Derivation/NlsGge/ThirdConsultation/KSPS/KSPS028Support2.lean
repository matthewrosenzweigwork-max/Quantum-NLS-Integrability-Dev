import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS020Host
import NlsGge.ThirdConsultation.M.M053Host
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1

/- KSPS-028 SUPPORT2 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS028Support2.lean.
   The two real-type facts used by KSPS-028, derived from `NlsGge.ThirdConsultation.MRiccati.RealPair φ`
   (OWNER DECISION 18 binder): toPotPair φ = realSlice u (u = (toPotPair φ).1), so
   (i) lamPlus/lamMinus (realSlice u) n are the real gap edges (GK38.lamPlus_real) with lamMinus <= lamPlus
       (GK38.periodic_pair_re_order38);
   (ii) hat phi2(n) = hat (star u)(n) = star hat u(-n) (Schur.physicalFourier_star38). -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS028Q
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS

theorem real_facts {N : ℕ} (φ : SobolevC N) (hφ : NlsGge.ThirdConsultation.MRiccati.RealPair φ) :
    (∀ n : ℤ, ∃ U L : ℝ, L ≤ U ∧ periodicPlus φ n = (U : ℂ) ∧ periodicMinus φ n = (L : ℂ)) ∧
    (∀ n : ℤ, physicalFourier (toPotPair φ).2 n = star (physicalFourier (toPotPair φ).1 (-n))) := by
  have hT : toPotPair φ = realSlice (NlsGge.ThirdConsultation.MRiccati.realPhysicalFromPair φ) := hφ
  constructor
  · intro n
    obtain ⟨hp, hm⟩ := lamPlus_real (NlsGge.ThirdConsultation.MRiccati.realPhysicalFromPair φ) n
    have hord := periodic_pair_re_order38 (NlsGge.ThirdConsultation.MRiccati.realPhysicalFromPair φ) n
    rw [hp, hm, Complex.ofReal_re, Complex.ofReal_re] at hord
    refine ⟨_, _, hord, ?_, ?_⟩
    · unfold periodicPlus; rw [hT]; exact hp
    · unfold periodicMinus; rw [hT]; exact hm
  · intro n
    have h2 : (toPotPair φ).2 = star (toPotPair φ).1 := by
      rw [hT]; exact NlsGge.GK38.realSlice_snd _
    rw [h2]
    exact NlsGge.Schur.physicalFourier_star38 _ n

end
end NlsGge.ThirdConsultation.KSPS028Q
