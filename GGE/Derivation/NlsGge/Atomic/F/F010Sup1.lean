import Mathlib
import NlsGge.Atomic.F.F010Host
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6024Sup2Core
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.NLS38.PhysicalFlow38

/- F010 SUP1 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/F/F010Sup1.lean. Supporting lemmas for packet F-010 (no packet increment), about the hosted
   literal inverse `inverseOnSobolev m = FinvH38 m ∘ finiteTInv m` of the fixed G6 map, for 2 ≤ m:
   * continuous_inverseOnSobolev: from G6027 (m-1) conjunct 2 (analyticity of inverseBirkhoffSobolev).
   * sobolevToL2_inverseOnSobolev: the realized field is physicalSobolevEmbed (m-1) of the G6 inverse
     (reflected coefficients undone by FinvH38; G6024S.fourierSeq38_eq, physicalSobolevEmbed_fourier).
   * physicalBirkhoff_inverseOnSobolev: Φ(sobolevToL2_38 (m-1) (inverseOnSobolev m w)) n = w n, from G6027
     conjuncts 4 (RightInverse) and 5 (Sobolev/L² compatibility) and sequenceSobolevEmbed_coe.
   Needs ROOT MAIN PROBE (G6027 and the G6 Sobolev hosts are absent from the worker mirror). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.F010Aux

theorem continuous_inverseOnSobolev (m : ℕ) (hm : 2 ≤ m) :
    Continuous (NlsGge.ThirdConsultation.F.inverseOnSobolev m) := by
  have hk : 1 ≤ m - 1 := by omega
  have hc : Continuous (inverseBirkhoffSobolev (m - 1)) :=
    continuousOn_univ.mp (G6027 (m - 1) hk).2.1.continuousOn
  exact (continuous_FinvH38 m).comp ((continuous_ofCarrier38 _).comp
    ((physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)).continuous.comp
      (hc.comp (continuous_toCarrier38 _))))

theorem sobolevToL2_inverseOnSobolev (m : ℕ) (w : Hm1 m) :
    sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSobolev m w) =
      physicalSobolevEmbed (m - 1) (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w)) := by
  apply NlsGge.NLS38.physicalFourier_injective38
  funext j
  rw [sobolevToL2_38_fourier]
  have h1 := NlsGge.ThirdConsultation.G6024S.fourierSeq38_eq
    (physicalSobolevEmbed (m - 1) (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w))) (-j)
  rw [physicalSobolevEmbed_fourier, neg_neg] at h1
  change -(carrierCoe38 ((m - 1 : ℕ) : ℝ) (physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)
    (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w))) (-j)) = _
  rw [h1, neg_neg]

theorem physicalBirkhoff_inverseOnSobolev (m : ℕ) (hm : 2 ≤ m) (w : Hm1 m) (n : ℤ) :
    physicalBirkhoff (sobolevToL2_38 (m - 1) (NlsGge.ThirdConsultation.F.inverseOnSobolev m w)) n =
      (show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from w) n := by
  have hk : 1 ≤ m - 1 := by omega
  obtain ⟨-, -, -, hR, hfwd, -⟩ := G6027 (m - 1) hk
  have hC : physicalBirkhoff (physicalSobolevEmbed (m - 1)
      (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w))) =
      sequenceSobolevEmbed (m - 1) (toCarrier38 _ w) := by
    rw [← (hfwd (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ w))).2, hR (toCarrier38 _ w)]
  rw [sobolevToL2_inverseOnSobolev, hC]
  exact congrFun (sequenceSobolevEmbed_coe (m - 1) (toCarrier38 _ w)) n

end NlsGge.ThirdConsultation.F010Aux
