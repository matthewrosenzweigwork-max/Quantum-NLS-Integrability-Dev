import Mathlib
import NlsGge.Birkhoff.F05Identity38

                                                                                                                                              
                                                                                                                                           
                                        
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure

namespace NlsGge.ThirdConsultation.F

theorem f008 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ)
    (hβ : ∀ j ≤ m, 0 < β j) :
    Continuous (Rm38 m β) ∧
    ∀ y : SobolevHilbert ((m - 1 : ℕ) : ℝ),
      Summable (fun n : ℤ =>
        |gapRemainderTermE02_38 (finiteWeightE02_38 m β)
          (sobolevToL2_38 (m - 1) y) n|) ∧
      0 ≤ Rm38 m β y := by
  obtain ⟨h1, h2, -⟩ := F04_spectral_lemma38 m hm β hβ
  exact ⟨h2, fun y => ⟨(h1 y).1, (h1 y).2⟩⟩

end NlsGge.ThirdConsultation.F
