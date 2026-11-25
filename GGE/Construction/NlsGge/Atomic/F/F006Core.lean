import Mathlib
import NlsGge.Spectral.F04Lemma38
import NlsGge.Spectral.F04LiteralBounds38
import NlsGge.Schur.PhysicalH1ComplexCarrierSchurBridge
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.NLS38.SolutionNotion38
import NlsGge.NLS38.PhysicalFlow38

                                                                                                 
                                                                                           
                                                                                                             
                                                                                                              
                                                                                                    
                                                                                                           
                                                                    
                                                                                     
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core NlsGge.Schur
open NlsGge.SpectralFoundations NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.F006Aux

theorem ball_bound (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (Φ : PhysicalL2 → ℤ → ℂ)
    (hact : ∀ (u : PhysicalL2) (n : ℤ), actualGapActionAllE02_38 u n = ‖Φ u n‖ ^ 2)
    (hpre : ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
      ∃ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)),
        physicalH1ComplexCarrierToL2Actual22 w = u ∧ ‖w‖ = ‖physicalSobolevL2 1 u hu‖)
    (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u)),
        ‖physicalSobolevL2 1 u hu‖ ≤ B → ∀ n : ℤ,
          actualGapActionAllE02_38 u n = ‖Φ u n‖ ^ 2 ∧
          |gapRemainderTermE02_38 (finiteWeightE02_38 m β) u n| ≤
            C * japaneseBracket n ^ (2 * m - 2) * ‖Φ u n‖ ^ 2 := by
  obtain ⟨C, hC, hCb⟩ := gapRemainderTerm_le_action38 m hm β hβ (max 1 B) (le_max_left 1 B)
  refine ⟨C, hC, fun u hu hnorm n => ⟨hact u n, ?_⟩⟩
  obtain ⟨w, hw, hnw⟩ := hpre u hu
  have hwB : ‖w‖ ≤ max 1 B := by
    rw [hnw]; exact hnorm.trans (le_max_right 1 B)
  have key := hCb w hwB n
  rw [hw, hact] at key
  exact key

theorem summable_abs (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (y : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ =>
      |gapRemainderTermE02_38 (finiteWeightE02_38 m β) (sobolevToL2_38 (m - 1) y) n|) :=
  ((F04_spectral_lemma38 m hm β hβ).1 y).1

theorem fourierSeq_mem (k : ℕ) (y : SobolevHilbert (k : ℝ)) :
    fourierSeq38 (sobolevToL2_38 k y) ∈ seqSobolev38 (k : ℝ) := by
  rw [NlsGge.NLS38.fourierSeq38_eq_refl38]
  exact NlsGge.NLS38.refl_mem_seqSobolev38
    ((mem_seqSobolev38_iff _ _).2 (sobolevToL2_38_sobolev k y))

end NlsGge.ThirdConsultation.F006Aux
