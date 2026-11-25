import Mathlib
import NlsGge.Atomic.I.I038FiniteGap
import NlsGge.ThirdConsultation.I.FiniteGapLaws
import NlsGge.Atomic.I.I020
import NlsGge.Birkhoff.S04Moments38

                                                                                                                      
                                                                                                    
                                  
                                                                                                          
                                                                                                                   
                                                                                                                     
                                                                                                              
                                                                                                               
                                                                                                              
                                                                                                                   
                                                                                                                 
                                                                                 
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Sobolev38
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I038P

theorem pathwise (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W)
    (w : ℤ → ℝ) (hw0 : ∀ n, 0 ≤ w n)
    (hgap : ∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PhysicalL2,
      SobolevSquareSummable 1 (physicalFourier u) → ‖physFS38 1 u‖ ≤ B → ∀ n : ℤ,
        |gapRemainderTermE02_38 W u n| ≤ C * w n * actualGapActionAllE02_38 u n)
    (z : ℤ → ℂ) (hz1 : z ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (hzs : Summable (fun n : ℤ => w n * ‖z n‖ ^ 2))
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    Summable (fun n : ℤ => |gapRemainderTermE02_38 W (physicalOfSequence z) n|) ∧
    (∀ N : ℕ, 0 ≤ remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) ∧
    Tendsto (fun N : ℕ => remainderForWeight W (physicalOfSequence (projFin38 (Λ N) z))) atTop
      (𝓝 (remainderForWeight W (physicalOfSequence z))) ∧
    0 ≤ remainderForWeight W (physicalOfSequence z) := by
  have hW : Continuous W := hW2.continuous
  have hP : ∀ N : ℕ, projFin38 (Λ N) z ∈ seqSobolev38 ((1 : ℕ) : ℝ) := fun N =>
    finiteSupport_mem_seqSobolev38 _ _ (finite_support_projFin38 (Λ N) z)
  simp only [← hB]
  obtain ⟨Bd, hBd1, hBdN, hBdz⟩ := Bk.exists_H1_bound38 z hz1 hΛ
  obtain ⟨C, hC, hCb⟩ := hgap Bd (by linarith)
  have hs1 : ∀ v : ℤ → ℂ, v ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      SobolevSquareSummable 1 (physicalFourier (Bk.cleanΦinv v)) := fun v hv => by
    simpa using Bk.sobolev_cleanΦinv38 1 v hv
  have hdomz : ∀ n, |gapRemainderTermE02_38 W (Bk.cleanΦinv z) n| ≤ C * (w n * ‖z n‖ ^ 2) := by
    intro n
    have hb : ‖physFS38 1 (Bk.cleanΦinv z)‖ ≤ Bd := by
      rw [← NlsGge.ThirdConsultation.I.i020_norm_eq _ (hs1 z hz1)]; exact hBdz _
    have := hCb _ (hs1 z hz1) hb n
    rw [Bk.action_cleanΦinv38 z hz1 n] at this
    linarith [show C * w n * ‖z n‖ ^ 2 = C * (w n * ‖z n‖ ^ 2) by ring]
  have hdomN : ∀ N n, |gapRemainderTermE02_38 W (Bk.cleanΦinv (projFin38 (Λ N) z)) n| ≤
      C * (w n * ‖z n‖ ^ 2) := by
    intro N n
    have hb : ‖physFS38 1 (Bk.cleanΦinv (projFin38 (Λ N) z))‖ ≤ Bd := by
      rw [← NlsGge.ThirdConsultation.I.i020_norm_eq _ (hs1 _ (hP N))]; exact hBdN N _
    have := hCb _ (hs1 _ (hP N)) hb n
    rw [Bk.action_cleanΦinv38 _ (hP N) n] at this
    refine this.trans ?_
    have hle : ‖projFin38 (Λ N) z n‖ ^ 2 ≤ ‖z n‖ ^ 2 := by
      by_cases hn : n ∈ Λ N
      · rw [projFin38_apply_of_mem hn]
      · rw [projFin38_apply_of_not_mem hn, norm_zero, zero_pow two_ne_zero]; positivity
    have := mul_le_mul_of_nonneg_left hle (mul_nonneg hC (hw0 n))
    linarith [show C * w n * ‖z n‖ ^ 2 = C * (w n * ‖z n‖ ^ 2) by ring]
  have hbsum : Summable (fun n : ℤ => C * (w n * ‖z n‖ ^ 2)) := hzs.mul_left C
  -- termwise convergence
  have hT : Tendsto (fun N : ℕ => Bk.cleanTinvC 1 (projFin38 (Λ N) z)) atTop (𝓝 (Bk.cleanTinvC 1 z)) := by
    rw [Bk.cleanTinvC_of_mem 1 z hz1]
    refine (((Bk.continuous_TinvC 1).tendsto _).comp
      (tendsto_carrier_proj38 ((1 : ℕ) : ℝ) z hz1 hΛ)).congr (fun N => ?_)
    rw [Bk.cleanTinvC_of_mem 1 _ (hP N)]
    rfl
  have hterm : ∀ n : ℤ, Tendsto (fun N : ℕ => gapRemainderTermE02_38 W (Bk.cleanΦinv (projFin38 (Λ N) z)) n)
      atTop (𝓝 (gapRemainderTermE02_38 W (Bk.cleanΦinv z) n)) := by
    intro n
    have hg : Tendsto (fun N : ℕ => gapIntW38 W (Bk.cleanΦinv (projFin38 (Λ N) z)) n) atTop
        (𝓝 (gapIntW38 W (Bk.cleanΦinv z) n)) := by
      rw [Bk.gapIntW38_cleanΦinv38 W z hz1 n]
      refine (((BirkhoffTop38.continuous_gapFnW38 W hW n).tendsto _).comp hT).congr (fun N => ?_)
      rw [Bk.gapIntW38_cleanΦinv38 W _ (hP N) n]
      rfl
    have hI : ∀ᶠ N in atTop, actualGapActionAllE02_38 (Bk.cleanΦinv (projFin38 (Λ N) z)) n =
        actualGapActionAllE02_38 (Bk.cleanΦinv z) n := by
      filter_upwards [hΛ.eventually_mem n] with N hN
      rw [Bk.action_cleanΦinv38 _ (hP N), Bk.action_cleanΦinv38 _ hz1, projFin38_apply_of_mem hN]
    have hI' : Tendsto (fun N : ℕ => actualGapActionAllE02_38 (Bk.cleanΦinv (projFin38 (Λ N) z)) n)
        atTop (𝓝 (actualGapActionAllE02_38 (Bk.cleanΦinv z) n)) :=
      tendsto_const_nhds.congr' (hI.mono fun N hN => hN.symm)
    simp only [gapRemainderTerm_eq_gapIntW38 W hW]
    exact hg.sub (hI'.const_mul _)
  have hlim : Tendsto (fun N : ℕ => remainderForWeight W (Bk.cleanΦinv (projFin38 (Λ N) z))) atTop
      (𝓝 (remainderForWeight W (Bk.cleanΦinv z))) :=
    tendsto_tsum_of_dominated_convergence hbsum hterm
      (Filter.Eventually.of_forall fun N n => by rw [Real.norm_eq_abs]; exact hdomN N n)
  have hfinN : ∀ N : ℕ, 0 ≤ remainderForWeight W (Bk.cleanΦinv (projFin38 (Λ N) z)) := by
    intro N
    obtain ⟨hs, hfin, -⟩ := Bk.finiteGap_structure38 (Λ N) z
    exact (NlsGge.ThirdConsultation.I038F.finiteGap_remainder W hW2 hconv _ hs hfin).2.2
  refine ⟨Summable.of_nonneg_of_le (fun n => abs_nonneg _) hdomz hbsum, hfinN, hlim,
    ge_of_tendsto' hlim hfinN⟩

end NlsGge.ThirdConsultation.I038P
