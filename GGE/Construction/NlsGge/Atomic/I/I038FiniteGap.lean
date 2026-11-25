import Mathlib
import NlsGge.Atomic.I.I014
import NlsGge.Birkhoff.H02Hierarchy38b
import NlsGge.ThirdConsultation.I.RemainderWeight

                                                                                                               
                                                                                                                    
                                  
                                                                                                         
                                                                                                                 
                                                                                                                    
                                                                                                                       
                                                                                                   
                                                                                               
                                                                                                                                            
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Birkhoff
open NlsGge.Atomic.I010 (spectralEnergy)

namespace NlsGge.ThirdConsultation.I038F

theorem sum_gapInt_eq (W : ℝ → ℝ) (hW : Continuous W) (u : PhysicalL2)
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) :
    ∑ n ∈ hfin.toFinset, gapIntW38 W u n =
      (2 / Real.pi) * ∫ l : ℝ, W (2 * l) * actualGapHeightE02_38 u l := by
  set F := hfin.toFinset with hF
  have hv : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hlev : ∀ n : ℤ, ∀ x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n),
      actualQuasimomentumRealPartE02_38 u x = (n : ℝ) * Real.pi := by
    intro n x hx
    have := (actualGapLevelSet_eq_Icc_E02_38 u n).2
    rw [← this] at hx
    exact hx
  set f : ℝ → ℝ := fun l => W (2 * l) * actualGapHeightE02_38 u l with hf
  have hfc : Continuous f := (hW.comp (continuous_const.mul continuous_id)).mul hv
  have hpt : ∀ l : ℝ, f l = ∑ n ∈ F, (Set.Ioo (actualGapLowerAllE02_38 u n)
      (actualGapUpperAllE02_38 u n)).indicator f l := by
    intro l
    by_cases h0 : actualGapHeightE02_38 u l = 0
    · have : f l = 0 := by simp [hf, h0]
      rw [this]
      symm; apply Finset.sum_eq_zero; intro n _
      apply Set.indicator_apply_eq_zero.mpr; intro _; simp [hf, h0]
    · obtain ⟨n0, hn0⟩ := actualGapHeight_mem_gap_of_ne_zero_E02_38 u l h0
      have hn0F : n0 ∈ F := by
        rw [hF, Set.Finite.mem_toFinset]; exact hn0.1.trans hn0.2
      rw [Finset.sum_eq_single n0]
      · rw [Set.indicator_of_mem hn0]
      · intro m _ hm
        apply Set.indicator_of_notMem
        intro hmem
        have h1 := hlev n0 l ⟨hn0.1.le, hn0.2.le⟩
        have h2 := hlev m l ⟨hmem.1.le, hmem.2.le⟩
        have : (n0 : ℝ) = m := by
          have := h1.symm.trans h2
          exact mul_right_cancel₀ Real.pi_ne_zero this
        exact hm (by exact_mod_cast this.symm)
      · intro h; exact absurd hn0F h
  have hint : ∀ n ∈ F, Integrable ((Set.Ioo (actualGapLowerAllE02_38 u n)
      (actualGapUpperAllE02_38 u n)).indicator f) := by
    intro n _
    rw [integrable_indicator_iff measurableSet_Ioo]
    exact hfc.continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  have hint2 : ∫ l : ℝ, f l = ∑ n ∈ F, ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n), f x := by
    have h1 : ∫ l : ℝ, f l = ∫ l : ℝ, ∑ n ∈ F, (Set.Ioo (actualGapLowerAllE02_38 u n)
        (actualGapUpperAllE02_38 u n)).indicator f l := integral_congr_ae
      (Filter.Eventually.of_forall hpt)
    rw [h1, integral_finsetSum _ hint]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hlt : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n := by
      rw [hF, Set.Finite.mem_toFinset] at hn; exact hn
    rw [integral_indicator measurableSet_Ioo, intervalIntegral.integral_of_le hlt.le,
      integral_Ioc_eq_integral_Ioo]
  rw [hint2, Finset.mul_sum]
  rfl

theorem finiteGap_remainder (W : ℝ → ℝ) (hW2 : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W)
    (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite) :
    Summable (fun n : ℤ => gapRemainderTermE02_38 W u n) ∧
    NlsGge.ThirdConsultation.I.remainderForWeight W u =
      spectralEnergy W u - ∑' n : ℤ, W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n ∧
    0 ≤ NlsGge.ThirdConsultation.I.remainderForWeight W u := by
  have hW : Continuous W := hW2.continuous
  obtain ⟨-, -, hsumA, -⟩ := NlsGge.Atomic.I009.finiteGap_convex_difference u hu hfin W hW2 hconv
  have hle := (NlsGge.Atomic.I014.i014 u hu hfin W hW2 hconv).2.2.2.2.2.2.2.2.2
  have hG0 : ∀ n ∉ hfin.toFinset, gapIntW38 W u n = 0 := by
    intro n hn
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hn
    have : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n :=
      le_antisymm (actualGapLower_le_upper38' u n) hn
    unfold gapIntW38
    rw [this, intervalIntegral.integral_same, mul_zero]
  have hGs : Summable (fun n : ℤ => gapIntW38 W u n) := summable_of_ne_finset_zero hG0
  have heq : ∀ n, gapRemainderTermE02_38 W u n =
      gapIntW38 W u n - W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n :=
    fun n => gapRemainderTerm_eq_gapIntW38 W hW u n
  have hsumR : Summable (fun n : ℤ => gapRemainderTermE02_38 W u n) :=
    (hGs.sub hsumA).congr (fun n => (heq n).symm)
  have hR : NlsGge.ThirdConsultation.I.remainderForWeight W u =
      spectralEnergy W u - ∑' n : ℤ, W (2 * Real.pi * (n : ℝ)) * actualGapActionAllE02_38 u n := by
    unfold NlsGge.ThirdConsultation.I.remainderForWeight
    rw [tsum_congr heq, hGs.tsum_sub hsumA, tsum_eq_sum hG0, sum_gapInt_eq W hW u hfin]
    rfl
  refine ⟨hsumR, hR, ?_⟩
  rw [hR]
  linarith

end NlsGge.ThirdConsultation.I038F
