import Mathlib
import NlsGge.ThirdConsultation.T.T027Host
import NlsGge.ThirdConsultation.T.T028Host
import NlsGge.Atomic.T.T027
import NlsGge.Atomic.I.I038Charge
import NlsGge.Birkhoff.W12Tilt38g
import NlsGge.Birkhoff.S01Equivariance38b
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

                                                                                                                
                                                                                                 
                                                                                                                   
                                                                                                                 
                                                                                                                  
                                                                             
                                                                                                                    
                                                                                                                 
                                                                                                                   
                                                                                                                    
                                                                                                        
                                                                                                                           
                                                                                                                   
                                                                                                                 
                                                                                                                    
                                                              
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.T

theorem t028_evenCharge_eq_local {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s)
    (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (hUu : smoothL2_38 U hU hper = physicalInclusion c s x) (j : ℕ) :
    evenCharge j (physicalInclusion c s x) = localCharge38 U j :=
  NlsGge.ThirdConsultation.I038C.chargeFn_eq_local (physicalInclusion c s x)
    (fun m => sobolev_physOfE38 c s (m : ℝ) x) U hU hper hUu (max 2 (j + 1)) j
    (le_max_left _ _) ((Nat.le_succ j).trans (le_max_right _ _))

theorem t028_localCharge_nonneg (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1) (j : ℕ) :
    0 ≤ localCharge38 U j :=
  (pow_nonneg (localCharge38_nonneg U hU hper) (j + 1)).trans (localCharge38_mass_le38 U hU hper j)

/-- The ENNReal identity (monotone convergence, via the landed `EB38_eq_chargeSeries`) together with
nonnegativity of every term. -/
theorem t028_EB38_eq_series {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s) :
    EB38 c.val (physicalInclusion c s x) =
      ∑' j : ℕ, ENNReal.ofReal
        (coefficient c.val (j + 1) * evenCharge j (physicalInclusion c s x)) ∧
    ∀ j : ℕ, 0 ≤ coefficient c.val (j + 1) * evenCharge j (physicalInclusion c s x) := by
  obtain ⟨U, hU, hper, hUu⟩ := exists_smooth_rep38 (physicalInclusion c s x)
    (fun m => sobolev_physOfE38 c s (m : ℝ) x)
  have hQ := t028_evenCharge_eq_local c s x U hU hper hUu
  refine ⟨?_, fun j => ?_⟩
  · rw [← hUu, EB38_eq_chargeSeries c U hU hper, hUu]
    unfold chargeSeriesW38
    refine tsum_congr (fun j => ?_)
    rw [coefficient_bCoef38, hQ j]
  · rw [hQ j, ← coefficient_bCoef38]
    exact mul_nonneg (coefficient_bCoef_nonneg38 c j) (t028_localCharge_nonneg U hU hper j)

/-- A nonnegative real sequence whose `ofReal` series is finite has the real sum `toReal`. -/
theorem t028_hasSum_toReal (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hfin : ∑' j : ℕ, ENNReal.ofReal (f j) ≠ ⊤) :
    HasSum f (∑' j : ℕ, ENNReal.ofReal (f j)).toReal := by
  have hcoe : ∀ j, ENNReal.ofReal (f j) = ((Real.toNNReal (f j) : NNReal) : ℝ≥0∞) := fun j => rfl
  simp_rw [hcoe] at hfin
  have hsNN : Summable (fun j => Real.toNNReal (f j)) := ENNReal.tsum_coe_ne_top_iff_summable.1 hfin
  have hs : Summable f := by
    have := NNReal.summable_coe.2 hsNN
    refine this.congr (fun j => ?_)
    exact Real.coe_toNNReal _ (hf j)
  rw [← ENNReal.ofReal_tsum_of_nonneg hf hs, ENNReal.toReal_ofReal (tsum_nonneg hf)]
  exact hs.hasSum

theorem lowerEnergy_eq_chargeSeries
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4)
    (x : ECarrier38 c s) :
    EB38 c.val (physicalInclusion c s x) ≠ ⊤ ∧
    EB38 c.val (physicalInclusion c s x) =
      ∑' j : ℕ, ENNReal.ofReal
        (coefficient c.val (j + 1) * evenCharge j (physicalInclusion c s x)) ∧
    HasSum (fun j : ℕ => coefficient c.val (j + 1) *
      evenCharge j (physicalInclusion c s x)) (lowerEnergy c s x) := by
  have hfin : EB38 c.val (physicalInclusion c s x) ≠ ⊤ :=
    (lowerEnergy_finite_continuous lo up c s hs hs').1 x
  obtain ⟨heq, hnn⟩ := t028_EB38_eq_series c s x
  refine ⟨hfin, heq, ?_⟩
  have h := t028_hasSum_toReal _ hnn (heq ▸ hfin)
  rw [← heq] at h
  exact h

end NlsGge.ThirdConsultation.T
