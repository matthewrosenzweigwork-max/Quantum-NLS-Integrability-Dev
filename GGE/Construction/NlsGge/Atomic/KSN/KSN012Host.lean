import Mathlib
import NlsGge.Atomic.KSN.KSN001Host
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

                                                                                                                  
                                                                                                                        
                                                                                                                      
                                                                                                                     
                                                                                                                        
                                       
                                                                                                                     
                                                                                                                       
                                                
                                                                                               
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

def rawCoefficient (s : ℝ) (x : PairScale s) (b : Bool) (n : ℤ) : ℂ :=
  x (b, n) / (scaleWeight s n : ℂ)

theorem rawCoefficient_mem (s : ℝ) (hs : 0 ≤ s) (x : PairScale s) (b : Bool) :
  Memℓp (rawCoefficient s x b) 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [memℓp_gen_iff hp]
  have h := (memℓp_gen_iff hp).1 x.2
  have h2 := h.comp_injective (Prod.mk_right_injective b)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h2
  have hw : 1 ≤ NlsGge.ThirdConsultation.KSN.scaleWeight s n := by
    unfold NlsGge.ThirdConsultation.KSN.scaleWeight NlsGge.ThirdConsultation.KSN.bracket
    exact Real.one_le_rpow (le_max_left _ _) hs
  have hwn : 1 ≤ ‖((NlsGge.ThirdConsultation.KSN.scaleWeight s n : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    exact hw
  simp only [Function.comp_apply, NlsGge.ThirdConsultation.KSN.rawCoefficient]
  apply Real.rpow_le_rpow (norm_nonneg _) _ hp.le
  rw [norm_div]
  exact div_le_self (norm_nonneg _) hwn

def pairPotential (s : ℝ) (hs : 0 ≤ s) (x : PairScale s) : PotPair :=
  (physicalFourierL2.symm ⟨rawCoefficient s x true, rawCoefficient_mem s hs x true⟩,
   physicalFourierL2.symm ⟨rawCoefficient s x false, rawCoefficient_mem s hs x false⟩)

def complexDomain (s : ℝ) (hs : 0 ≤ s) : Set (PairScale s) :=
  {x | pairPotential s hs x ∈ sourceBetaW}

def IsRealPair (s : ℝ) (x : PairScale s) : Prop :=
  ∀ n : ℤ, rawCoefficient s x false n = star (rawCoefficient s x true (-n))

end
end NlsGge.ThirdConsultation.KSN
