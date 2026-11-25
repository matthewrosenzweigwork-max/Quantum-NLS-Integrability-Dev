import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.Atomic.G6.G6025SupCore
import NlsGge.Atomic.KSN.KSN019
import NlsGge.Atomic.KSN.KSN001Sup1

                                                                                                         
                                                                                                                  
                                                                                                                     
                                                                                                                        
                                                                                                                       
                                                                                                        
                                                                                                             
                                                                   
                                                                                                 
                                                                                                                   

set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.PDE

open NlsGge.ThirdConsultation.G6024S

theorem smooth_coord (r : ℕ) (hr : 1 ≤ r) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 (r : ℝ)) (n : ℤ) :
    actualT38 x n - x n =
      fromSeqEq (r + 1) (complexSmoothing r (toPair r (carrierMk38 (r : ℝ) x hx))) n := by
  set z : SobolevCarrier38 (r : ℝ) := carrierMk38 (r : ℝ) x hx with hzdef
  set u : PhysicalSobolev38 (r : ℝ) := (physicalSobolevFourierEquiv38 (r : ℝ)).symm z with hudef
  have hz : physicalSobolevFourierEquiv38 (r : ℝ) u = z := by
    rw [hudef]; exact LinearIsometryEquiv.apply_symm_apply _ z
  have hv : fourierSeq38 (physicalSobolevEmbed r u) = x := funext fun k => by
    rw [physicalSobolevEmbed_fourier, hz, hzdef, carrierCoe38_mk]
  have hT : actualT38 x = (physicalBirkhoff (physicalSobolevEmbed r u) : ℤ → ℂ) := by
    rw [← hv]
    exact actualT38_fourierSeq38 _
  have hSR := NlsGge.ThirdConsultation.KSN.KSN001Aux.scalarBirkhoff_realSlice
  have hcoord := birkhoff_coord r u hSR n
  rw [hz] at hcoord
  rw [hT, hcoord, hzdef, carrierCoe38_mk, add_sub_cancel_left]
  -- smoothingCoefficient = stored / weight
  have hdom : toPair r z ∈ complexDomain (r : ℝ) (Nat.cast_nonneg r) := by
    have := toPair_mem_complexDomain r u
    rwa [hz] at this
  have hmem := ((KSN019_main r hr).2.1 _ hdom).1
  have hcs : complexSmoothing r (toPair r z) =
      ⟨storedSequence ((r : ℝ) + 1) (smoothingCoefficient r (toPair r z)), hmem⟩ := by
    unfold complexSmoothing sequenceLift
    rw [dif_pos hmem]
  have hw : ((scaleWeight ((r + 1 : ℕ) : ℝ) n : ℝ) : ℂ) ≠ 0 := by
    have : 0 < scaleWeight ((r + 1 : ℕ) : ℝ) n := by
      rw [sw_eq]; exact pow_pos (lt_of_lt_of_le one_pos (bracket_one_le _)) _
    exact_mod_cast this.ne'
  rw [← hzdef, hcs]
  show _ = storedSequence ((r : ℝ) + 1) (smoothingCoefficient r _) (true, n) / _
  unfold storedSequence
  rw [show ((r : ℝ) + 1) = ((r + 1 : ℕ) : ℝ) by push_cast; ring]
  field_simp

theorem actualT38_smooth_top (r : ℕ) (hr : 1 ≤ r) :
    ∀ x ∈ seqSobolev38 (r : ℝ),
      actualBirkhoffTop38.T x - x ∈ seqSobolev38 ((r + 1 : ℕ) : ℝ) := by
  intro x hx
  have e : actualBirkhoffTop38.T x - x =
      fromSeqEq (r + 1) (complexSmoothing r (toPair r (carrierMk38 (r : ℝ) x hx))) :=
    funext fun n => by
      show actualT38 x n - x n = _
      exact smooth_coord r hr x hx n
  rw [e]
  exact fromSeqEq_mem (r + 1) _

theorem actualT38_analytic_smooth_top (r : ℕ) (hr : 1 ≤ r) :
    AnalyticOnNhd ℝ
      (carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun x => actualBirkhoffTop38.T x - x)
        (actualT38_smooth_top r hr)) Set.univ := by
  have heq : carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ) (fun x => actualBirkhoffTop38.T x - x)
      (actualT38_smooth_top r hr) = fun z => fromPairEq (r + 1) (complexSmoothing r (toPair r z)) := by
    funext z
    apply carrierExt38
    funext n
    rw [carrierMap38_coe]
    show actualT38 (carrierCoe38 (r : ℝ) z) n - carrierCoe38 (r : ℝ) z n =
      fromSeqEq (r + 1) (complexSmoothing r (toPair r z)) n
    have hzz : carrierMk38 (r : ℝ) (carrierCoe38 (r : ℝ) z) (carrierCoe38_mem (r : ℝ) z) = z :=
      carrierExt38 rfl
    have h := smooth_coord r hr (carrierCoe38 (r : ℝ) z) (carrierCoe38_mem (r : ℝ) z) n
    rw [hzz] at h
    exact h
  rw [heq]
  intro z _
  set u : PhysicalSobolev38 (r : ℝ) := (physicalSobolevFourierEquiv38 (r : ℝ)).symm z with hudef
  have hz : physicalSobolevFourierEquiv38 (r : ℝ) u = z := by
    rw [hudef]; exact LinearIsometryEquiv.apply_symm_apply _ z
  have hdom : toPair r z ∈ complexDomain (r : ℝ) (Nat.cast_nonneg r) := by
    have := toPair_mem_complexDomain r u
    rwa [hz] at this
  have hC : AnalyticAt ℝ (complexSmoothing r) (toPair r z) :=
    ((KSN019_main r hr).1 _ hdom).restrictScalars
  have hT : AnalyticAt ℝ (fun z => toPair r z) z := (toPair r).analyticAt z
  have hCT : AnalyticAt ℝ (fun z => complexSmoothing r (toPair r z)) z :=
    AnalyticAt.comp (g := complexSmoothing r) (f := fun z => toPair r z) hC hT
  have hP : AnalyticAt ℝ (fun y => fromPairEq (r + 1) y) (complexSmoothing r (toPair r z)) :=
    (fromPairEq (r + 1)).analyticAt _
  exact AnalyticAt.comp (g := fun y => fromPairEq (r + 1) y)
    (f := fun z => complexSmoothing r (toPair r z)) hP hCT

end NlsGge.ThirdConsultation.PDE
