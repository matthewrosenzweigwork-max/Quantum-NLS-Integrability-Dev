import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffLevelZeroCore
import NlsGge.ThirdConsultation.PDE.BirkhoffRawInv
import NlsGge.ThirdConsultation.PDE.BirkhoffRawG6
import NlsGge.Atomic.G6.G6014
import NlsGge.Atomic.G6.G6028

                                                                                                                   
                                                                                                              
                                                                                                  
                                                                             
                                                                                                                     
                                                                                                                      
                                                                                                               
                                         
set_option autoImplicit false
open Set
open scoped ENNReal Topology
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

namespace BirkhoffLevelZeroGlue

/-- The selected map in `ℓ²` coordinates: `w ↦ Φ(F⁻¹ w)`. -/
def PPhi (w : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  physicalBirkhoff (reflectedFourierL2.symm w)

/-- Its literal inverse in `ℓ²` coordinates: `w ↦ F(Φ⁻¹ w)`. -/
def PPhiInv (w : lp (fun _ : ℤ => ℂ) 2) : lp (fun _ : ℤ => ℂ) 2 :=
  reflectedFourierL2 (physicalInverseBirkhoff w)

theorem actualT38_eq_PPhi (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) :
    actualT38 x = (PPhi (seqToLp38 x hx) : ℤ → ℂ) := by
  unfold actualT38
  rw [dif_pos hx]
  rfl

theorem actualTinv38_eq_PPhiInv (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0) :
    actualTinv38 x = (PPhiInv (seqToLp38 x hx) : ℤ → ℂ) := by
  rw [actualTinv38_of_mem x hx]
  rfl

theorem PPhi_analytic (hΦ : AnalyticOnNhd ℝ physicalBirkhoff Set.univ) :
    AnalyticOnNhd ℝ PPhi Set.univ := fun w _ =>
  (hΦ _ (Set.mem_univ _)).comp
    ((reflectedFourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).analyticAt w)

theorem PPhiInv_analytic (hΨ : AnalyticOnNhd ℝ physicalInverseBirkhoff Set.univ) :
    AnalyticOnNhd ℝ PPhiInv Set.univ := fun w _ =>
  ((reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).analyticAt _).comp
    (hΨ w (Set.mem_univ _))

theorem PPhi_hasFDerivAt (hΦ : AnalyticOnNhd ℝ physicalBirkhoff Set.univ) (w : lp (fun _ : ℤ => ℂ) 2) :
    HasFDerivAt PPhi ((fderiv ℝ physicalBirkhoff (reflectedFourierL2.symm w)).comp
      (reflectedFourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)) w :=
  ((hΦ _ (Set.mem_univ _)).differentiableAt.hasFDerivAt).comp w
    (reflectedFourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt

theorem PPhi_hasFDerivAt_zero (hΦ : AnalyticOnNhd ℝ physicalBirkhoff Set.univ)
    (hD0 : fderiv ℝ physicalBirkhoff 0 =
      reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) :
    HasFDerivAt PPhi (ContinuousLinearMap.id ℝ (lp (fun _ : ℤ => ℂ) 2)) 0 := by
  have h := PPhi_hasFDerivAt hΦ 0
  have h0 : reflectedFourierL2.symm (0 : lp (fun _ : ℤ => ℂ) 2) = 0 := map_zero _
  rw [h0, hD0] at h
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  show reflectedFourierL2 (reflectedFourierL2.symm w) = w
  exact LinearIsometryEquiv.apply_symm_apply _ _

/-- Real polarization: the ℂ-linear isometry `F⁻¹` preserves `⟪i a, b⟫_ℝ`. -/
theorem inner_I_symm (h k : lp (fun _ : ℤ => ℂ) 2) :
    inner ℝ ((Complex.I : ℂ) • reflectedFourierL2.symm h) (reflectedFourierL2.symm k) =
      inner ℝ ((Complex.I : ℂ) • h) k := by
  have e : (Complex.I : ℂ) • reflectedFourierL2.symm h =
      reflectedFourierL2.symm ((Complex.I : ℂ) • h) := (map_smul _ _ _).symm
  rw [e, real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

theorem PPhi_canonical (hΦ : AnalyticOnNhd ℝ physicalBirkhoff Set.univ)
    (hS : ∀ u h k : PhysicalL2,
      inner ℝ ((Complex.I : ℂ) • fderiv ℝ physicalBirkhoff u h)
        (fderiv ℝ physicalBirkhoff u k) = inner ℝ ((Complex.I : ℂ) • h) k)
    (w h k : lp (fun _ : ℤ => ℂ) 2) :
    stdSymplectic38 (fderiv ℝ PPhi w h : ℤ → ℂ) (fderiv ℝ PPhi w k : ℤ → ℂ) =
      stdSymplectic38 (h : ℤ → ℂ) (k : ℤ → ℂ) := by
  rw [(PPhi_hasFDerivAt hΦ w).fderiv, BirkhoffLevelZeroCore.stdSymplectic38_lp,
    BirkhoffLevelZeroCore.stdSymplectic38_lp]
  exact (hS _ _ _).trans (inner_I_symm h k)

end BirkhoffLevelZeroGlue

open BirkhoffLevelZeroGlue in
theorem actualT38_analytic_zero :
    AnalyticOnNhd ℝ
      (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) actualT38 (actualT38_mapsTo 0)) Set.univ :=
  BirkhoffLevelZeroCore.analytic_zero_of actualT38 PPhi actualT38_eq_PPhi (actualT38_mapsTo 0)
    (PPhi_analytic G6014.2.2.1)

open BirkhoffLevelZeroGlue in
theorem actualTinv38_analytic_zero :
    AnalyticOnNhd ℝ
      (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) actualTinv38 (actualTinv38_mapsTo 0)) Set.univ :=
  BirkhoffLevelZeroCore.analytic_zero_of actualTinv38 PPhiInv actualTinv38_eq_PPhiInv
    (actualTinv38_mapsTo 0) (PPhiInv_analytic G6014.2.2.2.1)

open BirkhoffLevelZeroGlue in
theorem actualT38_continuous_zero :
    Continuous (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) actualT38 (actualT38_mapsTo 0)) :=
  BirkhoffLevelZeroCore.continuous_zero_of actualT38 PPhi actualT38_eq_PPhi (actualT38_mapsTo 0)
    (PPhi_analytic G6014.2.2.1)

open BirkhoffLevelZeroGlue in
theorem actualTinv38_continuous_zero :
    Continuous (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) actualTinv38 (actualTinv38_mapsTo 0)) :=
  BirkhoffLevelZeroCore.continuous_zero_of actualTinv38 PPhiInv actualTinv38_eq_PPhiInv
    (actualTinv38_mapsTo 0) (PPhiInv_analytic G6014.2.2.2.1)

open BirkhoffLevelZeroGlue in
theorem actualT38_canonical_zero (x ξ η : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    stdSymplectic38
      (carrierCoe38 ((0 : ℕ) : ℝ)
        (fderiv ℝ (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) actualT38 (actualT38_mapsTo 0)) x ξ))
      (carrierCoe38 ((0 : ℕ) : ℝ)
        (fderiv ℝ (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) actualT38 (actualT38_mapsTo 0)) x η)) =
    stdSymplectic38
      (carrierCoe38 ((0 : ℕ) : ℝ) ξ)
      (carrierCoe38 ((0 : ℕ) : ℝ) η) :=
  BirkhoffLevelZeroCore.canonical_zero_of actualT38 PPhi actualT38_eq_PPhi (actualT38_mapsTo 0)
    (fun w => (PPhi_analytic G6014.2.2.1 w (Set.mem_univ w)).differentiableAt)
    (PPhi_canonical G6014.2.2.1 G6028.2.2.1) x ξ η

open BirkhoffLevelZeroGlue in
theorem actualT38_fderiv_zero :
    fderiv ℝ (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) actualT38 (actualT38_mapsTo 0)) 0 =
      ContinuousLinearMap.id ℝ (SobolevCarrier38 ((0 : ℕ) : ℝ)) :=
  BirkhoffLevelZeroCore.fderiv_zero_of actualT38 PPhi actualT38_eq_PPhi (actualT38_mapsTo 0)
    (PPhi_hasFDerivAt_zero G6014.2.2.1 G6014.2.2.2.2.2.2.2)

end
end NlsGge.ThirdConsultation.PDE
