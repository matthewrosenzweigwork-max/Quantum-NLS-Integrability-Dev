import Mathlib
import NlsGge.ThirdConsultation.G4.RealTrace
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38

                                                                                                                                   
                                                                                                                   
                                                                                                                
                                                                                                                 
                       
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def realX (n : ℤ) (u : PhysicalL2) : ℝ :=
  (cartesianX n (realSlice u)).re

def realY (n : ℤ) (u : PhysicalL2) : ℝ :=
  (cartesianY n (realSlice u)).re

abbrev CartesianReal := lp (fun _ : Bool × ℤ => ℝ) 2

def realCartesianSequence (u : PhysicalL2) (j : Bool × ℤ) : ℝ :=
  if j.1 then realX j.2 u else realY j.2 u

open Classical in
def realBirkhoffCartesian (u : PhysicalL2) : CartesianReal :=
  if h : Memℓp (realCartesianSequence u) 2 then
    ⟨realCartesianSequence u, h⟩ else 0

theorem realX_sq_add_realY_sq (n : ℤ) (u : PhysicalL2) :
    realX n u ^ 2 + realY n u ^ 2 = 2 * actualGapActionAllE02_38 u n :=
  cartesianX_sq_add_cartesianY_sq n u

theorem realActionNonneg38 (u : PhysicalL2) (n : ℤ) :
    0 ≤ actualGapActionAllE02_38 u n := by
  have h := realX_sq_add_realY_sq n u
  nlinarith [sq_nonneg (realX n u), sq_nonneg (realY n u)]

theorem realCartesianSequence_memℓp (u : PhysicalL2) :
    Memℓp (realCartesianSequence u) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have hsum : Summable fun n : ℤ => 2 * actualGapActionAllE02_38 u n :=
    (sourceFamily.Phi_mass u).1.summable.mul_left 2
  refine (summable_prod_of_nonneg (fun p => sq_nonneg (realCartesianSequence u p))).2
    ⟨fun b => ?_, Summable.of_finite⟩
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hsum
  have hpair := realX_sq_add_realY_sq n u
  cases b
  · show realY n u ^ 2 ≤ 2 * actualGapActionAllE02_38 u n
    nlinarith [sq_nonneg (realX n u)]
  · show realX n u ^ 2 ≤ 2 * actualGapActionAllE02_38 u n
    nlinarith [sq_nonneg (realY n u)]

theorem realBirkhoffCartesian_eq (u : PhysicalL2) :
    realBirkhoffCartesian u =
      ⟨realCartesianSequence u, realCartesianSequence_memℓp u⟩ :=
  dif_pos (realCartesianSequence_memℓp u)

theorem realBirkhoffCartesian_true (u : PhysicalL2) (n : ℤ) :
    realBirkhoffCartesian u (true, n) = realX n u := by
  rw [realBirkhoffCartesian_eq]
  rfl

theorem realBirkhoffCartesian_false (u : PhysicalL2) (n : ℤ) :
    realBirkhoffCartesian u (false, n) = realY n u := by
  rw [realBirkhoffCartesian_eq]
  rfl

end
end NlsGge.GKDefinitionDesign

