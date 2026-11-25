import Mathlib
import NlsGge.GK38.Lib.InterpolationHilbertOp
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Atomic.X.X006
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff
import NlsGge.Atomic.G4.G4042
import NlsGge.Atomic.G6.G6004
import NlsGge.Atomic.G6.G6007
import NlsGge.Atomic.G6.G6008

                                                                                                    
                                                                           
                                                                                                                                        
                                                                                                                                       
                                                                                                                         
                                                                                                                                        
                                                                                                                           
                                                                                              
                                                                                                                                       
                                                                                                                                    
                                                         
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G6009Aux

/-- Restriction of an `ell^2` sequence on `Bool × ℤ` to the block `{b} × ℤ`, as a bounded `ℝ`-linear map. -/
def restr (b : Bool) : CartesianReal →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟨fun n => z (b, n), by
        have hs := (lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
        exact memℓp_gen (hs.comp_injective (fun n m h => by simpa using h))⟩
      map_add' := fun x y => lp.ext (funext fun n => by simp <;> rfl)
      map_smul' := fun c x => lp.ext (funext fun n => by simp) }
    1 (fun z => by
      have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      have hs := (lp.memℓp z).summable hp
      rw [one_mul]
      apply lp.norm_le_of_tsum_le hp (norm_nonneg z)
      rw [lp.norm_rpow_eq_tsum hp z]
      exact tsum_comp_le_tsum_of_inj hs (fun j => by positivity)
        (i := fun n : ℤ => (b, n)) (fun n m h => by simpa using h))

/-- Coordinatewise real part `ℓ²(ℤ, ℂ) → ℓ²(ℤ, ℝ)`. -/
def reL : Lib.L2Z →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => (x n).re,
        (lp.memℓp x).mono' (fun n => by simpa using Complex.abs_re_le_norm (x n))⟩
      map_add' := fun x y => lp.ext (funext fun n => by simp <;> rfl)
      map_smul' := fun c x => lp.ext (funext fun n => by simp) }
    1 (fun x => by
      simpa using lp.norm_mono (p := 2) (by norm_num)
        (x := (⟨fun n => (x n).re,
          (lp.memℓp x).mono' (fun n => by simpa using Complex.abs_re_le_norm (x n))⟩ :
            lp (fun _ : ℤ => ℝ) 2))
        (y := x) (fun n => by simpa using Complex.abs_re_le_norm (x n)))

/-- Coordinatewise imaginary part `ℓ²(ℤ, ℂ) → ℓ²(ℤ, ℝ)`. -/
def imL : Lib.L2Z →L[ℝ] lp (fun _ : ℤ => ℝ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => (x n).im,
        (lp.memℓp x).mono' (fun n => by simpa using Complex.abs_im_le_norm (x n))⟩
      map_add' := fun x y => lp.ext (funext fun n => by simp <;> rfl)
      map_smul' := fun c x => lp.ext (funext fun n => by simp) }
    1 (fun x => by
      simpa using lp.norm_mono (p := 2) (by norm_num)
        (x := (⟨fun n => (x n).im,
          (lp.memℓp x).mono' (fun n => by simpa using Complex.abs_im_le_norm (x n))⟩ :
            lp (fun _ : ℤ => ℝ) 2))
        (y := x) (fun n => by simpa using Complex.abs_im_le_norm (x n)))

/-- The radius map on real Cartesian pairs, as a map from `CartesianReal` into `ell^1`. -/
def radiiReal (z : CartesianReal) : ActionSequence :=
  NlsGge.Atomic.G6008.coordinateRadii (WithLp.toLp 2 (fun b : Bool => restr b z))

theorem radiiReal_apply (z : CartesianReal) (n : ℤ) :
    radiiReal z n = (z (true, n) ^ 2 + z (false, n) ^ 2) / 2 := rfl

theorem radiiReal_continuous : Continuous radiiReal :=
  NlsGge.Atomic.G6008.continuous_coordinateRadii.comp
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun b => (restr b).continuous))

/-- The radius map on physical coordinates `z ∈ ℓ²(ℤ, ℂ)`: `z ↦ (|z_n|²)`. -/
def radiiComplex (z : Lib.L2Z) : ActionSequence :=
  NlsGge.Atomic.G6008.coordinateRadii
    (WithLp.toLp 2 (fun b : Bool =>
      if b then Real.sqrt 2 • reL z else Real.sqrt 2 • imL z))

theorem radiiComplex_apply (z : Lib.L2Z) (n : ℤ) : radiiComplex z n = ‖z n‖ ^ 2 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  show ((Real.sqrt 2 * (z n).re) ^ 2 + (Real.sqrt 2 * (z n).im) ^ 2) / 2 = ‖z n‖ ^ 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [h2]

theorem radiiComplex_continuous : Continuous radiiComplex := by
  refine NlsGge.Atomic.G6008.continuous_coordinateRadii.comp
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun b => ?_))
  cases b
  · exact (Real.sqrt 2 • imL).continuous
  · exact (Real.sqrt 2 • reL).continuous

/-- Properness descends along a continuous map into a Hausdorff space when the radius factorization holds. -/
theorem proper_of_factor {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space Y] {Ω : X → Y} {R : Y → Z} {I : X → Z} (hΩ : Continuous Ω) (hR : Continuous R)
    (hI : IsProperMap I) (hfac : ∀ x, I x = R (Ω x)) : IsProperMap Ω := by
  have hIR : I = R ∘ Ω := funext hfac
  exact isProperMap_of_comp_of_t2 hΩ hR (hIR ▸ hI)

theorem real_continuous : Continuous realBirkhoffCartesian :=
  continuousOn_univ.1 G4042.2.2.continuousOn

end G6009Aux

theorem G6009 :
  IsProperMap realBirkhoffCartesian ∧ IsProperMap physicalBirkhoff := by
  refine ⟨?_, ?_⟩
  · refine G6009Aux.proper_of_factor G6009Aux.real_continuous G6009Aux.radiiReal_continuous
      G6007.2.2 (fun u => ?_)
    refine lp.ext (funext fun n => ?_)
    rw [g6_actionSequence_apply, G6009Aux.radiiReal_apply, realBirkhoffCartesian_true,
      realBirkhoffCartesian_false]
    have := realX_sq_add_realY_sq n u
    linarith
  · refine G6009Aux.proper_of_factor sourceFamily.Phi_continuous G6009Aux.radiiComplex_continuous
      G6007.2.2 (fun u => ?_)
    refine lp.ext (funext fun n => ?_)
    rw [g6_actionSequence_apply, G6009Aux.radiiComplex_apply]
    exact (sourceFamily.Phi_action u n).symm

end
end NlsGge.GKDefinitionDesign
