                                                                                                            
                                                                                                                          
                                                                     
import NlsGge.Atomic.I.I009
import NlsGge.Spectral.ActualGapHeightHolderE02_38
import NlsGge.Spectral.ActualQuasimomentumE02_38
import NlsGge.Spectral.ActualSpectralRemainderE02_38
import Mathlib

                                           
                                        
                                                                                        
                                                                           
                                                                                                    
                                                                                                     
                                                                                          
                                                                           
                                                                                               
                                                                                                  
                                                 
                                                                                     
                                                                                               
                                                                                                  

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis
open NlsGge.SpectralFoundations

namespace NlsGge.Atomic.I010

/-- Copied verbatim from DEFINITIONS/I.lean.md lines 76-78. -/
noncomputable def spectralEnergy (W : ℝ → ℝ) (u : PhysicalL2) : ℝ :=
  (2 / Real.pi) * ∫ t : ℝ, W (2 * t) * actualGapHeightE02_38 u t

theorem hasDerivAt_scaled (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (x : ℝ) :
    HasDerivAt (fun y : ℝ => W (2 * y)) (2 * deriv W (2 * x)) x := by
  have h1 : HasDerivAt W (deriv W (2 * x)) (2 * x) :=
    ((hW.differentiable (by norm_num)) (2 * x)).hasDerivAt
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have h2 := h1.comp x hlin
  have e : deriv W (2 * x) * 2 = 2 * deriv W (2 * x) := mul_comm _ _
  rw [e] at h2
  exact h2

theorem convexOn_scaled (W : ℝ → ℝ) (hc : ConvexOn ℝ Set.univ W) :
    ConvexOn ℝ Set.univ (fun t : ℝ => W (2 * t)) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h := hc.2 (Set.mem_univ (2 * x)) (Set.mem_univ (2 * y)) ha hb hab
  have e : 2 * (a * x + b * y) = a * (2 * x) + b * (2 * y) := by ring
  simp only [smul_eq_mul] at h ⊢
  rw [e]
  exact h

theorem tangent_of_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)
    (p y : ℝ) : deriv f p * (y - p) ≤ f y - f p := by
  rcases lt_trichotomy p y with h | h | h
  · have h' := hf.deriv_le_slope (Set.mem_univ p) (Set.mem_univ y) h (hd p)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at h'
    exact h'
  · subst h
    simp
  · have h' := hf.slope_le_deriv (Set.mem_univ y) (Set.mem_univ p) h (hd p)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at h'
    have e : deriv f p * (y - p) = -(deriv f p * (p - y)) := by ring
    rw [e]
    linarith

theorem integrable_X_mul (F : ℝ → ℝ) (A : ℝ) (hF : Integrable F)
    (hz : ∀ x : ℝ, A < |x| → F x = 0) : Integrable (fun x : ℝ => x * F x) := by
  refine Integrable.mono' (hF.norm.const_mul A)
    (continuous_id.aestronglyMeasurable.mul hF.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  show ‖x * F x‖ ≤ A * ‖F x‖
  by_cases hx : A < |x|
  · rw [hz x hx]
    simp
  · push_neg at hx
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

/-- I-010, Pro's signature (STATEMENTS/I.md lines 187-203). -/
theorem i010 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (hfin : {n : ℤ | actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n}.Finite)
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hc : ConvexOn ℝ Set.univ W) :
    let v := actualGapHeightE02_38 u
    let p := actualQuasimomentumRealPartE02_38 u
    let f := fun x : ℝ => W (2 * x)
    (∀ x : ℝ, deriv f (p x) * (x - p x) ≤ f x - f (p x) ∧
      deriv f (p x) * (x - p x) * v x ≤ (f x - f (p x)) * v x) ∧
    Integrable (fun x => f x * v x) ∧
    Summable (fun n : ℤ => W (2 * Real.pi * n) * actualGapActionAllE02_38 u n) ∧
    Integrable (fun x => deriv f (p x) * (x - p x) * v x) ∧
    (2 / Real.pi) * (∫ x : ℝ, deriv f (p x) * (x - p x) * v x) ≤
      spectralEnergy W u - ∑' n : ℤ, W (2 * Real.pi * n) * actualGapActionAllE02_38 u n := by
  intro v p f
  obtain ⟨hint1, hrem, hsum, hid⟩ :=
    NlsGge.Atomic.I009.finiteGap_convex_difference u hu hfin W hW hc
  have hd : Differentiable ℝ f := fun t => (hasDerivAt_scaled W hW t).differentiableAt
  have hfc : ConvexOn ℝ Set.univ f := convexOn_scaled W hc
  have htan : ∀ x, deriv f (p x) * (x - p x) ≤ f x - f (p x) :=
    fun x => tangent_of_convex f hfc hd (p x) x
  have hdf : deriv f = fun t => 2 * deriv W (2 * t) :=
    funext fun t => (hasDerivAt_scaled W hW t).deriv
  have hcont : Continuous (deriv f) := by
    rw [hdf]
    exact continuous_const.mul
      ((hW.continuous_deriv (by norm_num)).comp (continuous_const.mul continuous_id))
  have hcontH : Continuous (fun t => t * deriv f t) := continuous_id.mul hcont
  obtain ⟨-, A, hA⟩ := actualGapHeight_support_finiteGap_E02_38 u hfin
  have hF : Integrable (fun l => deriv f (p l) * v l) :=
    (actualGapHeight_integral_eq_sum_E02_38 u hfin (deriv f) hcont).1
  have hH : Integrable (fun l => (p l * deriv f (p l)) * v l) :=
    (actualGapHeight_integral_eq_sum_E02_38 u hfin (fun t => t * deriv f t) hcontH).1
  have hX : Integrable (fun x => x * (deriv f (p x) * v x)) :=
    integrable_X_mul (fun x => deriv f (p x) * v x) A hF (fun x hx => by
      show deriv f (p x) * actualGapHeightE02_38 u x = 0
      rw [hA x hx, mul_zero])
  have hg : (fun x => deriv f (p x) * (x - p x) * v x) =
      fun x => x * (deriv f (p x) * v x) - (p x * deriv f (p x)) * v x := by
    funext x
    ring
  have hgint : Integrable (fun x => deriv f (p x) * (x - p x) * v x) := by
    rw [hg]
    exact hX.sub hH
  have hpt : ∀ x, deriv f (p x) * (x - p x) * v x ≤ (f x - f (p x)) * v x :=
    fun x => mul_le_mul_of_nonneg_right (htan x) (actualGapHeightE02_38_nonneg u x)
  have hremx : ∀ x, remainderIntegrandE02_38 W u x = (f x - f (p x)) * v x :=
    fun x => rfl
  refine ⟨fun x => ⟨htan x, hpt x⟩, hint1, hsum, hgint, ?_⟩
  have hmono : ∫ x : ℝ, deriv f (p x) * (x - p x) * v x ≤
      ∫ x : ℝ, remainderIntegrandE02_38 W u x :=
    integral_mono hgint hrem (fun x => by rw [hremx x]; exact hpt x)
  have hsE : spectralEnergy W u - ∑' n : ℤ, W (2 * Real.pi * n) * actualGapActionAllE02_38 u n
      = (2 / Real.pi) * ∫ x : ℝ, remainderIntegrandE02_38 W u x := by
    unfold spectralEnergy
    exact hid
  rw [hsE]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)


end NlsGge.Atomic.I010
