import Mathlib
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST033
import NlsGge.Atomic.KST.KST035
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST036Core
import NlsGge.ThirdConsultation.KST.KST036Support

                                                                                                        
                                                                                                     
                                                                                                                       
                                                                                                                          
                                                                                                                               
                                                                                                                           
set_option autoImplicit false
noncomputable section
open Filter Topology
open NlsGge.Atomic.KST (SlowWeight)
open NlsGge.Atomic.KST002

namespace NlsGge.ThirdConsultation.KST

theorem kst036_coordinate_criterion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ω : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (f : E → Weighted ω) (s : Set E) (hs : IsOpen s)
    (hcoord : ∀ channel m, AnalyticOnNhd ℂ (fun x => f x channel m) s)
    (hbounded : ∀ x ∈ s, ∃ e : ℝ, 0 < e ∧ ∃ C : ℝ,
      ∀ y ∈ Metric.ball x e, ‖f y‖ ≤ C) :
  AnalyticOnNhd ℂ f s :=
  KST036C.coord_criterion ω f s hs hcoord hbounded

theorem kst036 (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M)
    (hw : SlowWeight w Cw)
    (hunbounded : Tendsto (fun n : ℕ => w (n : ℤ)) atTop atTop)
    (v : ℤ → ℝ) (hv : SecondaryWeight v) :
  let ω := productWeight w v
  let hω := productOneLe hw.one_le hv.1.1
  letI := weightFact ω hω
  AnalyticOnNhd ℂ (adaptedFourier ω hω (adaptedThreshold w M))
    (componentOpenBall ω (2*M)) := by
  intro ω hω
  letI := weightFact ω hω
  have hw' : UnboundedWeight w := ⟨⟨hw.one_le, hw.even, hw.radial_mono⟩, hunbounded⟩
  obtain ⟨-, hcond, hmain⟩ := kst035 w Cw M hM hw hunbounded
  have hNd : diagonalThreshold w M ≤ adaptedThreshold w M := hcond.1
  have hball : ∀ x ∈ componentBall ω (2*M),
      weightedPotential ω hω x ∈ physicalComponentBall w (2*M) :=
    fun x hx => KST031S.ball_productWeight_subset w v hw.one_le hv.1.1 (2*M)
      (KST033S.wp_mem_ball ω hω x (2*M) hx)
  have hU : IsOpen (componentOpenBall ω (2*M)) := KST033S.isOpen_componentOpenBall ω (2*M)
  have hsub := KST033S.componentOpenBall_subset ω (2*M)
  have hcoord : ∀ (channel : Bool) (m : ℤ),
      AnalyticOnNhd ℂ (fun x => adaptedFourier ω hω (adaptedThreshold w M) x channel m)
        (componentOpenBall ω (2*M)) := by
    intro channel m
    have h1 := KST036S.coeff_analyticOnNhd w M hM hw' (adaptedThreshold w M) hNd ω hω hball channel m
    refine h1.congr hU fun x hx => ?_
    have h2 := (hmain v hv x (hsub hx)).1
    exact (congrFun (congrFun h2 channel) m).symm
  refine KST036C.coord_criterion ω _ _ hU hcoord ?_
  intro x hx
  obtain ⟨e, he, hball'⟩ := Metric.isOpen_iff.1 hU x hx
  refine ⟨e, he, ‖x‖ + e + M / 16, fun y hy => ?_⟩
  have hyU : y ∈ componentOpenBall ω (2*M) := hball' hy
  have h3 := (hmain v hv y (hsub hyU)).2
  have h4 : ‖y‖ ≤ ‖x‖ + e := by
    have := dist_le_norm_add_norm y x
    have h5 : ‖y - x‖ < e := by simpa [dist_eq_norm] using hy
    calc ‖y‖ = ‖x + (y - x)‖ := by simp
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + e := by linarith
  calc ‖adaptedFourier ω hω (adaptedThreshold w M) y‖
      = ‖(adaptedFourier ω hω (adaptedThreshold w M) y - y) + y‖ := by simp
    _ ≤ ‖adaptedFourier ω hω (adaptedThreshold w M) y - y‖ + ‖y‖ := norm_add_le _ _
    _ ≤ ‖x‖ + e + M / 16 := by linarith

end NlsGge.ThirdConsultation.KST
end
