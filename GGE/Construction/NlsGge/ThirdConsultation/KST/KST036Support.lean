import Mathlib
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST019
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST031
import NlsGge.Atomic.KST.KST032
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST033Host
import NlsGge.ThirdConsultation.KST.KST033Support
import NlsGge.ThirdConsultation.KST.KST034Host

                                                                               
                                                                                             
                                                                                                  
                                                                                                                        
                                                                                                                              
                                                                                                                     
set_option autoImplicit false
noncomputable section
open Filter Topology

namespace NlsGge.ThirdConsultation.KST.KST036S

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST004 NlsGge.Atomic.KST006 NlsGge.Pilot
open NlsGge.ThirdConsultation.KST NlsGge.ThirdConsultation.KST.KST033S

/-- `(z, φ) ↦ abc φ n z` is analytic at points where `1 - q` is a unit. -/
theorem abc_analyticAt (n : ℤ) (φ : PhysicalPairLp) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hu : IsUnit (1 - qOperator φ n z hz)) :
    AnalyticAt ℂ (fun p : ℂ × PhysicalPairLp => abc p.2 n p.1) (z, φ) :=
  NlsGge.Atomic.KST016.localABC_analyticOnNhd n (center n) (center_mem_strip n)
    (z, φ) (mem_domain n φ z hz hu)

section Diag

variable (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M) (hw : UnboundedWeight w) (n : ℤ)
  (hn : diagonalThreshold w M ≤ n.natAbs) (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
  [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
  (hball : ∀ x ∈ componentBall ω (2*M), weightedPotential ω hω x ∈ physicalComponentBall w (2*M))

include hM hw hn hball

/-- The triple `(a, b, c)` at the diagonal zero is analytic on the open component ball. -/
theorem abc_diag_analyticOnNhd :
    AnalyticOnNhd ℂ
      (fun x : Weighted ω => abc (weightedPotential ω hω x) n
        (diagonalZero n (weightedPotential ω hω x))) (componentOpenBall ω (2*M)) := by
  intro x hx
  have hxb : x ∈ componentBall ω (2*M) := componentOpenBall_subset ω (2*M) hx
  have hσ : AnalyticAt ℂ (fun y : Weighted ω => diagonalZero n (weightedPotential ω hω y)) x :=
    diagonalZero_analyticOnNhd w M hM hw n hn ω hω hball x hx
  obtain ⟨-, -, hmem, -, -⟩ := kst032 w M hM hw _ (hball x hxb) n hn
  have hzs : diagonalZero n (weightedPotential ω hω x) ∈ spectralStrip n :=
    closedBall_subset_strip n
      (Metric.closedBall_subset_closedBall (by linarith [Real.pi_pos]) hmem)
  obtain ⟨-, hall⟩ := (kst031 w M hM hw).2.1
  have hu : IsUnit (1 - qOperator (weightedPotential ω hω x) n
      (diagonalZero n (weightedPotential ω hω x)) hzs) :=
    ((hall _ (hball x hxb) n hn).2.1 _ hzs).2
  have hG := abc_analyticAt n (weightedPotential ω hω x) _ hzs hu
  have hpair : AnalyticAt ℂ
      (fun y : Weighted ω => (diagonalZero n (weightedPotential ω hω y), weightedPotential ω hω y)) x :=
    hσ.prod (wp_analyticAt ω hω x)
  exact AnalyticAt.comp (g := fun p : ℂ × PhysicalPairLp => abc p.2 n p.1)
    (f := fun y : Weighted ω => (diagonalZero n (weightedPotential ω hω y), weightedPotential ω hω y))
    hG hpair

theorem b_diag_analyticOnNhd :
    AnalyticOnNhd ℂ
      (fun x : Weighted ω => b (weightedPotential ω hω x) n
        (diagonalZero n (weightedPotential ω hω x))) (componentOpenBall ω (2*M)) := by
  intro x hx
  have h := abc_diag_analyticOnNhd w M hM hw n hn ω hω hball x hx
  exact (((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt _).comp h

theorem c_diag_analyticOnNhd :
    AnalyticOnNhd ℂ
      (fun x : Weighted ω => c (weightedPotential ω hω x) n
        (diagonalZero n (weightedPotential ω hω x))) (componentOpenBall ω (2*M)) := by
  intro x hx
  have h := abc_diag_analyticOnNhd w M hM hw n hn ω hω hball x hx
  exact (((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ (ℂ × ℂ))).analyticAt _).comp h

end Diag

section Low

variable (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]

/-- The `m`-th Fourier coefficient of the `channel` component, as a bounded linear functional. -/
def fourierCLM (channel : Bool) (m : ℤ) : PhysicalPairLp →L[ℂ] ℂ :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).comp
    ((physicalFourierL2.toContinuousLinearEquiv : PhysicalL2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2).comp
      (PiLp.proj 2 (fun _ : Bool => PhysicalL2) channel))

theorem fourierCLM_apply (channel : Bool) (m : ℤ) (φ : PhysicalPairLp) :
    fourierCLM channel m φ = physicalFourier (φ channel) m := by
  show physicalFourierL2 (φ channel) m = _
  exact physicalFourierL2_apply _ _

theorem low_analyticAt (channel : Bool) (m : ℤ) (x : Weighted ω) :
    AnalyticAt ℂ (fun y : Weighted ω => physicalFourier (weightedPotential ω hω y channel) m) x := by
  have e : (fun y : Weighted ω => physicalFourier (weightedPotential ω hω y channel) m) =
      (fourierCLM channel m) ∘ (weightedPotential ω hω) := by
    funext y
    exact (fourierCLM_apply channel m _).symm
  rw [e]
  exact ((fourierCLM channel m).analyticAt _).comp (wp_analyticAt ω hω x)

end Low

/-- Coordinates of the adapted coefficient map are analytic on the open component ball. -/
theorem coeff_analyticOnNhd (w : ℤ → ℝ) (M : ℝ) (hM : 1 ≤ M) (hw : UnboundedWeight w)
    (N : ℕ) (hN : diagonalThreshold w M ≤ N) (ω : ℤ → ℝ) (hω : ∀ k, 1 ≤ ω k)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (hball : ∀ x ∈ componentBall ω (2*M), weightedPotential ω hω x ∈ physicalComponentBall w (2*M))
    (channel : Bool) (m : ℤ) :
    AnalyticOnNhd ℂ (fun x : Weighted ω => adaptedCoefficients N (weightedPotential ω hω x) channel m)
      (componentOpenBall ω (2*M)) := by
  by_cases hm : m.natAbs ≤ N
  · intro x _
    have e : (fun y : Weighted ω => adaptedCoefficients N (weightedPotential ω hω y) channel m) =
        fun y : Weighted ω => physicalFourier (weightedPotential ω hω y channel) m := by
      funext y
      simp [adaptedCoefficients, hm, rawFourier]
    rw [e]
    exact low_analyticAt ω hω channel m x
  · have hn : diagonalThreshold w M ≤ m.natAbs := hN.trans (not_le.1 hm).le
    cases channel
    · have e : (fun y : Weighted ω => adaptedCoefficients N (weightedPotential ω hω y) false m) =
          fun y : Weighted ω => b (weightedPotential ω hω y) m
            (diagonalZero m (weightedPotential ω hω y)) := by
        funext y
        simp [adaptedCoefficients, hm]
      rw [e]
      exact b_diag_analyticOnNhd w M hM hw m hn ω hω hball
    · have hn' : diagonalThreshold w M ≤ (-m).natAbs := by simpa using hn
      have e : (fun y : Weighted ω => adaptedCoefficients N (weightedPotential ω hω y) true m) =
          fun y : Weighted ω => c (weightedPotential ω hω y) (-m)
            (diagonalZero (-m) (weightedPotential ω hω y)) := by
        funext y
        simp [adaptedCoefficients, hm]
      rw [e]
      exact c_diag_analyticOnNhd w M hM hw (-m) hn' ω hω hball

end NlsGge.ThirdConsultation.KST.KST036S
end
