import Mathlib
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.GK38.IsolatingDefs
import NlsGge.Atomic.G2.G2045SupB2
import NlsGge.Atomic.G2.G2045SupB3
import NlsGge.Atomic.G2.G2045SupC1
import NlsGge.Atomic.G2.G2045SupC3
-- WRAPPER-IMPORTS-BEGIN
import NlsGge.Atomic.G2.G2043
import NlsGge.Atomic.G2.G2075
-- WRAPPER-IMPORTS-END

                                                                     
                                                                                
                                                                                                   
                                                                                                                     
                                                          
                                                                                                                   
                                                                                                                 
                                                                                                                           
                                                                                                                      
                                                                                                                    
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

theorem g2045c_ball_trace_core (k : ℕ) (hk : 2 ≤ k) (W : Set PotPair) (h043 : g2045c_H43 k W)
    (hF : ∀ x A : PotPair, pairSobolev ((k - 1 : ℕ) : ℝ) x → pairSobolev ((k - 1 : ℕ) : ℝ) A →
      AnalyticOnNhd ℂ (fun s : ℂ => ∑' n : ℤ, higherAction k (x + s • A) n) {s : ℂ | x + s • A ∈ W})
    (hreal : ∀ u' : PhysicalL2, physicalSobolev ((k - 1 : ℕ) : ℝ) u' →
      ∑' n : ℤ, higherAction k (realSlice u') n =
        -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k (realSlice u'))
    (u : PhysicalL2) (hcW : realSlice u ∈ W)
    (hu : physicalSobolev ((k - 1 : ℕ) : ℝ) u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ψ ∈ g2045bBall (k - 1) (realSlice u) ρ,
      ψ ∈ W ∧ Summable (fun n : ℤ => ‖higherAction k ψ n‖) ∧
      ∑' n : ℤ, higherAction k ψ n =
        -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k ψ := by
  have hc : pairSobolev ((k - 1 : ℕ) : ℝ) (realSlice u) := g2045c_real_pair _ u hu
  obtain ⟨-, h43⟩ := h043 (realSlice u) hcW hc
  obtain ⟨δ, hδ, S₀, hS₀⟩ := h43 1 one_pos
  have hball : ∀ ψ ∈ g2045bBall (k - 1) (realSlice u) δ,
      ψ ∈ W ∧ Summable (fun n : ℤ => ‖higherAction k ψ n‖) := fun ψ hψ =>
    ⟨(hS₀ ψ hψ.1 hψ.2).1, (hS₀ ψ hψ.1 hψ.2).2.1⟩
  refine ⟨δ, hδ, ?_⟩
  set a : ℂ := (k : ℂ) / (2 * Complex.I) ^ (k - 1) with ha
  let f : PotPair → ℂ := fun φ => (∑' n : ℤ, higherAction k φ n) + a * hierarchyHamiltonian k φ
  have hf : ∀ x ∈ pairSobolevSub (k - 1), ∀ A ∈ pairSobolevSub (k - 1),
      AnalyticOnNhd ℂ (fun s : ℂ => f (x + s • A))
        {s : ℂ | x + s • A ∈ g2045bBall (k - 1) (realSlice u) δ} := by
    intro x hx A hA
    have h1 : AnalyticOnNhd ℂ (fun s : ℂ => ∑' n : ℤ, higherAction k (x + s • A) n)
        {s : ℂ | x + s • A ∈ g2045bBall (k - 1) (realSlice u) δ} :=
      (hF x A hx hA).mono (fun s (hs : x + s • A ∈ g2045bBall (k - 1) (realSlice u) δ) =>
        (hball _ hs).1)
    have h2 : AnalyticOnNhd ℂ (fun s : ℂ => a * hierarchyHamiltonian k (x + s • A))
        {s : ℂ | x + s • A ∈ g2045bBall (k - 1) (realSlice u) δ} :=
      ((analyticOnNhd_const (v := a)).mul
        (g2045b_hamiltonian_line_analytic k hk x A hx hA)).mono (subset_univ _)
    exact h1.add h2
  have hr : ∀ u' : PhysicalL2, realSlice u' ∈ g2045bBall (k - 1) (realSlice u) δ →
      f (realSlice u') = 0 := by
    intro u' hu'
    have h := hreal u' (g2045c_pair_real _ u' hu'.1)
    show (∑' n : ℤ, higherAction k (realSlice u') n) + a * hierarchyHamiltonian k (realSlice u') = 0
    rw [h, ha]
    ring
  have hid := g2045b_ball_identity (k - 1) (realSlice u) hc (potConj_realSlice u) δ f hf hr
  intro ψ hψ
  refine ⟨(hball ψ hψ).1, (hball ψ hψ).2, ?_⟩
  have h' : (∑' n : ℤ, higherAction k ψ n) + a * hierarchyHamiltonian k ψ = 0 := hid ψ hψ
  rw [ha] at h'
  linear_combination h'

-- WRAPPER-BEGIN
theorem g2045c_ball_trace (k : ℕ) (hk : 2 ≤ k) (u : PhysicalL2)
    (hu : physicalSobolev ((k - 1 : ℕ) : ℝ) u) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ψ ∈ g2045bBall (k - 1) (realSlice u) ρ,
      ψ ∈ sourceW ∧ Summable (fun n : ℤ => ‖higherAction k ψ n‖) ∧
      ∑' n : ℤ, higherAction k ψ n =
        -(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k ψ :=
  g2045c_ball_trace_core k hk sourceW (G2_043 k hk) (fun x A hx hA => g2045c_F_line_analytic k hk x A hx hA)
    (fun u' hu' => g2045c_real_trace k hk u' hu') u (G2_075.2.1 ⟨u, rfl⟩) hu
-- WRAPPER-END

end NlsGge.GKDefinitionDesign
end
