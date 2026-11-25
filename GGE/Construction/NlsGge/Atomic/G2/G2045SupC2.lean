import Mathlib
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.GK38.IsolatingDefs
import NlsGge.Atomic.G2.G2045SupB2
import NlsGge.Atomic.G2.G2045SupB4
import NlsGge.Atomic.G2.G2045SupC1
-- WRAPPER-IMPORTS-BEGIN
import NlsGge.Atomic.G2.G2042
import NlsGge.Atomic.G2.G2043
import NlsGge.Atomic.G2.G2075
-- WRAPPER-IMPORTS-END

                                                                     
                                                                                
                                                                                                               
                                                                                                               
                                                                                                         
                                                                                                                                                                    
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

theorem g2045c_norm_le_pn (N : ℕ) (d : PotPair) (hd : pairSobolev (N : ℝ) d) :
    ‖d‖ ≤ pairSobolevNorm (N : ℝ) d := by
  obtain ⟨h1, h2⟩ := g2045b_comp_le N d hd
  rw [Prod.norm_def]
  exact max_le h1 h2

theorem g2045c_pn_zero (r : ℝ) : pairSobolevNorm r (0 : PotPair) = 0 := by
  have := g2045b_pn_smul r (0 : ℂ) (0 : PotPair)
  simpa using this

theorem g2045c_F_continuous_core (k : ℕ) (W : Set PotPair) (hWgk : W ⊆ gkW)
    (h042 : ∀ n : ℤ, AnalyticOnNhd ℂ (fun φ : PotPair => higherAction k φ n) gkW)
    (h043 : g2045c_H43 k W) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ W)
    (hreg : pairSobolev ((k - 1 : ℕ) : ℝ) φ₀) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ φ : PotPair, pairSobolev ((k - 1 : ℕ) : ℝ) φ →
      pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ₀) < δ →
      ‖(∑' n : ℤ, higherAction k φ n) - ∑' n : ℤ, higherAction k φ₀ n‖ < ε := by
  intro ε hε
  obtain ⟨-, h43⟩ := h043 φ₀ hφ₀ hreg
  obtain ⟨δ₁, hδ₁, S₀, hS₀⟩ := h43 (ε / 3) (by positivity)
  have hG : ContinuousAt (fun φ : PotPair => ∑ n ∈ S₀, higherAction k φ n) φ₀ :=
    tendsto_finset_sum _ (fun n _ => ((h042 n) φ₀ (hWgk hφ₀)).continuousAt)
  obtain ⟨δ₂, hδ₂, hG2⟩ := Metric.continuousAt_iff.1 hG (ε / 3) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun φ hφ hn => ?_⟩
  have hsub : pairSobolev (((k - 1 : ℕ)) : ℝ) (φ - φ₀) :=
    (pairSobolevSub (k - 1)).sub_mem hφ hreg
  have hn1 : pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ₀) < δ₁ := lt_of_lt_of_le hn (min_le_left _ _)
  have hn2 : dist φ φ₀ < δ₂ := by
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (g2045c_norm_le_pn _ _ hsub) (lt_of_lt_of_le hn (min_le_right _ _))
  have h1 := (hS₀ φ hφ hn1).2.2 S₀ le_rfl
  have h0 := (hS₀ φ₀ hreg (by
    have : φ₀ - φ₀ = 0 := sub_self _
    rw [this]
    rw [g2045c_pn_zero]; exact hδ₁)).2.2 S₀ le_rfl
  have h2 := hG2 hn2
  rw [dist_eq_norm] at h2
  have e : (∑' n : ℤ, higherAction k φ n) - ∑' n : ℤ, higherAction k φ₀ n =
      ((∑' n : ℤ, higherAction k φ n) - ∑ n ∈ S₀, higherAction k φ n) +
      ((∑ n ∈ S₀, higherAction k φ n) - ∑ n ∈ S₀, higherAction k φ₀ n) -
      ((∑' n : ℤ, higherAction k φ₀ n) - ∑ n ∈ S₀, higherAction k φ₀ n) := by ring
  rw [e]
  calc _ ≤ ‖(∑' n : ℤ, higherAction k φ n) - ∑ n ∈ S₀, higherAction k φ n‖ +
        ‖(∑ n ∈ S₀, higherAction k φ n) - ∑ n ∈ S₀, higherAction k φ₀ n‖ +
        ‖(∑' n : ℤ, higherAction k φ₀ n) - ∑ n ∈ S₀, higherAction k φ₀ n‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
    _ < ε := by linarith

-- WRAPPER-BEGIN
theorem g2045c_F_continuous (k : ℕ) (hk : 2 ≤ k) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceW)
    (hreg : pairSobolev ((k - 1 : ℕ) : ℝ) φ₀) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ φ : PotPair, pairSobolev ((k - 1 : ℕ) : ℝ) φ →
      pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ₀) < δ →
      ‖(∑' n : ℤ, higherAction k φ n) - ∑' n : ℤ, higherAction k φ₀ n‖ < ε :=
  g2045c_F_continuous_core k sourceW G2_075.2.2.1 (G2_042 k hk).1 (G2_043 k hk) φ₀ hφ₀ hreg
-- WRAPPER-END

end NlsGge.GKDefinitionDesign
end
