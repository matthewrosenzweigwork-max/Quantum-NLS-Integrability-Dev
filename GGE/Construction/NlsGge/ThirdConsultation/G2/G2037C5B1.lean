import Mathlib
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.IsolatingTopology
import NlsGge.Atomic.G2.G2046

                                                                                                    
                                                                                                   
                                                                                                 
                                                                                                           
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G2037B1Aux

/-- Two distinct isolating balls of an isolating family have no common point. -/
theorem balls_disjoint {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ} (hf : IsolatingFamily38 φ C R)
    {k m : ℤ} (hkm : k ≠ m) {z : ℂ} (hk : z ∈ ball (C k) (R k)) (hm : z ∈ ball (C m) (R m)) :
    False := by
  obtain ⟨c, N, ⟨_, _, hc1, hdist, _⟩, _⟩ := hf
  have h1 := (hdist k m hkm).1
  have hpos : 0 < c⁻¹ * |((k - m : ℤ) : ℝ)| := by
    have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
    have : (1 : ℝ) ≤ |((k - m : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |k - m| := Int.one_le_abs (sub_ne_zero.2 hkm)
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|k - m| : ℤ) : ℝ) := by exact_mod_cast this
      simpa [Int.cast_abs] using h2
    positivity
  have h2 : ballDistance38 (C k) (C m) (R k) (R m) ≤ 0 := by
    unfold ballDistance38
    apply csInf_le
    · exact ⟨0, by rintro v ⟨a, _, b, _, rfl⟩; exact dist_nonneg⟩
    · exact ⟨z, hk, z, hm, by simp⟩
  linarith

end G2037B1Aux

/-- Each gap cut lies in the isolating ball of its index. -/
theorem g2037b1_gapSegment_subset_ball {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) (n : ℤ) : gapSegment φ n ⊆ ball (C n) (R n) := by
  obtain ⟨_, _, _, hS⟩ := hf
  unfold gapSegment
  exact (hS.1 n).1

/-- Distinct gap cuts of an isolating family are disjoint. -/
theorem g2037b1_gapSegment_disjoint {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) {m n : ℤ} (hmn : m ≠ n) :
    Disjoint (gapSegment φ m) (gapSegment φ n) := by
  rw [Set.disjoint_left]
  intro z hzm hzn
  exact G2037B1Aux.balls_disjoint hf hmn (g2037b1_gapSegment_subset_ball hf m hzm)
    (g2037b1_gapSegment_subset_ball hf n hzn)

/-- Distinct gap cuts of the real slice of any physical `u` are disjoint (the isolating family
exists for every real slice, by `isolating_family38` and `realSlice_mem_gkW`). -/
theorem g2037b1_realSlice_gapSegment_disjoint (u : PhysicalL2) {m n : ℤ} (hmn : m ≠ n) :
    Disjoint (gapSegment (realSlice u) m) (gapSegment (realSlice u) n) :=
  g2037b1_gapSegment_disjoint (isolating_family38 (realSlice u) (realSlice_mem_gkW u)) hmn

end
end NlsGge.GKDefinitionDesign
