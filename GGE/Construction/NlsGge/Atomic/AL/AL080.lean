import Mathlib
import NlsGge.Hierarchy.ALFreeFields38

                                                                                                                                    
                                                                                                                              
                                                                                                    
                                                                                                                
                                                                                                         
                                                                                               
set_option autoImplicit false
open Filter NlsGge.Pilot NlsGge.AblowitzLadik NlsGge.Weights
open scoped Topology

namespace NlsGge.ThirdConsultation.AL
namespace al080Aux

theorem admissible {lower upper : ℝ} (c : BoundedCoefficients lower upper) :
    AdmissibleWeight38 lower upper c.val := by
  obtain ⟨hl, -, hb⟩ := c.2
  exact ⟨hl, fun j => (hb j).1, fun j => (hb j).2⟩

theorem c0_pos {lower upper : ℝ} (c : BoundedCoefficients lower upper) : 0 < c.val 0 :=
  lt_of_lt_of_le (admissible c).1 ((admissible c).2.1 0)

theorem c0_le_comp {lower upper : ℝ} (c : BoundedCoefficients lower upper) (k : ℤ) :
    c.val 0 ≤ alRateComp38 c.val k := by
  unfold alRateComp38
  calc c.val 0 = weight c.val 0 := (weight_at_zero c.val).symm
    _ ≤ weight c.val (4 * |(k : ℝ)|) := weight_mono_abs38 (admissible c) (by simp)

end al080Aux

theorem al080 (lower upper : ℝ) (c : BoundedCoefficients lower upper) :
    (∀ N : ℕ, alMeshStep38 N ≤ c.val 0 / 2 →
      ∀ k : ℤ, |k| ≤ (N : ℤ) →
        0 < (1 / 2 : ℝ) * alRateComp38 c.val k ∧
        (1 / 2 : ℝ) * alRateComp38 c.val k ≤ alRateFree38 c.val N k) ∧
    (∀ k : ℤ, Tendsto (fun N : ℕ => alRateFree38 c.val N k) atTop
      (𝓝 (alRateCont38 c.val k))) := by
  refine ⟨?_, fun k => alRateFree_tendsto38 (al080Aux.admissible c) k⟩
  intro N hN k hk
  have hW := al080Aux.c0_le_comp c k
  have hc0 := al080Aux.c0_pos c
  obtain ⟨h1, -⟩ := alOmega_abs_bounds38 N k hk
  have hmono : alRateComp38 c.val k ≤ weight c.val (alOmegaFree38 N k) := by
    unfold alRateComp38
    refine weight_mono_abs38 (al080Aux.admissible c) ?_
    rw [abs_of_nonneg (by positivity)]
    exact h1
  unfold alRateFree38
  constructor
  · linarith
  · linarith

end NlsGge.ThirdConsultation.AL
