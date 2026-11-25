import Mathlib
import NlsGge.Atomic.G1.G1082Sup1
import NlsGge.Atomic.G1.G1082Sup3

                                                                                                        
                                                                                                                                    
                                                                                                                                 
                                                                       
                                                                                                                               
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1082Sup6
noncomputable section

theorem const_of_continuous_sq_const {f : ℝ → ℝ} (hf : Continuous f) (h : ∀ t, f t ^ 2 = f 0 ^ 2) (t : ℝ) :
    f t = f 0 := by
  by_contra hne
  have hneg : f t = -f 0 := (sq_eq_sq_iff_eq_or_eq_neg.mp (h t)).resolve_left hne
  have hne0 : f 0 ≠ 0 := by
    intro h0; apply hne; rw [hneg, h0]; simp
  have h0mem : (0 : ℝ) ∈ Set.uIcc (f 0) (f t) := by
    rw [hneg, Set.mem_uIcc]
    rcases le_total (f 0) 0 with h1 | h1
    · left; exact ⟨h1, by linarith⟩
    · right; exact ⟨by linarith, h1⟩
  obtain ⟨s, _, hs0⟩ := intermediate_value_uIcc (a := 0) (b := t) hf.continuousOn h0mem
  have h2 : f 0 ^ 2 = 0 := by rw [← h s, hs0]; norm_num
  exact hne0 (pow_eq_zero_iff (by norm_num) |>.mp h2)

theorem continuous_flow (n : ℤ) (u : PhysicalL2) : Continuous (fun t : ℝ => singleGapFlow n t u) :=
  continuous_iff_continuousAt.mpr fun t =>
    (NlsGge.Atomic.G1081Sup5.singleGapFlow_hasDerivAt n u t).continuousAt

theorem deltaMu_flow_other (n m : ℤ) (hmn : m ≠ n) (u : PhysicalL2) (t : ℝ) :
    deltaMu (singleGapFlow n t u) m = deltaMu u m := by
  have hc : Continuous (fun t : ℝ => deltaMu (singleGapFlow n t u) m) :=
    (continuousOn_univ.mp (analyticOnNhd_deltaMu38 m).continuousOn).comp (continuous_flow n u)
  have hsq : ∀ s : ℝ, deltaMu (singleGapFlow n s u) m ^ 2 =
      (discrim (realSlice u) (gkMu u m : ℂ)).re ^ 2 - 4 := by
    intro s
    have h := deltaMu_squared38 (singleGapFlow n s u) m
    rw [NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n s u,
      NlsGge.Atomic.G1082Sup1.gkMu_flow_other n m hmn u s] at h
    linarith
  have h := const_of_continuous_sq_const hc
    (fun s => by rw [hsq s, hsq 0]) t
  simpa [NlsGge.Atomic.G1081Sup5.singleGapFlow_zero] using h

/-- Signed Dirichlet data (`(mu_m, Re chi(mu_m))`) of all other indices are preserved by the n-th flow. -/
theorem signed_data_flow_other (n m : ℤ) (hmn : m ≠ n) (u : PhysicalL2) (t : ℝ) :
    (gkMu (singleGapFlow n t u) m, (antiDiscrim (realSlice (singleGapFlow n t u))
        (gkMu (singleGapFlow n t u) m : ℂ)).re) =
      (gkMu u m, (antiDiscrim (realSlice u) (gkMu u m : ℂ)).re) := by
  refine Prod.ext (NlsGge.Atomic.G1082Sup1.gkMu_flow_other n m hmn u t) ?_
  exact deltaMu_flow_other n m hmn u t

end
end NlsGge.Atomic.G1082Sup6
