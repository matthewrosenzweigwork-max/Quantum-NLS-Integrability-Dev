import Mathlib
import NlsGge.Atomic.G1.G1083Host
import NlsGge.Atomic.G1.G1083Sup1
import NlsGge.Atomic.G1.G1082
import NlsGge.Atomic.G1.G1082Sup1
import NlsGge.Atomic.G1.G1082Sup3
import NlsGge.Atomic.G1.G1082Sup5
import NlsGge.Atomic.G1.G1082Sup6

                                                                                                        
                                                                                                                                    
                                                                                                                                             
                                                
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign

namespace NlsGge.Atomic.G1083Sup2
noncomputable section

theorem oscSetup_flow (n : ℤ) (u : PhysicalL2)
    (ho : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n) :
    NlsGge.Atomic.G1083Sup1.OscSetup
      (fun t : ℝ => gkMu (singleGapFlow n t u) n)
      (fun t : ℝ => -(antiDiscrim (realSlice (singleGapFlow n t u))
          (gkMu (singleGapFlow n t u) n : ℂ)).re / 2)
      (fun x : ℝ => (discrim (realSlice u) (x : ℂ)).re ^ 2 - 4)
      (fun x : ℝ => (discrim (realSlice u) (x : ℂ) * deriv (discrim (realSlice u)) (x : ℂ)).re)
      (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
  have h82 := G1_082 n u
  have hΔ : AnalyticOnNhd ℂ (discrim (realSlice u)) Set.univ := analyticOnNhd_discrim_z _
  have hΔ' : AnalyticOnNhd ℂ (deriv (discrim (realSlice u))) Set.univ := hΔ.deriv
  have hc1 : Continuous (fun x : ℝ => discrim (realSlice u) (x : ℂ)) :=
    (continuousOn_univ.mp hΔ.continuousOn).comp Complex.continuous_ofReal
  have hc2 : Continuous (fun x : ℝ => deriv (discrim (realSlice u)) (x : ℂ)) :=
    (continuousOn_univ.mp hΔ'.continuousOn).comp Complex.continuous_ofReal
  have hf : (fun s : ℝ => deriv (fun r : ℝ => gkMu (singleGapFlow n r u) n) s) =
      fun s : ℝ => -(antiDiscrim (realSlice (singleGapFlow n s u))
        (gkMu (singleGapFlow n s u) n : ℂ)).re / 2 := funext fun s =>
    NlsGge.Atomic.G1082Sup1.deriv_gkMu_flow_self n u s
  exact
  { lt := ho
    hg := fun t => h82.2.1 t
    hv := fun t => by
      have := (h82.2.2 ho t).1
      rw [hf] at this
      exact this
    hrng := fun t => by
      have h := gkMu_mem_gap38 (singleGapFlow n t u) n
      rw [isospectral_gapLower_eq (NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n t u) n,
        isospectral_gapUpper_eq (NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n t u) n] at h
      exact h
    hen := fun t => by
      have h := NlsGge.Atomic.G1082Sup3.deltaMu_flow_sq n u t
      unfold deltaMu at h
      calc 4 * (-(antiDiscrim (realSlice (singleGapFlow n t u))
            (gkMu (singleGapFlow n t u) n : ℂ)).re / 2) ^ 2
          = (antiDiscrim (realSlice (singleGapFlow n t u))
            (gkMu (singleGapFlow n t u) n : ℂ)).re ^ 2 := by ring
        _ = _ := h
    hpos := fun x h1 h2 => by
      have := NlsGge.Atomic.G1082Sup3.sq_gt_four_of_mem_open_gap u n x h1 h2
      linarith
    hlo0 := by
      have := (NlsGge.Atomic.G1082Sup3.endpoint_values u n ho _ (Or.inl rfl)).1
      linarith
    hhi0 := by
      have := (NlsGge.Atomic.G1082Sup3.endpoint_values u n ho _ (Or.inr rfl)).1
      linarith
    hNc := ((Complex.continuous_re.comp hc1).pow 2).sub continuous_const
    hDc := Complex.continuous_re.comp (hc1.mul hc2)
    hDlo := (NlsGge.Atomic.G1082Sup3.endpoint_values u n ho _ (Or.inl rfl)).2
    hDhi := (NlsGge.Atomic.G1082Sup3.endpoint_values u n ho _ (Or.inr rfl)).2 }

/-- S83b, open gap: the orbit of the signed Dirichlet datum covers the gap circle. -/
theorem orbit_covers_gapCircle (n : ℤ) (u : PhysicalL2)
    (ho : actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n)
    (p : ℝ × ℝ) (hp : p ∈ gapCircle u n) :
    ∃ t : ℝ, signedDirichletData (singleGapFlow n t u) n = p := by
  obtain ⟨t, ht1, ht2⟩ := (oscSetup_flow n u ho).cover p.1 (-p.2 / 2) hp.1 hp.2.1
    (by have := hp.2.2; nlinarith)
  refine ⟨t, Prod.ext ht1 ?_⟩
  show (antiDiscrim (realSlice (singleGapFlow n t u)) (gkMu (singleGapFlow n t u) n : ℂ)).re = p.2
  linarith

/-- Collapsed gap: the signed datum is constant along the flow. -/
theorem signedData_flow_const_of_collapsed (n : ℤ) (u : PhysicalL2)
    (hc : ¬ actualGapLowerAllE02_38 u n < actualGapUpperAllE02_38 u n) (t : ℝ) :
    signedDirichletData (singleGapFlow n t u) n = signedDirichletData u n := by
  have hg : ∀ s : ℝ, gkMu (singleGapFlow n s u) n = gkMu u n := by
    intro s
    have h1 := gkMu_mem_gap38 (singleGapFlow n s u) n
    have h2 := gkMu_mem_gap38 u n
    rw [isospectral_gapLower_eq (NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n s u) n,
      isospectral_gapUpper_eq (NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral n s u) n] at h1
    push Not at hc
    linarith [h1.1, h1.2, h2.1, h2.2]
  have hcont : Continuous (fun s : ℝ => deltaMu (singleGapFlow n s u) n) :=
    (continuousOn_univ.mp (analyticOnNhd_deltaMu38 n).continuousOn).comp
      (NlsGge.Atomic.G1082Sup6.continuous_flow n u)
  have hsq : ∀ s : ℝ, deltaMu (singleGapFlow n s u) n ^ 2 = deltaMu (singleGapFlow n 0 u) n ^ 2 := by
    intro s
    rw [NlsGge.Atomic.G1082Sup3.deltaMu_flow_sq n u s, NlsGge.Atomic.G1082Sup3.deltaMu_flow_sq n u 0,
      hg s, hg 0]
  have h := NlsGge.Atomic.G1082Sup6.const_of_continuous_sq_const hcont hsq t
  rw [NlsGge.Atomic.G1081Sup5.singleGapFlow_zero] at h
  exact Prod.ext (hg t) h

end
end NlsGge.Atomic.G1083Sup2
