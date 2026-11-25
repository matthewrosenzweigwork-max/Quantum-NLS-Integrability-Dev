import Mathlib
import NlsGge.Atomic.G2.G2037
import NlsGge.Atomic.G2.G2044
import NlsGge.Atomic.G2.G2045SupA2
import NlsGge.Atomic.G2.G2045SupA3
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.ThirdConsultation.G1.Round6

                                                                                      
                                                                                                             
                                                                                                               
                                                                                                          
                                                                                                           
                                                                                                              
                                                                                                                
                                                                                   
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G2045SupA4Aux

/-- Core: everything but the two landed inputs, which enter as the displayed hypotheses
(`hAn`, `hEq`, `hf`, `hexp`, `hcoef` are exactly conclusions of `G2_037` and `G2_044`). -/
theorem trace_core (u : PhysicalL2) (S : Finset ℤ)
    (hAn : AnalyticOnNhd ℂ (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ)
    (hEq : ∀ z : ℂ, (realSlice u, z) ∈ rootDomain38 →
      deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z = finiteGapDifferential u S z)
    (R : ℝ) (hR : 0 < R) (hcuts : finiteGapCuts u S ⊆ Metric.closedBall (0 : ℂ) R)
    (f g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (hf : ∀ z : ℂ, R < ‖z‖ → HasDerivAt f (finiteGapDifferential u S z) z)
    (hexp : ∀ z : ℂ, R < ‖z‖ → f z = -Complex.I * z + g z⁻¹)
    (k : ℕ) (hk : 2 ≤ k)
    (hcoef : iteratedDeriv k g 0 / (Nat.factorial k : ℂ) =
      hierarchyHamiltonian k (realSlice u) / (2 * Complex.I) ^ k) :
    Summable (fun n : ℤ => ‖higherAction k (realSlice u) n‖) ∧
    HasSum (fun n : ℤ => higherAction k (realSlice u) n)
      (-(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k (realSlice u)) := by
  classical
  have hφ : realSlice u ∈ gkW := realSlice_mem_gkW u
  have hcutsOf : finiteGapCuts u S = NlsGge.G2045SupA3.cutsOf (realSlice u) S := rfl
  obtain ⟨ρ0, hρ0, hcirc⟩ := NlsGge.G2045SupA2.circle_pow_deriv R f g (finiteGapDifferential u S)
    hg hf hexp k hk
  set ρ : ℝ := max (max ρ0 R) 0 + 1 with hρ
  have hρ1 : ρ0 < ρ := by
    have := le_trans (le_max_left ρ0 R) (le_max_left (max ρ0 R) 0); linarith
  have hρ2 : R < ρ := by
    have := le_trans (le_max_right ρ0 R) (le_max_left (max ρ0 R) 0); linarith
  have hρpos : 0 < ρ := by
    have := le_max_right (max ρ0 R) 0; linarith
  have hKρ : NlsGge.G2045SupA3.cutsOf (realSlice u) S ⊆ ball (0 : ℂ) ρ := by
    intro z hz
    have := hcuts (hcutsOf ▸ hz)
    rw [mem_closedBall, dist_zero_right] at this
    rw [mem_ball, dist_zero_right]
    linarith
  have hFan : DifferentiableOn ℂ (finiteGapDifferential u S)
      (NlsGge.G2045SupA3.cutsOf (realSlice u) S)ᶜ := hAn.differentiableOn
  have hsum := NlsGge.G2045SupA3.sum_circles_eq_large (realSlice u) hφ S _ hFan hEq ρ hρpos hKρ k
  have hzero : ∀ n : ℤ, n ∉ S → higherAction k (realSlice u) n = 0 := by
    intro n hn
    unfold higherAction
    rw [NlsGge.G2045SupA3.circle_zero_of_not_mem (realSlice u) hφ S _ hFan hEq k n hn, mul_zero]
  have hnorm : ∀ n : ℤ, n ∉ S → ‖higherAction k (realSlice u) n‖ = 0 := fun n hn => by
    rw [hzero n hn, norm_zero]
  have hsm : Summable (fun n : ℤ => ‖higherAction k (realSlice u) n‖) :=
    summable_of_ne_finset_zero (s := S) hnorm
  refine ⟨hsm, ?_⟩
  have hHS : HasSum (fun n : ℤ => higherAction k (realSlice u) n)
      (∑ n ∈ S, higherAction k (realSlice u) n) :=
    hasSum_sum_of_ne_finset_zero (s := S) hzero
  convert hHS using 1
  -- value
  have e1 : ∑ n ∈ S, higherAction k (realSlice u) n =
      (1 / (Real.pi : ℂ)) * circleIntegral (fun z : ℂ => z ^ k * finiteGapDifferential u S z) 0 ρ := by
    rw [← hsum, Finset.mul_sum]
    rfl
  rw [e1, hcirc ρ hρ1]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hD : iteratedDeriv (j + 1) g 0 =
      (Nat.factorial (j + 1) : ℂ) * (hierarchyHamiltonian (j + 1) (realSlice u) / (2 * Complex.I) ^ (j + 1)) := by
    have hkf : ((j + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [← hcoef]; field_simp
  rw [Nat.add_sub_cancel, hD, Nat.factorial_succ]
  have hjf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2I : (2 * Complex.I : ℂ) ≠ 0 := by simp
  push_cast
  rw [pow_succ]
  field_simp

end G2045SupA4Aux

/-- **G2-045, finite-gap contour trace identity.**  For smooth finite-gap `u` and `k ≥ 2`, the higher actions
of `realSlice u` form an absolutely summable (finitely supported) family whose sum is
`-k/(2I)^(k-1) * H_k`. -/
theorem G2045SupA_finiteGap_trace (u : PhysicalL2)
    (hu : NlsGge.ThirdConsultation.KO.SmoothPhysical u)
    (hfg : NlsGge.ThirdConsultation.finiteGap u) (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun n : ℤ => ‖higherAction k (realSlice u) n‖) ∧
    HasSum (fun n : ℤ => higherAction k (realSlice u) n)
      (-(k : ℂ) / (2 * Complex.I) ^ (k - 1) * hierarchyHamiltonian k (realSlice u)) := by
  obtain ⟨S, hS, hAn, hEq, -, R, hR, hcuts, f, g, -, hfd, hg, hexp⟩ := G2_037 u hfg
  have hf : ∀ z : ℂ, R < ‖z‖ → HasDerivAt f (finiteGapDifferential u S z) z := by
    intro z hz
    refine hfd z (fun hzK => ?_)
    have := hcuts hzK
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  exact G2045SupA4Aux.trace_core u S hAn hEq R hR hcuts f g hg hf hexp k hk
    (G2_044 u hu hfg S hS R hR hcuts f g hg hf hexp k hk)

end
end NlsGge.GKDefinitionDesign
