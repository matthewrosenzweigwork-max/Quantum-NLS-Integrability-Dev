import Mathlib
import NlsGge.Atomic.M.M010
import NlsGge.Atomic.M.M013
import NlsGge.Atomic.M.M016DiscIdentity
import NlsGge.Atomic.M.M016RayUniform
import NlsGge.Atomic.M.M016RayCalibGK

                                                                                                     
                                                                                                                   
                                                                          
                                                                                                                     
                                                                                                               
                                                                                                                   
                                                                                                                          
                                                                                                                 
                                        
                                                                                                            
                                                                                                                 
                                                                                                         
                                                                                                                 
                                                                                  
                                                                              
                                                                                 

set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M016ChartAux

open NlsGge.ThirdConsultation.MPrimitive

theorem primitive_vacuum (z : ℂ)
    (h : (0 : PotPair) ∈ gkW ∧ z ∈ endpointClosureFiber (0 : PotPair)) :
    M.primitive ⟨((0 : PotPair), z), h⟩ = -Complex.I * z := by
  obtain ⟨hz, e⟩ := (M.primitive_gap_values (0 : PhysicalL2) 0).2.2.1 z
  have key : ∀ (ψ : PotPair), ψ = realSlice (0 : PhysicalL2) →
      ∀ h' : ψ ∈ gkW ∧ z ∈ endpointClosureFiber ψ, M.primitive ⟨(ψ, z), h'⟩ = -Complex.I * z := by
    rintro ψ rfl h'
    exact e
  exact key 0 realSlice_zero.symm h

theorem continuousAt_of_primitive (P : PotPair → ℂ → ℂ)
    (hP : ∀ (ψ : PotPair) (z : ℂ) (h : ψ ∈ gkW ∧ z ∈ endpointClosureFiber ψ),
      P ψ z = M.primitive ⟨(ψ, z), h⟩)
    (p : PotPair × ℂ) (hp : p ∈ M.primitiveDomain) : ContinuousAt (Function.uncurry P) p := by
  obtain ⟨U, hU, hpU, F, _, hFeq, hFan⟩ := M.primitive_analytic p hp
  have heq : F =ᶠ[𝓝 p] Function.uncurry P := by
    filter_upwards [hU.mem_nhds hpU] with r hr
    obtain ⟨hr', e⟩ := hFeq r hr
    rw [e]
    exact (hP r.1 r.2 hr').symm
  exact (hFan p hpU).continuousAt.congr heq

theorem primitive_ray_tendsto (P : PotPair → ℂ → ℂ)
    (hP : ∀ (ψ : PotPair) (z : ℂ) (h : ψ ∈ gkW ∧ z ∈ endpointClosureFiber ψ),
      P ψ z = M.primitive ⟨(ψ, z), h⟩)
    (φ : PotPair) (hφ : φ ∈ gkW) :
    Tendsto (fun t : ℝ => P φ (Complex.I * t) - t) atTop (𝓝 0) := by
  refine ray_tendsto_of_identity P ?_ ?_ M016AssemblyAux.ray_bound ?_ φ hφ
  · intro ψ hψ z hz
    exact continuousAt_of_primitive P hP (ψ, z) (show ψ ∈ gkW ∧ z ∉ gapSegments38 ψ from ⟨hψ, hz⟩)
  · intro ψ hψ z hz
    have h : ψ ∈ gkW ∧ z ∈ endpointClosureFiber ψ := ⟨hψ, Or.inl hz⟩
    rw [hP ψ z h]
    exact M.primitive_discriminant_identity ψ hψ z h.2
  · intro t
    have h0 : (0 : PotPair) ∈ gkW ∧ Complex.I * (t : ℂ) ∈ endpointClosureFiber (0 : PotPair) := by
      obtain ⟨hz, -⟩ := (M.primitive_gap_values (0 : PhysicalL2) 0).2.2.1 (Complex.I * (t : ℂ))
      simpa only [realSlice_zero] using hz
    rw [hP 0 _ h0, primitive_vacuum]
    linear_combination (-(t : ℂ)) * Complex.I_sq

end NlsGge.ThirdConsultation.M016ChartAux

namespace NlsGge.ThirdConsultation.M

open NlsGge.ThirdConsultation.M016ChartAux

/-- **(S5b)** in exactly the `hray` form consumed by `finitegap_pair_primitive_meromorphic_infinity_of_ray`. -/
theorem primitive_ray_calibration (φ : PotPair) (hφ : φ ∈ gkW) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T < t →
      ∀ h : φ ∈ gkW ∧ Complex.I * (t : ℂ) ∈ MPrimitive.endpointClosureFiber φ,
        ‖primitive ⟨(φ, Complex.I * (t : ℂ)), h⟩ - t‖ < ε := by
  classical
  let P : PotPair → ℂ → ℂ := fun ψ z =>
    if h : ψ ∈ gkW ∧ z ∈ MPrimitive.endpointClosureFiber ψ then primitive ⟨(ψ, z), h⟩ else 0
  have hP : ∀ (ψ : PotPair) (z : ℂ) (h : ψ ∈ gkW ∧ z ∈ MPrimitive.endpointClosureFiber ψ),
      P ψ z = primitive ⟨(ψ, z), h⟩ := fun ψ z h => dif_pos h
  have htend := primitive_ray_tendsto P hP φ hφ
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.1 (htend.eventually (Metric.ball_mem_nhds 0 hε))
  refine ⟨T, fun t ht h => ?_⟩
  have h1 : ‖P φ (Complex.I * t) - t‖ < ε := by
    simpa only [mem_ball, dist_zero_right] using hT t ht.le
  rw [hP φ _ h] at h1
  exact h1

end NlsGge.ThirdConsultation.M
