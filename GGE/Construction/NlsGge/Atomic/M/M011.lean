import Mathlib
import NlsGge.Atomic.M.M011Support2

                                                                                           
                                                                                                                           
                                                                                                                  
                                                                                                                     
                                                                  
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem primitive_analytic_open_gap
    (φ : PotPair) (z : ℂ) (hdom : (φ, z) ∈ primitiveDomain)
    (hgap : NlsGge.GKDefinitionDesign.gap φ 0 ≠ 0) :
    ∃ (V : Set PotPair) (hV : IsOpen V), φ ∈ V ∧
      ∃ F : PotPair → ℂ,
        (∀ ψ : PotPair, ∀ hψ : ψ ∈ V,
          ∃ hp : ψ ∈ gkW ∧ z ∈ MPrimitive.endpointClosureFiber ψ,
            (ψ, z) ∈ primitiveDomain ∧
            F ψ = primitive ⟨(ψ, z), hp⟩) ∧
        AnalyticOnNhd ℂ F V := by
  have hd : (φ, z) ∈ rootDomain38 := hdom
  obtain ⟨z1, hz1, hg1⟩ := M011Aux.base_good φ hd.1 hgap
  obtain ⟨V, hV, hφV, F, hF, hFan⟩ := M011Aux.good_of_good hd.1 hz1 hd.2 hg1
  refine ⟨V, hV, hφV, F, fun ψ hψ => ?_, hFan⟩
  obtain ⟨hψd, hval⟩ := hF ψ hψ
  exact ⟨⟨hψd.1, Or.inl hψd.2⟩, hψd, hval _⟩

end NlsGge.ThirdConsultation.M
