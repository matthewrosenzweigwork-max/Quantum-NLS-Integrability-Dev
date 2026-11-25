import Mathlib
import NlsGge.Atomic.M.M011Support2

/- M-011 PRODUCTION01 (proof development, AUTHOR; not reviewed).  Head VERBATIM from Pro round 14
   (PRO_DEFINITION_RESPONSE_FP80_14.md, cluster 7, "### M-011"); `NlsGge.GKDefinitionDesign.gap` is the landed G2-046 name.
   Route (Molnar Appendix A, proof of Lemma 3(i)): base point by the parametric Joukowski endpoint integral at the
   noncollapsed base gap (M011Support2.base_good), then transport along cut-free segments over the preconnected fiber
   (M011Support1.good_of_good).  No hypothesis beyond the head. -/
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
