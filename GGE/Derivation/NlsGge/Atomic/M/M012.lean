import Mathlib
import NlsGge.Atomic.M.M012Support1

/- M-012 PRODUCTION01 (proof development, AUTHOR; not reviewed).  Head VERBATIM from Pro round 14
   (PRO_DEFINITION_RESPONSE_FP80_14.md, cluster 7, "### M-012").
   Route (Molnar Appendix A, Lemma 3(i)): at the collapsed base gap the landed primitive at a nearby cut-free point equals
   `log ((Δ + canonRoot) / K)` (M012Support1.base_good_collapsed; an analytic, hence continuous, local representative),
   transported along cut-free segments (M011Support1.good_of_good).  The representative is analytic on V; the head
   only asks ContinuousAt at φ.  See M012_ROUTE.md. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem primitive_continuous_collapsed
    (φ : PotPair) (z : ℂ) (hdom : (φ, z) ∈ primitiveDomain)
    (hgap : NlsGge.GKDefinitionDesign.gap φ 0 = 0) :
    ∃ (V : Set PotPair) (hV : IsOpen V), φ ∈ V ∧
      ∃ F : PotPair → ℂ,
        (∀ ψ : PotPair, ∀ hψ : ψ ∈ V,
          ∃ hp : ψ ∈ gkW ∧ z ∈ MPrimitive.endpointClosureFiber ψ,
            (ψ, z) ∈ primitiveDomain ∧
            F ψ = primitive ⟨(ψ, z), hp⟩) ∧
        ContinuousAt F φ := by
  have hd : (φ, z) ∈ rootDomain38 := hdom
  obtain ⟨z1, hz1, hg1⟩ := M012Aux.base_good_collapsed φ hd.1 hgap
  obtain ⟨V, hV, hφV, F, hF, hFan⟩ := M011Aux.good_of_good hd.1 hz1 hd.2 hg1
  refine ⟨V, hV, hφV, F, fun ψ hψ => ?_, (hFan φ hφV).continuousAt⟩
  obtain ⟨hψd, hval⟩ := hF ψ hψ
  exact ⟨⟨hψd.1, Or.inl hψd.2⟩, hψd, hval _⟩

end NlsGge.ThirdConsultation.M
