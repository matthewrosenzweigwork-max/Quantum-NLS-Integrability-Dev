import Mathlib
import NlsGge.Atomic.LIB.LIB018

/- G6-003 SUPPORT 1 CORE (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6003Sup1Core.lean, namespace NlsGge.GKDefinitionDesign.G6003Aux.
   Generic real-analytic local inverse chart: a map analytic everywhere whose derivative at a is a continuous linear
   equivalence has open U, V around a, f a and an analytic inverse g on V with all four mapping/inverse identities.
   Built from the landed LIB-018 chart (analyticLocalInverseChart, localInverseChart_analyticOnNhd_target) and LIB-017
   (coe, source membership): U = chart.source ∩ f⁻¹ V, g = chart.symm. -/
set_option autoImplicit false

open Set Filter Topology

namespace NlsGge.GKDefinitionDesign
namespace G6003Aux
noncomputable section

theorem core6003 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (a : E) (hA : AnalyticOnNhd ℝ f Set.univ)
    (h2 : ∃ e : E ≃L[ℝ] F, e.toContinuousLinearMap = fderiv ℝ f a) :
    ∃ (U : Set E) (V : Set F) (g : F → E),
      IsOpen U ∧ a ∈ U ∧ IsOpen V ∧ f a ∈ V ∧
      AnalyticOnNhd ℝ f U ∧ AnalyticOnNhd ℝ g V ∧
      Set.MapsTo f U V ∧ Set.MapsTo g V U ∧
      (∀ v ∈ U, g (f v) = v) ∧
      (∀ z ∈ V, f (g z) = z) := by
  obtain ⟨L, hL⟩ := h2
  have hf : AnalyticAt ℝ f a := hA a (Set.mem_univ a)
  have hL' : fderiv ℝ f a = (L : E →L[ℝ] F) := hL.symm
  obtain ⟨V, hVo, hfaV, hVt, hgV⟩ :=
    NlsGge.Atomic.LIB018.localInverseChart_analyticOnNhd_target hf hL'
  set e := NlsGge.Atomic.LIB018.analyticLocalInverseChart hf hL' with he
  have hcoe : (e : E → F) = f := NlsGge.Atomic.LIB017.localInverseChart_coe _
  have hsrc : a ∈ e.source := NlsGge.Atomic.LIB017.mem_localInverseChart_source _
  have hfc : Continuous f := continuousOn_univ.mp hA.continuousOn
  refine ⟨e.source ∩ f ⁻¹' V, V, e.symm, e.open_source.inter (hVo.preimage hfc), ⟨hsrc, hfaV⟩,
    hVo, hfaV, fun v _ => hA v (Set.mem_univ v), hgV, fun v hv => hv.2, ?_, ?_, ?_⟩
  · intro z hz
    refine ⟨e.map_target (hVt hz), ?_⟩
    show f (e.symm z) ∈ V
    have hr := e.right_inv (hVt hz)
    rw [hcoe] at hr
    rw [hr]
    exact hz
  · intro v hv
    have hl := e.left_inv hv.1
    rw [hcoe] at hl
    exact hl
  · intro z hz
    have hr := e.right_inv (hVt hz)
    rw [hcoe] at hr
    exact hr

end
end G6003Aux
end NlsGge.GKDefinitionDesign
