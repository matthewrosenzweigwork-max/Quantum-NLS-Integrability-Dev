import Mathlib
import NlsGge.Atomic.G1.G1081Host
import NlsGge.Atomic.G1.G1081Sup5
import NlsGge.Atomic.G1.G1081Sup6
import NlsGge.Atomic.G1.S4L3

/- G1-081 S4 / L5 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/S4Asm.lean.
   NEW assembly lemma: the full G1-081 head with the analytic conjunct supplied by L1-L4 (S4L3.analyticOnNhd_complete_flow) instead of the
   strong `AnalyticFlowDependence`. Hypotheses: Pro S4 `exists_local_complex_analytic_flow`
   (now unconditional via proof development S4PicardAnalytic). -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign NlsGge.Atomic.G1081S4L3
namespace NlsGge.Atomic.G1081S4Asm
noncomputable section

theorem g1081_assembly_analytic_of_compact
    (hcpt : ∀ u : PhysicalL2, IsCompact (isospectralSet u))
    (n : ℤ) :
    (∃! f : ℝ → PhysicalL2 → PhysicalL2, completeGapFlow n f) ∧
    completeGapFlow n (singleGapFlow n) ∧
    AnalyticOnNhd ℝ
      (fun p : ℝ × PhysicalL2 => singleGapFlow n p.1 p.2) Set.univ ∧
    (∀ s t : ℝ, ∀ u : PhysicalL2,
      singleGapFlow n (s+t) u = singleGapFlow n s (singleGapFlow n t u)) ∧
    (∀ t : ℝ, ∀ u : PhysicalL2,
      isospectral u (singleGapFlow n t u)) := by
  have hc := NlsGge.Atomic.G1081Sup5.singleGapFlow_complete_of_compact hcpt n
  exact ⟨NlsGge.Atomic.G1081Sup5.completeGapFlow_existsUnique_of_compact hcpt n, hc,
    NlsGge.Atomic.G1081S4L3.analyticOnNhd_complete_flow n hc,
    fun s t u => NlsGge.Atomic.G1081Sup5.completeGapFlow_group n hc s t u,
    fun t u => NlsGge.Atomic.G1081Sup6.singleGapFlow_isospectral_of_compact hcpt n t u⟩

-- BEGIN G1080-DEPENDENT
theorem g1081_assembly_analytic
    (n : ℤ) :
    (∃! f : ℝ → PhysicalL2 → PhysicalL2, completeGapFlow n f) ∧
    completeGapFlow n (singleGapFlow n) ∧
    AnalyticOnNhd ℝ
      (fun p : ℝ × PhysicalL2 => singleGapFlow n p.1 p.2) Set.univ ∧
    (∀ s t : ℝ, ∀ u : PhysicalL2,
      singleGapFlow n (s+t) u = singleGapFlow n s (singleGapFlow n t u)) ∧
    (∀ t : ℝ, ∀ u : PhysicalL2,
      isospectral u (singleGapFlow n t u)) :=
  g1081_assembly_analytic_of_compact (fun v => (G1_080 v).1) n
-- END G1080-DEPENDENT

end
end NlsGge.Atomic.G1081S4Asm
