import QuantumNLS.RootHilbertQuantiles
/-! integrator-authored trusted spec for R-409128A9 lem:root-Hilbert-quantiles (Terra r134 ACCEPT): frozen statements of RootHilbertQuantiles restated verbatim. -/
namespace R409Spec
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open QuantumNLS.RootHilbert
open QuantumNLS QuantumNLS.RootHilbertQuantiles

set_option maxHeartbeats 4000000 in
theorem root_Hilbert_quantiles_spec  {ρ σ : ℝ → ℝ} (hρ : HilbertHyp ρ) (hσ : HilbertHyp σ) {m : ℝ}
    (hm : 0 < m) (hρm : ∫ x, ρ x = m) (hσm : ∫ x, σ x = m)
    (hd : MemLp (fun s => qtl ρ s - qtl σ s) 2 (volume.restrict (Ioo 0 m))) :
    Integrable (fun s => (qtl ρ s - qtl σ s) * hilbertPV ρ (qtl ρ s))
        (volume.restrict (Ioo 0 m)) ∧
      Integrable (fun s => (qtl ρ s - qtl σ s) * hilbertPV σ (qtl σ s))
        (volume.restrict (Ioo 0 m)) ∧
      ∫ s in Ioo 0 m, (qtl ρ s - qtl σ s) * (hilbertPV ρ (qtl ρ s) - hilbertPV σ (qtl σ s))
        ≤ 0 := by
  apply QuantumNLS.RootHilbertQuantiles.root_Hilbert_quantiles <;> assumption

end R409Spec
#print axioms R409Spec.root_Hilbert_quantiles_spec
