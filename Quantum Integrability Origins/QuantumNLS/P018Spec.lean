import QuantumNLS.Prop018SequenceOperatorPacket
/-! integrator-authored trusted spec for PROP-018 Q7A operator reconstruction (Terra r159 FULL ACCEPT under the printed section hypotheses): headline statement(s) copied verbatim from Prop018SequenceOperatorPacket (QuantumNLS.Prop018SequenceOperatorPacket). -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Complex Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace
namespace QuantumNLS.P018Spec
open QuantumNLS.Prop018SequenceOperatorPacket
open PhysicalTensor BetheLabels BulkResponseActual EmpiricalRapidity RootEvent Prop017Quantum
open Prop017Physical PROP018Probability Prop018SequencePhase Prop018SequenceScalar Prop018SequenceWindowOperators
open Extrapolation PeriodReconstructionCore
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem prop018_operator_reconstruct_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (R ε a : ℕ → ℝ) (idx : ℕ → ℕ)
    (hR : ∀ N, 0 < R N) (hε : ∀ N, 0 < ε N)
    (hseq : Tendsto (fun N : ℕ => ε N + 1 / R N ^ b + 1 / (N : ℝ)) atTop (𝓝 0))
    (hcut : ∀ᶠ N : ℕ in atTop, l0 ≤ idx N ∧ a N = PROP017UniformN.cutSeq L (idx N) ∧ 2 * R N ≤ a N)
    (d : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ Cp Cs : ℝ, 0 ≤ Cp ∧ 0 ≤ Cs ∧ ∀ r0 : ℝ, 0 < r0 → ∀ (f : ℂ → ℂ → ℂ) (qt : ℂ → ℂ → ℂ → ℂ),
        (∀ z w, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 → f z w = Prop018Phase.lam L κ (Gfull (μ : Measure ℝ)) z w) →
        (∀ z w v, ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < r0 →
          ‖v - deriv (sf L κ (Gfull (μ : Measure ℝ))) z‖ < r0 → qt z w v = Prop018Phase.qch L κ (Gfull (μ : Measure ℝ)) z w v) →
        ∀ᶠ N : ℕ in atTop, ∃ hN : 0 < N, ∀ p : ℕ → ℝ,
          (∀ z ∈ PeriodReconstruction.Gam (-(a N)) (a N) h,
            ∀ w, ContinuousAt (fun q : ℂ × ℂ => f q.1 q.2) (z, w)) →
          (∀ z ∈ PeriodReconstruction.Gam (-(a N)) (a N) h,
            ∀ w v, ContinuousAt (fun q : ℂ × (ℂ × ℂ) => qt q.1 q.2.1 q.2.2) (z, (w, v))) →
          WindowConclusion (L := L) hκ hN a h
            (EN (μ : Measure ℝ) (qAct L κ N) (R N) (a N) ρ h (eta0 L κ) (ε N) b)
            f qt p d
            (Cp * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a N) ^ (d + 1) / N)
            (Cs * (∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a N) ^ (d + 1) *
              (ε N + 1 / (R N) ^ b + 1 / (N : ℝ)))
            (cscal L κ (μ : Measure ℝ) a h p d N) := by
  exact QuantumNLS.Prop018SequenceOperatorPacket.prop018_operator_reconstruct hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc R ε a idx hR hε hseq hcut d

end QuantumNLS.P018Spec
#print axioms QuantumNLS.P018Spec.prop018_operator_reconstruct_spec
