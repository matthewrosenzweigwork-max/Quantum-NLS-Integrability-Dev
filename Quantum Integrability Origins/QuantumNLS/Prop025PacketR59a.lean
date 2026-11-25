import QuantumNLS.Prop025WitnessR59a

/-! Fix the two OPhase errors before taking any charge orders, rank, or boxes.
OPhase uses the sum of the Born failure masses for its two fixed-contour
events and the fixed-contour transfer and derivative tolerance. -/

set_option autoImplicit false
set_option maxHeartbeats 64000000
set_option synthInstance.maxHeartbeats 400000
set_option pp.proofs false

noncomputable section
namespace QuantumNLS.Prop025PacketR59a
open Prop025WitnessR59a
open MeasureTheory Filter Topology
open PhysicalTensor (L2T)
open BulkResponseActual (IsLimitingRapidityMeasure)
open Prop017Physical (RootSpectralInputs)
open Prop017Quantum (eta0)
open Prop025OTarget (enum)
open Def033HierarchyR24m (Smooth physical)
open ActualModelTargetR53a (HigherFlows)

def contourErrors :
    ∀ {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
      {μ : ProbabilityMeasure ℝ}, IsLimitingRapidityMeasure L κ hκ u hu μ →
      ∀ {h : ℝ}, eta0 L κ < h → ∀ {nI : ℕ}, (Fin nI → ℤ) → (ℕ → ℝ) × (ℕ → ℝ) :=
  @fixedContourPair%

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The frozen phase comparison at the very pair constructed from its
fixed-contour events, including their convergence and empty-set clauses. -/
theorem phase_at_packet (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d k : ℕ) (hd : 2 ≤ d) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    {nI : ℕ} (n : Fin nI → ℤ) (Θ : Fin nI → ℝ) (hΘ : ∀ i, 0 ≤ Θ i) :
    packetTail% (Prop025OPhase.quantum_comparison hκ u hu hμ hηh hδ hd0 hin d k hd ords hords T n Θ hΘ)
      using (contourErrors hκ u hu hμ hηh n) :=
  packetProof% (Prop025OPhase.quantum_comparison hκ u hu hμ hηh hδ hd0 hin d k hd ords hords T n Θ hΘ)

/-- Display the introductions explicitly for the OMain elimination. -/
theorem phase_intro (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d k : ℕ) (hd : 2 ≤ d) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    {nI : ℕ} (n : Fin nI → ℤ) (Θ : Fin nI → ℝ) (hΘ : ∀ i, 0 ≤ Θ i) :
    ∃ (η ρ : ℕ → ℝ),
      packetTail% (Prop025OPhase.quantum_comparison hκ u hu hμ hηh hδ hd0 hin d k hd ords hords T n Θ hΘ)
        using ((η, ρ)) :=
  ⟨(contourErrors hκ u hu hμ hηh n).1, (contourErrors hκ u hu hμ hηh n).2,
    phase_at_packet hκ u hu hμ hηh hδ hd0 hin d k hd ords hords T n Θ hΘ⟩

/-- The frozen total-error estimate at that same pair. -/
theorem core_at_packet (hκ : 0 < κ) (Prop021Input : Prop025OInputs.Prop021Input (L := L))
    (WindowInput : Prop025OInputs.WindowInput (L := L) hκ)
    (C : Def021ChartR41b.Chart L κ hκ) (hsob : Def044ChartR51a.SobolevRestrictions hκ C)
    (F : HigherFlows L κ) (u : Smooth L) (hu : ‖physical u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ (physical u) hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d : ℕ) (hd : 2 ≤ d) (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r ∧ r ≤ d) (T : ℕ → ℝ)
    (hT : ∀ r, 0 ≤ T r) (I : Finset ℤ) (Θ : ℤ → ℝ) (hΘ : ∀ n ∈ I, 0 ≤ Θ n) (k : ℕ) (hk : 1 ≤ k) :
    packetTail% (Prop025OMain.core hκ Prop021Input WindowInput C hsob F u hu hμ hηh hδ hd0 hin
      d hd R hR T hT I Θ hΘ k hk) using (contourErrors hκ (physical u) hu hμ hηh (enum I)) :=
  packetProofUsing% (Prop025OMain.core hκ Prop021Input WindowInput C hsob F u hu hμ hηh hδ hd0 hin
    d hd R hR T hT I Θ hΘ k hk) replacing Prop025OPhase.quantum_comparison with phase_intro

end QuantumNLS.Prop025PacketR59a
