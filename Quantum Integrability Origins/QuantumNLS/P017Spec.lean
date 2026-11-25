import QuantumNLS.Prop017Physical
import QuantumNLS.RootSpectralInputsDischarge
/-! integrator-authored trusted spec for PROP-017 Q7A:prop:packet (Terra r156 ACCEPT under printed hypotheses; owner-approved epsilon-indexed events): headline statement(s) copied verbatim from Prop017Physical. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace QuantumNLS.P017Spec
open QuantumNLS.Prop017Physical
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.BetheCoefficientTransform (bornLaw)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (tailFraction EN prop017Cb)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN rNbhd KGN sNsrc sLimsrc)
open QuantumNLS.NonvanishingD (Dsrc)
open QuantumNLS.PROP017UniformN (cutSeq prop017_uniform)
open QuantumNLS.PROP018Probability (cutN cutIdx propBound regime_eventually tendsto_of_bound)
open QuantumNLS.Prop017Quantum (qAct measurable_qAct eta0 eta0_pos ms_actual tail_actual Ctail Dtail)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem prop017_physical_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ R0 : ℝ, 1 ≤ R0 ∧ ∃ r : ℝ, 0 < r ∧
      (∀ R : ℝ, R0 ≤ R → ∀ a : ℝ, 2 * R ≤ a → r ≤ rNbhd a h ρ R δ) ∧
      ∃ N0 : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ N : ℕ, N0 ≤ N → 1 ≤ N →
        ∀ R : ℝ, R0 ≤ R → ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ, a = cutSeq L l → 2 * R ≤ a →
          (∀ p : ℕ, 1 ≤ p → eta0 L κ ≤ R →
              (bornMeasure (physBasis L hκ N) u hu).real (EN (μ : Measure ℝ) (qAct L κ N) R a ρ h (eta0 L κ) ε b)ᶜ
                ≤ (N : ℝ) * (Ctail (μ : Measure ℝ) p * (1 / R ^ (2 * p))) + Dtail κ p / R
                  + prop017Cb (eta0 L κ) h ρ Csharp b * (1 + a) / ((N : ℝ) * ε ^ 3)) ∧
          (∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) R a ρ h (eta0 L κ) ε b,
              (∀ j, |qAct L κ N m j| ≤ R) ∧
              (∀ z ∈ NbhdN a h ρ, ‖Gfull (μ : Measure ℝ) z - GN (qAct L κ N m) z‖ ≤
                2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ) * (ε + 1 / R ^ b)) ∧
              (∀ z ∈ NbhdN a h (ρ / 2), ∀ n : ℕ,
                ‖iteratedDeriv n (fun w => sNsrc κ L (qAct L κ N m) w - sLimsrc κ L (μ : Measure ℝ) w) z‖ ≤
                  n.factorial * (Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ)))
                    * max (κ ^ 2 / r ^ 2) (|κ| * (2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ)))
                    * (ε + 1 / R ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n)) ∧
          (∀ z ∈ NbhdN a h (ρ / 4), d0 / 2 ≤ ‖Dsrc κ L (μ : Measure ℝ) z‖) := by
  first
  | exact QuantumNLS.Prop017Physical.prop017_physical
  | (apply QuantumNLS.Prop017Physical.prop017_physical <;> assumption)

set_option maxHeartbeats 8000000 in
theorem prop017_physical_diagonal_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (θ γ : ℝ) (hθ : 0 < θ) (hγ : 0 < γ) (hsum : 3 * γ + θ < 1) (p : ℕ) (hp : 1 < 2 * (p : ℝ) * θ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) ∧
      (∀ᶠ N : ℕ in atTop, ∀ m ∈ EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ θ) (cutN L θ N) ρ h (eta0 L κ)
          ((N : ℝ) ^ (-γ)) b,
        (∀ j, |qAct L κ N m j| ≤ (N : ℝ) ^ θ) ∧
        ∀ z ∈ NbhdN (cutN L θ N) h ρ, ‖Gfull (μ : Measure ℝ) z - GN (qAct L κ N m) z‖ ≤
          2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ) * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) ∧
      Tendsto (fun N : ℕ => 2 * KGN (eta0 L κ) δ ρ (h + 5) Csharp b pc (μ : Measure ℝ) *
        ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b)) atTop (𝓝 0) := by
  exact QuantumNLS.Prop017Physical.prop017_physical_diagonal hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc θ γ hθ hγ hsum p hp

end QuantumNLS.P017Spec
#print QuantumNLS.Prop017Physical.RootSpectralInputs
#print QuantumNLS.RootSpectralInputsDischarge.EvenMoments
#print axioms QuantumNLS.P017Spec.prop017_physical_spec
#print axioms QuantumNLS.P017Spec.prop017_physical_diagonal_spec
