import QuantumNLS.Prop019FullLinearization
/-! integrator-authored trusted spec for PROP-019 Q7A:lem:linearization (Terra r161 FULL ACCEPT): headline statement(s) copied verbatim from Prop019FullLinearization (QuantumNLS.Prop019FullLinearization). -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace QuantumNLS.P019Spec
open QuantumNLS.Prop019FullLinearization
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (NbhdN)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.Prop019Linearization (pw continuous_pw rect_mem gammaN_abs rect_im_ne rect_wlen_le)
open QuantumNLS.MPContour (nu zθ uθ rectPieces)
open QuantumNLS.MPFamily (BgFam gθ dθ)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.Prop019FullOperators (C0 Linear EventProjection eventProjection pieces)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem prop019_full_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) (d k : ℕ) :
    ∃ ρ R0 η M c1 C : ℝ, 0 < ρ ∧ 2 * ρ < h ∧ 1 ≤ R0 ∧ 0 < η ∧ 1 ≤ M ∧ 0 ≤ c1 ∧ 0 ≤ C ∧
      ∃ N0 : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ q : ℕ, N0 ≤ k + q → ∀ hN : 1 ≤ k + q,
      ∀ R : ℝ, R0 ≤ R → ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ,
      a = QuantumNLS.PROP017UniformN.cutSeq L l → 2 * R ≤ a →
      ∃ B : BgFam (NbhdN a h (ρ / 8)) η (M + M * M) (1 / M) c1,
        B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧
        B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧ B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧
        B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
        ∃ P : EventProjection hκ hN u hu (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b),
        ∀ φ : SymSector ℂ (L2T L) (k + q), φ ∈ Set.range P.op → ‖φ‖ = 1 →
        ∀ (t : ℝ) (p : ℕ → ℝ),
          comparison (κ := κ) k q a h d p B t φ ≤
            ENNReal.ofReal (C * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) *
              (1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ))) := by
  exact QuantumNLS.Prop019FullLinearization.prop019_full hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc d k

set_option maxHeartbeats 8000000 in
theorem prop019_printed_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) (d k : ℕ) (θ : ℝ) (hθ : 0 < θ) :
    ∃ ρ R0 η M c1 C : ℝ, 0 < ρ ∧ 2 * ρ < h ∧ 1 ≤ R0 ∧ 0 < η ∧ 1 ≤ M ∧ 0 ≤ c1 ∧ 0 ≤ C ∧
      ∀ᶠ q : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ hN : 1 ≤ k + q,
      let a := QuantumNLS.PROP018Probability.cutN L θ (k + q)
      let R := (((k + q : ℕ) : ℝ) ^ θ)
      ∃ B : BgFam (NbhdN a h (ρ / 8)) η (M + M * M) (1 / M) c1,
        B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧
        B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧ B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧
        B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
        ∃ P : EventProjection hκ hN u hu (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b),
        ∀ φ : SymSector ℂ (L2T L) (k + q), φ ∈ Set.range P.op → ‖φ‖ = 1 →
        ∀ (T : ℝ), 0 ≤ T → ∀ (p : ℕ → ℝ) (t : ℝ), |t| ≤ T →
          comparison (κ := κ) k q a h d p B t φ ≤
            ENNReal.ofReal (C * (T * ∑ r ∈ Finset.range (d + 1), |p r|) *
              (1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ))) := by
  exact QuantumNLS.Prop019FullLinearization.prop019_printed hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc d k θ hθ

end QuantumNLS.P019Spec
#print axioms QuantumNLS.P019Spec.prop019_full_spec
#print axioms QuantumNLS.P019Spec.prop019_printed_spec
