import QuantumNLS.Prop026Uniform
/-! integrator-authored trusted spec for PROP-026 lem:MP-linearization (review record r15 FULL ACCEPT): headline statement(s) copied verbatim from Prop026Uniform (QuantumNLS.Prop026Uniform). -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace QuantumNLS.P026Spec
open QuantumNLS.Prop026Uniform
open QuantumNLS.PhysicalTensor (L2T physSector)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.Prop017Quantum (qAct eta0 Gfull_eq)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.Prop019Linearization (rect_mem rect_im_ne gammaN_abs)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces polyT continuous_polyT wlen)
open QuantumNLS.MPFamily (BgFam gθ dθ)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.MPFixedContour (bgfamOfG_union)
open QuantumNLS.MPLinearizationContours (mp_linearization_contours)
open QuantumNLS.Prop009ProbeDev (Gam_im_le)
open QuantumNLS.Prop026Mixed (IsEventProj common_projection mixedGap gam_family_background)
open QuantumNLS.MPFixedContour (rectGen rectGen_mem_Gam rectGen_im_ne rectGen_wlen_le)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}
open Classical in

set_option maxHeartbeats 8000000 in
theorem prop026_uniform_spec (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc)
    (d k : ℕ) (ords : Finset ℕ) (hRd : ∀ r ∈ ords, r ≤ d) (T : ℕ → ℝ)
    {r : ℕ} {n : Fin r → ℤ} {xm xp hf : Fin r → ℝ}
    (hxm : ∀ i, xm i ∈ QuantumNLS.Prop026Bound.cuts κ u) (hxp : ∀ i, xp i ∈ QuantumNLS.Prop026Bound.cuts κ u)
    (hlt : ∀ i, xm i < xp i) (hfpos : ∀ i, 0 < hf i) (hfh : ∀ i, hf i ≤ h)
    (h1 : ∀ i, 2 * Real.pi * (n i - 1) < exteriorForce L κ (QuantumNLS.Prop026Bound.M hκ u) (xm i))
    (h2 : ∀ i, exteriorForce L κ (QuantumNLS.Prop026Bound.M hκ u) (xm i) < 2 * Real.pi * n i)
    (h3 : ∀ i, 2 * Real.pi * n i < exteriorForce L κ (QuantumNLS.Prop026Bound.M hκ u) (xp i))
    (h4 : ∀ i, exteriorForce L κ (QuantumNLS.Prop026Bound.M hκ u) (xp i) < 2 * Real.pi * (n i + 1))
    (Θ : Fin r → ℝ) (hΘ : ∀ i, 0 ≤ Θ i) :
    ∃ ρ R0 : ℝ, 0 < ρ ∧ 1 ≤ R0 ∧ ∃ (EI : ∀ N : ℕ, Set (MArr N)) (ρI : ℕ → ℝ), (∀ N, 0 ≤ ρI N) ∧
      Tendsto ρI atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real (EI N)ᶜ) atTop (𝓝 0) ∧
      ∃ d₀ s₁ a₀ c₁ C : ℝ, 0 < d₀ ∧ 0 ≤ s₁ ∧ 0 < a₀ ∧ 0 ≤ c₁ ∧ 0 ≤ C ∧ ∃ N0 : ℕ,
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ q : ℕ, N0 ≤ k + q → ∀ hN : 1 ≤ k + q,
        ∀ R : ℝ, R0 ≤ R → ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ, a = QuantumNLS.PROP017UniformN.cutSeq L l → 2 * R ≤ a →
          (∃ Pg PI P : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) (k + q),
            IsEventProj hκ u hu (by omega : 0 < k + q)
              (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b) Pg ∧
            IsEventProj hκ u hu (by omega : 0 < k + q) (EI (k + q)) PI ∧
            IsEventProj hκ u hu (by omega : 0 < k + q)
              (EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b ∩ EI (k + q)) P ∧
            P = Pg * PI ∧
            ‖(1 - P) (QuantumNLS.HighMomentsOps.wvec (k + q) u)‖ ^ 2 ≤
              ‖(1 - Pg) (QuantumNLS.HighMomentsOps.wvec (k + q) u)‖ ^ 2 +
                ‖(1 - PI) (QuantumNLS.HighMomentsOps.wvec (k + q) u)‖ ^ 2) ∧
          ∀ φ : SymSector ℂ (L2T L) (k + q), ‖φ‖ = 1 →
            (∀ m ∉ EN (μ : Measure ℝ) (qAct L κ (k + q)) R a ρ h (eta0 L κ) ε b ∩ EI (k + q),
              ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0) →
            ∃ B : BgFam (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) (hf i)) d₀ s₁ a₀ c₁,
              B.c0 = (fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z) ∧ B.D = Df L κ (Gfull (μ : Measure ℝ)) ∧
              B.s = sf L κ (Gfull (μ : Measure ℝ)) ∧ B.A = Af κ (Gfull (μ : Measure ℝ)) ∧
              ∀ θf : Fin r → ℝ, (∀ i, |θf i| ≤ Θ i) →
              ∀ (t : ℕ → ℝ), (∀ r ∈ ords, |t r| ≤ T r) →
                mixedGap L κ h k q a ords t (rectFamily xm xp hf θf) B φ ≤
                  ENNReal.ofReal (C * ((1 + a) ^ (d + 1) * (ε + 1 / R ^ b + 1 / ((k + q : ℕ) : ℝ)) +
                    ρI (k + q))) := by
  exact QuantumNLS.Prop026Uniform.prop026_uniform hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc d k ords hRd T hxm hxp hlt hfpos hfh h1 h2 h3 h4 Θ hΘ

end QuantumNLS.P026Spec
#print axioms QuantumNLS.P026Spec.prop026_uniform_spec
