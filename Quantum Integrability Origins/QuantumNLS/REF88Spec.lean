import QuantumNLS.REF88Final
/-! integrator-authored trusted spec for R-EF8C2837 (review record r70 conditional PASS): headline statement(s) copied verbatim from REF88Final (QuantumNLS.REF88Final). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open scoped ENNReal Topology
open Filter
namespace QuantumNLS.REF88Spec
open QuantumNLS.REF88Final
open QuantumNLS.StrongSymplectic QuantumNLS.L2Flow QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88Finite QuantumNLS.REF88PrintedChart QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.Fourier QuantumNLS.REF88StageE
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ActionTorus (PosL1)
open QuantumNLS.REF88PrintedChartLocal (PrintedChartLocal)
open QuantumNLS.Fourier QuantumNLS.REF88QuantumDef QuantumNLS.REF88QuantumReduce
open QuantumNLS.REF88GradStructure QuantumNLS.REF88FieldRotation QuantumNLS.REF88QuantumTangent
open QuantumNLS.REF88StageDReduce QuantumNLS.REF88QuantumProfile QuantumNLS.REF88QuantumLine
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem global_physical_dynamics_spec {Φ : L2T L → K} (hκ : 0 < κ) (hΦ : PrintedChartLocal hκ Φ) :
    (∃ ν : ℤ → PosL1 → ℝ,
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n →
        Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν n (RootIndexedMasses.masses hκ u) : ℝ) : ℂ)) *
            Φ u n) ∧
      (∀ (u : L2T L) (t : ℝ) (n : ℤ), (RootIndexedMasses.masses hκ u).1 n = 0 →
        Φ (flowMap hκ.le u t) n = 0) ∧
      (∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
        (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
          ν' = ν n (RootIndexedMasses.masses hκ u)) ∧
      (∀ n : ℤ, ContinuousOn (ν n) {a : PosL1 | 0 < a.1 n}) ∧
      (∀ a : PosL1, ∀ z ∈ ActionTorus.actionTorus a, ∀ s t : ℝ,
        chartFlow hΦ.symp hκ.le t z ∈ ActionTorus.actionTorus a ∧ chartFlow hΦ.symp hκ.le 0 z = z ∧
        chartFlow hΦ.symp hκ.le (s + t) z = chartFlow hΦ.symp hκ.le s (chartFlow hΦ.symp hκ.le t z) ∧
        Continuous (fun t : ℝ => chartFlow hΦ.symp hκ.le t z)) ∧
      (∀ w : ℤ → ℝ, (∀ n, 0 ≤ w n) → ∀ z : K, (Summable fun n => w n * ‖z n‖ ^ 2) →
        (∀ t : ℝ, ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n‖ ^ 2 = ∑' n, w n * ‖z n‖ ^ 2) ∧
        ∀ t0 : ℝ, Tendsto (fun t : ℝ => ∑' n, w n * ‖chartFlow hΦ.symp hκ.le t z n -
          chartFlow hΦ.symp hκ.le t0 z n‖ ^ 2) (𝓝 t0) (𝓝 0))
      ∧ (∀ (u : L2T L) (F : Finset ℤ), F.Nonempty →
        (∀ n, n ∈ F ↔ 0 < (RootIndexedMasses.masses hκ u).1 n) →
        ∀ (hK : 0 < κ * ‖u‖ ^ 2) (v : L2T L), ‖v‖ = 1 →
        (∀ n, QuantumNLS.F04SelBand.II hK v n = (RootIndexedMasses.masses hκ u).1 n / ‖u‖ ^ 2) →
        Nonempty (QuantumNLS.ActualGapDataR26.Data hK v) ∧
        ∀ D : QuantumNLS.ActualGapDataR26.Data hK v,
        ∀ n ∈ F, ν n (RootIndexedMasses.masses hκ u) =
          QuantumNLS.REF88QuantumDef.qEnergy (QuantumNLS.F04SelBand.Mu hK v) +
          QuantumNLS.REF88QuantumDef.qT D.bd D.F +
          ∑ j ∈ F, QuantumNLS.F04SelBand.II hK v j * D.omega n j)
      ∧ RoughLimit ν ∧ H1Pair L hκ ν) ∧
    (∀ (s : ℝ) (hs : 0 ≤ s), ∃ e : H02 L s ≃ₜ h02 L s,
      ∀ u : H02 L s, toK hs (e u) = Φ (H02.toL2 hs u)) ∧
    (∀ (u : L2T L), (∃ F : Finset ℤ, ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0) →
      ∀ (s : ℝ), 0 ≤ s → MemHsLp L s u) := by
  exact QuantumNLS.REF88Final.global_physical_dynamics hκ hΦ

/-- integrator pin: `RoughLimit` literally. -/
theorem RoughLimit_literal (ν : ℤ → PosL1 → ℝ) : RoughLimit ν ↔ (
  ∀ (a : PosL1) (n : ℤ), 0 < a.1 n →
    (∃ aj : ℕ → PosL1, (∀ j, (∃ F : Finset ℤ, ∀ k, k ∉ F → (aj j).1 k = 0) ∧ 0 < (aj j).1 n) ∧
      Tendsto aj atTop (𝓝 a)) ∧
    ∀ aj : ℕ → PosL1, (∀ j, (∃ F : Finset ℤ, ∀ k, k ∉ F → (aj j).1 k = 0) ∧ 0 < (aj j).1 n) →
      Tendsto aj atTop (𝓝 a) →
        Tendsto (fun j => ν n (aj j)) atTop (𝓝 (ν n a)) ∧
        ∀ l : ℝ, Tendsto (fun j => ν n (aj j)) atTop (𝓝 l) → l = ν n a) := Iff.rfl
/-- integrator pin: `H1Pair` literally. -/
theorem H1Pair_literal (hκ : 0 < κ) (ν : ℤ → PosL1 → ℝ) : H1Pair L hκ ν ↔ (
  ∀ (u : H02 L 1) {a b : ℤ}, b < a →
    0 < (RootIndexedMasses.masses hκ u.val).1 a → 0 < (RootIndexedMasses.masses hκ u.val).1 b →
    ∀ (hK : 0 < κ * ‖u.val‖ ^ 2) (D0 : Data hK (FullMass.unitDir u.val)),
      ν a (RootIndexedMasses.masses hκ u.val) - ν b (RootIndexedMasses.masses hκ u.val) = D0.omega a b) := Iff.rfl
/-- integrator pin: ℰ = ∫₀¹ Q(t)² (quantile energy). -/
theorem qEnergy_literal (μ : MeasureTheory.Measure ℝ) :
    QuantumNLS.REF88QuantumDef.qEnergy μ = ∫ t, (QuantumNLS.QuantileTransport.qm μ t) ^ 2 ∂QuantumNLS.QuantileForm.uI := rfl
/-- integrator pin: the printed hypotheses, with the LOCAL conjugation normalization. -/
theorem PrintedChartLocal_iff (hκ : 0 < κ) (Φ : L2T L → K) :
    PrintedChartLocal hκ Φ ↔ (IsStronglySymplectic Φ ∧ (∀ u, AnalyticAt ℝ Φ u) ∧
      (∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n) ∧
      (∀ v, fderiv ℝ Φ 0 v = QuantumNLS.Fourier.fourierL2 L v) ∧
      (∀ᶠ u in 𝓝 (0 : L2T L), Φ (QuantumNLS.ResetNormalizationUniqueness.Cphys L u) = star (Φ u))) :=
  ⟨fun h => ⟨h.symp, h.analytic, h.moduli, h.fourier, h.conj_local⟩,
   fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

end QuantumNLS.REF88Spec
#print axioms QuantumNLS.REF88Spec.global_physical_dynamics_spec
