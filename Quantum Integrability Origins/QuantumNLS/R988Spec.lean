import QuantumNLS.UniformProjFinalR02
/-! integrator-authored trusted spec for R-98833BEE thm:uniform-projective (final): headline statement(s) copied verbatim from UniformProjFinalR02 (QuantumNLS.UniformProjFinalR02). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter Topology
noncomputable section
namespace QuantumNLS.R988Spec
open QuantumNLS.UniformProjFinalR02
open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.AuxiliaryDensity (rankOneOperator)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.BetheCoefficientTransform (HN)
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.UniformProjR01Compact (UR)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

set_option maxHeartbeats 8000000 in
theorem uniform_projective_final_spec (hκ : 0 < κ) :
    UniformProjR01.UniformProjectiveStatement98833BEE (L := L) hκ
      (UniformStaticBridgeR50b.toFullGauge (RetargetSelectionR49b.sectorGauge (L := L) hκ)) := by
  first
  | exact QuantumNLS.UniformProjFinalR02.uniform_projective_final
  | (apply QuantumNLS.UniformProjFinalR02.uniform_projective_final <;> assumption)

set_option maxHeartbeats 8000000 in
theorem uniform_projective_printed_spec (hκ : 0 < κ) :
    ∀ R : ℝ,
      Tendsto (fun n => ⨆ u : UR L R,
        traceNorm (Gamma hκ n (HighMomentsOps.wvec (1 + n) (u : L2T L)) - rankOneOperator (w (L := L) hκ u)))
        atTop (𝓝 0) ∧
      ∀ ψ : ∀ n : ℕ, L2T L → HN L (1 + n), (∀ n, ∀ u ∈ UR L R, ‖ψ n u‖ = 1) →
        Tendsto (fun n => ⨆ u : UR L R,
          ENNReal.ofReal ‖ψ n u - (HighMomentsOps.wvec (1 + n) (u : L2T L) : HN L (1 + n))‖)
          atTop (𝓝 0) →
        Tendsto (fun n => ⨆ u : UR L R, traceNorm (Gamma hκ n (ψ n u) - rankOneOperator (w (L := L) hκ u)))
          atTop (𝓝 0) ∧
        ∀ b : ℤ, ∀ r : ℝ, 0 < r →
          Tendsto (fun n => ⨆ u : ↥{u : L2T L | u ∈ UR L R ∧ r ≤ ‖w (L := L) hκ u b‖}, ENNReal.ofReal
              ‖(((‖Gamma hκ n (ψ n u) (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ n (ψ n u) (oneBasis b) -
                (conj (w (L := L) hκ u b) / ((‖w (L := L) hκ u b‖ : ℝ) : ℂ)) • w (L := L) hκ u‖) atTop (𝓝 0) ∧
          Tendsto (fun n => ⨆ u : ↥{u : L2T L | u ∈ UR L R ∧ r ≤ ‖w (L := L) hκ u b‖}, ENNReal.ofReal
              ‖(Def021ChartR41b.chart L κ hκ).Ψ
                  ((((‖Gamma hκ n (ψ n u) (oneBasis b)‖ : ℝ) : ℂ))⁻¹ • Gamma hκ n (ψ n u) (oneBasis b)) -
                (conj (w (L := L) hκ u b) / ((‖w (L := L) hκ u b‖ : ℝ) : ℂ)) • (u : L2T L)‖) atTop (𝓝 0) := by
  first
  | exact QuantumNLS.UniformProjFinalR02.uniform_projective_printed
  | (apply QuantumNLS.UniformProjFinalR02.uniform_projective_printed <;> assumption)

end QuantumNLS.R988Spec
#print axioms QuantumNLS.R988Spec.uniform_projective_final_spec
#print axioms QuantumNLS.R988Spec.uniform_projective_printed_spec
