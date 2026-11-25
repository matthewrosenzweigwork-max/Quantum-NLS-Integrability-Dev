import QuantumNLS.TerraMultiRound91QuantumTruncation
import QuantumNLS.TerraMultiRound91ClassicalCutoff
import QuantumNLS.TerraMultiRound91Mixed

/-! The finite-cutoff triangle in the printed full-torus proof, under the
fixed-product mixed convergence hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096
noncomputable section
open Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.CountRotations
open QuantumNLS.HighAngleRotations QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.ActualModelQuantumR52a QuantumNLS.TerraMultiRound91Mixed
open QuantumNLS.TerraMultiRound91QuantumTruncation
namespace QuantumNLS.TerraMultiRound91Comparison
variable {L κ : ℝ} [Fact (0 < L)]

def fullTerm (hκ : 0 < κ) (u : Smooth L) (orders : Finset ℕ)
    (k N : ℕ) (hk : k ≤ N+1) (t : ℕ → ℝ) (θ : AngleTorus) : ℝ≥0∞ :=
  let C := ActualModelBindingR53a.chart (L := L) hκ
  let F := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional hκ))
  TraceClass.traceNorm (reducedDensityN (N+1) k hk
      (quantumRotation (Def044D1SpectralR51a.basis (L := L) hκ N) θ
        (chargeUnitary hκ orders t N (HighMomentsOps.wvec (N+1) (physical u))) :
          HilbertTensorPower ℂ (L2T L) (N+1)) -
    Prop025OInputs.tensorProj k (C.Ψ (ActionTorus.rotate θ⁻¹
      (C.Φ (physical (jointSmooth (hamFlows F orders) t u))))))

def fullError (hκ : 0 < κ) (u : Smooth L) (orders : Finset ℕ)
    (T : ℕ → ℝ) (k N : ℕ) (hk : k ≤ N+1) : ℝ≥0∞ :=
  ⨆ t : {t : ℕ → ℝ // ∀ r ∈ orders, |t r| ≤ T r},
    ⨆ θ : AngleTorus, fullTerm hκ u orders k N hk t.val θ

/-- Compare the full torus with the exact fixed-product mixed input and the
two explicit cutoff errors. -/
theorem cutoff_comparison (hκ : 0 < κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (orders : Finset ℕ) (T : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (E : ℝ) (hE : 2 * ChargeEnergy.energyH1 κ (physical u : AddCircle L → ℂ) < E) :
    ∃ NE : ℕ, ∃ η : ℕ → ℝ, 0 < NE ∧ (∀ R, 0 ≤ η R) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∀ N : ℕ, NE ≤ N+1 → ∀ hkN : k ≤ N+1,
      fullError hκ u orders T k N hkN ≤
        ENNReal.ofReal (4 * Real.sqrt (ChargeEnergy.energyH1 κ (physical u : AddCircle L → ℂ) / E) + η R) +
          mixedError hκ u orders (angleBox R) T k N hkN + ENNReal.ofReal ε := by
  have hH : ProductEnergyPreparation.OneH1 (physical u) :=
    PhysicalProductPreparation.oneH1_smooth u.property
  obtain ⟨NE, η, hNE, hη, hlim, hquant⟩ :=
    product_quantum_truncation L hκ (physical u) hu hH E hE hk
  refine ⟨NE, η, hNE, hη, hlim, ?_⟩
  intro ε hε
  obtain ⟨R₀, hclass⟩ := TerraMultiRound91ClassicalCutoff.classical_projector_cutoff hκ u hu orders k ε hε
  refine ⟨R₀, ?_⟩
  intro R hRR N hN hkN
  apply iSup_le
  intro t
  apply iSup_le
  intro θ
  let b := Def044D1SpectralR51a.basis (L := L) hκ N
  let Ω := HighMomentsOps.wvec (N+1) (physical u)
  let C := ActualModelBindingR53a.chart (L := L) hκ
  let F : HigherFlows L κ := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ))
  let x := physical (jointSmooth (hamFlows F orders) t.val u)
  let A := reducedDensityN (N+1) k hkN (quantumRotation b θ (chargeUnitary hκ orders t.val N Ω)).val
  let B := reducedDensityN (N+1) k hkN (chargeUnitary hκ orders t.val N
    (quantumRotation b (truncate (angleBox R) θ) Ω)).val
  let D := Prop025OInputs.tensorProj k (C.Ψ (ActionTorus.rotate (truncate (angleBox R) θ)⁻¹ (C.Φ x)))
  let Z := Prop025OInputs.tensorProj k (C.Ψ (ActionTorus.rotate θ⁻¹ (C.Φ x)))
  have hq : TraceClass.traceNorm (A-B) ≤ ENNReal.ofReal
      (4 * Real.sqrt (ChargeEnergy.energyH1 κ (physical u : AddCircle L → ℂ) / E) + η R) :=
    hquant N hN hkN orders t.val R θ
  have hm : TraceClass.traceNorm (B-D) ≤ mixedError hκ u orders (angleBox R) T k N hkN := by
    exact le_iSup_of_le t (le_iSup (fun θ' => mixedTerm hκ u orders (angleBox R) k N hkN t.val θ') θ)
  have hc : TraceClass.traceNorm (D-Z) ≤ ENNReal.ofReal ε := by
    have heq : ∀ n : ℤ, |n| ≤ (R₀ : ℤ) → θ⁻¹ n = (truncate (angleBox R) θ)⁻¹ n := by
      intro n hn
      have hn' : |n| ≤ (R : ℤ) := hn.trans (by exact_mod_cast hRR)
      have hi := mem_angleBox R n hn'
      simp [truncate, hi]
    have hh := hclass t.val θ⁻¹ (truncate (angleBox R) θ)⁻¹ heq
    change TraceClass.traceNorm (Z-D) ≤ _ at hh
    have he : TraceClass.traceNorm (D-Z) = TraceClass.traceNorm (Z-D) := by
      rw [← neg_sub, TraceNormTopology.traceNorm_neg]
    rw [he]
    exact hh
  have h1 : TraceClass.traceNorm (A-Z) ≤ TraceClass.traceNorm (A-B) + TraceClass.traceNorm (B-Z) := by
    convert TraceClass.traceNorm_add_le (A-B) (B-Z) using 1 <;> congr 1 <;> abel
  have h2 : TraceClass.traceNorm (B-Z) ≤ TraceClass.traceNorm (B-D) + TraceClass.traceNorm (D-Z) := by
    convert TraceClass.traceNorm_add_le (B-D) (D-Z) using 1 <;> congr 1 <;> abel
  change TraceClass.traceNorm (A-Z) ≤ _
  exact (h1.trans (add_le_add le_rfl h2)).trans (by
    simpa only [add_assoc] using add_le_add hq (add_le_add hm hc))

#print axioms cutoff_comparison
end QuantumNLS.TerraMultiRound91Comparison
