import QuantumNLS.TerraMultiRound89FiniteAngle
import QuantumNLS.TerraMultiRound89Flow

/-! The fixed-profile, fixed-product mixed convergence actually assumed by
R-B2E70586. Circle parameters are truncated outside the fixed finite set;
the target rotates the already evolved profile, as in the printed formula. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.TraceClass
open QuantumNLS.Def033HierarchyR24m QuantumNLS.ActualModelTargetR53a
open QuantumNLS.ActualModelQuantumR52a QuantumNLS.HighAngleRotations
open QuantumNLS.CountRotations
namespace QuantumNLS.TerraMultiRound91Mixed
variable {L κ : ℝ} [Fact (0 < L)]

def mixedTerm (hκ : 0 < κ) (u : Smooth L) (orders : Finset ℕ)
    (I : Finset ℤ) (k N : ℕ) (hk : k ≤ N + 1) (t : ℕ → ℝ) (θ : AngleTorus) : ℝ≥0∞ :=
  let C := ActualModelBindingR53a.chart (L := L) hκ
  let F := higher (ActualModelBindingR53a.hierarchy_intermediate hκ
    (RB7BindFinal.hierarchyInputR25m_unconditional hκ))
  traceNorm (reducedDensityN (N + 1) k hk
      (chargeUnitary hκ orders t N
        (quantumRotation (Def044D1SpectralR51a.basis (L := L) hκ N) (truncate I θ)
          (HighMomentsOps.wvec (N + 1) (physical u))) :
            HilbertTensorPower ℂ (L2T L) (N + 1)) -
    Prop025OInputs.tensorProj k (C.Ψ (ActionTorus.rotate (truncate I θ)⁻¹
      (C.Φ (physical (jointSmooth (hamFlows F orders) t u))))))

def mixedError (hκ : 0 < κ) (u : Smooth L) (orders : Finset ℕ)
    (I : Finset ℤ) (T : ℕ → ℝ) (k N : ℕ) (hk : k ≤ N + 1) : ℝ≥0∞ :=
  ⨆ t : {t : ℕ → ℝ // ∀ r ∈ orders, |t r| ≤ T r},
    ⨆ θ : AngleTorus, mixedTerm hκ u orders I k N hk t.val θ

/-- Fixed u and fixed charge family; no rates, preparation uniformity, or
uniformity in the finite angle set or rank is assumed. Centered time boxes
are the boxes required for the printed conclusion after enlargement. -/
def MixedFiniteInput (hκ : 0 < κ) (u : Smooth L) (orders : Finset ℕ) : Prop :=
  ∀ (I : Finset ℤ) (k : ℕ) (T : ℕ → ℝ), (∀ r ∈ orders, 0 ≤ T r) →
    Tendsto (fun N => if hk : k ≤ N + 1 then mixedError hκ u orders I T k N hk else 0)
      atTop (𝓝 0)

/-- Any sequence of time and angle choices in one fixed box converges,
with no uniformity required in the choices. -/
theorem mixed_sample (hκ : 0 < κ) (u : Smooth L) (orders : Finset ℕ)
    (Input : MixedFiniteInput hκ u orders) (I : Finset ℤ) (k : ℕ) (T : ℕ → ℝ)
    (hT : ∀ r ∈ orders, 0 ≤ T r) (t : ℕ → ℕ → ℝ) (θ : ℕ → AngleTorus)
    (ht : ∀ N r, r ∈ orders → |t N r| ≤ T r) :
    Tendsto (fun N => if hk : k ≤ N + 1 then mixedTerm hκ u orders I k N hk (t N) (θ N)
      else 0) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (Input I k T hT)
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [] with N
    by_cases hk : k ≤ N + 1
    · simp only [dif_pos hk]
      exact le_iSup_of_le ⟨t N, fun r hr => ht N r hr⟩ (le_iSup (fun θ =>
        mixedTerm hκ u orders I k N hk (t N) θ) (θ N))
    · simp [hk]

#print axioms mixed_sample
#print MixedFiniteInput
end QuantumNLS.TerraMultiRound91Mixed
