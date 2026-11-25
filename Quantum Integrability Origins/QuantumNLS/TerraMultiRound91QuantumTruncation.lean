import QuantumNLS.TerraMultiRound91QuantumTail
import QuantumNLS.TerraMultiRound87Rotations
import QuantumNLS.ActualModelQuantumR52a

/-! Convert the sharp high-angle bound to low-angle truncation of the actual
charge-evolved product. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
noncomputable section
open Filter Topology
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.BetheCoefficientTransform
open QuantumNLS.BetheSpectralCharges QuantumNLS.HighAngleRotations QuantumNLS.CountRotations
open QuantumNLS.HaarSpectralTail QuantumNLS.ProductEnergyPreparation QuantumNLS.ChargeEnergy
open QuantumNLS.TerraMultiRound87Rotations QuantumNLS.ActualModelQuantumR52a
namespace QuantumNLS.TerraMultiRound91QuantumTruncation
variable (L : ℝ) [Fact (0 < L)]

def angleBox (R : ℕ) : Finset ℤ := Finset.Icc (-(R : ℤ)) (R : ℤ)

theorem mem_angleBox (R : ℕ) (n : ℤ) (hn : |n| ≤ (R : ℤ)) : n ∈ angleBox R := by
  exact Finset.mem_Icc.mpr (abs_le.mp hn)

theorem product_quantum_truncation {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (hH : OneH1 u) (E : ℝ) (hE : 2 * energyH1 κ (u : AddCircle L → ℂ) < E)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ NE : ℕ, ∃ η : ℕ → ℝ, 0 < NE ∧ (∀ R, 0 ≤ η R) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (N : ℕ), NE ≤ N + 1 → ∀ hkN : k ≤ N + 1,
      ∀ (orders : Finset ℕ) (t : ℕ → ℝ) (R : ℕ) (θ : AngleTorus),
      let b := Def044D1SpectralR51a.basis (L := L) hκ N
      let Ω := HighMomentsOps.wvec (N+1) u
      TraceClass.traceNorm
        (reducedDensityN (N+1) k hkN (quantumRotation b θ (chargeUnitary hκ orders t N Ω)).val -
         reducedDensityN (N+1) k hkN (chargeUnitary hκ orders t N
           (quantumRotation b (truncate (angleBox R) θ) Ω)).val) ≤
        ENNReal.ofReal (4 * Real.sqrt (energyH1 κ (u : AddCircle L → ℂ) / E) + η R) := by
  obtain ⟨NE, η, hNE, hη, hlim, htail⟩ :=
    TerraMultiRound91QuantumTail.product_high_angle_tail L hκ u hu hH E hE hk
  refine ⟨NE, η, hNE, hη, hlim, ?_⟩
  intro N hN hkN orders t R θ
  let b := Def044D1SpectralR51a.basis (L := L) hκ N
  let Ω := HighMomentsOps.wvec (N+1) u
  let low := truncate (angleBox R) θ
  let high := tailAngle (angleBox R) θ
  have hhigh : ∀ n : ℤ, |n| ≤ (R : ℤ) → high n = 1 := by
    intro n hn
    exact tailAngle_eq_one _ _ n (mem_angleBox R n hn)
  have h := htail (N+1) hN hkN (chargeSymbol (L := L) (κ := κ) orders t N) 1 low R high hhigh
  have hfull : quantumRotation b high (chargeUnitary hκ orders t N (quantumRotation b low Ω)) =
      quantumRotation b θ (chargeUnitary hκ orders t N Ω) := by
    change quantumRotation b high (evolution b (chargeSymbol (L := L) (κ := κ) orders t N) 1
      (quantumRotation b low Ω)) = _
    rw [← quantumRotation_evolution_commute, ← quantumRotation_mul, tailAngle_mul_low]
    rfl
  change TraceClass.traceNorm
    (reducedDensityN (N+1) k hkN (quantumRotation b high
      (chargeUnitary hκ orders t N (quantumRotation b low Ω))).val -
     reducedDensityN (N+1) k hkN (chargeUnitary hκ orders t N (quantumRotation b low Ω)).val) ≤ _ at h
  rw [hfull] at h
  exact h

#print axioms mem_angleBox
#print axioms product_quantum_truncation
end QuantumNLS.TerraMultiRound91QuantumTruncation
