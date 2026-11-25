import QuantumNLS.TerraMultiRound91MaskCommute
import QuantumNLS.TerraMultiRound91ExactTail

/-! The printed sharp quantum high-angle bound for an actual product followed
by arbitrary diagonal charge evolution and a low-angle rotation. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter Topology
open scoped InnerProductSpace
open QuantumNLS.PhysicalTensor QuantumNLS.TensorCarrier QuantumNLS.BetheCoefficientTransform
open QuantumNLS.BetheSpectralCharges QuantumNLS.HighAngleRotations QuantumNLS.CountRotations
open QuantumNLS.HaarSpectralTail QuantumNLS.ProductEnergyPreparation QuantumNLS.ChargeEnergy
open QuantumNLS.TerraMultiRound91ProductCompression QuantumNLS.TerraMultiRound91MaskCommute
open QuantumNLS.TerraMultiRound91ExactTail
namespace QuantumNLS.TerraMultiRound91QuantumTail
variable (L : ℝ) [Fact (0 < L)]

theorem product_high_angle_tail {κ : ℝ} (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (hH : OneH1 u) (E : ℝ) (hE : 2 * energyH1 κ (u : AddCircle L → ℂ) < E)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ NE : ℕ, ∃ η : ℕ → ℝ, 0 < NE ∧ (∀ R, 0 ≤ η R) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (N : ℕ), NE ≤ N → ∀ hkN : k ≤ N,
      ∀ (ev : BetheLabels.MArr N → ℝ) (τ : ℝ) (low : AngleTorus) (R : ℕ) (θ : AngleTorus),
      (∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = 1) →
      let b := bas L hκ (hk.trans hkN)
      let v := evolution b ev τ (quantumRotation b low (HighMomentsOps.wvec N u))
      TraceClass.traceNorm (reducedDensityN N k hkN (quantumRotation b θ v).val -
        reducedDensityN N k hkN v.val) ≤
        ENNReal.ofReal (4 * Real.sqrt (energyH1 κ (u : AddCircle L → ℂ) / E) + η R) := by
  have hC : 0 ≤ energyH1 κ (u : AddCircle L → ℂ) := by
    unfold energyH1
    apply add_nonneg
    · rw [kinetic_eq]
      exact tsum_nonneg (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · exact mul_nonneg hκ.le (quartic_nonneg _)
  have hEpos : 0 < E := by linarith
  obtain ⟨NE, η, hNE, hη, hlim, htail⟩ := QuantumHighAngleTail.natural_tail L hκ hEpos hk
  refine ⟨NE, η, hNE, hη, hlim, ?_⟩
  intro N hN hkN ev τ low R θ hθ
  let b := bas L hκ (hk.trans hkN)
  obtain ⟨P, hP, ht⟩ := htail N hN hkN
  obtain ⟨w₀, hw₀, hPw₀, hclose⟩ := product_compression κ hκ N (hk.trans hkN) u hu hH E hE P hP
  let Ω := HighMomentsOps.wvec N u
  have hΩ : ‖Ω‖ = 1 := by
    change ‖TensorCarrier.htpow N u‖ = 1
    rw [TensorCarrier.norm_htpow, hu, one_pow]
  let U := (quantumRotation b low).trans (evolution b ev τ)
  have hPw : P (U w₀) = U w₀ := by
    change P (evolution b ev τ (quantumRotation b low w₀)) = _
    rw [mask_evolution_commute b ev τ P (mask L κ N E) hP,
      mask_rotation_commute b low P (mask L κ N E) hP, hPw₀]
    rfl
  have hv : ‖U Ω‖ = 1 := by rw [U.norm_map, hΩ]
  have hw : ‖U w₀‖ = 1 := by rw [U.norm_map, hw₀]
  have htrace : TraceClass.traceNorm (InnerProductSpace.rankOne ℂ (U Ω) (U Ω) -
      InnerProductSpace.rankOne ℂ (U w₀) (U w₀)) =
      TraceClass.traceNorm (InnerProductSpace.rankOne ℂ Ω Ω - InnerProductSpace.rankOne ℂ w₀ w₀) := by
    rw [RankTwoTrace.traceNorm_unit_sub_eq _ _ hv hw,
      RankTwoTrace.traceNorm_unit_sub_eq _ _ hΩ hw₀, U.inner_map_map]
  have hc : TraceClass.traceNorm (InnerProductSpace.rankOne ℂ (U Ω) (U Ω) -
      InnerProductSpace.rankOne ℂ (U w₀) (U w₀)) ≤
      ENNReal.ofReal (2 * Real.sqrt (energyH1 κ (u : AddCircle L → ℂ) / E)) := by
    rw [htrace]
    exact hclose
  have h := exact_projection_cost N k hkN (U Ω) (U w₀) (quantumRotation b θ) hv hw
    (2 * Real.sqrt (energyH1 κ (u : AddCircle L → ℂ) / E)) (η R)
    (by positivity) (hη R) hc (ht (U w₀) hPw hw R θ hθ)
  convert h using 1 <;> congr 2 <;> ring

#print axioms product_high_angle_tail
end QuantumNLS.TerraMultiRound91QuantumTail
