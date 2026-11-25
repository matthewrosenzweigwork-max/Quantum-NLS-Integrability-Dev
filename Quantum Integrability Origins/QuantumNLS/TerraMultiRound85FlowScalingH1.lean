import QuantumNLS.TerraMultiRound85MildScaling

/-! Scaling identity for the actual L² physical flow at H¹ initial data. -/
set_option autoImplicit false
noncomputable section
open QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight QuantumNLS.LocalWellPosedness
open QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Global QuantumNLS.H1Bridge QuantumNLS.L2Flow
open QuantumNLS.TerraMultiRound85MildScaling
namespace QuantumNLS.TerraMultiRound85FlowScalingH1
variable {L : ℝ} [Fact (0 < L)]

/-- On the full H¹ range, the accepted physical flows obey amplitude scaling. -/
theorem flow_scale_H1 {κ : ℝ} (hκ : 0 ≤ κ) (r : ℝ) (g : h04 L 1) (t : ℝ) :
    flowMap hκ ((r : ℂ) • emb g) t =
      (r : ℂ) • flowMap (mul_nonneg hκ (sq_nonneg r)) (emb g) t := by
  have hκ' : 0 ≤ κ*r^2 := mul_nonneg hκ (sq_nonneg r)
  let u := umax (le_refl (1 : ℝ)) (κ*r^2) g
  have hu := umax_mild (hs := le_refl (1 : ℝ)) hκ' g
  rw [Imax1_eq_univ hκ' g] at hu
  have h := scaled_mild_is_flow hκ r g u hu t
  rw [flowMap_H1 hκ' g t]
  simpa only [map_smul] using h

#print axioms flow_scale_H1
end QuantumNLS.TerraMultiRound85FlowScalingH1
