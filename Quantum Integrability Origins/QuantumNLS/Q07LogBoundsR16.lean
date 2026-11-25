import QuantumNLS.Q07LogDifferentialsR16
import QuantumNLS.Q07NormalSeriesR15

/-! Quantitative logarithm Hessians from the actual transfer differentials.
The denominator lower bound is kept local; uniform contour nonvanishing
must be proved separately before the printed consumer can be assembled. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Metric
namespace QuantumNLS.Q07LogBoundsR16
open Q07LogDifferentialsR16

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem second_eq {f : E → ℂ} {u : E} (hf : ContDiffAt ℝ 2 f u) (v w : E) :
    second f u v w = fderiv ℝ (fderiv ℝ f) u w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) u :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (c := v) u)
  have he := DFunLike.congr_fun hh.fderiv w
  simpa only [second, first, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply, ContinuousLinearMap.map_zero,
    zero_add, ContinuousLinearMap.flip_apply] using he

theorem second_norm_le {f : E → ℂ} {u : E} (hf : ContDiffAt ℝ 2 f u) (v w : E) :
    ‖second f u v w‖ ≤ ‖fderiv ℝ (fderiv ℝ f) u‖ * ‖v‖ * ‖w‖ := by
  rw [second_eq hf]
  have hh := ((fderiv ℝ (fderiv ℝ f) u) w).le_opNorm v
  have hi := (fderiv ℝ (fderiv ℝ f) u).le_opNorm w
  exact hh.trans (by nlinarith [norm_nonneg v])

end Calculus

open PhysicalTensor (L2T)
variable {L κ : ℝ} [Fact (0 < L)]

/-- The full real Hilbert Hessian estimate at every regular spectral point,
with explicit dependence on a proved denominator and symbol bound. -/
theorem logarithm_hessian_bound (hκ : 0 < κ) {R b : ℝ} (hR : 1 ≤ R) (hb : 0 ≤ b) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ z : ℂ, -b ≤ z.im →
      ∀ u ∈ ball (0 : L2T L) R,
        RootCauchyJointR9.Regular κ (u,z) → ∀ d M : ℝ, 0 < d → 0 ≤ M →
          d ≤ ‖physicalDifference hκ z u‖ →
          ‖NormalizedTransfer.productSymbol L κ u z‖ ≤ M → ∀ v w : L2T L,
          ‖second (logarithm hκ z) u v w‖ ≤
            (d⁻¹*C2 + M*d⁻¹^3*C1^2)*‖v‖*‖w‖ := by
  obtain ⟨C1,C2,h1,h2,hbnd⟩ := Q07NormalSeriesR15.transfer_uniform_differentials (L := L) κ hR hb
  refine ⟨C1,C2,h1,h2,?_⟩
  intro z hz u hu hp d M hd hM hD hS v w
  have hs : ContDiffAt ℝ 2 (fun x : L2T L => NormalizedTransfer.productSymbol L κ x z) u :=
    (Q07NormalSeriesR15.transfer_contDiffOn (L := L) κ hR hb z hz).contDiffAt (isOpen_ball.mem_nhds hu)
  obtain ⟨hB1,hB2⟩ := hbnd z hz u hu
  have hV : ‖first (fun x => NormalizedTransfer.productSymbol L κ x z) u v‖ ≤ C1*‖v‖ :=
    ((fderiv ℝ (fun x => NormalizedTransfer.productSymbol L κ x z) u).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hB1 (norm_nonneg v))
  have hW : ‖first (fun x => NormalizedTransfer.productSymbol L κ x z) u w‖ ≤ C1*‖w‖ :=
    ((fderiv ℝ (fun x => NormalizedTransfer.productSymbol L κ x z) u).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right hB1 (norm_nonneg w))
  have hH : ‖second (fun x => NormalizedTransfer.productSymbol L κ x z) u v w‖ ≤ C2*‖v‖*‖w‖ :=
    (second_norm_le hs v w).trans (by gcongr)
  have hi : ‖(physicalDifference hκ z u)⁻¹‖ ≤ d⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ hd hD
  rw [(physical_log_differentials hκ hp v w).2]
  refine (norm_sub_le _ _).trans ?_
  simp only [norm_mul, norm_pow]
  calc
    _ ≤ d⁻¹*(C2*‖v‖*‖w‖) + M*(d⁻¹)^3*(C1*‖v‖)*(C1*‖w‖) := by
      gcongr
    _ = _ := by ring

end QuantumNLS.Q07LogBoundsR16
