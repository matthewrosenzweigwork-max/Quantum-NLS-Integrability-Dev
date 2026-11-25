import QuantumNLS.CFCCutoffsR13
import Mathlib.Topology.UniformSpace.Ascoli

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Filter Topology
namespace QuantumNLS.ContinuousExhaustionR13
open CFCCutoffsR13
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem strong (R : E →L[ℂ] E) (hR : 0 ≤ R) (hd : DenseRange R) (x : E) :
    Tendsto (fun n => cutoff R n x) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y,hy⟩ := hd.exists_dist_lt x (by linarith : 0 < ε/8)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*‖y‖/ε)
  refine ⟨N,fun n hn => ?_⟩
  have hnn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hnp : 0 < (n : ℝ)+1 := by positivity
  have hr : (1/((n : ℝ)+1))*‖y‖ < ε/2 := by
    have hh := (div_lt_iff₀ hε).mp hN
    rw [one_div_mul_eq_div,div_lt_iff₀ hnp]
    nlinarith
  have hbound : ‖R y-cutoff R n (R y)‖ ≤ (1/((n : ℝ)+1))*‖y‖ := by
    have hh := ((1-cutoff R n)*R).le_opNorm y
    simp only [mul_apply_eq_comp,sub_apply,one_apply_eq_self] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (residual_norm R hR n) (norm_nonneg _))
  have hc : ‖cutoff R n (x-R y)‖ ≤ ‖x-R y‖ := by
    exact ((cutoff R n).le_opNorm _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (cutoff_norm R n) (norm_nonneg (x-R y)))
  have he : cutoff R n x-x = cutoff R n (x-R y)-(x-R y)-(R y-cutoff R n (R y)) := by
    rw [map_sub]; abel
  rw [dist_eq_norm,he]
  have hh := norm_sub_le (cutoff R n (x-R y)-(x-R y)) (R y-cutoff R n (R y))
  have hh' := norm_sub_le (cutoff R n (x-R y)) (x-R y)
  rw [dist_eq_norm] at hy
  nlinarith

theorem uniform_compact (R : E →L[ℂ] E) (hR : 0 ≤ R) (hd : DenseRange R)
    (K : Set E) (hK : IsCompact K) :
    TendstoUniformly (fun n => fun x : K => cutoff R n x.val) (fun x => x.val) atTop := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLip : ∀ n, LipschitzWith 1 (fun x : K => cutoff R n x.val) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Subtype.dist_eq,dist_eq_norm,← map_sub,NNReal.coe_one,one_mul]
    exact ((cutoff R n).le_opNorm _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (cutoff_norm R n) (norm_nonneg (x.val-y.val)))
  have heq := (LipschitzWith.uniformEquicontinuous _ 1 hLip).equicontinuous
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (heq.tendsto_uniformFun_iff_pi atTop (fun x : K => x.val)).2
  exact tendsto_pi_nhds.mpr fun x => strong R hR hd x.val

end QuantumNLS.ContinuousExhaustionR13
