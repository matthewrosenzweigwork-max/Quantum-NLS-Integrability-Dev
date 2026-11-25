import QuantumNLS.RootMassSpectralR27

/-! Uniform bounded resolvent weights on compact subsets of nonnegative ell1. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootMassUniformR27
open ActionTorus RootWeightedCellsR26 RootMassSpectralR27
variable (L : ℝ) [Fact (0 < L)]

def weighted (Y : ℝ) (a : PosL1) : ℝ := ∑' n : ℤ,weight Y (momentum L n)*a.1 n

lemma weighted_nonneg (Y : ℝ) (a : PosL1) : 0 ≤ weighted L Y a :=
  tsum_nonneg (fun n => mul_nonneg (weight_nonneg _ _) (a.2 n))

lemma weighted_lipschitz (Y : ℝ) (a b : PosL1) :
    |weighted L Y a-weighted L Y b| ≤ dist a b := by
  have ha := weight_summable (L := L) a Y
  have hb := weight_summable (L := L) b Y
  have hs : Summable (fun n : ℤ => weight Y (momentum L n)*(a.1 n-b.1 n)) := by
    simpa only [mul_sub] using ha.sub hb
  have hd : Summable (fun n : ℤ => ‖a.1 n-b.1 n‖) := by
    simpa only [lp.coeFn_sub,Pi.sub_apply] using (Memℓp.summable_of_one (a.1-b.1).2).norm
  have he : (∑' n : ℤ,‖a.1 n-b.1 n‖) = dist a b := by
    have h := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num) (a.1-b.1)
    simpa only [ENNReal.toReal_one,Real.rpow_one,lp.coeFn_sub,Pi.sub_apply,
      Subtype.dist_eq,dist_eq_norm] using h.symm
  calc
    _ = ‖∑' n : ℤ,weight Y (momentum L n)*(a.1 n-b.1 n)‖ := by
      rw [Real.norm_eq_abs]
      congr 1
      simpa only [weighted,mul_sub] using (ha.tsum_sub hb).symm
    _ ≤ ∑' n : ℤ,‖weight Y (momentum L n)*(a.1 n-b.1 n)‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℤ,‖a.1 n-b.1 n‖ := hs.norm.tsum_le_tsum (fun n => by
      rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (weight_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one _ _)) hd
    _ = _ := he

lemma weight_tendsto (p : ℝ) : Tendsto (fun Y : ℝ => weight Y p) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).min ((tendsto_inv_atTop_zero.pow 2).const_mul (p^2))
  simpa only [weight,div_eq_mul_inv,inv_pow,zero_pow (by norm_num : 2 ≠ 0),mul_zero,min_eq_right (by norm_num : (0:ℝ) ≤ 1)] using h

lemma weighted_tendsto (a : PosL1) : Tendsto (fun Y : ℝ => weighted L Y a) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (summable_posL1 a)
    (fun n : ℤ => by simpa only [zero_mul] using (weight_tendsto (momentum L n)).mul_const (a.1 n))
    (Eventually.of_forall (fun Y n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (weight_nonneg _ _) (a.2 n))]
      exact mul_le_of_le_one_left (a.2 n) (weight_le_one _ _)))
  simpa only [weighted,tsum_zero] using h

lemma uniform_weighted {K : Set PosL1} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in atTop, ∀ a ∈ K, weighted L Y a < ε := by
  obtain ⟨t,_,ht,hcov⟩ := hK.finite_cover_balls (show 0 < ε/2 by positivity)
  have hev : ∀ᶠ Y : ℝ in atTop, ∀ a ∈ t, weighted L Y a < ε/2 := by
    rw [Filter.eventually_all_finite ht]
    intro a _
    exact (weighted_tendsto L a).eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with Y hY
  intro a ha
  obtain ⟨b,hb,hab⟩ := Set.mem_iUnion₂.mp (hcov ha)
  have hd : dist a b < ε/2 := Metric.mem_ball.mp hab
  have hw := weighted_lipschitz L Y a b
  have hle := le_abs_self (weighted L Y a-weighted L Y b)
  linarith [hY b hb]

lemma mass_norm (a : PosL1) : (∑' n : ℤ,a.1 n) = ‖a.1‖ := by
  have h := lp.norm_rpow_eq_tsum (p := (1 : ℝ≥0∞)) (by norm_num) a.1
  simpa only [ENNReal.toReal_one,Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (a.2 _)] using h.symm

end QuantumNLS.RootMassUniformR27
