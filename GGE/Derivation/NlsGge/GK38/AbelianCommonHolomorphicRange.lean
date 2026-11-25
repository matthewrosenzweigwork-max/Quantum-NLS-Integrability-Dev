import NlsGge.GK38.AbelianBoundedHolomorphicDerivative
import Mathlib.Topology.MetricSpace.Thickening

/-! A common holomorphic bound gives one input-tube radius for an entire
family. Compactness is used on the seed set, never on a Banach open ball.
The actual normalized spectral branches will realize the ordinary family
hypotheses separately. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38.P6HolomorphicBounds
noncomputable section
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem common_range_of_uniform_holomorphic_bound
    (K V : Set F) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (f : I → E → F) (b : I → F) (c : E) (R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M) (hb : ∀ i, b i ∈ K)
    (hbase : ∀ i, f i c=b i)
    (ha : ∀ i, AnalyticOnNhd ℂ (f i) (ball c R))
    (hbound : ∀ i, ∀ x ∈ ball c R, ‖f i x-b i‖ ≤ M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R/2 ∧
      ∀ i, ∀ x ∈ ball c ρ,
        f i x ∈ V ∧ ‖f i x-b i‖ ≤ (4*M/R)*‖x-c‖ := by
  obtain ⟨v,hv,hvV⟩ := hK.exists_cthickening_subset_open hV hKV
  let L : ℝ := 4*M/R
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLp : 0 < L+1 := by linarith
  let ρ : ℝ := min (R/2) (v/(L+1))
  have hρ : 0 < ρ := lt_min (half_pos hR) (div_pos hv hLp)
  have hρR : ρ ≤ R/2 := min_le_left _ _
  refine ⟨ρ,hρ,hρR,?_⟩
  intro i x hx
  have hxR : x ∈ ball c (R/2) := ball_subset_ball hρR hx
  have hdiff : ‖f i x-b i‖ ≤ L*‖x-c‖ := by
    have h := norm_sub_le_of_ball_bound (fun z => f i z-b i) c R M hR
      (fun z hz => (ha i z hz).sub analyticAt_const)
      (hbound i) x c hxR (mem_ball_self (half_pos hR))
    simpa only [hbase i,sub_self,sub_zero] using h
  have hxv : ‖x-c‖ < v/(L+1) :=
    (mem_ball_iff_norm.mp hx).trans_le (min_le_right _ _)
  have hprod : ‖x-c‖*(L+1) < v := (lt_div_iff₀ hLp).mp hxv
  have hsmall : ‖f i x-b i‖ ≤ v := by
    have hh : L*‖x-c‖ ≤ ‖x-c‖*(L+1) := by nlinarith [norm_nonneg (x-c)]
    exact (hdiff.trans hh).trans hprod.le
  exact ⟨hvV (closedBall_subset_cthickening (hb i) v (mem_closedBall_iff_norm.mpr hsmall)),hdiff⟩
end
end NlsGge.GK38.P6HolomorphicBounds
