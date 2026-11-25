import Mathlib
import QuantumNLS.MPChartSmooth

/-!
# PROP-026: uniform derivative bounds for the smooth extensions `f_z`

New module (continuation of `MPChartSmooth`).  For background data satisfying `Bg d₀ s₁ a₀ D s A` and every `i ≤ m`,
`w ∈ ℂ`:

`‖iteratedFDeriv ℝ i (gfun r c₀ D s A) w‖ ≤ Bder Cψ r ‖c₀‖ i`,    `Bder Cψ r c i = ∑_{j ≤ i} C(i,j) Cψ (i-j)! (c+1)/r^{i-j}`,

where `Cψ` bounds the first `m` derivatives of the radial cutoff.  The bound depends only on `(r, m, ‖c₀‖)`: it is the
"each required number of derivatives can be bounded uniformly" statement of the source, proved by Leibniz on `ball s ρ` and
Cauchy's estimate for the holomorphic chart on discs of radius `r`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open Complex Metric Set Filter
open scoped ContDiff

namespace QuantumNLS.MPChartDeriv

open QuantumNLS.MPChartBounds QuantumNLS.MPChartSmooth
open QuantumNLS.MixedTraceNorm (chartLambda)

/-- Explicit derivative bound. -/
def Bder (Cψ r c : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * Cψ * (((i - j).factorial : ℝ) * (c + 1) / r ^ (i - j))

theorem Bder_nonneg {Cψ r c : ℝ} (hC : 0 ≤ Cψ) (hr : 0 < r) (hc : 0 ≤ c) (i : ℕ) : 0 ≤ Bder Cψ r c i := by
  unfold Bder
  refine Finset.sum_nonneg (fun j _ => ?_)
  positivity

variable {d₀ s₁ a₀ : ℝ} {D s A : ℂ}

/-- Cauchy estimate for the real iterated derivatives of the chart. -/
theorem norm_iteratedFDeriv_chart_le (hB : Bg d₀ s₁ a₀ D s A) (c0 : ℂ) (k : ℕ) {w : ℂ}
    (hw : ‖w - s‖ ≤ rad d₀ s₁ a₀) :
    ‖iteratedFDeriv ℝ k (chartLambda c0 D s A) w‖ ≤
      (k.factorial : ℝ) * (‖c0‖ + 1) / (rad d₀ s₁ a₀) ^ k := by
  have hr := rad_pos hB
  have hρ := rho_pos hB.hd0 hB.hs0 hB.ha0
  have h3 : rho d₀ s₁ a₀ = 3 * rad d₀ s₁ a₀ := by unfold rad; ring
  have hU : IsOpen (ball s (rho d₀ s₁ a₀)) := isOpen_ball
  have hwU : w ∈ ball s (rho d₀ s₁ a₀) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hdiff := differentiableOn_chart hB c0
  have hCD : ContDiffAt ℂ ∞ (chartLambda c0 D s A) w :=
    ((hdiff.contDiffOn hU : ContDiffOn ℂ ∞ _ _)).contDiffAt (hU.mem_nhds hwU)
  have e1 : ((ContinuousMultilinearMap.restrictScalars ℝ) ∘ iteratedFDeriv ℂ k (chartLambda c0 D s A)) w =
      iteratedFDeriv ℝ k (chartLambda c0 D s A) w :=
    (hCD.of_le (by exact_mod_cast le_top)).restrictScalars_iteratedFDeriv
  have e2 : ‖iteratedFDeriv ℝ k (chartLambda c0 D s A) w‖ ≤ ‖iteratedFDeriv ℂ k (chartLambda c0 D s A) w‖ := by
    rw [← e1]
    simp only [Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars]
    exact le_rfl
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at e2
  refine e2.trans ?_
  -- Cauchy
  have hsub : closedBall w (rad d₀ s₁ a₀) ⊆ ball s (rho d₀ s₁ a₀) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    have : ‖z - s‖ ≤ ‖z - w‖ + ‖w - s‖ := by
      have := norm_add_le (z - w) (w - s); simpa using this
    linarith
  have hdc : DiffContOnCl ℂ (chartLambda c0 D s A) (ball w (rad d₀ s₁ a₀)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball w hr.ne']
    exact hdiff.mono hsub
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hdc (fun z hz => ?_)
  have hz' : ‖z - s‖ < rho d₀ s₁ a₀ := by
    have := hsub (sphere_subset_closedBall hz)
    rwa [mem_ball, dist_eq_norm] at this
  exact norm_chartLambda_le c0 hB.hd0 hB.hs0 hB.ha0 hB.hD hB.hs hB.hA hB.hAd hz'

theorem norm_iteratedFDeriv_gfun_le (hB : Bg d₀ s₁ a₀ D s A) (c0 : ℂ) {m : ℕ} {Cψ : ℝ}
    (hCψ : ∀ i ≤ m, ∀ v, ‖iteratedFDeriv ℝ i (cutoff (rad d₀ s₁ a₀)) v‖ ≤ Cψ) (hC0 : 0 ≤ Cψ)
    {i : ℕ} (hi : i ≤ m) (w : ℂ) :
    ‖iteratedFDeriv ℝ i (gfun (rad d₀ s₁ a₀) c0 D s A) w‖ ≤ Bder Cψ (rad d₀ s₁ a₀) ‖c0‖ i := by
  have hr := rad_pos hB
  have hρ := rho_pos hB.hd0 hB.hs0 hB.ha0
  have h3 : rho d₀ s₁ a₀ = 3 * rad d₀ s₁ a₀ := by unfold rad; ring
  by_cases hw : ‖w - s‖ ≤ rad d₀ s₁ a₀
  · have hU : IsOpen (ball s (rho d₀ s₁ a₀)) := isOpen_ball
    have hwU : w ∈ ball s (rho d₀ s₁ a₀) := by
      rw [mem_ball, dist_eq_norm]; linarith
    have hf : ContDiffOn ℝ ∞ (fun v : ℂ => ((cutoff (rad d₀ s₁ a₀) (v - s) : ℝ) : ℂ)) (ball s (rho d₀ s₁ a₀)) :=
      (Complex.ofRealCLM.contDiff.comp ((contDiff_cutoff _).comp (contDiff_id.sub contDiff_const))).contDiffOn
    have hl := contDiffOn_chart hB c0
    have hmul := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (N := ∞) hf hl hU.uniqueDiffOn hwU
      (n := i) (by exact_mod_cast le_top)
    have hEq : ∀ (f : ℂ → ℂ) (j : ℕ), iteratedFDerivWithin ℝ j f (ball s (rho d₀ s₁ a₀)) w =
        iteratedFDeriv ℝ j f w := fun f j => iteratedFDerivWithin_of_isOpen j hU hwU
    simp only [hEq] at hmul
    have hg : gfun (rad d₀ s₁ a₀) c0 D s A =
        fun y => ((cutoff (rad d₀ s₁ a₀) (y - s) : ℝ) : ℂ) * chartLambda c0 D s A y := rfl
    rw [hg]
    refine hmul.trans ?_
    unfold Bder
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h1 : ‖iteratedFDeriv ℝ j (fun v : ℂ => ((cutoff (rad d₀ s₁ a₀) (v - s) : ℝ) : ℂ)) w‖ ≤ Cψ := by
      have e : (fun v : ℂ => ((cutoff (rad d₀ s₁ a₀) (v - s) : ℝ) : ℂ)) =
          Complex.ofRealLI ∘ (fun v : ℂ => cutoff (rad d₀ s₁ a₀) (v - s)) := rfl
      have hψ : ContDiffAt ℝ ∞ (fun v : ℂ => cutoff (rad d₀ s₁ a₀) (v - s)) w :=
        ((contDiff_cutoff _).comp (contDiff_id.sub contDiff_const)).contDiffAt
      have hn := LinearIsometry.norm_iteratedFDeriv_comp_left (f := fun v : ℂ => cutoff (rad d₀ s₁ a₀) (v - s))
        (x := w) Complex.ofRealLI hψ (i := j) (by exact_mod_cast le_top)
      rw [e, hn, iteratedFDeriv_comp_sub]
      exact hCψ j (hj'.trans hi) _
    have h2 := norm_iteratedFDeriv_chart_le hB c0 (i - j) hw
    have hcn : (0 : ℝ) ≤ (i.choose j : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hcn) h2 (norm_nonneg _) (mul_nonneg hcn hC0)
  · have hw' : rad d₀ s₁ a₀ < ‖w - s‖ := not_le.1 hw
    have hnhds : {v : ℂ | rad d₀ s₁ a₀ < ‖v - s‖} ∈ nhds w :=
      (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).mem_nhds hw'
    have hz : gfun (rad d₀ s₁ a₀) c0 D s A =ᶠ[nhds w] fun _ => (0 : ℂ) := by
      filter_upwards [hnhds] with v hv
      unfold gfun
      rw [cutoff_eq_zero hr (le_of_lt hv)]
      simp
    have := (Filter.EventuallyEq.iteratedFDerivWithin (𝕜 := ℝ) (s := Set.univ) (n := i)
      (by rwa [nhdsWithin_univ] : gfun (rad d₀ s₁ a₀) c0 D s A =ᶠ[nhdsWithin w Set.univ] fun _ => (0 : ℂ)))
    have h0 := this.eq_of_nhdsWithin (mem_univ w)
    rw [iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h0
    rw [h0]
    have : iteratedFDeriv ℝ i (fun _ : ℂ => (0 : ℂ)) w = 0 := by
      have := iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := ℂ) (F := ℂ) (n := i)
      simpa using congrFun this w
    rw [this, norm_zero]
    exact Bder_nonneg hC0 hr (norm_nonneg _) i

end QuantumNLS.MPChartDeriv

#print axioms QuantumNLS.MPChartDeriv.norm_iteratedFDeriv_chart_le
#print axioms QuantumNLS.MPChartDeriv.norm_iteratedFDeriv_gfun_le
