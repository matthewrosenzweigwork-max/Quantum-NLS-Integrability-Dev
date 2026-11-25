import QuantumNLS.RootWeightedMomentsR26

/-! Compact smooth tests for the two principal-value pairings. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory Set Filter Topology
namespace QuantumNLS.RootWeightedCutoffsR26
open LabelKernelLimit

def bump : ContDiffBump (0 : ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def radius (n : ℕ) : ℝ := (n : ℝ)+1
def cut (n : ℕ) (x : ℝ) : ℝ := bump (x/radius n)
def linCut (n : ℕ) (x : ℝ) : ℝ := x*cut n x
def base (x : ℝ) : ℝ := x*bump x

theorem radius_pos (n : ℕ) : 0 < radius n := by unfold radius; positivity
theorem radius_ge_one (n : ℕ) : 1 ≤ radius n := by unfold radius; linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

theorem cut_smooth (n : ℕ) : ContDiff ℝ 1 (cut n) :=
  bump.contDiff.comp (contDiff_id.div_const _)

theorem cut_support (n : ℕ) : HasCompactSupport (cut n) := by
  change HasCompactSupport (fun x : ℝ => bump (x/radius n))
  simpa only [div_eq_mul_inv,mul_comm,smul_eq_mul] using
    bump.hasCompactSupport.comp_smul (inv_ne_zero (radius_pos n).ne')

theorem linCut_smooth (n : ℕ) : ContDiff ℝ 1 (linCut n) :=
  contDiff_id.mul (cut_smooth n)

theorem linCut_support (n : ℕ) : HasCompactSupport (linCut n) :=
  (cut_support n).mul_left

theorem cut_bounds (n : ℕ) (x : ℝ) : 0 ≤ cut n x ∧ cut n x ≤ 1 :=
  ⟨bump.nonneg,bump.le_one⟩

theorem linCut_bound (n : ℕ) (x : ℝ) : |linCut n x| ≤ |x| := by
  rw [linCut,abs_mul,abs_of_nonneg (cut_bounds n x).1]
  exact mul_le_of_le_one_right (abs_nonneg _) (cut_bounds n x).2

theorem cut_tendsto (x : ℝ) : Tendsto (fun n => cut n x) atTop (𝓝 1) := by
  have hr : Tendsto radius atTop atTop := tendsto_atTop_mono
    (fun n => show (n : ℝ) ≤ radius n by unfold radius; linarith) tendsto_natCast_atTop_atTop
  have ht := (tendsto_const_nhds (x := x)).div_atTop hr
  have hc := ((bump.contDiff : ContDiff ℝ 1 (bump : ℝ → ℝ)).continuous.tendsto 0).comp ht
  have hb : bump (0 : ℝ) = 1 := bump.one_of_mem_closedBall (by simp [bump])
  simpa only [cut,hb,Function.comp_def] using hc

theorem linCut_tendsto (x : ℝ) : Tendsto (fun n => linCut n x) atTop (𝓝 x) := by
  simpa only [linCut,mul_one] using (cut_tendsto x).const_mul x

theorem cut_deriv (n : ℕ) (x : ℝ) :
    deriv (cut n) x = deriv (bump : ℝ → ℝ) (x/radius n)/radius n := by
  have hd := ((bump.contDiff.differentiable one_ne_zero (x/radius n)).hasDerivAt).comp x
    ((hasDerivAt_id x).div_const (radius n))
  have hd' : HasDerivAt (cut n) (deriv (bump : ℝ → ℝ) (x/radius n)/radius n) x := by
    change HasDerivAt (fun y => bump (y/radius n)) _ x
    simpa only [id_eq,one_div,div_eq_mul_inv,Function.comp_def,one_mul] using hd
  exact hd'.deriv

theorem linCut_scale (n : ℕ) (x : ℝ) : linCut n x = radius n*base (x/radius n) := by
  unfold linCut cut base
  field_simp [(radius_pos n).ne']

theorem linCut_deriv (n : ℕ) (x : ℝ) :
    deriv (linCut n) x = deriv base (x/radius n) := by
  have hf : ContDiff ℝ 1 base := contDiff_id.mul bump.contDiff
  have hd := (((hf.differentiable one_ne_zero (x/radius n)).hasDerivAt).comp x
    ((hasDerivAt_id x).div_const (radius n))).const_mul (radius n)
  change HasDerivAt (fun y => radius n*base (y/radius n))
    (radius n*(deriv base (x/radius n)*(1/radius n))) x at hd
  have he : (fun y => radius n*base (y/radius n)) = linCut n :=
    funext fun y => (linCut_scale n y).symm
  rw [he] at hd
  have hh : radius n*(deriv base (x/radius n)*(1/radius n)) = deriv base (x/radius n) := by
    field_simp [(radius_pos n).ne']
  simpa only [hh] using hd.deriv

theorem dd_bounds : ∃ C : ℝ, 0 < C ∧ ∀ n x y,
    |dd (cut n) x y| ≤ C ∧ |dd (linCut n) x y| ≤ C := by
  have hf : ContDiff ℝ 1 base := contDiff_id.mul bump.contDiff
  have hfc : HasCompactSupport base := bump.hasCompactSupport.mul_left
  obtain ⟨A,B,hB,_,hbd,hbl⟩ := c1c_bounds (bump.contDiff : ContDiff ℝ 1 _) bump.hasCompactSupport
  obtain ⟨A',B',hB',_,hbd',hbl'⟩ := c1c_bounds hf hfc
  refine ⟨max B B',lt_max_of_lt_left hB,fun n x y => ⟨?_,?_⟩⟩
  · apply (dd_abs_le (C1 := B) ?_ ?_ x y).trans (le_max_left _ _)
    · intro t
      rw [cut_deriv,abs_div,abs_of_pos (radius_pos n)]
      apply (div_le_div_of_nonneg_right (hbd _) (radius_pos n).le).trans
      exact div_le_self hB.le (radius_ge_one n)
    · intro t s
      have hb := hbl (t/radius n) (s/radius n)
      change |bump (t/radius n)-bump (s/radius n)| ≤ _
      calc
        _ ≤ B*|t/radius n-s/radius n| := hb
        _ = B*|t-s|/radius n := by rw [← sub_div,abs_div,abs_of_pos (radius_pos n)]; ring
        _ ≤ B*|t-s| := div_le_self (mul_nonneg hB.le (abs_nonneg _)) (radius_ge_one n)
  · apply (dd_abs_le (C1 := B') ?_ ?_ x y).trans (le_max_right _ _)
    · intro t
      rw [linCut_deriv]
      exact hbd' _
    · intro t s
      rw [linCut_scale,linCut_scale,← mul_sub,abs_mul,abs_of_pos (radius_pos n)]
      calc
        _ ≤ radius n*(B'*|t/radius n-s/radius n|) :=
          mul_le_mul_of_nonneg_left (hbl' _ _) (radius_pos n).le
        _ = _ := by
          rw [← sub_div,abs_div,abs_of_pos (radius_pos n)]
          field_simp [(radius_pos n).ne']

/-- The two cutoff pairings tend to the constant and linear tests. -/
theorem pairings (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {g : ℝ → ℝ} (hbd : IndexedScalarMeasure.LocallyUniformBoundary μ g ∨
      IndexedScalarMeasure.BoundedAEBoundary μ g)
    (hg : Integrable g μ) (hxg : Integrable (fun x => x*g x) μ) :
    (∫ x,g x ∂μ) = 0 ∧ (∫ x,x*g x ∂μ) = 1/2 := by
  obtain ⟨C,hC,hCb⟩ := dd_bounds
  have hdiag : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p.1 ≠ p.2 :=
    measure_eq_zero_iff_ae_notMem.mp (prod_diagonal_null μ)
  have hl0 : Tendsto (fun n => ∫ x,cut n x*g x ∂μ) atTop (𝓝 (∫ x,g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun n => (cut_smooth n).continuous.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      hg.norm (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => by simpa using (cut_tendsto x).mul_const (g x))
    change ‖cut n x*g x‖ ≤ ‖g x‖
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (cut_bounds n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (cut_bounds n x).2
  have hl1 : Tendsto (fun n => ∫ x,linCut n x*g x ∂μ) atTop (𝓝 (∫ x,x*g x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖x*g x‖)
      (fun n => (linCut_smooth n).continuous.aestronglyMeasurable.mul hg.aestronglyMeasurable)
      hxg.norm (fun n => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => (linCut_tendsto x).mul_const (g x))
    change ‖linCut n x*g x‖ ≤ ‖x*g x‖
    rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (linCut_bound n x) (abs_nonneg _)
  have hr0 : Tendsto (fun n => ∫ p,dd (cut n) p.1 p.2 ∂μ.prod μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence (f := fun _ : ℝ × ℝ => (0 : ℝ)) (fun _ => C)
      (fun n => (continuous_dd (cut_smooth n)).aestronglyMeasurable)
      (integrable_const C)
      (fun n => ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using (hCb n p.1 p.2).1) (hdiag.mono fun p hp => ?_)
    · simpa using ht
    · simp only [dd,if_neg hp]
      simpa using ((cut_tendsto p.1).sub (cut_tendsto p.2)).div_const (p.1-p.2)
  have hr1 : Tendsto (fun n => ∫ p,dd (linCut n) p.1 p.2 ∂μ.prod μ) atTop (𝓝 1) := by
    have ht := tendsto_integral_of_dominated_convergence (f := fun _ : ℝ × ℝ => (1 : ℝ)) (fun _ => C)
      (fun n => (continuous_dd (linCut_smooth n)).aestronglyMeasurable)
      (integrable_const C)
      (fun n => ae_of_all _ fun p => by simpa only [Real.norm_eq_abs] using (hCb n p.1 p.2).2) (hdiag.mono fun p hp => ?_)
    · simpa using ht
    · simp only [dd,if_neg hp]
      simpa only [div_self (sub_ne_zero.mpr hp)] using
        ((linCut_tendsto p.1).sub (linCut_tendsto p.2)).div_const (p.1-p.2)
  constructor
  · have ht := hr0.const_mul (1/2 : ℝ)
    simp only [mul_zero] at ht
    apply tendsto_nhds_unique hl0
    exact ht.congr (fun n => (LabelIdentification.integral_reG μ hbd (cut_smooth n) (cut_support n)).symm)
  · have ht := hr1.const_mul (1/2 : ℝ)
    simp only [mul_one] at ht
    apply tendsto_nhds_unique hl1
    exact ht.congr (fun n => (LabelIdentification.integral_reG μ hbd (linCut_smooth n) (linCut_support n)).symm)

end QuantumNLS.RootWeightedCutoffsR26
