                                                                                                                                                                                                             
import NlsGge.Ramer.FiniteDivergenceGrowth

                                                                                                   
                                                                                        
                                                                                                     
                                                                                            
set_option autoImplicit false

open MeasureTheory Filter Real Set
open scoped Topology RealInnerProductSpace ENNReal
open NlsGge.Ramer

namespace NlsGge.ThirdConsultation.R
noncomputable section

def GaussianIBPAdmissible {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : E → ℝ) : Prop :=
  ContDiff ℝ 1 f ∧
  ∃ C : ℝ, ∀ x, |f x| + ‖fderiv ℝ f x‖ ≤ C*Real.exp (C*‖x‖)

namespace R016Aux

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem integrable_exp_norm (C : ℝ) :
    Integrable (fun x : V => Real.exp (C * ‖x‖)) (finiteStdGaussian V) := by
  rw [finiteStdGaussian, integrable_withDensity_iff_integrable_smul'
    (continuous_finiteGaussianDensity.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hmeas : AEStronglyMeasurable (fun x : V => ((ENNReal.ofReal (finiteGaussianDensity V x)).toReal •
      Real.exp (C * ‖x‖))) volume := by
    have : Continuous (fun x : V => finiteGaussianDensity V x * Real.exp (C * ‖x‖)) := by
      have := continuous_finiteGaussianDensity (V := V); fun_prop
    refine this.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (finiteGaussianDensity_pos x).le]
  refine Integrable.mono' (g := fun x : V => ((2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
    Real.exp (C ^ 2)) * Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2))
    (integrable_rexp_neg_quarter_sq_norm.const_mul _) hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [ENNReal.toReal_ofReal (finiteGaussianDensity_pos x).le, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (by have := finiteGaussianDensity_pos (V := V) x; positivity)]
  unfold finiteGaussianDensity
  have hc : (0 : ℝ) ≤ (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) := by positivity
  have key : Real.exp (-(‖x‖ ^ 2) / 2) * Real.exp (C * ‖x‖) ≤
      Real.exp (C ^ 2) * Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [sq_nonneg (‖x‖ / 2 - C)]
  calc (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2) / 2) * Real.exp (C * ‖x‖)
      = (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
        (Real.exp (-(‖x‖ ^ 2) / 2) * Real.exp (C * ‖x‖)) := by ring
    _ ≤ (2 * π) ^ (-(Module.finrank ℝ V : ℝ) / 2) *
        (Real.exp (C ^ 2) * Real.exp (-(1 / 4 : ℝ) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left key hc
    _ = _ := by ring

theorem integrable_of_le_exp {g : V → ℝ} (hg : AEStronglyMeasurable g (finiteStdGaussian V))
    (K C : ℝ) (h : ∀ x, ‖g x‖ ≤ K * Real.exp (C * ‖x‖)) :
    Integrable g (finiteStdGaussian V) :=
  Integrable.mono' ((integrable_exp_norm (V := V) C).const_mul K) hg
    (Filter.Eventually.of_forall h)

theorem tendsto_cut_integral {g : V → ℝ} (hgm : Continuous g) (K C : ℝ)
    (hb : ∀ x, ‖g x‖ ≤ K * Real.exp (C * ‖x‖)) :
    Tendsto (fun n : ℕ => ∫ x, cutR ((n : ℝ) + 1) x * g x ∂(finiteStdGaussian V)) atTop
      (𝓝 (∫ x, g x ∂(finiteStdGaussian V))) := by
  refine tendsto_integral_of_dominated_convergence (fun x => K * Real.exp (C * ‖x‖))
    (fun n => ((contDiff_cutR (V := V) _ 0).continuous.mul hgm).aestronglyMeasurable)
    ((integrable_exp_norm (V := V) C).const_mul K)
    (fun n => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
  · rw [norm_mul]
    have h0 := cutR_nonneg (V := V) ((n : ℝ) + 1) x
    have h1 := cutR_le_one (V := V) ((n : ℝ) + 1) x
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans (hb x)
  · obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have : ‖x‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    show g x = cutR ((n : ℝ) + 1) x * g x
    rw [cutR_eq_one (by positivity) this, one_mul]

theorem tendsto_cut_deriv_integral {g : V → ℝ} (hgm : Continuous g) (K C : ℝ)
    (hb : ∀ x, ‖g x‖ ≤ K * Real.exp (C * ‖x‖)) (e : V) (he : ‖e‖ = 1) :
    Tendsto (fun n : ℕ => ∫ x, g x * fderiv ℝ (cutR ((n : ℝ) + 1)) x e
        ∂(finiteStdGaussian V)) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_fderiv_cutR_le (V := V)
  have h0 : (0 : ℝ) = ∫ x, (0 : ℝ) ∂(finiteStdGaussian V) := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun x => K * M * Real.exp (C * ‖x‖))
    (fun n => (hgm.mul (((contDiff_cutR (V := V) _ 1).continuous_fderiv (by simp)).clm_apply
      continuous_const)).aestronglyMeasurable)
    (by simpa [mul_assoc] using (integrable_exp_norm (V := V) C).const_mul (K * M))
    (fun n => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
  · have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [norm_mul]
    have h1 : ‖fderiv ℝ (cutR ((n : ℝ) + 1)) x e‖ ≤ M := by
      calc _ ≤ ‖fderiv ℝ (cutR ((n : ℝ) + 1)) x‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ M := by rw [he, mul_one]; exact hM _ hR x
    calc ‖g x‖ * ‖fderiv ℝ (cutR ((n : ℝ) + 1)) x e‖ ≤ (K * Real.exp (C * ‖x‖)) * M :=
          mul_le_mul (hb x) h1 (norm_nonneg _) ((norm_nonneg _).trans (hb x))
      _ = K * M * Real.exp (C * ‖x‖) := by ring
  · obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
    have hlt : ‖x‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hev : (cutR (V := V) ((n : ℝ) + 1)) =ᶠ[𝓝 x] fun _ => 1 := by
      have hU : Metric.ball (0 : V) ((n : ℝ) + 1) ∈ 𝓝 x :=
        Metric.isOpen_ball.mem_nhds (by simpa using hlt)
      filter_upwards [hU] with y hy
      exact cutR_eq_one (by positivity) (by simpa using hy)
    show (0 : ℝ) = g x * fderiv ℝ (cutR ((n : ℝ) + 1)) x e
    rw [hev.fderiv_eq]
    simp

end R016Aux

theorem gaussian_coordinate_ibp {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (i : Fin d)
    (hf : GaussianIBPAdmissible f) :
    ∫ x, fderiv ℝ f x (EuclideanSpace.single i 1)
        ∂(finiteStdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ x, x i * f x ∂(finiteStdGaussian (EuclideanSpace ℝ (Fin d))) := by
  classical
  obtain ⟨hC1, C, hC⟩ := hf
  have hfd : Differentiable ℝ f := hC1.differentiable (by norm_num)
  have hf'c : Continuous (fderiv ℝ f) := hC1.continuous_fderiv (by norm_num)
  have hfc : Continuous f := hC1.continuous
  have hfb : ∀ x, ‖f x‖ ≤ C * Real.exp (C * ‖x‖) := fun x => by
    have := hC x; have := norm_nonneg (fderiv ℝ f x); rw [Real.norm_eq_abs]; linarith
  have hf'b : ∀ x, ‖fderiv ℝ f x‖ ≤ C * Real.exp (C * ‖x‖) := fun x => by
    have := hC x; have := abs_nonneg (f x); linarith
  set e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1 with he_def
  have he : ‖e‖ = 1 := by simp [e]
  have hpb : ∀ x, ‖fderiv ℝ f x e‖ ≤ C * Real.exp (C * ‖x‖) := fun x => by
    calc _ ≤ ‖fderiv ℝ f x‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by rw [he, mul_one]; exact hf'b x
  have hpc : Continuous (fun x => fderiv ℝ f x e) := hf'c.clm_apply continuous_const
  have hxic : Continuous (fun x : EuclideanSpace ℝ (Fin d) => x i) :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous
  have hxi : ∀ x : EuclideanSpace ℝ (Fin d), |x i| ≤ Real.exp ‖x‖ := fun x => by
    have h1 : |x i| ≤ ‖x‖ := by
      have := PiLp.norm_apply_le x i
      simpa [Real.norm_eq_abs] using this
    have h2 := Real.add_one_le_exp ‖x‖
    linarith
  have hgb : ∀ x : EuclideanSpace ℝ (Fin d), ‖x i * f x‖ ≤ C * Real.exp ((C + 1) * ‖x‖) := fun x => by
    rw [norm_mul, Real.norm_eq_abs]
    have h0 : 0 ≤ C * Real.exp (C * ‖x‖) := (norm_nonneg _).trans (hfb x)
    calc |x i| * ‖f x‖ ≤ Real.exp ‖x‖ * (C * Real.exp (C * ‖x‖)) :=
          mul_le_mul (hxi x) (hfb x) (norm_nonneg _) (Real.exp_pos _).le
      _ = C * Real.exp ((C + 1) * ‖x‖) := by
          rw [show (C + 1) * ‖x‖ = ‖x‖ + C * ‖x‖ by ring, Real.exp_add]; ring
  have hgc : Continuous (fun x : EuclideanSpace ℝ (Fin d) => x i * f x) := hxic.mul hfc
  -- the finite identity
  have hid : ∀ n : ℕ,
      ∫ x, cutR ((n : ℝ) + 1) x * (x i * f x) ∂(finiteStdGaussian (EuclideanSpace ℝ (Fin d))) =
        ∫ x, cutR ((n : ℝ) + 1) x * fderiv ℝ f x e ∂(finiteStdGaussian (EuclideanSpace ℝ (Fin d))) +
        ∫ x, f x * fderiv ℝ (cutR ((n : ℝ) + 1)) x e ∂(finiteStdGaussian (EuclideanSpace ℝ (Fin d))) := by
    intro n
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hφ1 : ContDiff ℝ 1 (fun x => cutR ((n : ℝ) + 1) x * f x) :=
      (contDiff_cutR _ 1).mul hC1
    have hφc : HasCompactSupport (fun x => cutR ((n : ℝ) + 1) x * f x) :=
      (hasCompactSupport_cutR (V := EuclideanSpace ℝ (Fin d)) hR).mul_right
    have h := integral_mul_finiteGaussianDivergence (fun x => cutR ((n : ℝ) + 1) x * f x)
      (fun _ => e) hφ1 hφc contDiff_const
    have hdiv : ∀ x : EuclideanSpace ℝ (Fin d), finiteGaussianDivergence (fun _ => e) x = x i := by
      intro x
      unfold finiteGaussianDivergence
      simp [e, EuclideanSpace.inner_single_right]
    simp only [hdiv] at h
    have hd1 : ∀ x, fderiv ℝ (fun y => cutR ((n : ℝ) + 1) y * f y) x e =
        cutR ((n : ℝ) + 1) x * fderiv ℝ f x e + f x * fderiv ℝ (cutR ((n : ℝ) + 1)) x e := by
      intro x
      rw [fderiv_cutR_mul hfd]
      simp [mul_comm]
    simp only [hd1] at h
    have hI1 : Integrable (fun x => cutR ((n : ℝ) + 1) x * fderiv ℝ f x e)
        (finiteStdGaussian (EuclideanSpace ℝ (Fin d))) := by
      refine R016Aux.integrable_of_le_exp (((contDiff_cutR _ 0).continuous.mul hpc).aestronglyMeasurable)
        C C (fun x => ?_)
      rw [norm_mul]
      have h0 := cutR_nonneg (V := EuclideanSpace ℝ (Fin d)) ((n : ℝ) + 1) x
      have h1 := cutR_le_one (V := EuclideanSpace ℝ (Fin d)) ((n : ℝ) + 1) x
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact (mul_le_of_le_one_left (norm_nonneg _) h1).trans (hpb x)
    obtain ⟨M, hM0, hM⟩ := exists_norm_fderiv_cutR_le (V := EuclideanSpace ℝ (Fin d))
    have hI2 : Integrable (fun x => f x * fderiv ℝ (cutR ((n : ℝ) + 1)) x e)
        (finiteStdGaussian (EuclideanSpace ℝ (Fin d))) := by
      have hR1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      refine R016Aux.integrable_of_le_exp (hfc.mul (((contDiff_cutR (V := EuclideanSpace ℝ (Fin d)) _ 1).continuous_fderiv (by simp)).clm_apply continuous_const)).aestronglyMeasurable
        (C * M) C (fun x => ?_)
      rw [norm_mul]
      have h1 : ‖fderiv ℝ (cutR ((n : ℝ) + 1)) x e‖ ≤ M := by
        calc _ ≤ ‖fderiv ℝ (cutR ((n : ℝ) + 1)) x‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ M := by rw [he, mul_one]; exact hM _ hR1 x
      calc ‖f x‖ * ‖fderiv ℝ (cutR ((n : ℝ) + 1)) x e‖ ≤ (C * Real.exp (C * ‖x‖)) * M :=
            mul_le_mul (hfb x) h1 (norm_nonneg _) ((norm_nonneg _).trans (hfb x))
        _ = C * M * Real.exp (C * ‖x‖) := by ring
    rw [← integral_add hI1 hI2, ← h]
    congr 1; funext x; ring
  have hT1 := R016Aux.tendsto_cut_integral (V := EuclideanSpace ℝ (Fin d)) hgc C (C + 1) hgb
  have hT2 := R016Aux.tendsto_cut_integral (V := EuclideanSpace ℝ (Fin d)) hpc C C hpb
  have hT3 := R016Aux.tendsto_cut_deriv_integral (V := EuclideanSpace ℝ (Fin d)) hfc C C
    (fun x => by exact hfb x) e he
  have hT4 := hT2.add hT3
  rw [add_zero] at hT4
  simp only [hid] at hT1
  exact (tendsto_nhds_unique hT4 hT1)

end
end NlsGge.ThirdConsultation.R
