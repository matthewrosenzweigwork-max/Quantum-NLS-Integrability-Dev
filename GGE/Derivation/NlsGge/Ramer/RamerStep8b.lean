import Mathlib
import NlsGge.Ramer.RamerStep8a
import NlsGge.Ramer.DivergenceIdentificationGlobal

/-!
# R8b: Ramer's inequality (**) (p.182-183)

See `RamerStep8b.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- If `D n = P n ∘ A - A` with `P n → id` strongly and `‖P n‖ ≤ 1`, then `‖D n‖_HS → 0`. -/
theorem tendsto_hsNorm_tail (A : HilbertSchmidt H H) (P : ℕ → H →L[ℝ] H)
    (hP : ∀ n x, ‖P n x‖ ≤ ‖x‖) (hlim : ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x))
    (D : ℕ → HilbertSchmidt H H)
    (hD : ∀ n h, (D n).toCLM h = P n (A.toCLM h) - A.toCLM h) :
    Tendsto (fun n => ‖D n‖) atTop (𝓝 0) := by
  set b := basis H with hb
  have hA := (HilbertSchmidt.hasSum_basis_sq A b).summable
  have hbd : ∀ n i, ‖(D n).toCLM (b i)‖ ^ 2 ≤ 4 * ‖A.toCLM (b i)‖ ^ 2 := by
    intro n i
    have : ‖(D n).toCLM (b i)‖ ≤ 2 * ‖A.toCLM (b i)‖ := by
      rw [hD]
      calc _ ≤ ‖P n (A.toCLM (b i))‖ + ‖A.toCLM (b i)‖ := norm_sub_le _ _
        _ ≤ _ := by linarith [hP n (A.toCLM (b i))]
    calc ‖(D n).toCLM (b i)‖ ^ 2 ≤ (2 * ‖A.toCLM (b i)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := by ring
  have hlim2 : Tendsto (fun n => ∑' i, ‖(D n).toCLM (b i)‖ ^ 2) atTop (𝓝 (∑' _i : NlsGge.Analysis.RegularizedDeterminant.basisIndex H, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (hA.mul_left 4) ?_
      (Eventually.of_forall fun n i => ?_)
    · intro i
      have h := ((hlim (A.toCLM (b i))).sub_const (A.toCLM (b i))).norm.pow 2
      simpa [hD] using h
    · rw [Real.norm_of_nonneg (by positivity)]; exact hbd n i
  simp only [tsum_zero] at hlim2
  have h3 := hlim2.sqrt
  simp only [Real.sqrt_zero] at h3
  refine h3.congr (fun n => ?_)
  rw [(HilbertSchmidt.hasSum_basis_sq (D n) b).tsum_eq, Real.sqrt_sq (norm_nonneg _)]

end Abstract

section Step8b

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem tendsto_hsDerivH_headProj (hs : (1 : ℝ) / 2 < s)
    (L : FullWeightedHilbert c s → ActualCM c) (hL : Differentiable ℝ L)
    (x : FullWeightedHilbert c s) :
    Tendsto (fun k : ℕ => hsDerivH c s hs (fun y => headProj c k (L y)) x) atTop
      (𝓝 (hsDerivH c s hs L x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine tendsto_hsNorm_tail (hsDerivH c s hs L x) (fun k => headProj c k)
    (fun k y => ?_) (headProj_tendsto c) _ (fun k h => ?_)
  · exact norm_cmTrunc_le c k y
  · have hDP : fderiv ℝ (fun y => headProj c k (L y)) x =
        (headProj c k).comp (fderiv ℝ L x) :=
      ((headProj c k).hasFDerivAt.comp x (hL x).hasFDerivAt).fderiv
    rw [HilbertSchmidt.toCLM_sub, sub_apply, hsDerivH_toCLM,
      hsDerivH_toCLM, hDP]
    rfl

theorem tendsto_det2_headProj (hs : (1 : ℝ) / 2 < s)
    (L : FullWeightedHilbert c s → ActualCM c) (hL : Differentiable ℝ L)
    (x : FullWeightedHilbert c s) :
    Tendsto (fun k : ℕ => det2 (hsDerivH c s hs (fun y => headProj c k (L y)) x)) atTop
      (𝓝 (det2 (hsDerivH c s hs L x))) :=
  (continuous_det2.tendsto _).comp (tendsto_hsDerivH_headProj c s hs L hL x)

theorem tendsto_Sn (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (x : FullWeightedHilbert c s) :
    Tendsto (fun k : ℕ => Sn c s hs k L x) atTop
      (𝓝 (x + inclE c s hs (L x))) := by
  unfold Sn
  exact tendsto_const_nhds.add (((inclE c s hs).continuous.tendsto _).comp
    (headProj_tendsto c (L x)))

theorem measurable_ramerA_coordE (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (hL : ContDiff ℝ 1 L) (n : ℕ) :
    Measurable (fun x => ramerA c s (zero_le_of_half_lt hs) n L (coordE c s x)) := by
  have h := measurable_ramerSum_comp c s (zero_le_of_half_lt hs) n L hL
    (fun z : ℤ → ℂ => headPt c n z) (NlsGge.Measure.fullWeightedSequenceRealization c s)
    (measurable_headPt c n) (NlsGge.Measure.measurable_fullWeightedSequenceRealization c s)
  exact h.comp (measurable_coordE c s)

theorem measurable_ramerJn (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    (hL : ContDiff ℝ 1 L) (n : ℕ) : Measurable (ramerJn c s n hs L) := by
  have hP : ContDiff ℝ 1 (fun y => headProj c n (L y)) :=
    (headProj c n).contDiff.comp hL
  have h1 := (continuous_det2_hsDerivH c s hs _ hP).abs.measurable
  have h2 := measurable_ramerA_coordE c s hs L hL n
  have h3 : Measurable (fun x => ‖headProj c n (L x)‖ ^ 2 / 2) :=
    ((hP.continuous.norm.pow 2).div_const 2).measurable
  have : ramerJn c s n hs L = fun x =>
      |det2 (hsDerivH c s hs (fun y => headProj c n (L y)) x)| *
        Real.exp (-(ramerA c s (zero_le_of_half_lt hs) n L (coordE c s x)) -
          ‖headProj c n (L x)‖ ^ 2 / 2) := funext (ramerJn_eq c s n hs L)
  rw [this]
  exact h1.mul (Real.measurable_exp.comp (h2.neg.sub h3))

/-- **R8b**: Ramer's inequality (**), for any `δL` that is the a.e. limit of `ramerA (φ j) L`
along a subsequence (L3b clause 4).  `F` is continuous and vanishes off `ball 0 (ε/2)`
(more general than: bounded, uniformly continuous, `tsupport F ⊆ ball 0 (ε/2)`). -/
theorem step8b (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c) {ε : ℝ}
    (hyp : Step8Hyp c s hs L ε) (δL : (ℤ → ℂ) → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hδ : ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
      Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (φ j) L z) atTop (𝓝 (δL z)))
    (F : FullWeightedHilbert c s → ℝ) (hF : Continuous F)
    (hF0 : ∀ y, y ∉ ball (0 : FullWeightedHilbert c s) (ε / 2) → F y = 0) :
    ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
        (fun y => y + inclE c s hs (L y)) ⁻¹' ball (0 : FullWeightedHilbert c s) (ε / 2),
      ENNReal.ofReal (F (x + inclE c s hs (L x))) * ENNReal.ofReal (ramerJE c s hs L δL x)
      ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) ≤
    ∫⁻ x in ball (0 : FullWeightedHilbert c s) (ε / 2), ENNReal.ofReal (F x)
      ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  set μ := NlsGge.Measure.fullWeightedSequenceGaussian c s with hμ
  set B := closedBall (0 : FullWeightedHilbert c s) ε with hB
  set Z := ball (0 : FullWeightedHilbert c s) (ε / 2) with hZ
  have hL1 : ContDiff ℝ 1 L := hyp.smooth.of_le (by norm_num)
  have hLd : Differentiable ℝ L := hL1.differentiable one_ne_zero
  have hLc : Continuous L := hL1.continuous
  set S : FullWeightedHilbert c s → FullWeightedHilbert c s :=
    fun y => y + inclE c s hs (L y) with hS
  have hSc : Continuous S := continuous_id.add ((inclE c s hs).continuous.comp hLc)
  have hBm : MeasurableSet B := measurableSet_closedBall
  set g : ℕ → FullWeightedHilbert c s → ℝ≥0∞ := fun k x =>
    ENNReal.ofReal (F (Sn c s hs k L x)) * ENNReal.ofReal (ramerJn c s k hs L x) with hg
  set g0 : FullWeightedHilbert c s → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (F (S x)) * ENNReal.ofReal (ramerJE c s hs L δL x) with hg0
  -- removing the indicator
  have hrem : ∀ (T : FullWeightedHilbert c s → FullWeightedHilbert c s), Continuous T →
      ∀ f : FullWeightedHilbert c s → ℝ≥0∞,
      (∀ x, f x ≠ 0 → T x ∈ Z) →
      ∫⁻ x in B ∩ T ⁻¹' Z, f x ∂μ = ∫⁻ x in B, f x ∂μ := by
    intro T hT f hf
    have hA : MeasurableSet (T ⁻¹' Z) := (isOpen_ball.preimage hT).measurableSet
    rw [inter_comm, ← Measure.restrict_restrict hA]
    exact setLIntegral_eq_of_support_subset (fun x hx => hf x hx)
  have hFz : ∀ y, ENNReal.ofReal (F y) ≠ 0 → y ∈ Z := by
    intro y hy
    by_contra h
    exact hy (by rw [hF0 y h]; simp)
  have hgsupp : ∀ (T : FullWeightedHilbert c s → FullWeightedHilbert c s) (a : _ → ℝ),
      ∀ x, ENNReal.ofReal (F (T x)) * ENNReal.ofReal (a x) ≠ 0 → T x ∈ Z := by
    intro T a x hx
    exact hFz _ (left_ne_zero_of_mul hx)
  have hstep : ∀ k, ∫⁻ x in B, g k x ∂μ = ∫⁻ x in Z, ENNReal.ofReal (F x) ∂μ := by
    intro k
    rw [← hrem (Sn c s hs k L) (continuous_Sn c s hs k L hLc) (g k)
      (hgsupp (Sn c s hs k L) (ramerJn c s k hs L))]
    exact (step8a c s k hs L hyp F hF.measurable).symm
  have hgm : ∀ k, Measurable (g k) := fun k =>
    (hF.measurable.comp (continuous_Sn c s hs k L hLc).measurable).ennreal_ofReal.mul
      (measurable_ramerJn c s hs L hL1 k).ennreal_ofReal
  -- a.e. convergence
  have hae : ∀ᵐ x ∂μ, Tendsto (fun j => g (φ j) x) atTop (𝓝 (g0 x)) := by
    have h1 := ae_of_ae_coordE c s hs hδ
    filter_upwards [h1] with x hx
    have hφt := hφ.tendsto_atTop
    have tF : Tendsto (fun j => F (Sn c s hs (φ j) L x)) atTop (𝓝 (F (S x))) :=
      (hF.tendsto _).comp ((tendsto_Sn c s hs L x).comp hφt)
    have tdet := (tendsto_det2_headProj c s hs L hLd x).comp hφt
    have tn : Tendsto (fun j => ‖headProj c (φ j) (L x)‖ ^ 2 / 2) atTop
        (𝓝 (‖L x‖ ^ 2 / 2)) :=
      ((((headProj_tendsto c (L x)).comp hφt).norm).pow 2).div_const 2
    have tJ : Tendsto (fun j => ramerJn c s (φ j) hs L x) atTop
        (𝓝 (ramerJE c s hs L δL x)) := by
      simp_rw [ramerJn_eq]
      rw [ramerJE_eq]
      exact tdet.abs.mul (Real.continuous_exp.tendsto _ |>.comp ((hx.neg).sub tn))
    exact ENNReal.Tendsto.mul (ENNReal.tendsto_ofReal tF) (Or.inr ENNReal.ofReal_ne_top)
      (ENNReal.tendsto_ofReal tJ) (Or.inr ENNReal.ofReal_ne_top)
  have hg0supp : ∀ x, g0 x ≠ 0 → S x ∈ Z :=
    hgsupp S (ramerJE c s hs L δL)
  calc ∫⁻ x in B ∩ S ⁻¹' Z, g0 x ∂μ = ∫⁻ x in B, g0 x ∂μ := hrem S hSc g0 hg0supp
    _ = ∫⁻ x in B, liminf (fun j => g (φ j) x) atTop ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae hae] with x hx
        exact hx.liminf_eq.symm
    _ ≤ liminf (fun j => ∫⁻ x in B, g (φ j) x ∂μ) atTop :=
        lintegral_liminf_le (fun j => hgm (φ j))
    _ = ∫⁻ x in Z, ENNReal.ofReal (F x) ∂μ := by
        simp_rw [hstep]
        exact (tendsto_const_nhds.liminf_eq)

/-- **R8b, final form**: with `δL` from L3b `divergence_identification` for `L`, and
`F` bounded, uniformly continuous, `≥ 0`, `tsupport F ⊆ ball 0 (ε/2)`:
`∫⁻_{B̄ ∩ S⁻¹ Z} F(S x) J^S(x) dγ_E ≤ ∫⁻_Z F dγ_E`. -/
theorem step8b_divergence (hs : (1 : ℝ) / 2 < s) (L : FullWeightedHilbert c s → ActualCM c)
    {ε : ℝ} (hyp : Step8Hyp c s hs L ε) :
    ∃ δL : (ℤ → ℂ) → ℝ,
      AEStronglyMeasurable δL (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ z ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val),
          Tendsto (fun j => ramerA c s (zero_le_of_half_lt hs) (φ j) L z) atTop (𝓝 (δL z))) ∧
      ∀ F : FullWeightedHilbert c s → ℝ, (∃ C, ∀ y, |F y| ≤ C) → UniformContinuous F →
        (∀ y, 0 ≤ F y) → tsupport F ⊆ ball (0 : FullWeightedHilbert c s) (ε / 2) →
        ∫⁻ x in closedBall (0 : FullWeightedHilbert c s) ε ∩
            (fun y => y + inclE c s hs (L y)) ⁻¹' ball (0 : FullWeightedHilbert c s) (ε / 2),
          ENNReal.ofReal (F (x + inclE c s hs (L x))) *
            ENNReal.ofReal (ramerJE c s hs L δL x)
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) ≤
        ∫⁻ x in ball (0 : FullWeightedHilbert c s) (ε / 2), ENNReal.ofReal (F x)
          ∂(NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  obtain ⟨δL, hm, -, -, ⟨φ, hφ, hlim⟩, -⟩ := divergence_identification c s hs L hyp.smooth
  refine ⟨δL, hm, ⟨φ, hφ, hlim⟩, fun F _ hu _ hts => ?_⟩
  exact step8b c s hs L hyp δL φ hφ hlim F hu.continuous
    (fun y hy => by
      by_contra h
      exact hy (hts (subset_tsupport _ h)))

end Step8b

end NlsGge.Ramer
