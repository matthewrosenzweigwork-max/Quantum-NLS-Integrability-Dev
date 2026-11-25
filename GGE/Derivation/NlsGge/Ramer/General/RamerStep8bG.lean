import Mathlib
import NlsGge.Ramer.General.RamerStep8aG
import NlsGge.Ramer.General.DivergenceIdentificationGlobalG

/-!
# R8b, generalized (GD7): Ramer's inequality (**) (p.182-183) over a `RamerSetting S`

Adapted from `NlsGge/Ramer/RamerStep8b.lean`.  Dictionary: `c, s, hs ↦ S`, `inclE ↦ S.incl`,
`headProj c k ↦ S.headProj k`, `hsDerivH ↦ S.hsDerivH`, `Sn ↦ S.Sn`, `ramerJE ↦ S.ramerJE`,
`fullWeightedSequenceGaussian c s ↦ S.γE`, `fullWeightSequenceGaussian c.val ↦ S.γ`.
No norm of `E` beyond continuity is used.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace NlsGge.Ramer.Gen

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

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer NlsGge.Analysis.RegularizedDeterminant

section Step8b

variable (S : NlsGge.Ramer.General.RamerSetting)

theorem tendsto_hsDerivH_headProj
    (L : S.E → S.H) (hL : Differentiable ℝ L)
    (x : S.E) :
    Tendsto (fun k : ℕ => S.hsDerivH (fun y => S.headProj k (L y)) x) atTop
      (𝓝 (S.hsDerivH L x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine NlsGge.Ramer.Gen.tendsto_hsNorm_tail (S.hsDerivH L x) (fun k => S.headProj k)
    (fun k y => ?_) S.headProj_tendsto _ (fun k h => ?_)
  · exact S.norm_headProj_le k y
  · have hDP : fderiv ℝ (fun y => S.headProj k (L y)) x =
        (S.headProj k).comp (fderiv ℝ L x) :=
      ((S.headProj k).hasFDerivAt.comp x (hL x).hasFDerivAt).fderiv
    rw [HilbertSchmidt.toCLM_sub, sub_apply, S.hsDerivH_toCLM,
      S.hsDerivH_toCLM, hDP]
    rfl

theorem tendsto_det2_headProj
    (L : S.E → S.H) (hL : Differentiable ℝ L)
    (x : S.E) :
    Tendsto (fun k : ℕ => det2 (S.hsDerivH (fun y => S.headProj k (L y)) x)) atTop
      (𝓝 (det2 (S.hsDerivH L x))) :=
  (continuous_det2.tendsto _).comp (S.tendsto_hsDerivH_headProj L hL x)

theorem tendsto_Sn (L : S.E → S.H)
    (x : S.E) :
    Tendsto (fun k : ℕ => S.Sn k L x) atTop
      (𝓝 (x + S.incl (L x))) := by
  unfold Sn
  exact tendsto_const_nhds.add ((S.incl.continuous.tendsto _).comp
    (S.headProj_tendsto (L x)))

theorem measurable_ramerA_coordE (L : S.E → S.H)
    (hL : ContDiff ℝ 1 L) (n : ℕ) :
    Measurable (fun x => S.ramerA n L (S.coordE x)) := by
  have h := S.measurable_ramerSum_comp n L hL
    (fun z : ℤ → ℂ => S.headPt n z) S.R
    (S.measurable_headPt n) S.measurable_R
  exact h.comp S.measurable_coordE

theorem measurable_ramerJn (L : S.E → S.H)
    (hL : ContDiff ℝ 1 L) (n : ℕ) : Measurable (S.ramerJn n L) := by
  have hP : ContDiff ℝ 1 (fun y => S.headProj n (L y)) :=
    (S.headProj n).contDiff.comp hL
  have h1 := (S.continuous_det2_hsDerivH _ hP).abs.measurable
  have h2 := S.measurable_ramerA_coordE L hL n
  have h3 : Measurable (fun x => ‖S.headProj n (L x)‖ ^ 2 / 2) :=
    ((hP.continuous.norm.pow 2).div_const 2).measurable
  have : S.ramerJn n L = fun x =>
      |det2 (S.hsDerivH (fun y => S.headProj n (L y)) x)| *
        Real.exp (-(S.ramerA n L (S.coordE x)) -
          ‖S.headProj n (L x)‖ ^ 2 / 2) := funext (S.ramerJn_eq n L)
  rw [this]
  exact h1.mul (Real.measurable_exp.comp (h2.neg.sub h3))

/-- **R8b**: Ramer's inequality (**), for any `δL` that is the a.e. limit of `ramerA (φ j) L`
along a subsequence (L3b clause 4).  `F` is continuous and vanishes off `ball 0 (ε/2)`
(more general than: bounded, uniformly continuous, `tsupport F ⊆ ball 0 (ε/2)`). -/
theorem step8b (L : S.E → S.H) {ε : ℝ}
    (hyp : S.Step8Hyp L ε) (δL : (ℤ → ℂ) → ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hδ : ∀ᵐ z ∂S.γ,
      Tendsto (fun j => S.ramerA (φ j) L z) atTop (𝓝 (δL z)))
    (F : S.E → ℝ) (hF : Continuous F)
    (hF0 : ∀ y, y ∉ ball (0 : S.E) (ε / 2) → F y = 0) :
    ∫⁻ x in closedBall (0 : S.E) ε ∩
        (fun y => y + S.incl (L y)) ⁻¹' ball (0 : S.E) (ε / 2),
      ENNReal.ofReal (F (x + S.incl (L x))) * ENNReal.ofReal (S.ramerJE L δL x)
      ∂S.γE ≤
    ∫⁻ x in ball (0 : S.E) (ε / 2), ENNReal.ofReal (F x)
      ∂S.γE := by
  set μ := S.γE with hμ
  set B := closedBall (0 : S.E) ε with hB
  set Z := ball (0 : S.E) (ε / 2) with hZ
  have hL1 : ContDiff ℝ 1 L := hyp.smooth.of_le (by norm_num)
  have hLd : Differentiable ℝ L := hL1.differentiable one_ne_zero
  have hLc : Continuous L := hL1.continuous
  set Tm : S.E → S.E :=
    fun y => y + S.incl (L y) with hTm
  have hSc : Continuous Tm := continuous_id.add ((S.incl).continuous.comp hLc)
  have hBm : MeasurableSet B := measurableSet_closedBall
  set g : ℕ → S.E → ℝ≥0∞ := fun k x =>
    ENNReal.ofReal (F (S.Sn k L x)) * ENNReal.ofReal (S.ramerJn k L x) with hg
  set g0 : S.E → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (F (Tm x)) * ENNReal.ofReal (S.ramerJE L δL x) with hg0
  -- removing the indicator
  have hrem : ∀ (T : S.E → S.E), Continuous T →
      ∀ f : S.E → ℝ≥0∞,
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
  have hgsupp : ∀ (T : S.E → S.E) (a : _ → ℝ),
      ∀ x, ENNReal.ofReal (F (T x)) * ENNReal.ofReal (a x) ≠ 0 → T x ∈ Z := by
    intro T a x hx
    exact hFz _ (left_ne_zero_of_mul hx)
  have hstep : ∀ k, ∫⁻ x in B, g k x ∂μ = ∫⁻ x in Z, ENNReal.ofReal (F x) ∂μ := by
    intro k
    rw [← hrem (S.Sn k L) (S.continuous_Sn k L hLc) (g k)
      (hgsupp (S.Sn k L) (S.ramerJn k L))]
    exact (S.step8a k L hyp F hF.measurable).symm
  have hgm : ∀ k, Measurable (g k) := fun k =>
    (hF.measurable.comp (S.continuous_Sn k L hLc).measurable).ennreal_ofReal.mul
      (S.measurable_ramerJn L hL1 k).ennreal_ofReal
  -- a.e. convergence
  have hae : ∀ᵐ x ∂μ, Tendsto (fun j => g (φ j) x) atTop (𝓝 (g0 x)) := by
    have h1 := S.ae_of_ae_coordE hδ
    filter_upwards [h1] with x hx
    have hφt := hφ.tendsto_atTop
    have tF : Tendsto (fun j => F (S.Sn (φ j) L x)) atTop (𝓝 (F (Tm x))) :=
      (hF.tendsto _).comp ((S.tendsto_Sn L x).comp hφt)
    have tdet := (S.tendsto_det2_headProj L hLd x).comp hφt
    have tn : Tendsto (fun j => ‖S.headProj (φ j) (L x)‖ ^ 2 / 2) atTop
        (𝓝 (‖L x‖ ^ 2 / 2)) :=
      ((((S.headProj_tendsto (L x)).comp hφt).norm).pow 2).div_const 2
    have tJ : Tendsto (fun j => S.ramerJn (φ j) L x) atTop
        (𝓝 (S.ramerJE L δL x)) := by
      simp_rw [S.ramerJn_eq]
      rw [S.ramerJE_eq]
      exact tdet.abs.mul (Real.continuous_exp.tendsto _ |>.comp ((hx.neg).sub tn))
    exact ENNReal.Tendsto.mul (ENNReal.tendsto_ofReal tF) (Or.inr ENNReal.ofReal_ne_top)
      (ENNReal.tendsto_ofReal tJ) (Or.inr ENNReal.ofReal_ne_top)
  have hg0supp : ∀ x, g0 x ≠ 0 → Tm x ∈ Z :=
    hgsupp Tm (S.ramerJE L δL)
  calc ∫⁻ x in B ∩ Tm ⁻¹' Z, g0 x ∂μ = ∫⁻ x in B, g0 x ∂μ := hrem Tm hSc g0 hg0supp
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
theorem step8b_divergence (L : S.E → S.H)
    {ε : ℝ} (hyp : S.Step8Hyp L ε) :
    ∃ δL : (ℤ → ℂ) → ℝ,
      AEStronglyMeasurable δL S.γ ∧
      (∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ᵐ z ∂S.γ,
          Tendsto (fun j => S.ramerA (φ j) L z) atTop (𝓝 (δL z))) ∧
      ∀ F : S.E → ℝ, (∃ C, ∀ y, |F y| ≤ C) → UniformContinuous F →
        (∀ y, 0 ≤ F y) → tsupport F ⊆ ball (0 : S.E) (ε / 2) →
        ∫⁻ x in closedBall (0 : S.E) ε ∩
            (fun y => y + S.incl (L y)) ⁻¹' ball (0 : S.E) (ε / 2),
          ENNReal.ofReal (F (x + S.incl (L x))) *
            ENNReal.ofReal (S.ramerJE L δL x)
          ∂S.γE ≤
        ∫⁻ x in ball (0 : S.E) (ε / 2), ENNReal.ofReal (F x)
          ∂S.γE := by
  obtain ⟨δL, hm, -, -, ⟨φ, hφ, hlim⟩, -⟩ := S.divergence_identification L hyp.smooth
  refine ⟨δL, hm, ⟨φ, hφ, hlim⟩, fun F _ hu _ hts => ?_⟩
  exact S.step8b L hyp δL φ hφ hlim F hu.continuous
    (fun y hy => by
      by_contra h
      exact hy (hts (subset_tsupport _ h)))

end Step8b

end NlsGge.Ramer.General.RamerSetting
