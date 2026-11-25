import Mathlib
import NlsGge.ThirdConsultation.R.CylCore06
import NlsGge.Ramer.CylindricalClosability
import NlsGge.ThirdConsultation.R.R021Support1

                                                                                                                
                                                                                            
                                                                                                     
                                                           
                                                                                 
                                                                                                                         
                                                                                                             
                                                             
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace NlsGge.ThirdConsultation.R
noncomputable section

open NlsGge.Ramer NlsGge.Pilot

variable {lower upper : ℝ}

theorem r021_core_contDiff {c : BoundedCoefficients lower upper} {N : ℕ}
    {f : actualCMHead c N → actualCMHead c N} (h : GaussianL2CylindricalCore c N f) :
    ContDiff ℝ 2 f := by
  unfold GaussianL2CylindricalCore at h; exact h.1

theorem r021_core_memLp {c : BoundedCoefficients lower upper} {N : ℕ}
    {f : actualCMHead c N → actualCMHead c N} (h : GaussianL2CylindricalCore c N f) :
    MemLp f 2 (finiteStdGaussian (actualCMHead c N)) := by
  unfold GaussianL2CylindricalCore at h; exact h.2.1

theorem r021_core_memLp_div {c : BoundedCoefficients lower upper} {N : ℕ}
    {f : actualCMHead c N → actualCMHead c N} (h : GaussianL2CylindricalCore c N f) :
    MemLp (finiteGaussianDivergence f) 2 (finiteStdGaussian (actualCMHead c N)) := by
  unfold GaussianL2CylindricalCore at h; exact h.2.2

/-- The head point map is continuous. -/
theorem r021_continuous_headPt (c : BoundedCoefficients lower upper) (N : ℕ) :
    Continuous (headPt c N) := by
  have hL : Continuous ((actualCMHeadCoord c N).symm.toContinuousLinearEquiv :
      FourierPlane N → actualCMHead c N) :=
    (actualCMHeadCoord c N).symm.toContinuousLinearEquiv.continuous
  have hπ : Continuous (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) :=
    continuous_pi fun i => continuous_apply _
  exact hL.comp hπ

/-- The `H`-valued cylinder of a continuous level-`N` field is almost everywhere strongly measurable. -/
theorem r021_aesm_cylField (c : BoundedCoefficients lower upper) (N : ℕ)
    {μ : Measure (ℤ → ℂ)} (f : actualCMHead c N → actualCMHead c N) (hf : Continuous f) :
    AEStronglyMeasurable (cylField c N f) μ := by
  have h1 : Continuous (fun z : ℤ → ℂ => f (headPt c N z)) :=
    hf.comp (r021_continuous_headPt c N)
  have hval : Continuous (fun v : actualCMHead c N => (v : ActualCM c)) := continuous_subtype_val
  exact hval.comp_aestronglyMeasurable h1.aestronglyMeasurable

/-- `L²` membership of a continuous level-`N` field on the finite head law is `L²` membership of its
`H`-valued cylinder on the coordinate law. -/
theorem r021_memLp_head_iff (c : BoundedCoefficients lower upper) (N : ℕ)
    (f : actualCMHead c N → actualCMHead c N) (hf : Continuous f) :
    MemLp f 2 (finiteStdGaussian (actualCMHead c N)) ↔
      MemLp (cylField c N f) 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  have hA : AEStronglyMeasurable (f ∘ headPt c N)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
    (hf.comp (r021_continuous_headPt c N)).aestronglyMeasurable
  rw [← headPt_map c N]
  refine (memLp_map_measure_iff hf.aestronglyMeasurable
    (measurable_headPt c N).aemeasurable).trans ?_
  exact (memLp_norm_iff hA).symm.trans (memLp_norm_iff (r021_aesm_cylField c N f hf))

/-- `L²` membership of the finite divergence transfers to the cylindrical divergence. -/
theorem r021_memLp_cylDiv_iff (c : BoundedCoefficients lower upper) (N : ℕ)
    (f : actualCMHead c N → actualCMHead c N) (hf : ContDiff ℝ 1 f) :
    MemLp (finiteGaussianDivergence f) 2 (finiteStdGaussian (actualCMHead c N)) ↔
      MemLp (cylDiv c N f) 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  rw [← headPt_map c N]
  exact memLp_map_measure_iff (continuous_finiteGaussianDivergence hf).aestronglyMeasurable
    (measurable_headPt c N).aemeasurable

/-- **Level lifting preserves the L² graph core.** For `N ≤ M`, the lift of a `GaussianL2CylindricalCore`
field of level `N` is a `GaussianL2CylindricalCore` of level `M`. -/
theorem r021_lift_core (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (g : actualCMHead c N → actualCMHead c N) (hg : GaussianL2CylindricalCore c N g) :
    GaussianL2CylindricalCore c M (liftField c h g) := by
  have hgC : ContDiff ℝ 2 g := r021_core_contDiff hg
  have hgL := r021_core_memLp hg
  have hgD := r021_core_memLp_div hg
  have hC : ContDiff ℝ 2 (liftField c h g) :=
    (levelIncl c h).contDiff.comp (hgC.comp (levelProj c N M).contDiff)
  have hC1 : ContDiff ℝ 1 (liftField c h g) := hC.of_le (by norm_num)
  have hC1' : ContDiff ℝ 1 g := hgC.of_le (by norm_num)
  have hcyl : cylField c M (liftField c h g) = cylField c N g :=
    funext fun z => cylField_lift c h g z
  have hdcyl : cylDiv c M (liftField c h g) = cylDiv c N g :=
    funext fun z => cylDiv_lift c h g (hgC.differentiable (by norm_num)) z
  unfold GaussianL2CylindricalCore
  refine ⟨hC, ?_, ?_⟩
  · rw [r021_memLp_head_iff c M _ hC.continuous, hcyl,
      ← r021_memLp_head_iff c N g hgC.continuous]
    exact hgL
  · rw [r021_memLp_cylDiv_iff c M _ hC1, hdcyl, ← r021_memLp_cylDiv_iff c N g hC1']
    exact hgD

/-- **Mixed-level bound on the L² core.** For a level-`N` field `g` in `GaussianL2CylindricalCore`,
a bounded `C¹` test `φ` of the level-`N₀` window with bounded derivative:
`φ(z_{window N₀}) · δ_cyl g` is integrable and
`|∫ φ δ_cyl g dγ| ≤ ‖Dφ‖_∞ ‖L‖ · ‖ ‖g(x_N)‖_H ‖_{L²(γ)}` (in `ℝ≥0∞`). -/
theorem r021_mixed_level (c : BoundedCoefficients lower upper) (N₀ : ℕ)
    (φ : FourierPlane N₀ → ℝ) (hφ : ContDiff ℝ 1 φ) (Bφ Bφ' : ℝ)
    (hφb : ∀ x, ‖φ x‖ ≤ Bφ) (hφ'b : ∀ x, ‖fderiv ℝ φ x‖ ≤ Bφ')
    {N : ℕ} (g : actualCMHead c N → actualCMHead c N) (hg : GaussianL2CylindricalCore c N g) :
    Integrable (fun z => φ (fun i => z (modeIndex N₀ i)) * cylDiv c N g z)
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) ∧
    ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * cylDiv c N g z
        ∂(NlsGge.Measure.fullWeightSequenceGaussian c.val)| ≤
      ENNReal.ofReal (Bφ' * ‖headCoordCLM c N₀‖) *
        eLpNorm (fun z => ‖cylField c N g z‖) 2
          (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  set M := max N₀ N with hM
  have h0M : N₀ ≤ M := le_max_left _ _
  have hNM : N ≤ M := le_max_right _ _
  set Lc := headCoordCLM c N₀ with hLc
  set P := levelProj c N₀ M with hP
  set Λ : actualCMHead c M →L[ℝ] FourierPlane N₀ := Lc.comp P with hΛ
  set ψ : actualCMHead c M → ℝ := fun x => φ (Λ x) with hψ
  set G := liftField c hNM g with hG
  have hGC : ContDiff ℝ 2 G := r021_core_contDiff (r021_lift_core c hNM g hg)
  have hGL : MemLp G 2 (finiteStdGaussian (actualCMHead c M)) :=
    r021_core_memLp (r021_lift_core c hNM g hg)
  have hGD : MemLp (finiteGaussianDivergence G) 2 (finiteStdGaussian (actualCMHead c M)) :=
    r021_core_memLp_div (r021_lift_core c hNM g hg)
  have hG1 : ContDiff ℝ 1 G := hGC.of_le (by norm_num)
  have hgC : ContDiff ℝ 2 g := r021_core_contDiff hg
  have hgd : Differentiable ℝ g := hgC.differentiable (by norm_num)
  have hBφ' : 0 ≤ Bφ' := (norm_nonneg _).trans (hφ'b 0)
  have hK : 0 ≤ Bφ' * ‖Lc‖ := mul_nonneg hBφ' (ContinuousLinearMap.opNorm_nonneg Lc)
  have hΛn : ‖Λ‖ ≤ ‖Lc‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg Lc) (fun u => ?_)
    calc ‖Λ u‖ = ‖Lc (P u)‖ := rfl
      _ ≤ ‖Lc‖ * ‖P u‖ := Lc.le_opNorm _
      _ ≤ ‖Lc‖ * ‖u‖ := mul_le_mul_of_nonneg_left (norm_levelProj_apply_le c h0M u)
          (ContinuousLinearMap.opNorm_nonneg Lc)
  -- the test function on the level-M head
  have hψcd : ContDiff ℝ 1 ψ := hφ.comp Λ.contDiff
  have hψD : ∀ x, fderiv ℝ ψ x = (fderiv ℝ φ (Λ x)).comp Λ := fun x =>
    (((hφ.differentiable (by norm_num)) (Λ x)).hasFDerivAt.comp x Λ.hasFDerivAt).fderiv
  have hψb : ∀ x, ‖ψ x‖ ≤ Bφ := fun x => hφb _
  have hψ'b : ∀ x, ‖fderiv ℝ ψ x‖ ≤ Bφ' * ‖Lc‖ := by
    intro x
    rw [hψD]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hφ'b _) hΛn (norm_nonneg _) hBφ')
  -- the L² integration by parts on the level-M head
  obtain ⟨hi1, -, hEq⟩ := r021_ibp_L2 hGC hGL hGD hψcd Bφ (Bφ' * ‖Lc‖) hψb hψ'b
  -- pointwise identities
  have hΛhead : ∀ z, Λ (headPt c M z) = fun i => z (modeIndex N₀ i) := fun z => by
    change Lc (levelProj c N₀ M (headPt c M z)) = _
    rw [levelProj_headPt c h0M, hLc, headCoordCLM_headPt]
  have hdiv : ∀ z, finiteGaussianDivergence G (headPt c M z) = cylDiv c N g z := fun z =>
    cylDiv_lift c hNM g hgd z
  have hfld : ∀ z, ‖G (headPt c M z)‖ = ‖cylField c N g z‖ := fun z => by
    rw [← cylField_lift c hNM g z]; rfl
  have hfun : (fun z => φ (fun i => z (modeIndex N₀ i)) * cylDiv c N g z) =
      fun z => ψ (headPt c M z) * finiteGaussianDivergence G (headPt c M z) := by
    funext z
    rw [hdiv z]
    simp only [hψ]
    rw [hΛhead z]
  have hint : Integrable (fun z => ψ (headPt c M z) * finiteGaussianDivergence G (headPt c M z))
      γ := by
    have := hi1
    rw [← headPt_map c M] at this
    exact this.comp_measurable (measurable_headPt c M)
  have hcont1 : Continuous (fun v => ψ v * finiteGaussianDivergence G v) :=
    hψcd.continuous.mul (continuous_finiteGaussianDivergence hG1)
  have hcont2 : Continuous (fun v => fderiv ℝ ψ v (G v)) :=
    (hψcd.continuous_fderiv (by norm_num)).clm_apply hGC.continuous
  have e1 := integral_comp_headPt c M _ hcont1
  have e2 := integral_comp_headPt c M _ hcont2
  have hI : ∫ z, φ (fun i => z (modeIndex N₀ i)) * cylDiv c N g z ∂γ =
      ∫ z, fderiv ℝ ψ (headPt c M z) (G (headPt c M z)) ∂γ := by
    rw [hfun]
    exact e1.trans (hEq.trans e2.symm)
  have hmeas : AEStronglyMeasurable (fun z => ‖cylField c N g z‖) γ :=
    (r021_aesm_cylField c N g hgC.continuous).norm
  refine ⟨by rw [hfun]; exact hint, ?_⟩
  rw [hI]
  refine ofReal_abs_integral_le_mul_eLpNorm γ _ _ _ hK hmeas (fun z => ?_)
  calc |fderiv ℝ ψ (headPt c M z) (G (headPt c M z))|
      = ‖fderiv ℝ ψ (headPt c M z) (G (headPt c M z))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ ψ (headPt c M z)‖ * ‖G (headPt c M z)‖ := (fderiv ℝ ψ _).le_opNorm _
    _ ≤ (Bφ' * ‖Lc‖) * ‖G (headPt c M z)‖ :=
        mul_le_mul_of_nonneg_right (hψ'b _) (norm_nonneg _)
    _ = (Bφ' * ‖Lc‖) * ‖‖cylField c N g z‖‖ := by rw [hfld z, norm_norm]

end
end NlsGge.ThirdConsultation.R
