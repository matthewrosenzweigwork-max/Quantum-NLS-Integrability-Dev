import NlsGge.Ramer.CylindricalDivergence
import NlsGge.Ramer.FiniteDivergenceGrowth
import NlsGge.Ramer.CylinderSeparation
import NlsGge.Ramer.DivergenceIdentification

/-!
# Closability of the cylindrical divergence on the actual source law

See `CylindricalClosability.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot

variable {lower upper : ℝ}

/-! ### Generic `L¹ ≤ L²` bound in extended reals -/

theorem ofReal_abs_integral_le_mul_eLpNorm {α : Type*} {m : MeasurableSpace α}
    (μ : Measure α) [IsProbabilityMeasure μ] (f h : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hh : AEStronglyMeasurable h μ) (hfh : ∀ z, |f z| ≤ B * ‖h z‖) :
    ENNReal.ofReal |∫ z, f z ∂μ| ≤ ENNReal.ofReal B * eLpNorm h 2 μ := by
  calc ENNReal.ofReal |∫ z, f z ∂μ| = ‖∫ z, f z ∂μ‖ₑ := by
        rw [← Real.norm_eq_abs, ofReal_norm]
    _ ≤ ∫⁻ z, ‖f z‖ₑ ∂μ := enorm_integral_le_lintegral_enorm f
    _ ≤ ∫⁻ z, ENNReal.ofReal B * ‖h z‖ₑ ∂μ := by
        refine lintegral_mono fun z => ?_
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hB]
        exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hfh z)
    _ = ENNReal.ofReal B * ∫⁻ z, ‖h z‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal B * eLpNorm h 1 μ := by rw [eLpNorm_one_eq_lintegral_enorm hh]
    _ ≤ ENNReal.ofReal B * eLpNorm h 2 μ := by
        have h12 : eLpNorm h 1 μ ≤ eLpNorm h 2 μ :=
          eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
        exact mul_le_mul_right h12 _

/-! ### Norms of the level maps -/

theorem norm_levelIncl_apply (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (v : actualCMHead c N) : ‖levelIncl c h v‖ = ‖v‖ := rfl

theorem norm_levelProj_apply_le (c : BoundedCoefficients lower upper) {N M : ℕ} (h : N ≤ M)
    (u : actualCMHead c M) : ‖levelProj c N M u‖ ≤ ‖u‖ := by
  set w := levelProj c N M u with hw
  have h1 : ‖w‖ * ‖w‖ ≤ ‖u‖ * ‖w‖ := by
    calc ‖w‖ * ‖w‖ = ⟪w, w⟫ := (real_inner_self_eq_norm_mul_norm w).symm
      _ = ⟪u, levelIncl c h w⟫ := (inner_levelIncl c h u w).symm
      _ ≤ ‖u‖ * ‖levelIncl c h w‖ := real_inner_le_norm _ _
      _ = ‖u‖ * ‖w‖ := by rw [norm_levelIncl_apply]
  rcases (norm_nonneg w).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right h1 h0

/-- Head coordinates as a continuous linear map `V_N → FourierPlane N`. -/
def headCoordCLM (c : BoundedCoefficients lower upper) (N : ℕ) :
    actualCMHead c N →L[ℝ] FourierPlane N :=
  LinearMap.toContinuousLinearMap (actualCMHeadCoord c N : actualCMHead c N →ₗ[ℝ] FourierPlane N)

theorem headCoordCLM_headPt (c : BoundedCoefficients lower upper) (N : ℕ) (z : ℤ → ℂ) :
    headCoordCLM c N (headPt c N z) = fun i => z (modeIndex N i) := by
  change actualCMHeadCoord c N (headPt c N z) = _
  exact (actualCMHeadCoord c N).apply_symm_apply _

/-- Smoothness and polynomial growth are preserved by lifting a level-`N` field to level `M`. -/
theorem liftField_growth (c : BoundedCoefficients lower upper) {N M : ℕ} (hNM : N ≤ M)
    (g : actualCMHead c N → actualCMHead c N) (hg : ContDiff ℝ 1 g) (C : ℝ) (p : ℕ)
    (hgg : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ p)
    (hDg : ∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ p) :
    ContDiff ℝ 1 (liftField c hNM g) ∧ (∀ x, ‖liftField c hNM g x‖ ≤ C * (1 + ‖x‖) ^ p) ∧
      ∀ x, ‖fderiv ℝ (liftField c hNM g) x‖ ≤ C * (1 + ‖x‖) ^ p := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgg 0)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  refine ⟨(levelIncl c hNM).contDiff.comp (hg.comp (levelProj c N M).contDiff), fun x => ?_,
    fun x => ?_⟩
  · have : ‖liftField c hNM g x‖ = ‖g (levelProj c N M x)‖ := rfl
    rw [this]
    refine (hgg _).trans ?_
    have := norm_levelProj_apply_le c hNM x
    gcongr
  · have hGD : fderiv ℝ (liftField c hNM g) x =
        (levelIncl c hNM).comp ((fderiv ℝ g (levelProj c N M x)).comp (levelProj c N M)) := by
      have h1 := (hgd (levelProj c N M x)).hasFDerivAt.comp x (levelProj c N M).hasFDerivAt
      exact ((levelIncl c hNM).hasFDerivAt.comp x h1).fderiv
    rw [hGD]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
    have hQ := norm_levelProj_apply_le c hNM x
    have hQw := norm_levelProj_apply_le c hNM w
    calc ‖((levelIncl c hNM).comp ((fderiv ℝ g (levelProj c N M x)).comp
            (levelProj c N M))) w‖
        = ‖fderiv ℝ g (levelProj c N M x) (levelProj c N M w)‖ := rfl
      _ ≤ ‖fderiv ℝ g (levelProj c N M x)‖ * ‖levelProj c N M w‖ :=
          (fderiv ℝ g (levelProj c N M x)).le_opNorm _
      _ ≤ (C * (1 + ‖x‖) ^ p) * ‖w‖ := by
          refine mul_le_mul ((hDg _).trans ?_) hQw (norm_nonneg _) (by positivity)
          gcongr

theorem aestronglyMeasurable_cylDiv (c : BoundedCoefficients lower upper) {N : ℕ}
    (g : actualCMHead c N → actualCMHead c N) (hg : ContDiff ℝ 1 g) :
    AEStronglyMeasurable (cylDiv c N g) (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
  ((continuous_finiteGaussianDivergence hg).measurable.comp
    (measurable_headPt c N)).aestronglyMeasurable

/-! ### Mixed-level integration by parts -/

/-- For a `C¹` polynomially bounded level-`N` field `g` and a `C¹` bounded test function `φ` of
the level-`N₀` window with bounded derivative,
`φ(z_{window N₀}) · δ_cyl g` is integrable and
`|∫ φ δ_cyl g dγ| ≤ ‖Dφ‖_∞ ‖L‖ · ‖ ‖g(x_N)‖_H ‖_{L²(γ)}` (in `ℝ≥0∞`). -/
theorem integral_cylTest_mul_cylDiv_le (c : BoundedCoefficients lower upper) (N₀ : ℕ)
    (φ : FourierPlane N₀ → ℝ) (hφ : ContDiff ℝ 1 φ) (Bφ Bφ' : ℝ)
    (hφb : ∀ x, ‖φ x‖ ≤ Bφ) (hφ'b : ∀ x, ‖fderiv ℝ φ x‖ ≤ Bφ')
    {N : ℕ} (g : actualCMHead c N → actualCMHead c N) (hg : ContDiff ℝ 1 g) (C : ℝ) (p : ℕ)
    (hgg : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ p)
    (hDg : ∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ p) :
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
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgg 0)
  have hBφ' : 0 ≤ Bφ' := (norm_nonneg _).trans (hφ'b 0)
  have hK : 0 ≤ Bφ' * ‖Lc‖ := mul_nonneg hBφ' (ContinuousLinearMap.opNorm_nonneg Lc)
  have hΛn : ‖Λ‖ ≤ ‖Lc‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg Lc) (fun u => ?_)
    calc ‖Λ u‖ = ‖Lc (P u)‖ := rfl
      _ ≤ ‖Lc‖ * ‖P u‖ := Lc.le_opNorm _
      _ ≤ ‖Lc‖ * ‖u‖ := mul_le_mul_of_nonneg_left (norm_levelProj_apply_le c h0M u)
          (ContinuousLinearMap.opNorm_nonneg Lc)
  -- properties of the lifted field
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  obtain ⟨hGcd, hGg, hDG⟩ := liftField_growth c hNM g hg C p hgg hDg
  -- the test function
  have hψcd : ContDiff ℝ 1 ψ := hφ.comp Λ.contDiff
  have hψD : ∀ x, fderiv ℝ ψ x = (fderiv ℝ φ (Λ x)).comp Λ := fun x =>
    (((hφ.differentiable (by norm_num)) (Λ x)).hasFDerivAt.comp x Λ.hasFDerivAt).fderiv
  have hψb : ∀ x, ‖ψ x‖ ≤ Bφ := fun x => hφb _
  have hψ'b : ∀ x, ‖fderiv ℝ ψ x‖ ≤ Bφ' * ‖Lc‖ := by
    intro x
    rw [hψD]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hφ'b _) hΛn (norm_nonneg _) hBφ')
  obtain ⟨hi1, -, hEq⟩ := integral_mul_finiteGaussianDivergence_of_growth hGcd C p hGg hDG
    hψcd Bφ (Bφ' * ‖Lc‖) hψb hψ'b
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
    hψcd.continuous.mul (continuous_finiteGaussianDivergence hGcd)
  have hcont2 : Continuous (fun v => fderiv ℝ ψ v (G v)) :=
    (hψcd.continuous_fderiv (by norm_num)).clm_apply hGcd.continuous
  have e1 := integral_comp_headPt c M _ hcont1
  have e2 := integral_comp_headPt c M _ hcont2
  have hI : ∫ z, φ (fun i => z (modeIndex N₀ i)) * cylDiv c N g z ∂γ =
      ∫ z, fderiv ℝ ψ (headPt c M z) (G (headPt c M z)) ∂γ := by
    rw [hfun]
    exact e1.trans (hEq.trans e2.symm)
  have hmeas : AEStronglyMeasurable (fun z => ‖cylField c N g z‖) γ :=
    (hg.continuous.norm.measurable.comp (measurable_headPt c N)).aestronglyMeasurable
  refine ⟨by rw [hfun]; exact hint, ?_⟩
  rw [hI]
  refine ofReal_abs_integral_le_mul_eLpNorm γ _ _ _ hK hmeas (fun z => ?_)
  calc |fderiv ℝ ψ (headPt c M z) (G (headPt c M z))|
      = ‖fderiv ℝ ψ (headPt c M z) (G (headPt c M z))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ ψ (headPt c M z)‖ * ‖G (headPt c M z)‖ := (fderiv ℝ ψ _).le_opNorm _
    _ ≤ (Bφ' * ‖Lc‖) * ‖G (headPt c M z)‖ :=
        mul_le_mul_of_nonneg_right (hψ'b _) (norm_nonneg _)
    _ = (Bφ' * ‖Lc‖) * ‖‖cylField c N g z‖‖ := by rw [hfld z, norm_norm]

/-! ### Closability -/

/-- **Closability of the cylindrical divergence on the actual source law.**
If cylindrical fields `g k` of levels `N k` (`C¹`, polynomially bounded with derivative) have
`H`-valued fields tending to `0` in `L²(γ)` (in the sense `eLpNorm ‖g_k(x_{N_k})‖_H → 0`) and
their divergences tend in `L²(γ)` to `η`, then `η = 0` `γ`-a.e. -/
theorem cylDiv_closable {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    {N : ℕ → ℕ} (g : ∀ k, actualCMHead c (N k) → actualCMHead c (N k))
    (hg : ∀ k, ContDiff ℝ 1 (g k)) (C : ℕ → ℝ) (p : ℕ → ℕ)
    (hgg : ∀ k v, ‖g k v‖ ≤ C k * (1 + ‖v‖) ^ p k)
    (hDg : ∀ k v, ‖fderiv ℝ (g k) v‖ ≤ C k * (1 + ‖v‖) ^ p k)
    (η : (ℤ → ℂ) → ℝ) (hη : MemLp η 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hF : Tendsto (fun k => eLpNorm (fun z => ‖cylField c (N k) (g k) z‖) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0))
    (hδ : Tendsto (fun k => eLpNorm (fun z => cylDiv c (N k) (g k) z - η z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    η =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] 0 := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hηi : Integrable η γ := hη.integrable (by norm_num)
  refine ae_eq_zero_of_integral_cylinder_mul_eq_zero c η hηi (fun N₀ φ hφ hφc => ?_)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (mod_cast le_top)
  obtain ⟨Bφ, hBφ⟩ := hφ1.continuous.bounded_above_of_compact_support hφc
  obtain ⟨Bφ', hBφ'⟩ := (hφ1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0)
  have hBφ'0 : 0 ≤ Bφ' := (norm_nonneg _).trans (hBφ' 0)
  set K : ℝ := Bφ' * ‖headCoordCLM c N₀‖ with hK
  have hπm : Measurable (fun z : ℤ → ℂ => fun i => z (modeIndex N₀ i)) := measurable_windowProj N₀
  have hφπm : AEStronglyMeasurable (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i))) γ :=
    (hφ1.continuous.measurable.comp hπm).aestronglyMeasurable
  have hφηi : Integrable (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i)) * η z) γ :=
    hηi.bdd_mul hφπm (ae_of_all _ fun z => hBφ _)
  have hk : ∀ k, ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ| ≤
      ENNReal.ofReal Bφ * eLpNorm (fun z => cylDiv c (N k) (g k) z - η z) 2 γ +
        ENNReal.ofReal K * eLpNorm (fun z => ‖cylField c (N k) (g k) z‖) 2 γ := by
    intro k
    obtain ⟨hint, hbd⟩ := integral_cylTest_mul_cylDiv_le c N₀ φ hφ1 Bφ Bφ' hBφ hBφ' (g k)
      (hg k) (C k) (p k) (hgg k) (hDg k)
    have hcylm : AEStronglyMeasurable (fun z => cylDiv c (N k) (g k) z) γ :=
      aestronglyMeasurable_cylDiv c (g k) (hg k)
    have hi1 : Integrable (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i)) *
        (η z - cylDiv c (N k) (g k) z)) γ := by
      have e : (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i)) *
          (η z - cylDiv c (N k) (g k) z)) = fun z => φ (fun i => z (modeIndex N₀ i)) * η z -
            φ (fun i => z (modeIndex N₀ i)) * cylDiv c (N k) (g k) z := by
        funext z; ring
      rw [e]; exact hφηi.sub hint
    have hsplit : ∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ =
        ∫ z, φ (fun i => z (modeIndex N₀ i)) * (η z - cylDiv c (N k) (g k) z) ∂γ +
          ∫ z, φ (fun i => z (modeIndex N₀ i)) * cylDiv c (N k) (g k) z ∂γ := by
      rw [← integral_add hi1 hint]
      congr 1; funext z; ring
    have hb1 := ofReal_abs_integral_le_mul_eLpNorm γ
      (fun z => φ (fun i => z (modeIndex N₀ i)) * (η z - cylDiv c (N k) (g k) z))
      (fun z => cylDiv c (N k) (g k) z - η z) Bφ hBφ0 (hcylm.sub hη.aestronglyMeasurable)
      (fun z => by
        calc |φ (fun i => z (modeIndex N₀ i)) * (η z - cylDiv c (N k) (g k) z)|
            = |φ (fun i => z (modeIndex N₀ i))| * ‖cylDiv c (N k) (g k) z - η z‖ := by
              rw [abs_mul, Real.norm_eq_abs, ← abs_neg (cylDiv c (N k) (g k) z - η z), neg_sub]
          _ ≤ Bφ * ‖cylDiv c (N k) (g k) z - η z‖ :=
              mul_le_mul_of_nonneg_right (by simpa using hBφ _) (norm_nonneg _))
    calc ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ|
        ≤ ENNReal.ofReal (|∫ z, φ (fun i => z (modeIndex N₀ i)) *
              (η z - cylDiv c (N k) (g k) z) ∂γ| +
            |∫ z, φ (fun i => z (modeIndex N₀ i)) * cylDiv c (N k) (g k) z ∂γ|) := by
          rw [hsplit]; exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) *
              (η z - cylDiv c (N k) (g k) z) ∂γ| +
            ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * cylDiv c (N k) (g k) z ∂γ| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add hb1 hbd
  have hlim : Tendsto (fun k => ENNReal.ofReal Bφ *
        eLpNorm (fun z => cylDiv c (N k) (g k) z - η z) 2 γ +
      ENNReal.ofReal K * eLpNorm (fun z => ‖cylField c (N k) (g k) z‖) 2 γ) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul hδ (Or.inr (ENNReal.ofReal_ne_top (r := Bφ)))
    have h2 := ENNReal.Tendsto.const_mul hF (Or.inr (ENNReal.ofReal_ne_top (r := K)))
    simpa using h1.add h2
  have h0 : ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ| ≤ 0 :=
    ge_of_tendsto' hlim hk
  have := ENNReal.ofReal_eq_zero.1 (le_zero_iff.1 h0)
  exact abs_nonpos_iff.1 this

/-- **Uniqueness of the closure.** If two cylindrical approximating sequences (levels `N k`,
`N' k`) have `H`-valued fields approaching each other in `L²(γ)` and divergences tending in
`L²(γ)` to `η` and `η'` respectively, then `η = η'` almost everywhere. Proof: lift both to the
common level `max (N k) (N' k)` and apply `cylDiv_closable` to the difference. -/
theorem cylDiv_closure_unique {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    {N N' : ℕ → ℕ} (g : ∀ k, actualCMHead c (N k) → actualCMHead c (N k))
    (g' : ∀ k, actualCMHead c (N' k) → actualCMHead c (N' k))
    (hg : ∀ k, ContDiff ℝ 1 (g k)) (hg' : ∀ k, ContDiff ℝ 1 (g' k))
    (C C' : ℕ → ℝ) (p p' : ℕ → ℕ)
    (hgg : ∀ k v, ‖g k v‖ ≤ C k * (1 + ‖v‖) ^ p k)
    (hDg : ∀ k v, ‖fderiv ℝ (g k) v‖ ≤ C k * (1 + ‖v‖) ^ p k)
    (hgg' : ∀ k v, ‖g' k v‖ ≤ C' k * (1 + ‖v‖) ^ p' k)
    (hDg' : ∀ k v, ‖fderiv ℝ (g' k) v‖ ≤ C' k * (1 + ‖v‖) ^ p' k)
    (η η' : (ℤ → ℂ) → ℝ) (hη : MemLp η 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hη' : MemLp η' 2 (NlsGge.Measure.fullWeightSequenceGaussian c.val))
    (hFF : Tendsto (fun k => eLpNorm
      (fun z => ‖cylField c (N k) (g k) z - cylField c (N' k) (g' k) z‖) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0))
    (hδ : Tendsto (fun k => eLpNorm (fun z => cylDiv c (N k) (g k) z - η z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0))
    (hδ' : Tendsto (fun k => eLpNorm (fun z => cylDiv c (N' k) (g' k) z - η' z) 2
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)) atTop (𝓝 0)) :
    η =ᵐ[NlsGge.Measure.fullWeightSequenceGaussian c.val] η' := by
  set γ := NlsGge.Measure.fullWeightSequenceGaussian c.val with hγ
  have hN : ∀ k, N k ≤ max (N k) (N' k) := fun k => le_max_left _ _
  have hN' : ∀ k, N' k ≤ max (N k) (N' k) := fun k => le_max_right _ _
  set G : ∀ k, actualCMHead c (max (N k) (N' k)) → actualCMHead c (max (N k) (N' k)) :=
    fun k v => liftField c (hN k) (g k) v - liftField c (hN' k) (g' k) v with hG
  have hgr := fun k => liftField_growth c (hN k) (g k) (hg k) (C k) (p k) (hgg k) (hDg k)
  have hgr' := fun k => liftField_growth c (hN' k) (g' k) (hg' k) (C' k) (p' k) (hgg' k)
    (hDg' k)
  have hC : ∀ k, 0 ≤ C k := fun k => by simpa using (norm_nonneg (g k 0)).trans (hgg k 0)
  have hC' : ∀ k, 0 ≤ C' k := fun k => by simpa using (norm_nonneg (g' k 0)).trans (hgg' k 0)
  have hpow : ∀ (k : ℕ) (v : actualCMHead c (max (N k) (N' k))),
      (1 + ‖v‖) ^ p k ≤ (1 + ‖v‖) ^ (max (p k) (p' k)) ∧
        (1 + ‖v‖) ^ p' k ≤ (1 + ‖v‖) ^ (max (p k) (p' k)) := fun k v =>
    ⟨pow_le_pow_right₀ (by linarith [norm_nonneg v]) (le_max_left _ _),
      pow_le_pow_right₀ (by linarith [norm_nonneg v]) (le_max_right _ _)⟩
  have hGcd : ∀ k, ContDiff ℝ 1 (G k) := fun k => (hgr k).1.sub (hgr' k).1
  have hGg : ∀ k v, ‖G k v‖ ≤ (C k + C' k) * (1 + ‖v‖) ^ (max (p k) (p' k)) := by
    intro k v
    calc ‖G k v‖ ≤ ‖liftField c (hN k) (g k) v‖ + ‖liftField c (hN' k) (g' k) v‖ :=
          norm_sub_le _ _
      _ ≤ C k * (1 + ‖v‖) ^ p k + C' k * (1 + ‖v‖) ^ p' k :=
          add_le_add ((hgr k).2.1 v) ((hgr' k).2.1 v)
      _ ≤ C k * (1 + ‖v‖) ^ (max (p k) (p' k)) + C' k * (1 + ‖v‖) ^ (max (p k) (p' k)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hpow k v).1 (hC k))
            (mul_le_mul_of_nonneg_left (hpow k v).2 (hC' k))
      _ = _ := by ring
  have hDG : ∀ k v, ‖fderiv ℝ (G k) v‖ ≤ (C k + C' k) * (1 + ‖v‖) ^ (max (p k) (p' k)) := by
    intro k v
    have d1 : DifferentiableAt ℝ (liftField c (hN k) (g k)) v :=
      ((hgr k).1.differentiable (by norm_num)) v
    have d2 : DifferentiableAt ℝ (liftField c (hN' k) (g' k)) v :=
      ((hgr' k).1.differentiable (by norm_num)) v
    have : fderiv ℝ (G k) v = fderiv ℝ (liftField c (hN k) (g k)) v -
        fderiv ℝ (liftField c (hN' k) (g' k)) v := fderiv_fun_sub d1 d2
    rw [this]
    calc ‖fderiv ℝ (liftField c (hN k) (g k)) v - fderiv ℝ (liftField c (hN' k) (g' k)) v‖
        ≤ ‖fderiv ℝ (liftField c (hN k) (g k)) v‖ +
            ‖fderiv ℝ (liftField c (hN' k) (g' k)) v‖ := by
          rw [sub_eq_add_neg]
          exact (ContinuousLinearMap.opNorm_add_le _ _).trans
            (by rw [ContinuousLinearMap.opNorm_neg])
      _ ≤ C k * (1 + ‖v‖) ^ p k + C' k * (1 + ‖v‖) ^ p' k :=
          add_le_add ((hgr k).2.2 v) ((hgr' k).2.2 v)
      _ ≤ C k * (1 + ‖v‖) ^ (max (p k) (p' k)) + C' k * (1 + ‖v‖) ^ (max (p k) (p' k)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hpow k v).1 (hC k))
            (mul_le_mul_of_nonneg_left (hpow k v).2 (hC' k))
      _ = _ := by ring
  have hfield : ∀ k z, cylField c (max (N k) (N' k)) (G k) z =
      cylField c (N k) (g k) z - cylField c (N' k) (g' k) z := fun k z => by
    rw [← cylField_lift c (hN k) (g k) z, ← cylField_lift c (hN' k) (g' k) z]; rfl
  have hdiv : ∀ k z, cylDiv c (max (N k) (N' k)) (G k) z =
      cylDiv c (N k) (g k) z - cylDiv c (N' k) (g' k) z := fun k z => by
    rw [← cylDiv_lift c (hN k) (g k) ((hg k).differentiable (by norm_num)) z,
      ← cylDiv_lift c (hN' k) (g' k) ((hg' k).differentiable (by norm_num)) z]
    exact finiteGaussianDivergence_sub _ _ _
      (((hgr k).1.differentiable (by norm_num)) _) (((hgr' k).1.differentiable (by norm_num)) _)
  have hF : Tendsto (fun k => eLpNorm (fun z => ‖cylField c (max (N k) (N' k)) (G k) z‖) 2 γ)
      atTop (𝓝 0) := by
    refine hFF.congr (fun k => ?_)
    congr 1
    funext z
    rw [hfield]
  have hηη : MemLp (fun z => η z - η' z) 2 γ := hη.sub hη'
  have hδδ : Tendsto (fun k => eLpNorm (fun z => cylDiv c (max (N k) (N' k)) (G k) z -
      (η z - η' z)) 2 γ) atTop (𝓝 0) := by
    have hs : Tendsto (fun k => eLpNorm (fun z => cylDiv c (N k) (g k) z - η z) 2 γ +
        eLpNorm (fun z => cylDiv c (N' k) (g' k) z - η' z) 2 γ) atTop (𝓝 0) := by
      simpa using hδ.add hδ'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun k => bot_le)
      (fun k => ?_)
    have := eLpNorm_sub_le (μ := γ) (f := fun z => cylDiv c (N k) (g k) z - η z)
      (g := fun z => cylDiv c (N' k) (g' k) z - η' z) (p := 2) (by norm_num)
    have e : (fun z => cylDiv c (max (N k) (N' k)) (G k) z - (η z - η' z)) =
        (fun z => cylDiv c (N k) (g k) z - η z) - (fun z => cylDiv c (N' k) (g' k) z - η' z) := by
      funext z
      simp only [Pi.sub_apply, hdiv]
      ring
    rw [e]
    exact this
  have key := cylDiv_closable c (N := fun k => max (N k) (N' k)) G hGcd
    (fun k => C k + C' k) (fun k => max (p k) (p' k)) hGg hDG (fun z => η z - η' z) hηη hF hδδ
  filter_upwards [key] with z hz
  have : η z - η' z = 0 := hz
  linarith

end NlsGge.Ramer
