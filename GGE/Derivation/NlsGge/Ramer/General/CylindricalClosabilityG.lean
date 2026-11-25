import NlsGge.Ramer.General.CylindricalDivergenceG
import NlsGge.Ramer.General.CylinderSeparationG
import NlsGge.Ramer.FiniteDivergenceGrowth
import NlsGge.Ramer.DivergenceIdentification

/-!
# Closability of the cylindrical divergence on the actual source law

Generalization (GA4) of `NlsGge/Ramer/CylindricalClosability.lean` to a `RamerSetting S`.
S-specific declarations live in `NlsGge.Ramer.General.RamerSetting` (dot notation `S.cylDiv_closable`);
the generic `L¹ ≤ L²` helper lives in `NlsGge.Ramer.Gen`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace ENNReal

namespace NlsGge.Ramer.Gen

open NlsGge.Pilot

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

end NlsGge.Ramer.Gen

namespace NlsGge.Ramer.General.RamerSetting

open NlsGge.Pilot NlsGge.Ramer

variable (S : NlsGge.Ramer.General.RamerSetting)

/-! ### Norms of the level maps -/

theorem norm_levelIncl_apply {N M : ℕ} (h : N ≤ M)
    (v : S.head N) : ‖S.levelIncl h v‖ = ‖v‖ := rfl

theorem norm_levelProj_apply_le {N M : ℕ} (h : N ≤ M)
    (u : S.head M) : ‖S.levelProj N M u‖ ≤ ‖u‖ := by
  set w := S.levelProj N M u with hw
  have h1 : ‖w‖ * ‖w‖ ≤ ‖u‖ * ‖w‖ := by
    calc ‖w‖ * ‖w‖ = ⟪w, w⟫ := (real_inner_self_eq_norm_mul_norm w).symm
      _ = ⟪u, S.levelIncl h w⟫ := (S.inner_levelIncl h u w).symm
      _ ≤ ‖u‖ * ‖S.levelIncl h w‖ := real_inner_le_norm _ _
      _ = ‖u‖ * ‖w‖ := by rw [norm_levelIncl_apply]
  rcases (norm_nonneg w).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · exact le_of_mul_le_mul_right h1 h0

/-- Head coordinates as a continuous linear map `V_N → FourierPlane N`. -/
def headCoordCLM (N : ℕ) :
    S.head N →L[ℝ] FourierPlane N :=
  LinearMap.toContinuousLinearMap (S.headCoord N : S.head N →ₗ[ℝ] FourierPlane N)

theorem headCoordCLM_headPt (N : ℕ) (z : ℤ → ℂ) :
    S.headCoordCLM N (S.headPt N z) = fun i => z (modeIndex N i) := by
  change S.headCoord N (S.headPt N z) = _
  exact (S.headCoord N).apply_symm_apply _

/-- Smoothness and polynomial growth are preserved by lifting a level-`N` field to level `M`. -/
theorem liftField_growth {N M : ℕ} (hNM : N ≤ M)
    (g : S.head N → S.head N) (hg : ContDiff ℝ 1 g) (C : ℝ) (p : ℕ)
    (hgg : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ p)
    (hDg : ∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ p) :
    ContDiff ℝ 1 (S.liftField hNM g) ∧ (∀ x, ‖S.liftField hNM g x‖ ≤ C * (1 + ‖x‖) ^ p) ∧
      ∀ x, ‖fderiv ℝ (S.liftField hNM g) x‖ ≤ C * (1 + ‖x‖) ^ p := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgg 0)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  refine ⟨(S.levelIncl hNM).contDiff.comp (hg.comp (S.levelProj N M).contDiff), fun x => ?_,
    fun x => ?_⟩
  · have : ‖S.liftField hNM g x‖ = ‖g (S.levelProj N M x)‖ := rfl
    rw [this]
    refine (hgg _).trans ?_
    have := S.norm_levelProj_apply_le hNM x
    gcongr
  · have hGD : fderiv ℝ (S.liftField hNM g) x =
        (S.levelIncl hNM).comp ((fderiv ℝ g (S.levelProj N M x)).comp (S.levelProj N M)) := by
      have h1 := (hgd (S.levelProj N M x)).hasFDerivAt.comp x (S.levelProj N M).hasFDerivAt
      exact ((S.levelIncl hNM).hasFDerivAt.comp x h1).fderiv
    rw [hGD]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
    have hQ := S.norm_levelProj_apply_le hNM x
    have hQw := S.norm_levelProj_apply_le hNM w
    calc ‖((S.levelIncl hNM).comp ((fderiv ℝ g (S.levelProj N M x)).comp
            (S.levelProj N M))) w‖
        = ‖fderiv ℝ g (S.levelProj N M x) (S.levelProj N M w)‖ := rfl
      _ ≤ ‖fderiv ℝ g (S.levelProj N M x)‖ * ‖S.levelProj N M w‖ :=
          (fderiv ℝ g (S.levelProj N M x)).le_opNorm _
      _ ≤ (C * (1 + ‖x‖) ^ p) * ‖w‖ := by
          refine mul_le_mul ((hDg _).trans ?_) hQw (norm_nonneg _) (by positivity)
          gcongr

theorem aestronglyMeasurable_cylDiv {N : ℕ}
    (g : S.head N → S.head N) (hg : ContDiff ℝ 1 g) :
    AEStronglyMeasurable (S.cylDiv N g) (S.γ) :=
  ((continuous_finiteGaussianDivergence hg).measurable.comp
    (S.measurable_headPt N)).aestronglyMeasurable

/-! ### Mixed-level integration by parts -/

/-- For a `C¹` polynomially bounded level-`N` field `g` and a `C¹` bounded test function `φ` of
the level-`N₀` window with bounded derivative,
`φ(z_{window N₀}) · δ_cyl g` is integrable and
`|∫ φ δ_cyl g dγ| ≤ ‖Dφ‖_∞ ‖L‖ · ‖ ‖g(x_N)‖_H ‖_{L²(γ)}` (in `ℝ≥0∞`). -/
theorem integral_cylTest_mul_cylDiv_le (N₀ : ℕ)
    (φ : FourierPlane N₀ → ℝ) (hφ : ContDiff ℝ 1 φ) (Bφ Bφ' : ℝ)
    (hφb : ∀ x, ‖φ x‖ ≤ Bφ) (hφ'b : ∀ x, ‖fderiv ℝ φ x‖ ≤ Bφ')
    {N : ℕ} (g : S.head N → S.head N) (hg : ContDiff ℝ 1 g) (C : ℝ) (p : ℕ)
    (hgg : ∀ v, ‖g v‖ ≤ C * (1 + ‖v‖) ^ p)
    (hDg : ∀ v, ‖fderiv ℝ g v‖ ≤ C * (1 + ‖v‖) ^ p) :
    Integrable (fun z => φ (fun i => z (modeIndex N₀ i)) * S.cylDiv N g z)
        (S.γ) ∧
    ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * S.cylDiv N g z
        ∂(S.γ)| ≤
      ENNReal.ofReal (Bφ' * ‖S.headCoordCLM N₀‖) *
        eLpNorm (fun z => ‖S.cylField N g z‖) 2
          (S.γ) := by
  set γ := S.γ with hγ
  set M := max N₀ N with hM
  have h0M : N₀ ≤ M := le_max_left _ _
  have hNM : N ≤ M := le_max_right _ _
  set Lc := S.headCoordCLM N₀ with hLc
  set P := S.levelProj N₀ M with hP
  set Λ : S.head M →L[ℝ] FourierPlane N₀ := Lc.comp P with hΛ
  set ψ : S.head M → ℝ := fun x => φ (Λ x) with hψ
  set G := S.liftField hNM g with hG
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgg 0)
  have hBφ' : 0 ≤ Bφ' := (norm_nonneg _).trans (hφ'b 0)
  have hK : 0 ≤ Bφ' * ‖Lc‖ := mul_nonneg hBφ' (ContinuousLinearMap.opNorm_nonneg Lc)
  have hΛn : ‖Λ‖ ≤ ‖Lc‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg Lc) (fun u => ?_)
    calc ‖Λ u‖ = ‖Lc (P u)‖ := rfl
      _ ≤ ‖Lc‖ * ‖P u‖ := Lc.le_opNorm _
      _ ≤ ‖Lc‖ * ‖u‖ := mul_le_mul_of_nonneg_left (S.norm_levelProj_apply_le h0M u)
          (ContinuousLinearMap.opNorm_nonneg Lc)
  -- properties of the lifted field
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  obtain ⟨hGcd, hGg, hDG⟩ := S.liftField_growth hNM g hg C p hgg hDg
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
  have hΛhead : ∀ z, Λ (S.headPt M z) = fun i => z (modeIndex N₀ i) := fun z => by
    change Lc (S.levelProj N₀ M (S.headPt M z)) = _
    rw [S.levelProj_headPt h0M, hLc, headCoordCLM_headPt]
  have hdiv : ∀ z, finiteGaussianDivergence G (S.headPt M z) = S.cylDiv N g z := fun z =>
    S.cylDiv_lift hNM g hgd z
  have hfld : ∀ z, ‖G (S.headPt M z)‖ = ‖S.cylField N g z‖ := fun z => by
    rw [← S.cylField_lift hNM g z]; rfl
  have hfun : (fun z => φ (fun i => z (modeIndex N₀ i)) * S.cylDiv N g z) =
      fun z => ψ (S.headPt M z) * finiteGaussianDivergence G (S.headPt M z) := by
    funext z
    rw [hdiv z]
    simp only [hψ]
    rw [hΛhead z]
  have hint : Integrable (fun z => ψ (S.headPt M z) * finiteGaussianDivergence G (S.headPt M z))
      γ := by
    have := hi1
    rw [← S.headPt_map M] at this
    exact this.comp_measurable (S.measurable_headPt M)
  have hcont1 : Continuous (fun v => ψ v * finiteGaussianDivergence G v) :=
    hψcd.continuous.mul (continuous_finiteGaussianDivergence hGcd)
  have hcont2 : Continuous (fun v => fderiv ℝ ψ v (G v)) :=
    (hψcd.continuous_fderiv (by norm_num)).clm_apply hGcd.continuous
  have e1 := S.integral_comp_headPt M _ hcont1
  have e2 := S.integral_comp_headPt M _ hcont2
  have hI : ∫ z, φ (fun i => z (modeIndex N₀ i)) * S.cylDiv N g z ∂γ =
      ∫ z, fderiv ℝ ψ (S.headPt M z) (G (S.headPt M z)) ∂γ := by
    rw [hfun]
    exact e1.trans (hEq.trans e2.symm)
  have hmeas : AEStronglyMeasurable (fun z => ‖S.cylField N g z‖) γ :=
    (hg.continuous.norm.measurable.comp (S.measurable_headPt N)).aestronglyMeasurable
  refine ⟨by rw [hfun]; exact hint, ?_⟩
  rw [hI]
  refine NlsGge.Ramer.Gen.ofReal_abs_integral_le_mul_eLpNorm γ _ _ _ hK hmeas (fun z => ?_)
  calc |fderiv ℝ ψ (S.headPt M z) (G (S.headPt M z))|
      = ‖fderiv ℝ ψ (S.headPt M z) (G (S.headPt M z))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ ψ (S.headPt M z)‖ * ‖G (S.headPt M z)‖ := (fderiv ℝ ψ _).le_opNorm _
    _ ≤ (Bφ' * ‖Lc‖) * ‖G (S.headPt M z)‖ :=
        mul_le_mul_of_nonneg_right (hψ'b _) (norm_nonneg _)
    _ = (Bφ' * ‖Lc‖) * ‖‖S.cylField N g z‖‖ := by rw [hfld z, norm_norm]

/-! ### Closability -/

/-- **Closability of the cylindrical divergence on the actual source law.**
If cylindrical fields `g k` of levels `N k` (`C¹`, polynomially bounded with derivative) have
`H`-valued fields tending to `0` in `L²(γ)` (in the sense `eLpNorm ‖g_k(x_{N_k})‖_H → 0`) and
their divergences tend in `L²(γ)` to `η`, then `η = 0` `γ`-a.e. -/
theorem cylDiv_closable {N : ℕ → ℕ} (g : ∀ k, S.head (N k) → S.head (N k))
    (hg : ∀ k, ContDiff ℝ 1 (g k)) (C : ℕ → ℝ) (p : ℕ → ℕ)
    (hgg : ∀ k v, ‖g k v‖ ≤ C k * (1 + ‖v‖) ^ p k)
    (hDg : ∀ k v, ‖fderiv ℝ (g k) v‖ ≤ C k * (1 + ‖v‖) ^ p k)
    (η : (ℤ → ℂ) → ℝ) (hη : MemLp η 2 (S.γ))
    (hF : Tendsto (fun k => eLpNorm (fun z => ‖S.cylField (N k) (g k) z‖) 2
      (S.γ)) atTop (𝓝 0))
    (hδ : Tendsto (fun k => eLpNorm (fun z => S.cylDiv (N k) (g k) z - η z) 2
      (S.γ)) atTop (𝓝 0)) :
    η =ᵐ[S.γ] 0 := by
  set γ := S.γ with hγ
  have hηi : Integrable η γ := hη.integrable (by norm_num)
  refine NlsGge.Ramer.Gen.ae_eq_zero_of_integral_cylinder_mul_eq_zero S η hηi (fun N₀ φ hφ hφc => ?_)
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (mod_cast le_top)
  obtain ⟨Bφ, hBφ⟩ := hφ1.continuous.bounded_above_of_compact_support hφc
  obtain ⟨Bφ', hBφ'⟩ := (hφ1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0)
  have hBφ'0 : 0 ≤ Bφ' := (norm_nonneg _).trans (hBφ' 0)
  set K : ℝ := Bφ' * ‖S.headCoordCLM N₀‖ with hK
  have hπm : Measurable (fun z : ℤ → ℂ => fun i => z (modeIndex N₀ i)) := NlsGge.Ramer.Gen.measurable_windowProj N₀
  have hφπm : AEStronglyMeasurable (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i))) γ :=
    (hφ1.continuous.measurable.comp hπm).aestronglyMeasurable
  have hφηi : Integrable (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i)) * η z) γ :=
    hηi.bdd_mul hφπm (ae_of_all _ fun z => hBφ _)
  have hk : ∀ k, ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ| ≤
      ENNReal.ofReal Bφ * eLpNorm (fun z => S.cylDiv (N k) (g k) z - η z) 2 γ +
        ENNReal.ofReal K * eLpNorm (fun z => ‖S.cylField (N k) (g k) z‖) 2 γ := by
    intro k
    obtain ⟨hint, hbd⟩ := S.integral_cylTest_mul_cylDiv_le N₀ φ hφ1 Bφ Bφ' hBφ hBφ' (g k)
      (hg k) (C k) (p k) (hgg k) (hDg k)
    have hcylm : AEStronglyMeasurable (fun z => S.cylDiv (N k) (g k) z) γ :=
      S.aestronglyMeasurable_cylDiv (g k) (hg k)
    have hi1 : Integrable (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i)) *
        (η z - S.cylDiv (N k) (g k) z)) γ := by
      have e : (fun z : ℤ → ℂ => φ (fun i => z (modeIndex N₀ i)) *
          (η z - S.cylDiv (N k) (g k) z)) = fun z => φ (fun i => z (modeIndex N₀ i)) * η z -
            φ (fun i => z (modeIndex N₀ i)) * S.cylDiv (N k) (g k) z := by
        funext z; ring
      rw [e]; exact hφηi.sub hint
    have hsplit : ∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ =
        ∫ z, φ (fun i => z (modeIndex N₀ i)) * (η z - S.cylDiv (N k) (g k) z) ∂γ +
          ∫ z, φ (fun i => z (modeIndex N₀ i)) * S.cylDiv (N k) (g k) z ∂γ := by
      rw [← integral_add hi1 hint]
      congr 1; funext z; ring
    have hb1 := NlsGge.Ramer.Gen.ofReal_abs_integral_le_mul_eLpNorm γ
      (fun z => φ (fun i => z (modeIndex N₀ i)) * (η z - S.cylDiv (N k) (g k) z))
      (fun z => S.cylDiv (N k) (g k) z - η z) Bφ hBφ0 (hcylm.sub hη.aestronglyMeasurable)
      (fun z => by
        calc |φ (fun i => z (modeIndex N₀ i)) * (η z - S.cylDiv (N k) (g k) z)|
            = |φ (fun i => z (modeIndex N₀ i))| * ‖S.cylDiv (N k) (g k) z - η z‖ := by
              rw [abs_mul, Real.norm_eq_abs, ← abs_neg (S.cylDiv (N k) (g k) z - η z), neg_sub]
          _ ≤ Bφ * ‖S.cylDiv (N k) (g k) z - η z‖ :=
              mul_le_mul_of_nonneg_right (by simpa using hBφ _) (norm_nonneg _))
    calc ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * η z ∂γ|
        ≤ ENNReal.ofReal (|∫ z, φ (fun i => z (modeIndex N₀ i)) *
              (η z - S.cylDiv (N k) (g k) z) ∂γ| +
            |∫ z, φ (fun i => z (modeIndex N₀ i)) * S.cylDiv (N k) (g k) z ∂γ|) := by
          rw [hsplit]; exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) *
              (η z - S.cylDiv (N k) (g k) z) ∂γ| +
            ENNReal.ofReal |∫ z, φ (fun i => z (modeIndex N₀ i)) * S.cylDiv (N k) (g k) z ∂γ| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add hb1 hbd
  have hlim : Tendsto (fun k => ENNReal.ofReal Bφ *
        eLpNorm (fun z => S.cylDiv (N k) (g k) z - η z) 2 γ +
      ENNReal.ofReal K * eLpNorm (fun z => ‖S.cylField (N k) (g k) z‖) 2 γ) atTop (𝓝 0) := by
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
theorem cylDiv_closure_unique     {N N' : ℕ → ℕ} (g : ∀ k, S.head (N k) → S.head (N k))
    (g' : ∀ k, S.head (N' k) → S.head (N' k))
    (hg : ∀ k, ContDiff ℝ 1 (g k)) (hg' : ∀ k, ContDiff ℝ 1 (g' k))
    (C C' : ℕ → ℝ) (p p' : ℕ → ℕ)
    (hgg : ∀ k v, ‖g k v‖ ≤ C k * (1 + ‖v‖) ^ p k)
    (hDg : ∀ k v, ‖fderiv ℝ (g k) v‖ ≤ C k * (1 + ‖v‖) ^ p k)
    (hgg' : ∀ k v, ‖g' k v‖ ≤ C' k * (1 + ‖v‖) ^ p' k)
    (hDg' : ∀ k v, ‖fderiv ℝ (g' k) v‖ ≤ C' k * (1 + ‖v‖) ^ p' k)
    (η η' : (ℤ → ℂ) → ℝ) (hη : MemLp η 2 (S.γ))
    (hη' : MemLp η' 2 (S.γ))
    (hFF : Tendsto (fun k => eLpNorm
      (fun z => ‖S.cylField (N k) (g k) z - S.cylField (N' k) (g' k) z‖) 2
      (S.γ)) atTop (𝓝 0))
    (hδ : Tendsto (fun k => eLpNorm (fun z => S.cylDiv (N k) (g k) z - η z) 2
      (S.γ)) atTop (𝓝 0))
    (hδ' : Tendsto (fun k => eLpNorm (fun z => S.cylDiv (N' k) (g' k) z - η' z) 2
      (S.γ)) atTop (𝓝 0)) :
    η =ᵐ[S.γ] η' := by
  set γ := S.γ with hγ
  have hN : ∀ k, N k ≤ max (N k) (N' k) := fun k => le_max_left _ _
  have hN' : ∀ k, N' k ≤ max (N k) (N' k) := fun k => le_max_right _ _
  set G : ∀ k, S.head (max (N k) (N' k)) → S.head (max (N k) (N' k)) :=
    fun k v => S.liftField (hN k) (g k) v - S.liftField (hN' k) (g' k) v with hG
  have hgr := fun k => S.liftField_growth (hN k) (g k) (hg k) (C k) (p k) (hgg k) (hDg k)
  have hgr' := fun k => S.liftField_growth (hN' k) (g' k) (hg' k) (C' k) (p' k) (hgg' k)
    (hDg' k)
  have hC : ∀ k, 0 ≤ C k := fun k => by simpa using (norm_nonneg (g k 0)).trans (hgg k 0)
  have hC' : ∀ k, 0 ≤ C' k := fun k => by simpa using (norm_nonneg (g' k 0)).trans (hgg' k 0)
  have hpow : ∀ (k : ℕ) (v : S.head (max (N k) (N' k))),
      (1 + ‖v‖) ^ p k ≤ (1 + ‖v‖) ^ (max (p k) (p' k)) ∧
        (1 + ‖v‖) ^ p' k ≤ (1 + ‖v‖) ^ (max (p k) (p' k)) := fun k v =>
    ⟨pow_le_pow_right₀ (by linarith [norm_nonneg v]) (le_max_left _ _),
      pow_le_pow_right₀ (by linarith [norm_nonneg v]) (le_max_right _ _)⟩
  have hGcd : ∀ k, ContDiff ℝ 1 (G k) := fun k => (hgr k).1.sub (hgr' k).1
  have hGg : ∀ k v, ‖G k v‖ ≤ (C k + C' k) * (1 + ‖v‖) ^ (max (p k) (p' k)) := by
    intro k v
    calc ‖G k v‖ ≤ ‖S.liftField (hN k) (g k) v‖ + ‖S.liftField (hN' k) (g' k) v‖ :=
          norm_sub_le _ _
      _ ≤ C k * (1 + ‖v‖) ^ p k + C' k * (1 + ‖v‖) ^ p' k :=
          add_le_add ((hgr k).2.1 v) ((hgr' k).2.1 v)
      _ ≤ C k * (1 + ‖v‖) ^ (max (p k) (p' k)) + C' k * (1 + ‖v‖) ^ (max (p k) (p' k)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hpow k v).1 (hC k))
            (mul_le_mul_of_nonneg_left (hpow k v).2 (hC' k))
      _ = _ := by ring
  have hDG : ∀ k v, ‖fderiv ℝ (G k) v‖ ≤ (C k + C' k) * (1 + ‖v‖) ^ (max (p k) (p' k)) := by
    intro k v
    have d1 : DifferentiableAt ℝ (S.liftField (hN k) (g k)) v :=
      ((hgr k).1.differentiable (by norm_num)) v
    have d2 : DifferentiableAt ℝ (S.liftField (hN' k) (g' k)) v :=
      ((hgr' k).1.differentiable (by norm_num)) v
    have : fderiv ℝ (G k) v = fderiv ℝ (S.liftField (hN k) (g k)) v -
        fderiv ℝ (S.liftField (hN' k) (g' k)) v := fderiv_fun_sub d1 d2
    rw [this]
    calc ‖fderiv ℝ (S.liftField (hN k) (g k)) v - fderiv ℝ (S.liftField (hN' k) (g' k)) v‖
        ≤ ‖fderiv ℝ (S.liftField (hN k) (g k)) v‖ +
            ‖fderiv ℝ (S.liftField (hN' k) (g' k)) v‖ := by
          rw [sub_eq_add_neg]
          exact (ContinuousLinearMap.opNorm_add_le _ _).trans
            (by rw [ContinuousLinearMap.opNorm_neg])
      _ ≤ C k * (1 + ‖v‖) ^ p k + C' k * (1 + ‖v‖) ^ p' k :=
          add_le_add ((hgr k).2.2 v) ((hgr' k).2.2 v)
      _ ≤ C k * (1 + ‖v‖) ^ (max (p k) (p' k)) + C' k * (1 + ‖v‖) ^ (max (p k) (p' k)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hpow k v).1 (hC k))
            (mul_le_mul_of_nonneg_left (hpow k v).2 (hC' k))
      _ = _ := by ring
  have hfield : ∀ k z, S.cylField (max (N k) (N' k)) (G k) z =
      S.cylField (N k) (g k) z - S.cylField (N' k) (g' k) z := fun k z => by
    rw [← S.cylField_lift (hN k) (g k) z, ← S.cylField_lift (hN' k) (g' k) z]; rfl
  have hdiv : ∀ k z, S.cylDiv (max (N k) (N' k)) (G k) z =
      S.cylDiv (N k) (g k) z - S.cylDiv (N' k) (g' k) z := fun k z => by
    rw [← S.cylDiv_lift (hN k) (g k) ((hg k).differentiable (by norm_num)) z,
      ← S.cylDiv_lift (hN' k) (g' k) ((hg' k).differentiable (by norm_num)) z]
    exact finiteGaussianDivergence_sub _ _ _
      (((hgr k).1.differentiable (by norm_num)) _) (((hgr' k).1.differentiable (by norm_num)) _)
  have hF : Tendsto (fun k => eLpNorm (fun z => ‖S.cylField (max (N k) (N' k)) (G k) z‖) 2 γ)
      atTop (𝓝 0) := by
    refine hFF.congr (fun k => ?_)
    congr 1
    funext z
    rw [hfield]
  have hηη : MemLp (fun z => η z - η' z) 2 γ := hη.sub hη'
  have hδδ : Tendsto (fun k => eLpNorm (fun z => S.cylDiv (max (N k) (N' k)) (G k) z -
      (η z - η' z)) 2 γ) atTop (𝓝 0) := by
    have hs : Tendsto (fun k => eLpNorm (fun z => S.cylDiv (N k) (g k) z - η z) 2 γ +
        eLpNorm (fun z => S.cylDiv (N' k) (g' k) z - η' z) 2 γ) atTop (𝓝 0) := by
      simpa using hδ.add hδ'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun k => bot_le)
      (fun k => ?_)
    have := eLpNorm_sub_le (μ := γ) (f := fun z => S.cylDiv (N k) (g k) z - η z)
      (g := fun z => S.cylDiv (N' k) (g' k) z - η' z) (p := 2) (by norm_num)
    have e : (fun z => S.cylDiv (max (N k) (N' k)) (G k) z - (η z - η' z)) =
        (fun z => S.cylDiv (N k) (g k) z - η z) - (fun z => S.cylDiv (N' k) (g' k) z - η' z) := by
      funext z
      simp only [Pi.sub_apply, hdiv]
      ring
    rw [e]
    exact this
  have key := S.cylDiv_closable (N := fun k => max (N k) (N' k)) G hGcd
    (fun k => C k + C' k) (fun k => max (p k) (p' k)) hGg hDG (fun z => η z - η' z) hηη hF hδδ
  filter_upwards [key] with z hz
  have : η z - η' z = 0 := hz
  linarith

end NlsGge.Ramer.General.RamerSetting
