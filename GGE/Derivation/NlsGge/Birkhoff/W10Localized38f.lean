import NlsGge.Birkhoff.W10Localized38e
import NlsGge.Birkhoff.W06Jacobian38b

/-! # W10b, file 2 (W10.06): dominated convergence and the identification of the limit

Source: `paper/v2.tex` l.1657-1663. Conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`,
for `1/2 < s < 3/4`.

* `tendsto_localIntegral38`: `∫ F χ_R(𝓕⁻¹P_N x) f_N dγ_W → ∫ g(T⁻¹z) dγ_W(z)`, with
  `g = F χ_R e^{-R_W}` on `E_s` (W10a for `N` large, pointwise convergence `tendsto_PsiN38` at every
  `z ∈ E_s`, bound `2 sup|F|`, dominated convergence on the probability space `(E_s, γ_W)`).
* `integral_gLoc_comp_symm38`: `∫ g(T⁻¹ z) dγ_W(z) = Z_W ∫ F χ_R dμ_W`, from W06 (`(T⁻¹)_#γ_W = J_T γ_W`,
  `μ_W = Z_W⁻¹ (𝓕⁻¹)_#(e^{-R_W} J_T γ_W)`).
* `W10_localized_Es38`: the first assertion of `D:thm:localized`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.Ramer Filter Topology
open scoped ENNReal Real

/-- The limiting integrand `F χ_R e^{-R_W}` on `E_s` (v2: `F(𝓕⁻¹T⁻¹z) χ_R(𝓕⁻¹T⁻¹z) e^{-R_W(𝓕⁻¹T⁻¹z)}`,
here as a function of `x = T⁻¹z`). -/
def gLoc38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) {s : ℝ} (χ : ℝ → ℝ) (R : ℝ)
    (F : PhysicalL2 → ℝ) (y : FullWeightedHilbert c s) : ℝ :=
  F (physOfE38 c s y) * chiR38 χ R (physOfE38 c s y) *
    Real.exp (-(remainder38 c.val (physOfE38 c s y)))

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
theorem continuous_gLoc38 (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ} (hχ : CutoffProfile38 χ)
    (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) :
    Continuous (gLoc38 c (s := s) χ R F) :=
  (hF.mul (continuous_chiR38_physOfE38 c s hχ hR)).mul
    (B.continuous_remainder_physOfE38 c s O hs').neg.rexp

include B O in
theorem abs_gLoc38_le (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ} (hχ : CutoffProfile38 χ)
    (hR : 0 < R) (F : PhysicalL2 → ℝ) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (y : ECarrier38 c s) :
    |gLoc38 c (s := s) χ R F y| ≤ M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hrem : 0 ≤ remainder38 c.val (physOfE38 c s y) :=
    (B.finiteGap_approximation_PM_W05_38 c s O hs' y).2.2.2
  have h1 : Real.exp (-(remainder38 c.val (physOfE38 c s y))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by linarith)
  have hc := chiR38_mem_Icc hχ hR (physOfE38 c s y)
  unfold gLoc38
  rw [abs_mul, abs_mul, abs_of_nonneg hc.1, abs_of_pos (Real.exp_pos _)]
  calc _ ≤ M * 1 * 1 :=
        mul_le_mul (mul_le_mul (hM y) hc.2 hc.1 hM0) h1 (Real.exp_pos _).le (by positivity)
    _ = M := by ring

include B O in
/-- **W10.06 (dominated convergence).** `∫ F χ_R(𝓕⁻¹P_N x) f_N dγ_W → ∫ g(T⁻¹z) dγ_W(z)`. -/
theorem tendsto_localIntegral38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ x, locIntegrand38 c χ R F N x ∂(fullWeightedSequenceGaussian c s))
      atTop (𝓝 (∫ z, gLoc38 c (s := s) χ R F ((B.weightedHomeoE38 O c s).symm z)
        ∂(fullWeightedSequenceGaussian c s))) := by
  have hs1 : s ≤ 1 := by linarith
  obtain ⟨N₀, hN₀⟩ := B.W10a_localChange38 O c hs hs' hχ hR F hF M hM
  have hmeasF : ∀ N ≥ N₀, Measurable (fun z : FullWeightedHilbert c s =>
      B.PsiN38 O c hs1 χ R F N (headPt c N (coordE c s z))) := fun N hN =>
    (hN₀ N hN).2.2.1.comp ((measurable_headPt c N).comp (measurable_coordE c s))
  have hlim : Tendsto (fun N : ℕ => ∫ z, B.PsiN38 O c hs1 χ R F N (headPt c N (coordE c s z))
      ∂(fullWeightedSequenceGaussian c s)) atTop
      (𝓝 (∫ z, gLoc38 c (s := s) χ R F ((B.weightedHomeoE38 O c s).symm z)
        ∂(fullWeightedSequenceGaussian c s))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 2 * M) ?_ ?_
      (integrable_const _) (Filter.Eventually.of_forall fun z => ?_)
    · filter_upwards [eventually_ge_atTop N₀] with N hN
      exact (hmeasF N hN).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop N₀] with N hN
      refine Filter.Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs]
      exact (hN₀ N hN).2.2.2.1 _
    · have := B.tendsto_PsiN38 O c hs' hs1 hχ hR F hF M hM z
      exact this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop N₀] with N hN
  exact ((hN₀ N hN).2.2.2.2).symm

include B O in
/-- **`μ_W` through `f_W γ_W` (W06).** With `J_T` the Ramer density of `(T⁻¹)_#γ_W = J_T γ_W`
and `f_W = e^{-R_W} J_T`: for every `G`, `∫ G dμ_W = Z_W⁻¹ ∫ f_W(x) G(𝓕⁻¹x) dγ_W(x)`. -/
theorem muW_integral_formula38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ J : FullWeightedHilbert c s → ℝ,
      (fullWeightedSequenceGaussian c s).map (TW06_38 B O c s).symm =
        (fullWeightedSequenceGaussian c s).withDensity (fun x => ENNReal.ofReal (J x)) ∧
      (∀ x, 0 < J x) ∧ Integrable J (fullWeightedSequenceGaussian c s) ∧
      ∀ G : PhysicalL2 → ℝ, ∫ u, G u ∂(B.muW38 c.val) =
        (1 / B.ZW38 c.val) * ∫ x, (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x) *
          G (physOfE38 c s x) ∂(fullWeightedSequenceGaussian c s) := by
  have hs1 : s ≤ 1 := by linarith
  obtain ⟨δK, -, hmap, hpos, hint, -⟩ := ramer_W06_38 B O c s hs hs1
  set γ := fullWeightedSequenceGaussian c s with hγ
  set J := JW06_38 c s hs (B.KW06_38 O c hs1) δK with hJ
  refine ⟨J, hmap, hpos, hint, fun G => ?_⟩
  have hZ := (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1
  have hJm : AEMeasurable (fun x => ENNReal.ofReal (J x)) γ := hint.aemeasurable.ennreal_ofReal
  have hmu := muW38_eq_map_W06 B c s O hs hs'.le J hmap hJm
  have hrc : Continuous (fun x : FullWeightedHilbert c s =>
      remainder38 c.val (physOfE38 c s x)) := B.continuous_remainder_physOfE38 c s O hs'
  set f : FullWeightedHilbert c s → ℝ :=
    fun x => Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x with hf
  have hfm : AEMeasurable (fun x => ENNReal.ofReal (f x)) γ :=
    (((hrc.neg.rexp).aestronglyMeasurable.mul hint.aestronglyMeasurable)).aemeasurable.ennreal_ofReal
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (Real.exp_pos _).le (hpos x).le
  rw [hmu, integral_smul_measure, ENNReal.toReal_ofReal (one_div_pos.2 hZ).le, smul_eq_mul]
  congr 1
  rw [(measurableEmbedding_physFW06_38 c s).integral_map]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hfm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hf0 x), smul_eq_mul]
  rfl

include B O in
/-- **Identification of the limit.** `∫ g(T⁻¹z) dγ_W(z) = Z_W ∫ F χ_R dμ_W`
(`(T⁻¹)_#γ_W = J_T γ_W` and `μ_W = Z_W⁻¹ (𝓕⁻¹)_#(e^{-R_W} J_T γ_W)`, W06). -/
theorem integral_gLoc_comp_symm38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) :
    ∫ z, gLoc38 c (s := s) χ R F ((B.weightedHomeoE38 O c s).symm z)
        ∂(fullWeightedSequenceGaussian c s) =
      B.ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂(B.muW38 c.val) := by
  obtain ⟨J, hmap, hpos, hint, hmu⟩ := B.muW_integral_formula38 O c hs hs'
  set γ := fullWeightedSequenceGaussian c s with hγ
  have hZ := (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1
  have hg : Continuous (fun y : FullWeightedHilbert c s => gLoc38 c (s := s) χ R F y) :=
    B.continuous_gLoc38 O c hs' hχ hR F hF
  have hL1 : ∫ z, gLoc38 c (s := s) χ R F ((B.weightedHomeoE38 O c s).symm z) ∂γ =
      ∫ x, (Real.exp (-(remainder38 c.val (physOfE38 c s x))) * J x) *
        (F (physOfE38 c s x) * chiR38 χ R (physOfE38 c s x)) ∂γ := by
    have e1 : ∫ z, gLoc38 c (s := s) χ R F ((B.weightedHomeoE38 O c s).symm z) ∂γ =
        ∫ y : FullWeightedHilbert c s, gLoc38 c (s := s) χ R F y
          ∂(γ.map (TW06_38 B O c s).symm) :=
      (integral_map (TW06_38 B O c s).symm.continuous.measurable.aemeasurable
        hg.aestronglyMeasurable).symm
    rw [e1, hmap, integral_withDensity_eq_integral_toReal_smul₀ hint.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal (hpos x).le, smul_eq_mul, gLoc38]
    ring
  rw [hL1, hmu (fun u => F u * chiR38 χ R u)]
  field_simp

include B O in
/-- **`D:thm:localized`, first assertion (`E_s`-continuous `F`).** For `1/2 < s < 3/4`, every cutoff profile
`χ`, every `R > 0` and every `F` that is bounded and continuous on `𝓕⁻¹E_s` (topology of `E_s`),
`∫ F(𝓕⁻¹P_N x) χ_R(𝓕⁻¹P_N x) f_N(x) dγ_W(x) → Z_W ∫ F χ_R dμ_W`. -/
theorem W10_localized_Es38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ x, F (physOfE38 c s (projE38 c s N x)) *
        chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
        ∂(fullWeightedSequenceGaussian c s))
      atTop (𝓝 (B.ZW38 c.val * ∫ u, F u * chiR38 χ R u ∂(B.muW38 c.val))) := by
  obtain ⟨M, hM⟩ := hFb
  rw [← B.integral_gLoc_comp_symm38 O c hs hs' hχ hR F hF]
  exact B.tendsto_localIntegral38 O c hs hs' hχ hR F hF M hM

end BirkhoffInput38

end NlsGge.Birkhoff
end
