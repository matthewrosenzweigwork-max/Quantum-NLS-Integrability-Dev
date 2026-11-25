import NlsGge.Birkhoff.F09Limit38e
import NlsGge.Birkhoff.S04Moments38

/-! # NEW-F09, file 6: `inf_N Z_N > 0`, the normalized exponential `H²` moment (B-free given the bound)

Source: `paper/v2.tex` l.1786-1787 ("Convergence to a positive normalizer, together with positivity of every
finite `Z_N(W)`, gives `inf_N Z_N(W) > 0`. Divide `F:eq:unnormexp` by this infimum to obtain `F:eq:expH2`").

* `exists_pos_lower_of_tendsto38`: a positive sequence with a positive limit is bounded below by a positive constant;
* `integrable_nuWN38`: integrability against `ν_{W,N}` from integrability of `G f_N^F` against `γ_N`;
* `expMoment_nuWN38`: given `δ ≤ Z_N` for all `N`, `sup_N ∫ e^{η ‖u‖²_{H²}} dν_{W,N} < ∞`, with `η = c₋/128`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

theorem exists_pos_lower_of_tendsto38 (z : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hz : ∀ n, 0 < z n)
    (h : Tendsto z atTop (𝓝 L)) : ∃ δ : ℝ, 0 < δ ∧ ∀ n, δ ≤ z n := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (h.eventually (lt_mem_nhds (by linarith : L / 2 < L)))
  have key : ∀ k : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ n < k, δ ≤ z n := by
    intro k
    induction k with
    | zero => exact ⟨1, one_pos, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨δ, hδ, hk⟩ := ih
      refine ⟨min δ (z k), lt_min hδ (hz k), fun n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with h1 | h1
      · exact (min_le_left _ _).trans (hk n h1)
      · subst h1; exact min_le_right _ _
  obtain ⟨δ, hδ, hk⟩ := key N0
  refine ⟨min δ (L / 2), lt_min hδ (by linarith), fun n => ?_⟩
  by_cases hn : n < N0
  · exact (min_le_left _ _).trans (hk n hn)
  · exact (min_le_right _ _).trans (hN0 n (not_lt.1 hn)).le

section Law

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper)

theorem integrable_nuWN38 (N : ℕ) (G : PhysicalL2 → ℝ)
    (h : Integrable (fun z => G (planeL2 N z) * fFourier38 c N z) (fullWeightFourierGaussian N c.val)) :
    Integrable G (nuWN38 c N) := by
  have hlo := c.property.1
  have hden := fullWeightFourierGaussian_density lower upper c.val hlo (coef_bound38 c)
    (coef_upper38 c) N
  have hρ : Measurable (fun z : FourierPlane N => ENNReal.ofReal (Real.exp (-fullEnergy38 c N z))) :=
    (continuous_fullEnergy38 c N).neg.rexp.measurable.ennreal_ofReal
  have hpdfm : Measurable (fun z : FourierPlane N => ENNReal.ofReal
      (∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi) *
        Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2))) :=
    (measurable_fullWeightFourierGaussianPDF N c.val).ennreal_ofReal
  have hpdf0 : ∀ z : FourierPlane N, 0 ≤ ∏ i, (fullWeightRate c.val (modeIndex N i) / Real.pi) *
      Real.exp (-fullWeightRate c.val (modeIndex N i) * ‖z i‖ ^ 2) := fun z =>
    Finset.prod_nonneg fun i _ => mul_nonneg
      (div_nonneg (fullWeightRate_pos38 c _).le Real.pi_pos.le) (Real.exp_pos _).le
  unfold nuWN38
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  rw [(measurableEmbedding_planeL2_38 N).integrable_map_iff]
  rw [integrable_withDensity_iff_integrable_smul' hρ
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [hden, integrable_withDensity_iff_integrable_smul' hpdfm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at h
  have h2 := h.const_mul (freeNormalizer38 c N)
  refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.comp, ENNReal.toReal_ofReal (hpdf0 z), ENNReal.toReal_ofReal (Real.exp_pos _).le,
    smul_eq_mul]
  rw [planeGaussPDF_mul_fFourier38 c N z]
  unfold freeNormalizer38
  ring

theorem physH38_physOfE38 (s : ℝ) (y : ECarrier38 c s) :
    physH38 2 (physOfE38 c s y) = eToSob38 c s (((1 + 1 : ℕ)) : ℝ) y := by
  have hmem : fourierSeq38 (physOfE38 c s y) ∈ seqSobolev38 (((1 + 1 : ℕ)) : ℝ) := by
    rw [fourierSeq38_physOfE38]
    exact seqE38_subset_seqSobolev38 c s _ (eCoe38_mem c s y)
  rw [show physH38 2 (physOfE38 c s y) = physH38 (1 + 1) (physOfE38 c s y) from rfl,
    physH38_of_mem (1 + 1) _ hmem]
  apply carrierExt38
  funext n
  rw [carrierCoe38_mk, carrierCoe_eToSob38, fourierSeq38_physOfE38]

include c in
theorem norm_sq_physH38_planeL2 (N : ℕ) (z : FourierPlane N) :
    ‖physH38 2 (planeL2 N z)‖ ^ 2 = planeH2NormSq38 N z := by
  rw [planeL2_eq_physOfE_projE_sectionE38 c 1 N z, physH38_physOfE38,
    norm_sq_eToSob2_projE38, planeOfSeq38_coordE_sectionE38]

include c in
theorem fourierSeq_planeL2_mem38 (N : ℕ) (z : FourierPlane N) :
    fourierSeq38 (planeL2 N z) ∈ seqSobolev38 (((2 : ℕ)) : ℝ) := by
  rw [planeL2_eq_physOfE_projE_sectionE38 c 1 N z, fourierSeq38_physOfE38]
  exact seqE38_subset_seqSobolev38 c 1 _ (eCoe38_mem c 1 _)

/-- **Normalized exponential `H²` moment (`F:eq:expH2`), given a positive lower bound for the normalizers.**
`η = c₋/128` and the constant `C = C₀/δ` (`C₀` from NEW-F08, `δ ≤ Z_N`). The law `ν_{W,N}` is concentrated on
`H²` (so the cleaned `physH38` is the genuine `H²` norm), and the integrand is integrable. -/
theorem expMoment_nuWN38 (hlu : lower ≤ upper) (δ : ℝ) (hδ : 0 < δ)
    (hZ : ∀ N, δ ≤ relativePartition38 c N) :
    ∃ η C : ℝ, 0 < η ∧ ∀ N : ℕ,
      (∀ᵐ u ∂(nuWN38 c N), fourierSeq38 u ∈ seqSobolev38 (((2 : ℕ)) : ℝ)) ∧
      Integrable (fun u => Real.exp (η * ‖physH38 2 u‖ ^ 2)) (nuWN38 c N) ∧
      ∫ u, Real.exp (η * ‖physH38 2 u‖ ^ 2) ∂(nuWN38 c N) ≤ C := by
  obtain ⟨η, C, hη, hC, hmom⟩ := exponentialH2Moment38 lower upper (coef_lower38 c) hlu
  refine ⟨η, C / δ, hη, fun N => ⟨?_, ?_, ?_⟩⟩
  · unfold nuWN38
    refine Measure.ae_smul_measure ?_ _
    rw [(measurableEmbedding_planeL2_38 N).ae_map_iff]
    exact Filter.Eventually.of_forall fun z => fourierSeq_planeL2_mem38 c N z
  all_goals
    have hGeq : (fun z : FourierPlane N => Real.exp (η * ‖physH38 2 (planeL2 N z)‖ ^ 2)) =
        fun z => Real.exp (η * planeH2NormSq38 N z) :=
      funext fun z => by rw [norm_sq_physH38_planeL2 c N z]
    have hGm : Measurable (fun z : FourierPlane N => Real.exp (η * ‖physH38 2 (planeL2 N z)‖ ^ 2)) := by
      rw [hGeq]; exact (continuous_planeH2NormSq38 N |>.const_smul η |>.rexp).measurable
  · refine integrable_nuWN38 c N _ ?_
    have := (hmom c N).1
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    rw [norm_sq_physH38_planeL2 c N z]
    ring
  · rw [integral_nuWN38_gauss c N _ hGm.aestronglyMeasurable]
    have hZp : 0 < relativePartition38 c N := lt_of_lt_of_le hδ (hZ N)
    have h1 : ∫ z, Real.exp (η * ‖physH38 2 (planeL2 N z)‖ ^ 2) * fFourier38 c N z
        ∂(fullWeightFourierGaussian N c.val) ≤ C := by
      refine le_trans (le_of_eq ?_) (hmom c N).2
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      beta_reduce
      rw [norm_sq_physH38_planeL2 c N z]
      ring
    have h0 : 0 ≤ ∫ z, Real.exp (η * ‖physH38 2 (planeL2 N z)‖ ^ 2) * fFourier38 c N z
        ∂(fullWeightFourierGaussian N c.val) :=
      integral_nonneg fun z => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    calc _ ≤ (1 / δ) * C := by
          refine mul_le_mul ?_ h1 h0 (by positivity)
          exact one_div_le_one_div_of_le hδ (hZ N)
      _ = C / δ := by ring

end Law

end NlsGge.Birkhoff
end
