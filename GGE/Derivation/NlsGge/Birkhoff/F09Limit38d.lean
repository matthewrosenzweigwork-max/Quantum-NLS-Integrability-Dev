import NlsGge.Birkhoff.F09Limit38c

/-! # NEW-F09, file 4: the `h²` tail on `E_s` and the localized difference (v2 l.1774-1779)

`B`-free. Source: `paper/v2.tex` l.1774-1779.

* `tail_Es38`: transfer of NEW-F08 (`F:eq:unnormtail`) to `E_s`:
  `∫_{‖P_N x‖_{h²} > R} f_N dγ_W ≤ C e^{-η R²}`, `C, η` depending only on `c₋, c₊`;
* `unloc_sub_loc38`: for `R > 0` and `F` bounded by `M`:
  `|∫ F(𝓕⁻¹P_N x) f_N dγ_W - ∫ F χ_R(𝓕⁻¹P_N x) f_N dγ_W| ≤ M ∫_{‖P_N x‖_{h²} > R} f_N dγ_W`
  (this proves `0 ≤ 1 - χ_R ≤ 1_{‖u‖_{H²} > R}` on the finite sections, for `R > 0`);
* `double_limit38`: the abstract `N → ∞` then `R → ∞` argument.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

theorem double_limit38 (a : ℕ → ℝ) (b : ℝ → ℕ → ℝ) (m e : ℝ → ℝ) (L : ℝ)
    (h1 : ∀ R, 0 < R → Tendsto (b R) atTop (𝓝 (m R)))
    (h2 : ∀ R, 0 < R → ∀ N, |a N - b R N| ≤ e R)
    (h3 : Tendsto e atTop (𝓝 0)) (h4 : Tendsto m atTop (𝓝 L)) : Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have e3 : ∀ᶠ R in atTop, e R < ε / 3 := by
    have := (Metric.tendsto_nhds.1 h3 (ε / 3) (by linarith))
    filter_upwards [this] with R hR
    rw [Real.dist_eq, sub_zero] at hR
    exact lt_of_le_of_lt (le_abs_self _) hR
  have e4 : ∀ᶠ R in atTop, dist (m R) L < ε / 3 := Metric.tendsto_nhds.1 h4 (ε / 3) (by linarith)
  obtain ⟨R, ⟨hR1, hR2⟩, hR3⟩ := ((e3.and e4).and (eventually_gt_atTop (0 : ℝ))).exists
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (h1 R hR3) (ε / 3) (by linarith)
  refine ⟨N0, fun N hN => ?_⟩
  have := hN0 N hN
  have h5 := h2 R hR3 N
  rw [Real.dist_eq] at this hR2 ⊢
  calc |a N - L| = |(a N - b R N) + (b R N - m R) + (m R - L)| := by ring_nf
    _ ≤ |a N - b R N| + |b R N - m R| + |m R - L| := abs_add_three _ _ _
    _ < ε := by linarith

section Tail

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- The tail set `{x ∈ E_s : ‖P_N x‖_{h²} > R}`. -/
def tailSet38 (N : ℕ) (R : ℝ) : Set (FullWeightedHilbert c s) :=
  {x | R < ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (projE38 c s N x)‖}

theorem isOpen_tailSet38 (N : ℕ) (R : ℝ) : IsOpen (tailSet38 c s N R) :=
  isOpen_lt continuous_const
    ((continuous_eToSob38 c s _).comp (projE38 c s N).continuous).norm

theorem norm_eToSob2_projE38_eq (N : ℕ) (x : FullWeightedHilbert c s) :
    ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (projE38 c s N x)‖ =
      planeH2Norm38 N (planeOfSeq38 N (coordE c s x)) := by
  unfold planeH2Norm38
  rw [← norm_sq_eToSob2_projE38 c s N x, Real.sqrt_sq (norm_nonneg _)]

/-- **NEW-F08 transferred to `E_s`.** -/
theorem tail_Es38 (lo up : ℝ) (hl : 0 < lo) (hlu : lo ≤ up) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ (c : BoundedCoefficients lo up) (s : ℝ), (1 : ℝ) / 2 < s →
      ∀ (N : ℕ) (R : ℝ), 0 ≤ R →
        Integrable ((tailSet38 c s N R).indicator (fN38 c s N)) (fullWeightedSequenceGaussian c s) ∧
        ∫ x, (tailSet38 c s N R).indicator (fN38 c s N) x ∂(fullWeightedSequenceGaussian c s) ≤
          C * Real.exp (-(η * R ^ 2)) := by
  obtain ⟨η, C, hη, hC, hmom⟩ := exponentialH2MomentTail38 lo up hl hlu
  refine ⟨η, C, hη, hC, fun c s hs N R hR => ⟨?_, ?_⟩⟩
  · exact (BirkhoffInput38.integrable_fN38 c hs N).indicator (isOpen_tailSet38 c s N R).measurableSet
  · have hb := ((hmom c N).2 R hR).2
    have hset : MeasurableSet {z : FourierPlane N | R < planeH2Norm38 N z} :=
      (isOpen_lt continuous_const
        (Real.continuous_sqrt.comp (continuous_planeH2NormSq38 N))).measurableSet
    have hfc : Measurable (fFourier38 c N) := by
      unfold fFourier38
      have := continuous_fullEnergy38 c N
      fun_prop
    have e1 : (fun x => (tailSet38 c s N R).indicator (fN38 c s N) x) = fun x =>
        ({z : FourierPlane N | R < planeH2Norm38 N z}.indicator (fFourier38 c N))
          (planeOfSeq38 N (coordE c s x)) := by
      funext x
      have hmem : x ∈ tailSet38 c s N R ↔
          planeOfSeq38 N (coordE c s x) ∈ {z : FourierPlane N | R < planeH2Norm38 N z} := by
        simp only [tailSet38, Set.mem_ofPred_eq, norm_eToSob2_projE38_eq]
      by_cases h : x ∈ tailSet38 c s N R
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.1 h), fN38_eq_fNseq]; rfl
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.2 h'))]
    rw [e1, integral_transfer38 c s hs N _ (hfc.indicator hset).aestronglyMeasurable,
      integral_indicator hset]
    exact hb

end Tail

section Loc

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

theorem unloc_sub_loc38 (hs : (1 : ℝ) / 2 < s) {χ : ℝ → ℝ} {R : ℝ} (hχ : CutoffProfile38 χ)
    (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y))) (M : ℝ)
    (hM : ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (N : ℕ) :
    |(∫ x, F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x ∂(fullWeightedSequenceGaussian c s)) -
        ∫ x, locIntegrand38 c χ R F N x ∂(fullWeightedSequenceGaussian c s)| ≤
      M * ∫ x, (tailSet38 c s N R).indicator (fN38 c s N) x ∂(fullWeightedSequenceGaussian c s) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hcont : Continuous (fun x : FullWeightedHilbert c s => F (physOfE38 c s (projE38 c s N x))) :=
    hF.comp (projE38 c s N).continuous
  have hI1 : Integrable (fun x : FullWeightedHilbert c s => F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x)
      (fullWeightedSequenceGaussian c s) :=
    Integrable.bdd_mul (c := M) (BirkhoffInput38.integrable_fN38 c hs N) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM _)
  have hI2 : Integrable (fun x : FullWeightedHilbert c s => locIntegrand38 c χ R F N x)
      (fullWeightedSequenceGaussian c s) := by
    have hproj := (projE38 c s N).continuous
    have hc2 : Continuous (fun x : FullWeightedHilbert c s =>
        chiR38 χ R (physOfE38 c s (projE38 c s N x))) :=
      (continuous_chiR38_physOfE38 c s hχ hR).comp hproj
    refine Integrable.bdd_mul (c := M) (BirkhoffInput38.integrable_fN38 c hs N) (hcont.mul hc2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h2 := chiR38_mem_Icc hχ hR (physOfE38 c s (projE38 c s N x))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2.1]
    calc _ ≤ M * 1 := mul_le_mul (hM _) h2.2 h2.1 hM0
      _ = M := mul_one M
  have hIt : Integrable (fun x : FullWeightedHilbert c s => M * (tailSet38 c s N R).indicator (fN38 c s N) x)
      (fullWeightedSequenceGaussian c s) :=
    ((BirkhoffInput38.integrable_fN38 c hs N).indicator (isOpen_tailSet38 c s N R).measurableSet).const_mul M
  rw [← integral_sub hI1 hI2, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x => abs_nonneg _) hIt (Filter.Eventually.of_forall fun x => ?_))
  have hf0 := (fN38_pos c s N x).le
  have hchi := chiR38_mem_Icc hχ hR (physOfE38 c s (projE38 c s N x))
  have hFx := hM (projE38 c s N x)
  simp only [locIntegrand38]
  have e : F (physOfE38 c s (projE38 c s N x)) * fN38 c s N x -
      F (physOfE38 c s (projE38 c s N x)) * chiR38 χ R (physOfE38 c s (projE38 c s N x)) *
        fN38 c s N x = F (physOfE38 c s (projE38 c s N x)) *
        (1 - chiR38 χ R (physOfE38 c s (projE38 c s N x))) * fN38 c s N x := by ring
  rw [e]
  by_cases h : x ∈ tailSet38 c s N R
  · rw [Set.indicator_of_mem h, abs_mul, abs_mul, abs_of_nonneg hf0,
      abs_of_nonneg (by linarith [hchi.2] : 0 ≤ 1 - chiR38 χ R (physOfE38 c s (projE38 c s N x)))]
    have h1 : 1 - chiR38 χ R (physOfE38 c s (projE38 c s N x)) ≤ 1 := by linarith [hchi.1]
    have h2 : 0 ≤ 1 - chiR38 χ R (physOfE38 c s (projE38 c s N x)) := by linarith [hchi.2]
    calc |F (physOfE38 c s (projE38 c s N x))| *
          (1 - chiR38 χ R (physOfE38 c s (projE38 c s N x))) * fN38 c s N x
        ≤ M * 1 * fN38 c s N x := by
          refine mul_le_mul_of_nonneg_right ?_ hf0
          exact mul_le_mul hFx h1 h2 hM0
      _ = M * fN38 c s N x := by ring
  · have hle : ‖eToSob38 c s (((1 + 1 : ℕ)) : ℝ) (projE38 c s N x)‖ ≤ R := not_lt.1 h
    have h1 : chiR38 χ R (physOfE38 c s (projE38 c s N x)) = 1 := by
      rw [chiR38_physOfE38]
      exact hχ.eq_one _ (div_nonneg (norm_nonneg _) hR.le) ((div_le_one hR).2 hle)
    rw [h1, Set.indicator_of_notMem h]
    simp

end Loc

end NlsGge.Birkhoff
end
