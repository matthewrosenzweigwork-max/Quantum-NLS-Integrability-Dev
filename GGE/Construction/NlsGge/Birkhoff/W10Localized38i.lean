import NlsGge.Birkhoff.W10Localized38h

/-! # W10: integrability of every integrand in `D:thm:localized`, and non-vacuity of the cutoff profile

Source: `paper/v2.tex` l.1635-1643. Conditional on `B`, `O`, `1/2 < s < 3/4`.

The theorem `W10_38` uses Lean's totalized integrals. This file proves that every integral that occurs there
is a genuine Bochner integral (the integrand is integrable), so no junk value `0` enters:

* `integrable_fN38`: `f_N ∈ L¹(γ_W)` (so the integrals `∫ f_N dγ_W = Z_N` are genuine);
* `integrable_locIntegrand38`: `F(𝓕⁻¹P_Nx) χ_R(𝓕⁻¹P_Nx) f_N(x) ∈ L¹(γ_W)`;
* `integrable_chiR_fN38`: the denominator integrand `χ_R(𝓕⁻¹P_Nx) f_N(x) ∈ L¹(γ_W)`;
* `integrable_F_chiR_muW38`: `F χ_R ∈ L¹(μ_W)`;
* `exists_cutoffProfile38`: a cutoff profile exists (`χ(t) = max 0 (min 1 (2 - t))`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.Ramer Filter Topology
open scoped ENNReal Real

/-- A cutoff profile exists: the piecewise linear `χ(t) = max 0 (min 1 (2 - t))`. -/
theorem exists_cutoffProfile38 : ∃ χ : ℝ → ℝ, CutoffProfile38 χ := by
  refine ⟨fun t => max 0 (min 1 (2 - t)), ?_, ?_, ?_, ?_, ?_⟩
  · exact (by fun_prop : Continuous (fun t : ℝ => max 0 (min 1 (2 - t)))).continuousOn
  · intro a _ b _ hab
    exact max_le_max le_rfl (min_le_min le_rfl (by linarith))
  · intro t _
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · intro t _ ht1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  · intro t ht
    rw [max_eq_left]
    exact le_trans (min_le_right _ _) (by linarith)

section Integrability

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

theorem integrable_fN38 (hs : (1 : ℝ) / 2 < s) (N : ℕ) :
    Integrable (fN38 c s N) (fullWeightedSequenceGaussian c s) := by
  have hmp := measurePreserving_coordE c s hs
  have h := (hmp.integrable_comp (integrable_fNseq38 c N).aestronglyMeasurable).2
    (integrable_fNseq38 c N)
  have e : (fN38 c s N) = fNseq38 c N ∘ coordE c s := funext (fN38_eq_fNseq c s N)
  rw [e]
  exact h

include B O in
theorem integrable_locIntegrand38 (hs : (1 : ℝ) / 2 < s) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) (N : ℕ) :
    Integrable (locIntegrand38 c χ R F N) (fullWeightedSequenceGaussian c s) := by
  obtain ⟨M, hM⟩ := hFb
  have hproj : Continuous (fun x : FullWeightedHilbert c s => projE38 c s N x) :=
    (projE38 c s N).continuous
  have hc1 : Continuous (fun x : FullWeightedHilbert c s =>
      F (physOfE38 c s (projE38 c s N x))) := hF.comp hproj
  have hc2 : Continuous (fun x : FullWeightedHilbert c s =>
      chiR38 χ R (physOfE38 c s (projE38 c s N x))) :=
    (continuous_chiR38_physOfE38 c s hχ hR).comp hproj
  refine Integrable.bdd_mul (c := M) (integrable_fN38 c hs N) (hc1.mul hc2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have h1 := hM (projE38 c s N x)
  have h2 := chiR38_mem_Icc hχ hR (physOfE38 c s (projE38 c s N x))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2.1]
  calc _ ≤ M * 1 := mul_le_mul h1 h2.2 h2.1 hM0
    _ = M := mul_one M

include B O in
theorem integrable_chiR_fN38 (hs : (1 : ℝ) / 2 < s) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (N : ℕ) :
    Integrable (fun x : FullWeightedHilbert c s =>
      chiR38 χ R (physOfE38 c s (projE38 c s N x)) * fN38 c s N x)
      (fullWeightedSequenceGaussian c s) := by
  have := B.integrable_locIntegrand38 O c hs hχ hR (fun _ => 1) continuous_const
    ⟨1, fun _ => by simp⟩ N
  unfold locIntegrand38 at this
  simpa only [one_mul] using this

include B O in
/-- `μ_W` is concentrated on `𝓕⁻¹ E_s` (so the junk values of `F` off `𝓕⁻¹E_s` are irrelevant). -/
theorem ae_mem_range_muW38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∀ᵐ u ∂(B.muW38 c.val), u ∈ Set.range (physOfE38 c s) := by
  obtain ⟨J, -, -, hmu⟩ := B.muW_measure_formula38 O c hs hs'
  rw [hmu]
  refine Measure.ae_smul_measure ?_ _
  rw [(measurableEmbedding_physFW06_38 c s).ae_map_iff]
  exact Filter.Eventually.of_forall fun x => ⟨x, rfl⟩

include B O in
theorem integrable_F_chiR_muW38 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) {χ : ℝ → ℝ} {R : ℝ}
    (hχ : CutoffProfile38 χ) (hR : 0 < R) (F : PhysicalL2 → ℝ)
    (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Integrable (fun u => F u * chiR38 χ R u) (B.muW38 c.val) := by
  obtain ⟨M, hM⟩ := hFb
  have hprob := B.isProbabilityMeasure_muW38 lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)
  have hcont : Continuous (fun y : ECarrier38 c s =>
      (fun u => F u * chiR38 χ R u) (physOfE38 c s y)) :=
    hF.mul (continuous_chiR38_physOfE38 c s hχ hR)
  have hm := B.aestronglyMeasurable_muW38 O c hs hs' (fun u => F u * chiR38 χ R u) hcont
  refine Integrable.of_bound hm M ?_
  filter_upwards [B.ae_mem_range_muW38 O c hs hs'] with u hu
  obtain ⟨y, rfl⟩ := hu
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have h2 := chiR38_mem_Icc hχ hR (physOfE38 c s y)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2.1]
  calc _ ≤ M * 1 := mul_le_mul (hM y) h2.2 h2.1 hM0
    _ = M := mul_one M

end BirkhoffInput38

end Integrability

end NlsGge.Birkhoff
end
