import NlsGge.Birkhoff.W11Equivalence38b

/-! # W11 (`D:thm:equivalence`), part c: the weight data and `L¹ ⇒ weak convergence` (W11.02)

Conditional on `B : BirkhoffInput38`, `O : OneSmoothingInput38 B`, `1/2 < s < 3/4`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open scoped ENNReal Real

/-- The facts about a limit density `f` (a version of `f_W`) that the equivalence proof consumes: all of
them are *proved* (not assumed) for `f = fW06_38 ... δK` below (`exists_weight_W11`, `weight_W11`). -/
structure W11Weight38 (B : BirkhoffInput38) {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (s : ℝ) (f : FullWeightedHilbert c s → ℝ) : Prop where
  integrable : Integrable f (fullWeightedSequenceGaussian c s)
  nonneg : ∀ᵐ x ∂(fullWeightedSequenceGaussian c s), 0 ≤ f x
  integral_eq : ∫ x, f x ∂(fullWeightedSequenceGaussian c s) = B.ZW38 c.val
  inMeasure : TendstoInMeasure (fullWeightedSequenceGaussian c s) (fun N x => fN38 c s N x) atTop f
  muW : ∀ G : PhysicalL2 → ℝ, ∫ u, G u ∂(B.muW38 c.val) =
    (1 / B.ZW38 c.val) * ∫ x, f x * G (physOfE38 c s x) ∂(fullWeightedSequenceGaussian c s)

namespace W11Weight38

variable {B : BirkhoffInput38} {lower upper : ℝ} {c : BoundedCoefficients lower upper} {s : ℝ}
  {f g : FullWeightedHilbert c s → ℝ}

theorem congr (h : W11Weight38 B c s f) (hfg : f =ᵐ[fullWeightedSequenceGaussian c s] g) :
    W11Weight38 B c s g where
  integrable := h.integrable.congr hfg
  nonneg := by filter_upwards [h.nonneg, hfg] with x hx he; rw [← he]; exact hx
  integral_eq := by rw [← integral_congr_ae hfg]; exact h.integral_eq
  inMeasure := h.inMeasure.congr_right hfg
  muW G := by
    rw [h.muW G]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hfg] with x hx
    rw [hx]

end W11Weight38

namespace BirkhoffInput38

variable (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {lower upper : ℝ}
  (c : BoundedCoefficients lower upper) {s : ℝ}

include B O in
/-- Existence of a Gaussian divergence (E05) with all the weight facts. -/
theorem exists_weight_W11 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    ∃ δK : (ℤ → ℂ) → ℝ,
      RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK ∧
      W11Weight38 B c s
        (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δK) := by
  have hs1 := le_one_of_lt_three_quarters_W06_38 hs'
  obtain ⟨δK, hdiv, hmap, hpos, hint, hone, hconv⟩ := B.ramer_W06_cyl_38 O c hs hs1
  obtain ⟨hfpos, hfi, hfint, hmu, -⟩ := density_W06_38 B c s O hs hs' _ hmap hint hpos
  have hZ := (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c)
    (coef_upper38 c)).1
  have hrc : Continuous (fun x : FullWeightedHilbert c s =>
      remainder38 c.val (physOfE38 c s x)) := B.continuous_remainder_physOfE38 c s O hs'
  set f := fW06_38 c s hs (B.KW06_38 O c hs1) δK with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfpos x).le
  have hfm : AEMeasurable (fun x => ENNReal.ofReal (f x)) (fullWeightedSequenceGaussian c s) :=
    hfi.aemeasurable.ennreal_ofReal
  have hmu' : B.muW38 c.val = ENNReal.ofReal (1 / B.ZW38 c.val) •
      ((fullWeightedSequenceGaussian c s).withDensity
        (fun x => ENNReal.ofReal (f x))).map (physFW06_38 c s) := hmu
  refine ⟨δK, hdiv, ⟨hfi, Filter.Eventually.of_forall hf0, hfint,
    B.tendstoInMeasure_fN_W07 O c hs hs' hs1 δK hconv, fun G => ?_⟩⟩
  rw [hmu', integral_smul_measure, ENNReal.toReal_ofReal (one_div_pos.2 hZ).le, smul_eq_mul]
  congr 1
  rw [(measurableEmbedding_physFW06_38 c s).integral_map]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hfm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (hf0 x), smul_eq_mul]
  rfl

include B O in
/-- The weight facts hold for *every* Gaussian divergence in the sense of `RamerDivergence38`
(the weight is `γ_W`-a.e. independent of the choice, `fW06_ae_unique_W07`). -/
theorem weight_W11 (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) (δ : (ℤ → ℂ) → ℝ)
    (hδ : RamerDivergence38 c s (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δ) :
    W11Weight38 B c s
      (fW06_38 c s hs (B.KW06_38 O c (le_one_of_lt_three_quarters_W06_38 hs')) δ) := by
  obtain ⟨δ₀, hδ₀, h₀⟩ := B.exists_weight_W11 O c hs hs'
  exact h₀.congr (fW06_ae_unique_W07 c s B O hs (le_one_of_lt_three_quarters_W06_38 hs') δ₀ δ hδ₀ hδ)

theorem ZW_pos_W11 : 0 < B.ZW38 c.val :=
  (B.ZW38_pos_le_one lower upper c.val c.property.1 (coef_bound38 c) (coef_upper38 c)).1

section Core

variable {f : FullWeightedHilbert c s → ℝ}

/-- **W11.01** (`(1) ⇔ (2)`, first half): `Z_N → Z_W ⇔ f_N → f_W` in `L¹(γ_W)`. -/
theorem tendsto_Z_iff_l1_W11 (hs : (1 : ℝ) / 2 < s) (hW : W11Weight38 B c s f) :
    Tendsto (fun N : ℕ => relativePartition38 c N) atTop (𝓝 (B.ZW38 c.val)) ↔
      Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x - f x| ∂(fullWeightedSequenceGaussian c s))
        atTop (𝓝 0) := by
  have h := tendsto_iff_l1_W11 (fullWeightedSequenceGaussian c s) (fun N x => fN38 c s N x) f
    (fun N => integrable_fN38 c hs N) hW.integrable (fun N x => (fN38_pos c s N x).le)
    hW.nonneg hW.inMeasure
  simp_rw [integral_fN38 c s hs, hW.integral_eq] at h
  exact h

/-- **W11.01** (`(2)`: `L¹` convergence ⇔ uniform integrability of `(f_N)`). -/
theorem l1_iff_uniformIntegrable_W11' (hs : (1 : ℝ) / 2 < s) (hW : W11Weight38 B c s f) :
    Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x - f x| ∂(fullWeightedSequenceGaussian c s))
        atTop (𝓝 0) ↔
      UniformIntegrable (fun N x => fN38 c s N x) 1 (fullWeightedSequenceGaussian c s) :=
  l1_iff_uniformIntegrable_W11 (fullWeightedSequenceGaussian c s) (fun N x => fN38 c s N x) f
    (fun N => integrable_fN38 c hs N) hW.integrable (fun N x => (fN38_pos c s N x).le)
    hW.nonneg hW.inMeasure

/-- **W11.02.** `L¹` convergence of the weights implies weak convergence of the field laws on `𝓕⁻¹E_s`:
for every `F` bounded and continuous on `𝓕⁻¹E_s`, `∫ F dν_{W,N} → ∫ F dμ_W`. -/
theorem weak_of_l1_W11 (hs : (1 : ℝ) / 2 < s) (hW : W11Weight38 B c s f)
    (hL1 : Tendsto (fun N : ℕ => ∫ x, |fN38 c s N x - f x| ∂(fullWeightedSequenceGaussian c s))
      atTop (𝓝 0))
    (F : PhysicalL2 → ℝ) (hF : Continuous (fun y : ECarrier38 c s => F (physOfE38 c s y)))
    (hFb : ∃ M, ∀ y : ECarrier38 c s, |F (physOfE38 c s y)| ≤ M) :
    Tendsto (fun N : ℕ => ∫ u, F u ∂(nuWN38 c N)) atTop (𝓝 (∫ u, F u ∂(B.muW38 c.val))) := by
  obtain ⟨M, hM⟩ := hFb
  set γ := fullWeightedSequenceGaussian c s with hγ
  have hZpos := B.ZW_pos_W11 c
  have hZ := (B.tendsto_Z_iff_l1_W11 c hs hW).2 hL1
  have hF' : Continuous (fun y : FullWeightedHilbert c s => F (physOfE38 c s y)) := hF
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set FN : ℕ → FullWeightedHilbert c s → ℝ := fun N x => F (physOfE38 c s (projE38 c s N x))
    with hFN
  set Finf : FullWeightedHilbert c s → ℝ := fun x => F (physOfE38 c s x) with hFinf
  have hFNc : ∀ N, Continuous (FN N) := fun N => hF'.comp (continuous_projFW38 c s N)
  have hFNb : ∀ N x, |FN N x| ≤ M := fun N x => hM _
  have hFib : ∀ x, |Finf x| ≤ M := fun x => hM _
  have hfN : ∀ N, Integrable (fN38 c s N) γ := fun N => integrable_fN38 c hs N
  have hf0 := hW.nonneg
  -- the numerators
  have hA : Tendsto (fun N => ∫ x, FN N x * fN38 c s N x ∂γ) atTop (𝓝 (∫ x, Finf x * f x ∂γ)) := by
    have hint1 : ∀ N, Integrable (fun x => FN N x * fN38 c s N x) γ := fun N =>
      Integrable.bdd_mul (c := M) (hfN N) (hFNc N).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFNb N x)
    have hint2 : Integrable (fun x => Finf x * f x) γ :=
      Integrable.bdd_mul (c := M) hW.integrable hF'.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hFib x)
    have hint3 : ∀ N, Integrable (fun x => |FN N x - Finf x| * f x) γ := fun N =>
      Integrable.bdd_mul (c := 2 * M) hW.integrable
        (((hFNc N).sub hF').abs.aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_abs]
          calc |FN N x - Finf x| ≤ |FN N x| + |Finf x| := abs_sub _ _
            _ ≤ M + M := add_le_add (hFNb N x) (hFib x)
            _ = 2 * M := by ring)
    have hint4 : ∀ N, Integrable (fun x => |fN38 c s N x - f x|) γ := fun N =>
      ((hfN N).sub hW.integrable).abs
    -- second piece tends to zero (dominated convergence)
    have hB : Tendsto (fun N => ∫ x, |FN N x - Finf x| * f x ∂γ) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := γ)
        (F := fun N x => |FN N x - Finf x| * f x) (f := fun _ => (0 : ℝ))
        (fun x => 2 * M * f x)
        (fun N => (hint3 N).aestronglyMeasurable) (hW.integrable.const_mul _)
        (fun N => by
          filter_upwards [hf0] with x hx
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) hx)]
          refine mul_le_mul_of_nonneg_right ?_ hx
          calc |FN N x - Finf x| ≤ |FN N x| + |Finf x| := abs_sub _ _
            _ ≤ M + M := add_le_add (hFNb N x) (hFib x)
            _ = 2 * M := by ring)
        (Filter.Eventually.of_forall fun x => by
          have h1 : Tendsto (fun N => FN N x) atTop (𝓝 (Finf x)) :=
            (hF'.tendsto _).comp (tendsto_projE38 c s x)
          have h2 := ((h1.sub_const (Finf x)).abs).mul_const (f x)
          simpa using h2)
      simpa using this
    have hC := hL1.const_mul M
    have hD := hC.add hB
    rw [mul_zero, add_zero] at hD
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hD
    rw [Real.norm_eq_abs, ← integral_sub (hint1 N) hint2]
    have hg : Integrable (fun x => M * |fN38 c s N x - f x| + |FN N x - Finf x| * f x) γ :=
      ((hint4 N).const_mul M).add (hint3 N)
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |FN N x * fN38 c s N x - Finf x * f x| ∂γ
        ≤ ∫ x, (M * |fN38 c s N x - f x| + |FN N x - Finf x| * f x) ∂γ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) hg ?_
          filter_upwards [hf0] with x hx
          have e : FN N x * fN38 c s N x - Finf x * f x =
              FN N x * (fN38 c s N x - f x) + (FN N x - Finf x) * f x := by ring
          rw [e]
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg hx]
          exact add_le_add (mul_le_mul_of_nonneg_right (hFNb N x) (abs_nonneg _) |>.trans
            (by rw [mul_comm])) le_rfl
      _ = M * ∫ x, |fN38 c s N x - f x| ∂γ + ∫ x, |FN N x - Finf x| * f x ∂γ := by
          rw [integral_add ((hint4 N).const_mul M) (hint3 N), integral_const_mul]
  have hnu : ∀ N, ∫ u, F u ∂(nuWN38 c N) =
      (1 / relativePartition38 c N) * ∫ x, FN N x * fN38 c s N x ∂γ := fun N =>
    integral_nuWN38 c s hs N F hF
  have hmu : ∫ u, F u ∂(B.muW38 c.val) = (1 / B.ZW38 c.val) * ∫ x, Finf x * f x ∂γ := by
    rw [hW.muW F]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  simp_rw [hnu]
  rw [hmu]
  exact (tendsto_const_nhds.div hZ hZpos.ne').mul hA

end Core

end BirkhoffInput38

end NlsGge.Birkhoff
end
