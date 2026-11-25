import NlsGge.Schur.ParityBasis

/-!
# Actual restriction to the unit source interval

Probability Haar on the doubled circle equals one-half ordinary doubled volume.
Actual parity gives equal half-interval square norms before constructing the
unit-interval restriction map. Its surjective signed extension remains separate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur

abbrev SourceIntervalL2 : Type :=
  Lp ℂ 2 (volume.restrict (Set.Ioc (0 : ℝ) 1))

theorem spectralSign_norm (n : ℤ) : ‖spectralSign n‖ = 1 := by
  unfold spectralSign
  split_ifs <;> simp

/-- Actual Haar null sets pull back to null sets on the source first half. -/
theorem spectral_ae_pullback_first_half {a b : SpectralCircle → ℂ}
    (h : a =ᵐ[spectralHaar] b) :
    (fun x : ℝ => a (x : SpectralCircle)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun x : ℝ => b (x : SpectralCircle)) := by
  have hv : a =ᵐ[(volume : Measure SpectralCircle)] b := by
    rw [spectral_volume_eq_two_smul]
    exact Measure.ae_smul_measure h (2 : ℝ≥0∞)
  have hr : (fun x : ℝ => a (x : SpectralCircle)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 2)]
      (fun x : ℝ => b (x : SpectralCircle)) := by
    simpa only [Function.comp_def, zero_add] using
      (AddCircle.measurePreserving_mk (2 : ℝ) 0).quasiMeasurePreserving.ae_eq_comp hv
  have hs : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioc (0 : ℝ) 2 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  exact ae_restrict_of_ae_restrict_of_subset hs hr

/-- The actual kernel equality yields the representative parity law a.e. -/
theorem scalarParity_ae_halfShift (n : ℤ) (f : scalarParity n) :
    (fun x : SpectralCircle => f.val (x + ((1 : ℝ) : SpectralCircle))) =ᵐ[spectralHaar]
      (fun x : SpectralCircle => spectralSign n * f.val x) := by
  have he := (mem_scalarParity n f.val).mp f.property
  filter_upwards [halfTranslation_ae f.val, Lp.coeFn_smul (spectralSign n) f.val]
    with x ht hs
  rw [he, hs] at ht
  change spectralSign n * f.val x = f.val (x + ((1 : ℝ) : SpectralCircle)) at ht
  exact ht.symm

/-- Actual parity gives equal square norms under the half-shift on the first half. -/
theorem scalarParity_norm_sq_halfShift_ae (n : ℤ) (f : scalarParity n) :
    (fun x : ℝ => ‖f.val ((x + 1 : ℝ) : SpectralCircle)‖ ^ 2)
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun x : ℝ => ‖f.val (x : SpectralCircle)‖ ^ 2) := by
  have h := spectral_ae_pullback_first_half (scalarParity_ae_halfShift n f)
  filter_upwards [h] with x hx
  simpa only [AddCircle.coe_add, norm_mul, spectralSign_norm, one_mul] using
    congrArg (fun z : ℂ => ‖z‖ ^ 2) hx

/-- Proved integrability of both halves precedes interval splitting. -/
theorem scalarParity_norm_sq_source_interval (n : ℤ) (f : scalarParity n) :
    ‖f‖ ^ 2 =
      ∫ x in Set.Ioc (0 : ℝ) 1, ‖f.val (x : SpectralCircle)‖ ^ 2 := by
  let g : ℝ → ℝ := fun x => ‖f.val (x : SpectralCircle)‖ ^ 2
  have hfull : IntegrableOn g (Set.Ioc (0 : ℝ) 2) volume :=
    spectral_integrableOn_norm_sq_doubled_interval f.val
  have hfirst : IntegrableOn g (Set.Ioc (0 : ℝ) 1) volume :=
    hfull.mono_set (fun x hx => ⟨hx.1, hx.2.trans (by norm_num)⟩)
  have hsecond : IntegrableOn g (Set.Ioc (1 : ℝ) 2) volume :=
    hfull.mono_set (fun x hx => ⟨(by norm_num : (0 : ℝ) < 1).trans hx.1, hx.2⟩)
  have hi01 : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hfirst
  have hi12 : IntervalIntegrable g volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hsecond
  have he : (∫ x in (1 : ℝ)..2, g x) = ∫ x in (0 : ℝ)..1, g x := by
    calc
      (∫ x in (1 : ℝ)..2, g x) = ∫ x in (0 : ℝ)..1, g (x + 1) := by
        simpa only [zero_add, one_add_one_eq_two] using
          (intervalIntegral.integral_comp_add_right (f := g) (a := (0 : ℝ))
            (b := (1 : ℝ)) 1).symm
      _ = ∫ x in (0 : ℝ)..1, g x := by
        apply intervalIntegral.integral_congr_ae_restrict
        simpa only [g, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
          scalarParity_norm_sq_halfShift_ae n f
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi01 hi12
  rw [he] at hadd
  rw [← Submodule.norm_coe f]
  rw [spectral_norm_sq_doubled_interval f.val]
  change (1 / 2 : ℝ) * (∫ x in Set.Ioc (0 : ℝ) 2, g x) =
    ∫ x in Set.Ioc (0 : ℝ) 1, g x
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2), ← hadd]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  ring

/-- Actual pullback membership on the source interval, before toLp. -/
theorem scalarParity_restrict_memLp (n : ℤ) (f : scalarParity n) :
    MemLp (fun x : ℝ => f.val (x : SpectralCircle)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hf : MemLp f.val 2 (volume : Measure SpectralCircle) := (Lp.memLp f.val).of_haarAddCircle
  have hd : MemLp (fun x : ℝ => f.val (x : SpectralCircle)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 2)) := by
    simpa only [Function.comp_def, zero_add] using
      hf.comp_measurePreserving (AddCircle.measurePreserving_mk (2 : ℝ) 0)
  have hs : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioc (0 : ℝ) 2 := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  exact hd.mono_measure (Measure.restrict_mono_set volume hs)

def scalarParityRestrictValue (n : ℤ) (f : scalarParity n) : SourceIntervalL2 :=
  (scalarParity_restrict_memLp n f).toLp (fun x : ℝ => f.val (x : SpectralCircle))

theorem scalarParityRestrictValue_ae (n : ℤ) (f : scalarParity n) :
    scalarParityRestrictValue n f =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun x : ℝ => f.val (x : SpectralCircle)) :=
  (scalarParity_restrict_memLp n f).coeFn_toLp

/-- The actual source L² norm is its integrable square norm. -/
theorem sourceInterval_norm_sq (f : SourceIntervalL2) :
    ‖f‖ ^ 2 = ∫ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ ^ 2 := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ = ∫ x in Set.Ioc (0 : ℝ) 1, RCLike.re (inner ℂ (f x) (f x)) := by
      rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
    _ = ∫ x in Set.Ioc (0 : ℝ) 1, ‖f x‖ ^ 2 := by
      simp only [← norm_sq_eq_re_inner (𝕜 := ℂ)]

theorem scalarParityRestrictValue_norm (n : ℤ) (f : scalarParity n) :
    ‖scalarParityRestrictValue n f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [sourceInterval_norm_sq, scalarParity_norm_sq_source_interval]
  exact integral_congr_ae (by
    filter_upwards [scalarParityRestrictValue_ae n f] with x hx
    rw [hx])

def scalarParityRestrictLinear (n : ℤ) : scalarParity n →ₗ[ℂ] SourceIntervalL2 where
  toFun := scalarParityRestrictValue n
  map_add' f g := by
    apply Lp.ext
    have hfg := spectral_ae_pullback_first_half (Lp.coeFn_add f.val g.val)
    filter_upwards [scalarParityRestrictValue_ae n (f + g),
      scalarParityRestrictValue_ae n f, scalarParityRestrictValue_ae n g, hfg,
      Lp.coeFn_add (scalarParityRestrictValue n f) (scalarParityRestrictValue n g)]
      with x hsum hf hg hin hout
    rw [hsum, hout]
    change (f.val + g.val) (x : SpectralCircle) =
      scalarParityRestrictValue n f x + scalarParityRestrictValue n g x
    rw [hin]
    change f.val (x : SpectralCircle) + g.val (x : SpectralCircle) =
      scalarParityRestrictValue n f x + scalarParityRestrictValue n g x
    rw [hf, hg]
  map_smul' c f := by
    change scalarParityRestrictValue n (c • f) = c • scalarParityRestrictValue n f
    apply Lp.ext
    have hin := spectral_ae_pullback_first_half (Lp.coeFn_smul c f.val)
    filter_upwards [scalarParityRestrictValue_ae n (c • f), hin,
      scalarParityRestrictValue_ae n f, Lp.coeFn_smul c (scalarParityRestrictValue n f)]
      with x hsum hinput hf hout
    rw [hsum, hout]
    change (c • f.val) (x : SpectralCircle) = c * scalarParityRestrictValue n f x
    rw [hinput]
    change c * f.val (x : SpectralCircle) = c * scalarParityRestrictValue n f x
    rw [hf]

/-- Derived restriction isometry; signed-extension surjectivity is a separate obligation. -/
def scalarParityRestrict (n : ℤ) : scalarParity n →ₗᵢ[ℂ] SourceIntervalL2 where
  toLinearMap := scalarParityRestrictLinear n
  norm_map' := scalarParityRestrictValue_norm n

end NlsGge.Schur
