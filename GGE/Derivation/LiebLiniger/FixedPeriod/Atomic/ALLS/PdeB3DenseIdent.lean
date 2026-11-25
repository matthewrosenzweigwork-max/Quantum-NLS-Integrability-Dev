import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB3Hm1Crude
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB2DuhamelDense

/-! # Track B, step B3: the actual `H⁻¹` Duhamel integral of a dense forcing

For a dense forcing `F(r,x) = Σ_{k∈S} F_k(r) e_k(x)` (time-Schwartz modes, finitely many modes),
the actual `H⁻¹`-valued Bochner integral `∫₀ᵗ e^{i(t-r)∂ₓ²}(-iF(r)) dr` has `n`-th coefficient
`-i ∫₀ᵗ e^{-i(2πn)²(t-r)} F_n(r) dr` (`carrierCoe38_duhamel_dense`), hence at every time `t` with
`η(t) = 1` it is the `L²` field `x ↦ -i Σ_k h_k(t) e_k(x)` built from the fixed-cutoff Duhamel output
`h_k = duhOut η ((2πk)²) F_k` of `PdeB2DuhamelSchwartz` (`duhamel_dense_eq_l2ToHm1`). This links the
Fourier-side dense estimates of `PdeB2DuhamelDense` to the actual Bochner Duhamel integral.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open SchwartzMap

attribute [local instance] isProbabilityMeasure_spatialMeasure

/-- The dense spacetime field as a function on `ℝ × 𝕋`. -/
def denseSp (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ)) (p : ℝ × PhysicalCircle) : ℂ :=
  denseField S F p.1 p.2

theorem denseSp_apply (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ)) (p : ℝ × PhysicalCircle) :
    denseSp S F p = ∑ k ∈ S, F k p.1 * fourier k p.2 := by
  simp only [denseSp, denseField, torusPoly_apply]

theorem continuous_denseSp (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ)) : Continuous (denseSp S F) := by
  have h : denseSp S F = fun p => ∑ k ∈ S, F k p.1 * fourier k p.2 :=
    funext (denseSp_apply S F)
  rw [h]
  exact continuous_finsetSum _ fun k _ =>
    ((F k).continuous.comp continuous_fst).mul ((fourier k).continuous.comp continuous_snd)

/-- Dense forcings are integrable on every slab `[a,b] × 𝕋`. -/
theorem integrable_denseSp_slab (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ)) (a b : ℝ) :
    Integrable (denseSp S F) (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) := by
  have hk : ∀ k ∈ S, Integrable (fun p : ℝ × PhysicalCircle => ‖F k p.1‖ * (1 : ℝ))
      (((volume : Measure ℝ).restrict (Set.Icc a b)).prod spatialMeasure) := fun k _ =>
    ((F k).integrable.norm.integrableOn (s := Set.Icc a b)).mul_prod (integrable_const (1 : ℝ))
  refine Integrable.mono' (integrable_finsetSum S hk) (continuous_denseSp S F).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  rw [denseSp_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((ContinuousMap.norm_coe_le_norm _ p.2).trans (fourier_norm k).le) (norm_nonneg _)

theorem physicalFourier_denseSlice (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ)) (hF : ∀ k ∉ S, F k = 0)
    (r : ℝ) (n : ℤ) : physicalFourier (fun x => denseSp S F (r, x)) n = F n r := by
  unfold physicalFourier denseSp denseField
  exact fourierCoeff_torusPoly S (fun k => F k r) (fun k hk => by simp [hF k hk]) n

theorem freePhase_eq_ph (s : ℝ) (n : ℤ) : freePhase s n = ph (-disp n) s := by
  simp only [freePhase, ph]
  congr 1
  push_cast
  ring

/-- **Bochner = Fourier for dense forcings**: coefficients of the actual `H⁻¹` Duhamel integral. -/
theorem carrierCoe38_duhamel_dense (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ)) (hF : ∀ k ∉ S, F k = 0)
    (t : ℝ) (n : ℤ) :
    carrierCoe38 (-1) (∫ r in (0 : ℝ)..t,
        freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => denseSp S F (r, x))))) n =
      -Complex.I * ∫ r in (0 : ℝ)..t, ph (-disp n) (t - r) * F n r := by
  rw [carrierCoe38_duhamel_integral (fun T => integrable_denseSp_slab S F (-T) T) t 0 t n,
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [physicalFourier_denseSlice S F hF r n, freePhase_eq_ph]
  ring

theorem duhOut_zero (η : 𝓢(ℝ, ℂ)) (lam : ℝ) : duhOut η lam 0 = 0 := by
  ext t
  rw [duhOut_apply]
  simp

/-- **Identification**: at every time `t` with `η(t) = 1`, the actual `H⁻¹` Bochner Duhamel integral
of a dense forcing is the `L²` field `-i Σ_k (duhOut η ((2πk)²) F_k)(t) e_k`. -/
theorem duhamel_dense_eq_l2ToHm1 (η : 𝓢(ℝ, ℂ)) (S : Finset ℤ) (F : ℤ → 𝓢(ℝ, ℂ))
    (hF : ∀ k ∉ S, F k = 0) (t : ℝ) (hη : η t = 1) :
    ∫ r in (0 : ℝ)..t, freeProp (-1) (t - r) (negIMul (-1) (fnToHm1 (fun x => denseSp S F (r, x)))) =
      l2ToHm1 (ContinuousMap.toLp 2 spatialMeasure ℂ
        (torusPoly S (fun k => -Complex.I * duhOut η (disp k) (F k) t))) := by
  refine carrierExt38 (funext fun n => ?_)
  rw [carrierCoe38_duhamel_dense S F hF t n, carrierCoe38_l2ToHm1,
    physicalFourier_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (μ := spatialMeasure) (𝕜 := ℂ) _)]
  unfold physicalFourier
  rw [fourierCoeff_torusPoly S _ (fun k hk => by simp [hF k hk, duhOut_zero]) n, duhOut_apply, hη,
    one_mul]

end LiebLiniger.FixedPeriod.ALLS.PdeB
