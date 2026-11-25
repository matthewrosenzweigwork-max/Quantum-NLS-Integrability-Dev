import NlsGge.GK38.PairRealBridgeSeq
import NlsGge.GK38.PairAnalyticProbe

/-!
# F4 probes: the bridge at `u = 0` and at the constant real-slice potential

* `u = 0`: through the bridge `actualPhysicalUnitHalfTrace32 0 z = cos z` (E02's Dyson series at `t = 1`
  is the free `diag(e^{-iz}, e^{iz})`), agreeing with `discrim_zero`, and `perChar (realSlice 0) = -4 sin²`;
* constant potential `u ≡ a` (F2 probe closed form `zsConstFund`): E02's Dyson matrix is
  `cos(κt) I + (sin(κt)/κ) A` on `[0,1]` and `Δh = cos κ`, `κ² = z² - |a|²`, `κ ≠ 0`;
* the double point `z₀² = |a|²`: `Δ = 2`, `χ_p = 0` (F3 probe through the bridge);
* consequences of the real-analytic statement: `u ↦ Δh(u, z)` is continuous on `L²_r`.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis NlsGge.SpectralFoundations

/-! ### `u = 0` -/

/-- E02's Dyson series for the zero potential, at `t = 1`, is the free `E_z(1)`. -/
theorem dyson_zero_at_one (z : ℂ) :
    actualComplexZsDysonTsum (e02Pot38 0) z 1 = freeE z 1 := by
  rw [← monodromyPair_realSlice 0 z, realSlice_zero]
  exact monodromyPair_zero_potential z

/-- E02's half trace of the zero potential is `cos z`, through the bridge. -/
theorem actualPhysicalUnitHalfTrace32_zero (z : ℂ) :
    actualPhysicalUnitHalfTrace32 0 z = Complex.cos z := by
  have h := discrim_realSlice 0 z
  rw [realSlice_zero, discrim_zero] at h
  linear_combination (-(1 : ℂ) / 2) * h

theorem perChar_realSlice_zero (z : ℂ) :
    perChar (realSlice 0) z = -4 * Complex.sin z ^ 2 := by
  rw [realSlice_zero]; exact perChar_zero z

/-- Cross-check with E02's radicand: `Δh² - 1 = cos² - 1 = -sin²`. -/
theorem halfTrace_radicand_zero (z : ℂ) :
    actualPhysicalUnitHalfTrace32 0 z ^ 2 - 1 = -Complex.sin z ^ 2 := by
  rw [actualPhysicalUnitHalfTrace32_zero]
  linear_combination Complex.sin_sq_add_cos_sq z

/-! ### The constant potential `u ≡ a` -/

theorem dyson_const_eq (a z κ : ℂ) (hκ : κ ≠ 0) (hκ2 : κ ^ 2 = z ^ 2 - a * star a)
    (t : Set.Icc (0 : ℝ) 1) :
    actualComplexZsDysonTsum (e02Pot38 (constL2 a)) z t = zsConstFund a z κ t := by
  rw [← fundPair_realSlice, fundPair_realSlice_const a z κ hκ hκ2]

theorem actualPhysicalUnitHalfTrace32_const (a z κ : ℂ) (hκ : κ ≠ 0)
    (hκ2 : κ ^ 2 = z ^ 2 - a * star a) :
    actualPhysicalUnitHalfTrace32 (constL2 a) z = Complex.cos κ := by
  have h := discrim_realSlice (constL2 a) z
  rw [discrim, trace_monodromyPair_realSlice_const a z κ hκ hκ2] at h
  linear_combination (-1 / 2 : ℂ) * h

theorem perChar_realSlice_const (a z κ : ℂ) (hκ : κ ≠ 0) (hκ2 : κ ^ 2 = z ^ 2 - a * star a) :
    perChar (realSlice (constL2 a)) z = -4 * Complex.sin κ ^ 2 := by
  rw [perChar_realSlice, actualPhysicalUnitHalfTrace32_const a z κ hκ hκ2]
  linear_combination 4 * Complex.sin_sq_add_cos_sq κ

/-- At the double point `κ = 0` (`z₀² = |a|²`), `Δh = 1` and the radicand of E02 vanishes:
a consequence of the analyticity of `Δ` (F3) transported through the bridge. -/
theorem actualPhysicalUnitHalfTrace32_const_double (a z₀ : ℂ) (hz₀ : z₀ ^ 2 = a * star a) :
    actualPhysicalUnitHalfTrace32 (constL2 a) z₀ = 1 := by
  have h := discrim_realSlice (constL2 a) z₀
  rw [discrim, trace_monodromyPair_realSlice_const_double a z₀ hz₀] at h
  linear_combination (-1 / 2 : ℂ) * h

theorem perChar_realSlice_const_double (a z₀ : ℂ) (hz₀ : z₀ ^ 2 = a * star a) :
    perChar (realSlice (constL2 a)) z₀ = 0 := by
  rw [perChar_realSlice, actualPhysicalUnitHalfTrace32_const_double a z₀ hz₀]
  ring

/-! ### Consequences of real-analyticity -/

/-- `u ↦ Δh(u, z)` is continuous on `L²_r`. -/
theorem continuous_actualPhysicalUnitHalfTrace32 (z : ℂ) :
    Continuous (fun u : PhysicalL2 => actualPhysicalUnitHalfTrace32 u z) := by
  have h := (analyticOnNhd_discrim_real z).continuousOn
  have h2 : Continuous (fun u : PhysicalL2 => discrim (realSlice u) z) :=
    continuousOn_univ.1 h
  have : (fun u : PhysicalL2 => actualPhysicalUnitHalfTrace32 u z) =
      fun u => discrim (realSlice u) z / 2 := by
    funext u; rw [discrim_realSlice]; ring
  rw [this]
  exact h2.div_const 2

/-- Joint continuity in `(u, z)`. -/
theorem continuous_discrim_realSlice_joint :
    Continuous (fun p : PhysicalL2 × ℂ => discrim (realSlice p.1) p.2) :=
  continuousOn_univ.1 analyticOnNhd_discrim_real_joint.continuousOn

end

end NlsGge.GK38
