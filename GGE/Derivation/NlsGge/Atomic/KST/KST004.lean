import NlsGge.Atomic.KST.KST003
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Tactic

/-!
# KST complementary denominator estimate on the full signed spectrum

The strip and denominator are those of Kappeler--Serier--Topalov, equation
(11). The integer label is the source label: the upper component's raw
Fourier character is `e_{-k}`, while the lower component's is `e_k`. The
proved KST-003 projection `spectralQn` is the full doubled-space complement;
this estimate is not restricted to a parity sector.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace NlsGge.Atomic.KST004

open NlsGge.Atomic.KST003
open NlsGge.Schur

/-- The literal closed source strip around the free spectral center `nπ`. -/
def spectralStrip (n : ℤ) : Set ℂ :=
  {z | |z.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2}

private theorem natAbs_cast_ge_one {k n : ℤ} (hkn : k ≠ n) :
    (1 : ℝ) ≤ (Int.natAbs (k - n) : ℝ) := by
  have hpos : 0 < Int.natAbs (k - n) :=
    Int.natAbs_pos.mpr (sub_ne_zero.mpr hkn)
  exact_mod_cast (Nat.succ_le_of_lt hpos)

/-- The closest complementary lattice point to the closed strip remains at
least `|k-n|`; both real-strip edges and all signed integers are included. -/
theorem complementary_denominator (n k : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (hkn : k ≠ n) :
    (Int.natAbs (k - n) : ℝ) ≤ ‖z - (k : ℂ) * (Real.pi : ℂ)‖ := by
  let d : ℝ := (Int.natAbs (k - n) : ℝ)
  have hd : 1 ≤ d := natAbs_cast_ge_one hkn
  have hpi : 2 ≤ Real.pi := Real.two_le_pi
  have hdist : |(k : ℝ) * Real.pi - (n : ℝ) * Real.pi| = d * Real.pi := by
    dsimp [d]
    rw [← sub_mul, ← Int.cast_sub, Nat.cast_natAbs, Int.cast_abs,
      Int.cast_sub, abs_mul, abs_of_pos Real.pi_pos]
  have hstrip : |z.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2 := hz
  have htriangle :
      |(k : ℝ) * Real.pi - (n : ℝ) * Real.pi| ≤
        |(k : ℝ) * Real.pi - z.re| + |z.re - (n : ℝ) * Real.pi| := by
    have heq : (k : ℝ) * Real.pi - (n : ℝ) * Real.pi =
        ((k : ℝ) * Real.pi - z.re) + (z.re - (n : ℝ) * Real.pi) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hreal : d ≤ |z.re - (k : ℝ) * Real.pi| := by
    have hsep : d * Real.pi ≤
        |z.re - (k : ℝ) * Real.pi| + Real.pi / 2 := by
      have htri := htriangle
      rw [hdist] at htri
      rw [abs_sub_comm ((k : ℝ) * Real.pi) z.re] at htri
      linarith [hstrip]
    have hhalf_nonneg : 0 ≤ d - (1 / 2 : ℝ) := by linarith
    have hpi_mul : 2 * (d - (1 / 2 : ℝ)) ≤
        Real.pi * (d - (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hpi hhalf_nonneg
    have hd_mul : d ≤ 2 * (d - (1 / 2 : ℝ)) := by linarith
    have hlower : Real.pi * (d - (1 / 2 : ℝ)) ≤
        |z.re - (k : ℝ) * Real.pi| := by
      nlinarith [hsep]
    exact le_trans (le_trans hd_mul hpi_mul) hlower
  have hcomplex := Complex.abs_re_le_norm (z - (k : ℂ) * (Real.pi : ℂ))
  have hre : (z - (k : ℂ) * (Real.pi : ℂ)).re =
      z.re - (k : ℝ) * Real.pi := by
    simp [Complex.mul_re]
  rw [hre] at hcomplex
  exact le_trans hreal (by simpa only [abs_sub_comm] using hcomplex)

/-- A complementary denominator never vanishes in the closed source strip. -/
theorem complementary_denominator_ne_zero (n k : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (hkn : k ≠ n) :
    z - (k : ℂ) * (Real.pi : ℂ) ≠ 0 := by
  intro hzero
  have hd := complementary_denominator n k z hz hkn
  rw [hzero, norm_zero] at hd
  have hpositive := natAbs_cast_ge_one hkn
  linarith

/-- The reciprocal multiplier coefficient obeys the source `Q_n` bound. -/
theorem complementary_reciprocal_bound (n k : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (hkn : k ≠ n) :
    ‖(z - (k : ℂ) * (Real.pi : ℂ))⁻¹‖ ≤
      1 / (Int.natAbs (k - n) : ℝ) := by
  have hd := complementary_denominator n k z hz hkn
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le
    (by have h := natAbs_cast_ge_one hkn; linarith) hd

/-- The actual source diagonal coefficient, set to zero on the resonant slot
removed by the checked full-space projection `spectralQn`. -/
def complementaryResolventCoeff (n : ℤ) (z : ℂ) (k : ℤ) : ℂ :=
  if k = n then 0 else (z - (k : ℂ) * (Real.pi : ℂ))⁻¹

@[simp] theorem complementaryResolventCoeff_resonant (n : ℤ) (z : ℂ) :
    complementaryResolventCoeff n z n = 0 := by
  simp [complementaryResolventCoeff]

/-- Uniform pointwise coefficient bound, including the zero resonant slot. -/
theorem complementaryResolventCoeff_bound (n k : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
    ‖complementaryResolventCoeff n z k‖ ≤
      1 / (Int.natAbs (k - n) : ℝ) := by
  by_cases hkn : k = n
  · subst k
    simp [complementaryResolventCoeff]
  · simpa [complementaryResolventCoeff, hkn] using
      complementary_reciprocal_bound n k z hz hkn

/-- The source spectral label of a raw period-two Fourier mode in one
component: upper modes use `e_{-k}`, lower modes use `e_k`. -/
def sourceModeIndex (upper : Bool) (m : ℤ) : ℤ := if upper then -m else m

/-- The bounded diagonal on square-summable Fourier coefficients in the
actual source label convention. -/
noncomputable def sourceModeDiagonal (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  lp.mapCLM 2
    (fun m : ℤ => complementaryResolventCoeff n z (sourceModeIndex upper m) •
      ContinuousLinearMap.id ℂ ℂ)
    zero_le_one
    (by
      intro m
      by_cases hm : sourceModeIndex upper m = n
      · simp [hm, complementaryResolventCoeff, norm_smul]
      · have hb := complementaryResolventCoeff_bound n (sourceModeIndex upper m) z hz
        have hd := natAbs_cast_ge_one hm
        have hi : 1 / (Int.natAbs (sourceModeIndex upper m - n) : ℝ) ≤ 1 := by
          simpa using (one_div_le_one_div_of_le zero_lt_one hd)
        have hc := le_trans hb hi
        simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hc)

/-- Coordinate formula for the actual source-label diagonal. -/
@[simp] theorem sourceModeDiagonal_apply (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool)
    (x : lp (fun _ : ℤ => ℂ) 2) (m : ℤ) :
    sourceModeDiagonal n z hz upper x m =
      complementaryResolventCoeff n z (sourceModeIndex upper m) * x m := by
  simp [sourceModeDiagonal, lp.mapCLM]

/-- The actual Fourier-diagonal complementary multiplier on one source
component, transported through the complete period-two Hilbert basis. -/
noncomputable def scalarComplementaryMultiplier (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) :
    SpectralScalarL2 →L[ℂ] SpectralScalarL2 :=
  ((fourierBasis (T := (2 : ℝ))).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((sourceModeDiagonal n z hz upper).comp
      (fourierBasis (T := (2 : ℝ))).repr.toContinuousLinearEquiv.toContinuousLinearMap)

/-- Fourier coordinates of the transported scalar multiplier obey the actual
source-label diagonal formula. -/
theorem scalarComplementaryMultiplier_repr (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (f : SpectralScalarL2) (m : ℤ) :
    (fourierBasis (T := (2 : ℝ))).repr
      (scalarComplementaryMultiplier n z hz upper f) m =
      complementaryResolventCoeff n z (sourceModeIndex upper m) *
        (fourierBasis (T := (2 : ℝ))).repr f m := by
  change (fourierBasis (T := (2 : ℝ))).repr
      ((fourierBasis (T := (2 : ℝ))).repr.symm
        (sourceModeDiagonal n z hz upper
          ((fourierBasis (T := (2 : ℝ))).repr f))) m = _
  rw [LinearIsometryEquiv.apply_symm_apply, sourceModeDiagonal_apply]

/-- The actual complementary multiplier on the full doubled KST source
space. It acts on all integer modes and vanishes at the two resonant vectors. -/
noncomputable def complementaryMultiplier (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) : KSTPairL2 →L[ℂ] KSTPairL2 :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Bool => SpectralScalarL2)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi (fun upper : Bool =>
      (scalarComplementaryMultiplier n z hz upper).comp
        (PiLp.proj (p := 2) (β := fun _ : Bool => SpectralScalarL2) upper)))

/-- The scalar multiplier acts diagonally in the actual period-two Fourier
basis, with the source-label sign accounted for in the upper component. -/
theorem scalarComplementaryMultiplier_basis (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (upper : Bool) (m : ℤ) :
    scalarComplementaryMultiplier n z hz upper (spectralBasis m) =
      complementaryResolventCoeff n z (sourceModeIndex upper m) • spectralBasis m := by
  apply (fourierBasis (T := (2 : ℝ))).repr.injective
  apply lp.ext
  funext j
  have hrepr :
      (fourierBasis (T := (2 : ℝ))).repr (spectralBasis m) =
        lp.single 2 m (1 : ℂ) := by
    simpa [spectralBasis] using
      (fourierBasis (T := (2 : ℝ))).repr_self m
  rw [scalarComplementaryMultiplier_repr, map_smul, hrepr]
  by_cases hj : j = m
  · subst j
    simp
  · simp [hj]

/-- On an actual KST source vector the diagonal label is `k` in both
components, even though the upper raw Fourier mode is indexed by `-k`. -/
theorem complementaryMultiplier_upper_vector (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (k : ℤ) :
    complementaryMultiplier n z hz (kstPnUpper k) =
      complementaryResolventCoeff n z k • kstPnUpper k := by
  apply PiLp.ext
  intro upper
  cases upper
  · simp [complementaryMultiplier, kstPnUpper]
  · simp [complementaryMultiplier, kstPnUpper, scalarComplementaryMultiplier_basis,
      sourceModeIndex]

/-- The lower source component carries the unreflected Fourier mode `e_k`. -/
theorem complementaryMultiplier_lower_vector (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) (k : ℤ) :
    complementaryMultiplier n z hz (kstPnLower k) =
      complementaryResolventCoeff n z k • kstPnLower k := by
  apply PiLp.ext
  intro upper
  cases upper
  · simp [complementaryMultiplier, kstPnLower, scalarComplementaryMultiplier_basis,
      sourceModeIndex]
  · simp [complementaryMultiplier, kstPnLower]

/-- The full source multiplier vanishes on both actual resonant source
vectors, exactly the range of the checked projection `spectralPn`. -/
theorem complementaryMultiplier_annihilates_resonant_vectors (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
    complementaryMultiplier n z hz (kstPnUpper n) = 0 ∧
      complementaryMultiplier n z hz (kstPnLower n) = 0 := by
  constructor
  · rw [complementaryMultiplier_upper_vector, complementaryResolventCoeff_resonant]
    simp
  · rw [complementaryMultiplier_lower_vector, complementaryResolventCoeff_resonant]
    simp

/-- The full complementary multiplier annihilates the actual source
projection `P_n`, hence acts only on `Q_n = Id - P_n`. -/
theorem complementaryMultiplier_comp_spectralPn_eq_zero (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
    (complementaryMultiplier n z hz).comp (spectralPn n) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change complementaryMultiplier n z hz (spectralPn n x) = 0
  rw [spectralPn_apply]
  have hu := (complementaryMultiplier_annihilates_resonant_vectors n z hz).1
  have hl := (complementaryMultiplier_annihilates_resonant_vectors n z hz).2
  simp only [map_add, map_smul, hu, hl, smul_zero, zero_add]

/-- Right composition by the checked full-space `Q_n` leaves the multiplier
unchanged. -/
theorem complementaryMultiplier_comp_spectralQn (n : ℤ) (z : ℂ)
    (hz : z ∈ spectralStrip n) :
    (complementaryMultiplier n z hz).comp (spectralQn n) =
      complementaryMultiplier n z hz := by
  apply ContinuousLinearMap.ext
  intro x
  change complementaryMultiplier n z hz (x - spectralPn n x) =
    complementaryMultiplier n z hz x
  rw [map_sub]
  have hzero := congrArg (fun T : KSTPairL2 →L[ℂ] KSTPairL2 => T x)
    (complementaryMultiplier_comp_spectralPn_eq_zero n z hz)
  have hPx : complementaryMultiplier n z hz (spectralPn n x) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, zero_apply] using hzero
  rw [hPx]
  simp

/-- On the full KST carrier, the complement removes both resonant source
vectors at their literal labels (upper `e_{-n}`, lower `e_n`). -/
theorem spectralQn_annihilates_resonant_vectors (n : ℤ) :
    spectralQn n (kstPnUpper n) = 0 ∧ spectralQn n (kstPnLower n) = 0 := by
  constructor
  · simp [spectralQn, spectralPn_upper]
  · simp [spectralQn, spectralPn_lower]

end NlsGge.Atomic.KST004
