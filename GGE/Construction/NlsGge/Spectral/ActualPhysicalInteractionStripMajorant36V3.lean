import NlsGge.Spectral.ActualInteractionPairKernel32V2
import NlsGge.Spectral.ActualPhysicalL2DoubledIntervalMemLpV1
import NlsGge.Spectral.GenericRoughMatrixDysonSummability32V1
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open CumulativePowerV3 CumulativePowerGeneralEndpointV1

/-- The physical raw-cover majorant for the gauged interaction coefficient
on a bounded upper-half-plane height strip. -/
def actualPhysicalInteractionStripMajorant36V3
    (u : PhysicalL2) (Y₀ t : ℝ) : ℝ :=
  Real.exp (2 * Y₀) *
    ‖naturalPhysicalCoverL2 u (t : SpectralCircle)‖

theorem actualPhysicalInteractionStripMajorant36V3_nonneg
    (u : PhysicalL2) (Y₀ t : ℝ) :
    0 ≤ actualPhysicalInteractionStripMajorant36V3 u Y₀ t :=
  mul_nonneg (Real.exp_pos _).le (norm_nonneg _)

theorem actualPhysicalInteractionStripMajorant36V3_intervalIntegrable
    (u : PhysicalL2) (Y₀ : ℝ) :
    IntervalIntegrable (actualPhysicalInteractionStripMajorant36V3 u Y₀)
      volume 0 1 := by
  have hU : IntervalIntegrable
      (fun t : ℝ => naturalPhysicalCoverL2 u (t : SpectralCircle)) volume 0 1 := by
    apply (naturalPhysicalCoverL2_intervalIntegrable_doubled u).mono_set
    simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1),
      Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
    intro t ht
    exact ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hfun : actualPhysicalInteractionStripMajorant36V3 u Y₀ =
      (fun t : ℝ => Real.exp (2 * Y₀) *
        ‖naturalPhysicalCoverL2 u (t : SpectralCircle)‖) := by
    funext t
    rfl
  rw [hfun]
  exact hU.norm.const_mul (Real.exp (2 * Y₀))

/-- Exact actual-entry majorant: the two off-diagonal exponential norms have
opposite signs, both controlled by the strip height; diagonal entries vanish. -/
theorem actualPhysicalInteraction_entrySup_boundedHeight36V3
    (u : PhysicalL2) (z : ℂ) (Y₀ t : ℝ)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ z.im) (hY' : z.im ≤ Y₀)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    actualComplexMatrixEntrySup
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z t) ≤
      actualPhysicalInteractionStripMajorant36V3 u Y₀ t := by
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let B : Matrix (Fin 2) (Fin 2) ℂ := actualZsInteractionCoefficient32 U z t
  have hentries := actualInteractionCoefficient_entries32 U z t
  have h00 : B 0 0 = 0 := by
    simp [B, actualZsInteractionCoefficient32]
  have h11 : B 1 1 = 0 := by
    simp [B, actualZsInteractionCoefficient32]
  have h01norm : ‖B 0 1‖ = ‖U t‖ * Real.exp (-2 * t * z.im) := by
    change ‖actualZsInteractionCoefficient32 U z t 0 1‖ = _
    rw [hentries.1]
    simp [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have h10norm : ‖B 1 0‖ = ‖U t‖ * Real.exp (2 * t * z.im) := by
    change ‖actualZsInteractionCoefficient32 U z t 1 0‖ = _
    rw [hentries.2]
    simp [norm_mul, norm_star, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  have hnegative : Real.exp (-2 * t * z.im) ≤ Real.exp (2 * Y₀) := by
    have harg : -2 * t * z.im ≤ 0 := by nlinarith [mul_nonneg ht.1 hY]
    calc
      Real.exp (-2 * t * z.im) ≤ 1 := Real.exp_le_one_iff.mpr harg
      _ ≤ Real.exp (2 * Y₀) := Real.one_le_exp_iff.mpr (by positivity)
  have hty : t * z.im ≤ Y₀ := by
    calc
      t * z.im ≤ 1 * z.im := mul_le_mul_of_nonneg_right ht.2 hY
      _ = z.im := by ring
      _ ≤ Y₀ := hY'
  have hpositive : Real.exp (2 * t * z.im) ≤ Real.exp (2 * Y₀) :=
    Real.exp_le_exp.mpr (by nlinarith [hty])
  have hqpos := actualPhysicalInteractionStripMajorant36V3_nonneg u Y₀ t
  have h00norm : ‖B 0 0‖ ≤ actualPhysicalInteractionStripMajorant36V3 u Y₀ t := by
    simpa [h00] using hqpos
  have h01bound : ‖B 0 1‖ ≤ actualPhysicalInteractionStripMajorant36V3 u Y₀ t := by
    rw [h01norm]
    dsimp [U, actualPhysicalInteractionStripMajorant36V3]
    calc
      ‖U t‖ * Real.exp (-2 * t * z.im) ≤
          ‖U t‖ * Real.exp (2 * Y₀) :=
        mul_le_mul_of_nonneg_left hnegative (norm_nonneg _)
      _ = Real.exp (2 * Y₀) * ‖U t‖ := by ring
  have h10bound : ‖B 1 0‖ ≤ actualPhysicalInteractionStripMajorant36V3 u Y₀ t := by
    rw [h10norm]
    dsimp [U, actualPhysicalInteractionStripMajorant36V3]
    calc
      ‖U t‖ * Real.exp (2 * t * z.im) ≤
          ‖U t‖ * Real.exp (2 * Y₀) :=
        mul_le_mul_of_nonneg_left hpositive (norm_nonneg _)
      _ = Real.exp (2 * Y₀) * ‖U t‖ := by ring
  have h11norm : ‖B 1 1‖ ≤ actualPhysicalInteractionStripMajorant36V3 u Y₀ t := by
    simpa [h11] using hqpos
  change actualComplexMatrixEntrySup B ≤ _
  unfold actualComplexMatrixEntrySup
  exact max_le (max_le h00norm h01bound) (max_le h10bound h11norm)

/-- The generic factorial coefficient bound instantiated with the actual
physical interaction coefficient and the realized physical majorant. -/
theorem actualPhysicalInteractionDysonTerm_factorial_boundedHeight36V3
    (u : PhysicalL2) (z : ℂ) (Y₀ : ℝ)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ z.im) (hY' : z.im ≤ Y₀)
    (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin 2) :
    ‖genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z)
      n t i j‖ ≤
      (2 * actualCumulativeRealIntegral
        (actualPhysicalInteractionStripMajorant36V3 u Y₀) 1) ^ n /
        (n.factorial : ℝ) := by
  exact genericRoughMatrixDysonTerm_uniform_bound32
    (actualZsInteractionCoefficient32
      (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z)
    (actualPhysicalInteractionStripMajorant36V3 u Y₀) 1
    (actualPhysicalInteractionStripMajorant36V3_intervalIntegrable u Y₀)
    (actualPhysicalInteractionStripMajorant36V3_nonneg u Y₀)
    (fun s hs => actualPhysicalInteraction_entrySup_boundedHeight36V3
      u z Y₀ s hY₀ hY hY' hs)
    n t ht i j

/-- Actual Dyson entrywise summability on the strip follows from the same
realized q, rather than an assumed coefficient majorant. -/
theorem actualPhysicalInteractionDysonTerm_summable_boundedHeight36V3
    (u : PhysicalL2) (z : ℂ) (Y₀ : ℝ)
    (hY₀ : 0 ≤ Y₀) (hY : 0 ≤ z.im) (hY' : z.im ≤ Y₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    Summable (fun n : ℕ => genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z)
      n t i j) := by
  exact summable_genericRoughMatrixDysonTerm32
    (actualZsInteractionCoefficient32
      (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) z)
    (actualPhysicalInteractionStripMajorant36V3 u Y₀) 1
    (actualPhysicalInteractionStripMajorant36V3_intervalIntegrable u Y₀)
    (actualPhysicalInteractionStripMajorant36V3_nonneg u Y₀)
    (fun s hs => actualPhysicalInteraction_entrySup_boundedHeight36V3
      u z Y₀ s hY₀ hY hY' hs)
    t ht i j

/-- The actual Dyson entry series has a common factorial tail over the full
unbounded real-frequency direction, bounded height strip, and unit time
interval. -/
theorem actualPhysicalInteractionDysonTerm_hasSumUniformlyOn_boundedHeight36V3
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) (i j : Fin 2) :
    HasSumUniformlyOn
      (fun n : ℕ => fun p : ℂ × ℝ =>
        genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) p.1)
          n p.2 i j)
      (fun p : ℂ × ℝ => ∑' n : ℕ,
        genericRoughMatrixDysonTerm32
          (actualZsInteractionCoefficient32
            (fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)) p.1)
          n p.2 i j)
      {p : ℂ × ℝ | 0 ≤ p.1.im ∧ p.1.im ≤ Y₀ ∧
        p.2 ∈ Set.Icc (0 : ℝ) 1} := by
  let q := actualPhysicalInteractionStripMajorant36V3 u Y₀
  have hbound : Summable (fun n : ℕ =>
      (2 * actualCumulativeRealIntegral q 1) ^ n / (n.factorial : ℝ)) := by
    exact (NormedSpace.expSeries_div_hasSum_exp
      (2 * actualCumulativeRealIntegral q 1)).summable
  apply HasSumUniformlyOn.of_norm_le_summable hbound
  intro n p hp
  exact actualPhysicalInteractionDysonTerm_factorial_boundedHeight36V3
    u p.1 Y₀ hY₀ hp.1 hp.2.1 n p.2 hp.2.2 i j

end NlsGge.SpectralFoundations
end
