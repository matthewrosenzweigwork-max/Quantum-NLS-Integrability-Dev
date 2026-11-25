import NlsGge.GK38.PairAsymptoticsSeqPerturbed
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# G1-015: GK Appendix D.2 at bounded complex frequency perturbations

The existing power-series/finite-window Parseval proof supplies the Bessel
estimate. The interval version below uses zero extension solely to avoid any
measurability assumption outside `[0,1]`. Square summability is a conclusion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.Atomic.G1015

private theorem osc_indicator_unit (f : ℝ → ℂ) (z : ℂ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    seqOsc38 ((Ioc (0 : ℝ) 1).indicator f) z t = seqOsc38 f z t := by
  unfold seqOsc38
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall fun s hs => by
    rw [Set.uIoc_of_le ht.1] at hs
    rw [Set.indicator_of_mem (show s ∈ Ioc (0 : ℝ) 1 from ⟨hs.1, hs.2.trans ht.2⟩)]

/-- The full square-sum estimate for every `L²[0,1]` representative, uniformly
for every unit-interval time and every complex perturbation bounded by `a`.
The interval integral on the right is exactly its squared L² norm. -/
theorem perturbed_fourier_bessel {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    {a : ℝ} (α : ℤ → ℂ) (hα : ∀ n, ‖α n‖ ≤ a)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Summable (fun n : ℤ => ‖seqOsc38 f ((n : ℂ) * Real.pi + α n) t‖ ^ 2) ∧
      ∑' n : ℤ, ‖seqOsc38 f ((n : ℂ) * Real.pi + α n) t‖ ^ 2 ≤
        Real.exp (2 * a) * (∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2) := by
  let g : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator f
  have hg : MemLp g 2 volume := (memLp_indicator_iff_restrict measurableSet_Ioc).mpr hf
  have hgs : IntervalIntegrable (fun s => ‖g s‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable.restrict).mp (hg.restrict (Ioc (0 : ℝ) 1)))
  have ha : 0 ≤ a := (norm_nonneg (α 0)).trans (hα 0)
  have hfreq (n : ℤ) : ‖((n : ℂ) * Real.pi + α n) - (n : ℂ) * Real.pi‖ ≤ a := by
    simpa only [add_sub_cancel_left] using hα n
  have h := seqOsc38_l2 hg.aestronglyMeasurable hgs ht ha
    (fun n => (n : ℂ) * Real.pi + α n) hfreq
  have heq (n : ℤ) : seqOsc38 g ((n : ℂ) * Real.pi + α n) t =
      seqOsc38 f ((n : ℂ) * Real.pi + α n) t := osc_indicator_unit f _ ht
  have henergy : (∫ s in (0 : ℝ)..1, ‖g s‖ ^ 2) =
      ∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall fun s hs => by
      rw [Set.uIoc_of_le zero_le_one] at hs
      dsimp [g]
      rw [Set.indicator_of_mem hs]
  have hexp : Real.exp a ^ 2 = Real.exp (2 * a) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [heq, henergy, hexp] using h

/-- The same estimate on the actual period-one physical L² carrier, with its
literal Hilbert norm and the repository's measurable interval representative. -/
theorem perturbed_fourier_bessel_physical (f : PhysicalL2)
    {a : ℝ} (α : ℤ → ℂ) (hα : ∀ n, ‖α n‖ ≤ a)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Summable (fun n : ℤ => ‖seqOsc38 (coverRep38 f) ((n : ℂ) * Real.pi + α n) t‖ ^ 2) ∧
      ∑' n : ℤ, ‖seqOsc38 (coverRep38 f) ((n : ℂ) * Real.pi + α n) t‖ ^ 2 ≤
        Real.exp (2 * a) * ‖f‖ ^ 2 := by
  have hf : MemLp (coverRep38 f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_coverRep38 f).aestronglyMeasurable.restrict).mpr
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegrable_coverRep38_sq_one f))
  simpa only [integral_sq_coverRep38_one] using perturbed_fourier_bessel hf α hα ht

end NlsGge.Atomic.G1015
