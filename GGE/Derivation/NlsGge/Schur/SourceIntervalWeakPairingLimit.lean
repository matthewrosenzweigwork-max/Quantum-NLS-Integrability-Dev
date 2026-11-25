import NlsGge.Schur.SourceInterval
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! NEW-F02.02: the actual bilinear test pairing on interval L2 is bounded.
This gives a legitimate limit passage for finite Fourier integration by parts.
It does not assert the spectral/physical weak-H1 domain equivalence. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.Schur

def sourceIntervalTestPairing (test : SourceIntervalL2) :
    SourceIntervalL2 →L[ℂ] ℂ := innerSL ℂ (star test)

lemma sourceIntervalTestPairing_integral (test f : SourceIntervalL2) :
    sourceIntervalTestPairing test f =
      ∫ x in Set.Ioc (0 : ℝ) 1, f x * test x := by
  change inner ℂ (star test) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star test] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  change f x * star (star (test x)) = f x * test x
  rw [star_star]

lemma sourceIntervalTestPairing_integrable (test f : SourceIntervalL2) :
    Integrable (fun x => f x * test x)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (star test) f).congr
  filter_upwards [Lp.coeFn_star test] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  change f x * star (star (test x)) = f x * test x
  rw [star_star]

lemma sourceIntervalTestPairing_tendsto (test : SourceIntervalL2)
    (f : ℕ → SourceIntervalL2) (F : SourceIntervalL2)
    (hf : Tendsto f atTop (nhds F)) :
    Tendsto (fun k => ∫ x in Set.Ioc (0 : ℝ) 1, f k x * test x)
      atTop (nhds (∫ x in Set.Ioc (0 : ℝ) 1, F x * test x)) := by
  simpa only [Function.comp_def, sourceIntervalTestPairing_integral] using
    ((sourceIntervalTestPairing test).continuous.tendsto F).comp hf

lemma sourceIntervalWeakPairingLimit
    (f g : ℕ → SourceIntervalL2) (F G test testDerivative : SourceIntervalL2)
    (hf : Tendsto f atTop (nhds F)) (hg : Tendsto g atTop (nhds G))
    (hweak : ∀ k,
      (∫ x in Set.Ioc (0 : ℝ) 1, f k x * testDerivative x) =
        -(∫ x in Set.Ioc (0 : ℝ) 1, g k x * test x)) :
    (∫ x in Set.Ioc (0 : ℝ) 1, F x * testDerivative x) =
      -(∫ x in Set.Ioc (0 : ℝ) 1, G x * test x) := by
  have hleft := sourceIntervalTestPairing_tendsto testDerivative f F hf
  have hright := (sourceIntervalTestPairing_tendsto test g G hg).neg
  exact tendsto_nhds_unique hleft (hright.congr (fun k => (hweak k).symm))

end NlsGge.Schur
