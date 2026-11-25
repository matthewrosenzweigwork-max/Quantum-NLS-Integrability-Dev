import NlsGge.GK38.GradFundamentalStar
import NlsGge.GK38.PairVolterraProbe
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # K1: explicit free-solution star probe with distinct spectral parameters. -/
set_option autoImplicit false
open Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section

/-- Explicit real-to-complex exponential differentiability adapter. -/
theorem k1ContDiffCexpReal38 (c : ℂ) :
    ContDiff ℝ 1 (fun s : ℝ => Complex.exp (c * (s : ℂ))) := by
  have hof : ContDiff ℝ 1 (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
  exact Complex.contDiff_exp.comp (contDiff_const.mul hof)

def k1FreeVec38 (z : ℂ) (s : ℝ) : PairVec38 :=
  ![Complex.exp (-(Complex.I * z) * (s : ℂ)), Complex.exp ((Complex.I * z) * (s : ℂ))]

theorem isPairSolution_k1FreeVec38 (z : ℂ) : IsPairSolution38 0 z (k1FreeVec38 z) := by
  constructor
  · intro i
    fin_cases i
    · change AbsolutelyContinuousOnInterval
        (fun s : ℝ => Complex.exp (-(Complex.I * z) * (s : ℂ))) 0 1
      exact (k1ContDiffCexpReal38 _).contDiffOn.absolutelyContinuousOnInterval
    · change AbsolutelyContinuousOnInterval
        (fun s : ℝ => Complex.exp ((Complex.I * z) * (s : ℂ))) 0 1
      exact (k1ContDiffCexpReal38 _).contDiffOn.absolutelyContinuousOnInterval
  · intro i
    filter_upwards [coverRep38_zero_ae] with s hs hmem
    have he : zsCoeffPot38 0 z s = !![-Complex.I * z, 0; 0, Complex.I * z] := by
      simp [zsCoeffPot38, zsCoeffPair, potRepFst38, potRepSnd38, hs]
    rw [he]
    fin_cases i
    · simpa [k1FreeVec38, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_assoc,
        neg_mul] using hasDerivAt_cexp_mul (-(Complex.I * z)) s
    · simpa [k1FreeVec38, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_assoc]
        using hasDerivAt_cexp_mul (Complex.I * z) s

/-- Both sides of the integrated star identity use free exponentials at μ≠ν. -/
theorem probe_k1_free_star_integral38 (t : Set.Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..(t : ℝ),
      pairBracket38 (starProd38 (k1FreeVec38 0 s) (k1FreeVec38 0 s))
        (starProd38 (k1FreeVec38 1 s) (k1FreeVec38 1 s))) =
      (pairBracket38 (k1FreeVec38 0 t) (k1FreeVec38 1 t) ^ 2 -
        pairBracket38 (k1FreeVec38 0 0) (k1FreeVec38 1 0) ^ 2) /
          (2 * Complex.I * ((0 : ℂ) - 1)) := by
  simpa only [pow_two] using integrated_starIdentity_div38 (by norm_num : (0 : ℂ) ≠ 1)
    (isPairSolution_k1FreeVec38 0) (isPairSolution_k1FreeVec38 1)
    (isPairSolution_k1FreeVec38 0) (isPairSolution_k1FreeVec38 1) t

end
end NlsGge.GK38
