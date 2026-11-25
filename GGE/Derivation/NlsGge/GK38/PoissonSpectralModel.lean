import NlsGge.GK38.GradFundamental

/-! K3 first contract: actual discriminant spectral Poisson commutation.
GK book ChapterI Lemma8.3 (GKP Lemma7.3), book sign -i.
All complex L2 potential pairs; no simple-root, real-type or W restriction.
-/
set_option autoImplicit false
open Set Filter Topology MeasureTheory NlsGge.GK38
namespace NlsGge.GK38.PoissonSpectral38
noncomputable section

def spectralGradientWedge38 (φ : PotPair) (z w : ℂ) (s : ℝ) : ℂ :=
  gradDiscrim38 φ z s 0 * gradDiscrim38 φ w s 1 -
    gradDiscrim38 φ z s 1 * gradDiscrim38 φ w s 0

def spectralDiscrimPoisson38 (φ : PotPair) (z w : ℂ) : ℂ :=
  -Complex.I * ∫ s in (0 : ℝ)..1, spectralGradientWedge38 φ z w s

def spectralDiscrimHamField38 (φ : PotPair) (w : ℂ) : PotPair :=
  (-Complex.I • (gradDiscrimL2 φ w).2,
    Complex.I • (gradDiscrimL2 φ w).1)

def SpectralDiscrimCommuteTarget : Prop :=
  ∀ (φ : PotPair) (z w : ℂ),
    IntervalIntegrable (spectralGradientWedge38 φ z w) volume 0 1 ∧
      spectralDiscrimPoisson38 φ z w = 0 ∧
      gradDiscrimCLM φ z (spectralDiscrimHamField38 φ w) =
        spectralDiscrimPoisson38 φ z w

/-- The actual cyclic monodromy conjugate; adjugate is used before det-one. -/
def cyclicMatrix38 (φ : PotPair) (z : ℂ) (s : ℝ) : PairMat38 :=
  ext38 (fundContP φ z) s * monodromyPair φ z *
    (ext38 (fundContP φ z) s).adjugate

def traceProduct38 (A B : PairMat38) : ℂ := (A * B) 0 0 + (A * B) 1 1

def cyclicTraceProduct38 (φ : PotPair) (z w : ℂ) (s : ℝ) : ℂ :=
  traceProduct38 (cyclicMatrix38 φ z s) (cyclicMatrix38 φ w s)

theorem continuous_spectralGradientWedge38 (φ : PotPair) (z w : ℂ) :
    Continuous (spectralGradientWedge38 φ z w) := by
  exact (((continuous_apply 0).comp (continuous_gradDiscrim38 φ z)).mul
    ((continuous_apply 1).comp (continuous_gradDiscrim38 φ w))).sub
      (((continuous_apply 1).comp (continuous_gradDiscrim38 φ z)).mul
        ((continuous_apply 0).comp (continuous_gradDiscrim38 φ w)))

theorem intervalIntegrable_spectralGradientWedge38 (φ : PotPair) (z w : ℂ) :
    IntervalIntegrable (spectralGradientWedge38 φ z w) volume 0 1 :=
  (continuous_spectralGradientWedge38 φ z w).intervalIntegrable 0 1

end
end NlsGge.GK38.PoissonSpectral38
