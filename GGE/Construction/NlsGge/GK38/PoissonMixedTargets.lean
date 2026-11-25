import NlsGge.GK38.PoissonDirichletProbe
import NlsGge.GK38.PoissonSpectralCommute
import NlsGge.GK38.GradEigenPeriodic
import NlsGge.GK38.DirichletRealSign
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Prospective remaining K3 spectral/norming contracts. No proof credit.
Source anchors: GK Chapter I Section 8, Lemmas 8.4/8.5/8.8 and Proposition 8.9.
All brackets use the book sign -i. The ordered canonical bracket is {kappa,mu}=+1.
-/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38 NlsGge.GK38.PoissonDirichlet38
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.PoissonMixed38
noncomputable section

def kernelWedge38 (g h : PairKernelCont38) (s : ℝ) : ℂ :=
  pairKernelExt38 g s 0 * pairKernelExt38 h s 1 -
    pairKernelExt38 g s 1 * pairKernelExt38 h s 0

def kernelPoisson38 (g h : PairKernelCont38) : ℂ :=
  -Complex.I * ∫ s in (0 : ℝ)..1, kernelWedge38 g h s

def kernelHamField38 (g : PairKernelCont38) : PotPair :=
  let a := pairKernelL2Class38 g
  (-Complex.I • a.2, Complex.I • a.1)

def dirInterpolation38 (φ : PotPair) (z ζ : ℂ) : ℂ :=
  dslope (dirichletChar φ) z ζ / deriv (dirichletChar φ) z

def normingSpectral38 (φ : PotPair) (z : ℂ) : ℂ :=
  (fundSpectralIntegral38 φ z t1 0 0 + fundSpectralIntegral38 φ z t1 0 1 +
    fundSpectralIntegral38 φ z t1 1 0 + fundSpectralIntegral38 φ z t1 1 1) / 2

def normingKernel38 (φ : PotPair) (z : ℂ) : PairKernelCont38 :=
  (2*Complex.I)⁻¹ • mixedSquare (state φ z ![1,1]) (state φ z (terminalSeed φ z))

def normingCLM38 (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  integralPairCLM38 (normingKernel38 φ z) t1

def periodicKernel38 (φ : PotPair) (z : ℂ) : PairKernelCont38 :=
  -(deriv (discrim φ) z)⁻¹ • gradDiscrimCont38 φ z

def kappaKernel38 (φ : PotPair) (z : ℂ) : PairKernelCont38 :=
  (2 / normingFactor φ z) •
    (normingSpectral38 φ z • dirEigenKernel38 φ z + normingKernel38 φ z)

def kappaCLM38 (φ : PotPair) (z : ℂ) : PotPair →L[ℂ] ℂ :=
  integralPairCLM38 (kappaKernel38 φ z) t1

def signedNorming38 (u : PhysicalL2) (n : ℤ) : ℝ :=
  (parity n * normingFactor (realSlice u) (gkMu u n : ℂ)).re

def realKappa38 (u : PhysicalL2) (n : ℤ) : ℝ :=
  2 * Real.log (signedNorming38 u n)

def realKappaCLM38 (u : PhysicalL2) (n : ℤ) : PhysicalL2 →L[ℝ] ℝ :=
  (Complex.reCLM.comp
    ((kappaCLM38 (realSlice u) (gkMu u n : ℂ)).restrictScalars ℝ)).comp realSlice

def relativeKappa38 (φ : PotPair) (z : ℂ) (ρ : PotPair → ℂ) (ψ : PotPair) : ℂ :=
  2 * Complex.log (normingFactor ψ (ρ ψ) / normingFactor φ z)

def KernelPairingTarget : Prop :=
  ∀ g h : PairKernelCont38,
    IntervalIntegrable (kernelWedge38 g h) volume 0 1 ∧
    IntervalIntegrable (fun s => pairKernelExt38 g s 0 * potRepFst38 (kernelHamField38 h) s +
      pairKernelExt38 g s 1 * potRepSnd38 (kernelHamField38 h) s) volume 0 1 ∧
    integralPairCLM38 g t1 (kernelHamField38 h) = kernelPoisson38 g h

def NormingDifferentiabilityTarget : Prop :=
  AnalyticOnNhd ℂ (fun p : PotPair × ℂ => normingFactor p.1 p.2) univ ∧
  ∀ (φ : PotPair) (z : ℂ),
    HasDerivAt (normingFactor φ) (normingSpectral38 φ z) z ∧
    HasFDerivAt (fun ψ : PotPair => normingFactor ψ z) (normingCLM38 φ z) φ

def DirichletInterpolationTarget : Prop :=
  ∀ (φ : PotPair) (z : ℂ), dirichletChar φ z = 0 → deriv (dirichletChar φ) z ≠ 0 →
    AnalyticOnNhd ℂ (dirInterpolation38 φ z) univ ∧ dirInterpolation38 φ z z = 1 ∧
    (∀ ζ : ℂ, ζ ≠ z → dirInterpolation38 φ z ζ =
      dirichletChar φ ζ / ((ζ-z) * deriv (dirichletChar φ) z)) ∧
    (∀ w : ℂ, dirichletChar φ w = 0 →
      dirInterpolation38 φ z w = if w=z then 1 else 0)

def NormingRootDataTarget : Prop :=
  ∀ (φ : PotPair) (z : ℂ), dirichletChar φ z = 0 → deriv (dirichletChar φ) z ≠ 0 →
    normingFactor φ z ≠ 0 ∧ Q (state φ z ![1,1]) ≠ 0 ∧
    Q (state φ z ![1,1]) = 2 * deriv (dirichletChar φ) z * normingFactor φ z ∧
    state φ z ![1,1] t1 = normingFactor φ z • (![1,1] : PairVec38) ∧
    (normingFactor φ z)^2 - 1 = normingFactor φ z * antiDiscrim φ z

def DiscriminantDirichletMixedTarget : Prop :=
  ∀ (φ : PotPair) (z ζ : ℂ), dirichletChar φ z = 0 → deriv (dirichletChar φ) z ≠ 0 →
    Q (state φ z ![1,1]) ≠ 0 ∧
    2 * kernelPoisson38 (gradDiscrimCont38 φ ζ) (dirEigenKernel38 φ z) =
      antiDiscrim φ z * dirInterpolation38 φ z ζ

def NormingDirichletMixedTarget : Prop :=
  ∀ (φ : PotPair) (z ζ : ℂ), dirichletChar φ z = 0 → deriv (dirichletChar φ) z ≠ 0 →
    normingFactor φ z ≠ 0 ∧ Q (state φ z ![1,1]) ≠ 0 ∧
    2 * kernelPoisson38 (normingKernel38 φ ζ) (dirEigenKernel38 φ z) =
      normingFactor φ z * dirInterpolation38 φ z ζ

def PeriodicRootKernelTarget : Prop :=
  ∀ (φ : PotPair) (z : ℂ), perChar φ z=0 → deriv (perChar φ) z ≠ 0 →
    deriv (discrim φ) z ≠ 0 ∧
    integralPairCLM38 (periodicKernel38 φ z) t1 = perImplicitGradient φ z ∧
    ∃ (U : Set PotPair) (ρ : PotPair → ℂ),
      IsOpen U ∧ φ ∈ U ∧ AnalyticOnNhd ℂ ρ U ∧ ρ φ=z ∧
      (∀ ψ ∈ U, perChar ψ (ρ ψ)=0) ∧
      HasFDerivAt ρ (integralPairCLM38 (periodicKernel38 φ z) t1) φ

def PeriodicDirichletMixedTarget : Prop :=
  ∀ (φ : PotPair) (ζ z : ℂ),
    perChar φ ζ = 0 → deriv (perChar φ) ζ ≠ 0 →
    dirichletChar φ z = 0 → deriv (dirichletChar φ) z ≠ 0 →
    deriv (discrim φ) ζ ≠ 0 ∧
    2 * kernelPoisson38 (periodicKernel38 φ ζ) (dirEigenKernel38 φ z) =
      -(antiDiscrim φ z * dirInterpolation38 φ z ζ) / deriv (discrim φ) ζ

def PeriodicMutualTarget : Prop :=
  ∀ (φ : PotPair) (z w : ℂ),
    perChar φ z = 0 → perChar φ w = 0 →
    deriv (perChar φ) z ≠ 0 → deriv (perChar φ) w ≠ 0 →
    deriv (discrim φ) z ≠ 0 ∧ deriv (discrim φ) w ≠ 0 ∧
    kernelPoisson38 (periodicKernel38 φ z) (periodicKernel38 φ w) = 0

def NormingSpectralMutualTarget : Prop :=
  ∀ (φ : PotPair) (z w : ℂ),
    kernelPoisson38 (normingKernel38 φ z) (normingKernel38 φ w) = 0

def ComplexKappaLocalDerivativeTarget : Prop :=
  ∀ (φ : PotPair) (z : ℂ), dirichletChar φ z = 0 → deriv (dirichletChar φ) z ≠ 0 →
    normingFactor φ z ≠ 0 ∧
    ∃ (U : Set PotPair) (ρ : PotPair → ℂ),
      IsOpen U ∧ φ ∈ U ∧ AnalyticOnNhd ℂ ρ U ∧ ρ φ=z ∧
      (∀ ψ ∈ U, dirichletChar ψ (ρ ψ)=0 ∧ normingFactor ψ (ρ ψ) ≠ 0 ∧
        normingFactor ψ (ρ ψ) / normingFactor φ z ∈ Complex.slitPlane) ∧
      HasFDerivAt ρ (dirImplicitGradient φ z) φ ∧
      AnalyticOnNhd ℂ (relativeKappa38 φ z ρ) U ∧ relativeKappa38 φ z ρ φ=0 ∧
      (∀ ψ ∈ U, Complex.exp (relativeKappa38 φ z ρ ψ / 2) =
        normingFactor ψ (ρ ψ) / normingFactor φ z) ∧
      HasFDerivAt (relativeKappa38 φ z ρ) (kappaCLM38 φ z) φ

def ComplexKappaBracketsTarget : Prop :=
  ∀ (φ : PotPair) (z w : ℂ),
    dirichletChar φ z=0 → dirichletChar φ w=0 →
    deriv (dirichletChar φ) z ≠ 0 → deriv (dirichletChar φ) w ≠ 0 →
    normingFactor φ z ≠ 0 ∧ normingFactor φ w ≠ 0 ∧
    Q (state φ z ![1,1]) ≠ 0 ∧ Q (state φ w ![1,1]) ≠ 0 ∧
    kernelPoisson38 (kappaKernel38 φ z) (dirEigenKernel38 φ w) = (if z=w then 1 else 0) ∧
    kernelPoisson38 (dirEigenKernel38 φ z) (kappaKernel38 φ w) = -(if z=w then 1 else 0) ∧
    kernelPoisson38 (kappaKernel38 φ z) (kappaKernel38 φ w) = 0

def RealCanonicalNormingTarget : Prop :=
  (∀ n : ℤ, AnalyticOnNhd ℝ (fun u : PhysicalL2 => realKappa38 u n) univ) ∧
  ∀ (u : PhysicalL2) (n : ℤ),
    0 < signedNorming38 u n ∧
    (normingFactor (realSlice u) (gkMu u n : ℂ)).im=0 ∧
    normingFactor (realSlice u) (gkMu u n : ℂ) ≠ 0 ∧
    Real.exp (realKappa38 u n / 2) = signedNorming38 u n ∧
    HasFDerivAt (fun v : PhysicalL2 => realKappa38 v n) (realKappaCLM38 u n) u ∧
    realSlice (kernelHamField38 (kappaKernel38 (realSlice u) (gkMu u n : ℂ))).1 =
      kernelHamField38 (kappaKernel38 (realSlice u) (gkMu u n : ℂ))

def RealCanonicalKappaBracketsTarget : Prop :=
  ∀ (u : PhysicalL2) (m n : ℤ),
    kernelPoisson38 (kappaKernel38 (realSlice u) (gkMu u m : ℂ))
      (dirEigenKernel38 (realSlice u) (gkMu u n : ℂ)) = (if m=n then 1 else 0) ∧
    kernelPoisson38 (dirEigenKernel38 (realSlice u) (gkMu u m : ℂ))
      (kappaKernel38 (realSlice u) (gkMu u n : ℂ)) = -(if m=n then 1 else 0) ∧
    kernelPoisson38 (kappaKernel38 (realSlice u) (gkMu u m : ℂ))
      (kappaKernel38 (realSlice u) (gkMu u n : ℂ)) = 0 ∧
    (fderiv ℝ (fun v : PhysicalL2 => realKappa38 v m) u)
      (kernelHamField38 (dirEigenKernel38 (realSlice u) (gkMu u n : ℂ))).1 =
        (if m=n then 1 else 0) ∧
    (fderiv ℝ (fun v : PhysicalL2 => gkMu v m) u)
      (kernelHamField38 (kappaKernel38 (realSlice u) (gkMu u n : ℂ))).1 =
        -(if m=n then 1 else 0) ∧
    (fderiv ℝ (fun v : PhysicalL2 => realKappa38 v m) u)
      (kernelHamField38 (kappaKernel38 (realSlice u) (gkMu u n : ℂ))).1 = 0

def FreeKappaCalibrationTarget : Prop :=
  realKappa38 0 0=0 ∧ normingFactor 0 0=1 ∧ normingSpectral38 0 0=0 ∧
  (∀ t : Time, normingKernel38 0 0 t = ![Complex.I/2,-Complex.I/2] ∧
    kappaKernel38 0 0 t = ![Complex.I,-Complex.I]) ∧
  kernelHamField38 (dirEigenKernel38 0 0) = realSlice (constL2 (-Complex.I/2)) ∧
  kernelPoisson38 (kappaKernel38 0 0) (dirEigenKernel38 0 0) = 1 ∧
  kernelPoisson38 (dirEigenKernel38 0 0) (kappaKernel38 0 0) = -1 ∧
  HasFDerivAt (fun v : PhysicalL2 => realKappa38 v 0) (realKappaCLM38 0 0) 0 ∧
  (fderiv ℝ (fun v : PhysicalL2 => realKappa38 v 0) 0) (constL2 (-Complex.I/2)) = 1

end
end NlsGge.GK38.PoissonMixed38
