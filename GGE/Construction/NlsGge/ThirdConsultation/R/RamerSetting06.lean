import Mathlib
import NlsGge.ThirdConsultation.R.Round4Core
import NlsGge.Atomic.R.R018
import NlsGge.Atomic.R.R023
import NlsGge.Atomic.R.R040
import NlsGge.Atomic.R.R053
import NlsGge.Ramer.FiniteGaussian
import NlsGge.Ramer.RamerStep8a
import NlsGge.Ramer.CylindricalDivergence
import NlsGge.Ramer.SpaceTransfer

                                                                                                                         
                                                                                                                           
                                                                                                                                   
                                                                                                                   
                                                               
                                                                                                                       
                             
set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

def localDomain
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (ε : ℝ) : Set (RamerE c s) :=
  Metric.closedBall (0 : RamerE c s) ε

abbrev Step8Hyp
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (L : RamerE c s → RamerH c) (ε : ℝ) : Prop :=
  NlsGge.Ramer.Step8Hyp c s hs L ε

section ActualRamerSetting
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "μ" => ramerGaussian c s
local notation "i" => cmEmbedding c s hs
local notation "P" => NlsGge.Ramer.headProj c
local notation "Q" => ambientProjection c s
local notation "J" => ramerJac c s hs
local notation "Smap" => TM c s hs

def hgrad (η : E → ℝ) (x : E) : H :=
  (InnerProductSpace.toDual ℝ H).symm ((fderiv ℝ η x).comp i)

def ProductRuleClass (η : E → ℝ) : Prop :=
  ContDiff ℝ 2 η ∧
    ∃ B : ℝ, ∀ x : E, ‖η x‖ ≤ B ∧ ‖hgrad c s hs η x‖ ≤ B

def ramerApprox (K : E → H) (N : ℕ) (x : E) : ℝ :=
  NlsGge.Ramer.ramerA c s (le_of_lt (lt_trans (by norm_num) hs))
    N K (NlsGge.Ramer.coordE c s x)

def literalCylDiv (K : E → H) (N : ℕ) (x : E) : ℝ :=
  NlsGge.Ramer.cylDiv c N (NlsGge.Ramer.truncField c s K N)
    (NlsGge.Ramer.coordE c s x)

def LocalRamerApproxLimit (K : E → H) (d : E → ℝ) : Prop :=
  ∀ x₀ : E, ∃ r : ℝ, 0 < r ∧
    Tendsto (fun N : ℕ => eLpNorm
      ((ball x₀ r).indicator (fun x : E => ramerApprox c s hs K N x - d x))
      2 μ) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => eLpNorm
      ((ball x₀ r).indicator (fun x : E => literalCylDiv c s K N x - d x))
      2 μ) atTop (𝓝 0)

def SmallFibreField (Φ : E → H) (ε : ℝ) : Prop :=
  0 < ε ∧
    (∀ y ∈ closedBall (0 : E) ε, DifferentiableAt ℝ Φ y) ∧
    (∀ y ∈ closedBall (0 : E) ε, ‖i (Φ y)‖ ≤ ε / 4) ∧
    (∀ y ∈ closedBall (0 : E) ε, ‖HDeriv i Φ y‖ ≤ (1 / 2 : ℝ))

def finiteLevelLocalJacobi
    (ε : ℝ) (T : E → E) (density : E → ℝ) : Prop :=
  ∀ f : E → ℝ, Measurable f →
    (∫⁻ y in ball (0 : E) (ε / 2), ENNReal.ofReal (f y) ∂μ) =
      ∫⁻ x in localDomain c s ε ∩ T ⁻¹' ball (0 : E) (ε / 2),
        ENNReal.ofReal (f (T x)) * ENNReal.ofReal (density x) ∂μ

def RamerHomeomorphismData
    (T : E ≃ₜ E) (K Kinv : E → H) : Prop :=
  ContDiff ℝ 2 K ∧ ContDiff ℝ 2 Kinv ∧
    (∀ x : E, T x = Smap K x) ∧
    (∀ y : E, T.symm y = Smap Kinv y)

def IsSmallInverse (L : E → H) (ε : ℝ) (F : E → E) : Prop :=
  ∀ z ∈ ball (0 : E) (ε / 2),
    F z ∈ closedBall (0 : E) ε ∧ F z + i (L (F z)) = z

structure NormalizationChart where
  linear : E ≃L[ℝ] E
  e₁ : H
  e₂ : H
  radius : ℝ
  fieldBound : ℝ

def normalizedField
    (T : E ≃ₜ E) (K Kinv : E → H) (x₀ : E)
    (chart : NormalizationChart c s) (y : E) : H :=
  -chart.e₁ - chart.e₂ + K (y - i chart.e₁) +
    fderiv ℝ Kinv (T x₀)
      (y - i chart.e₁ + i (K (y - i chart.e₁)))

def NormalizedSmallDerivativeChart
    (T : E ≃ₜ E) (K Kinv : E → H) (x₀ : E)
    (chart : NormalizationChart c s) : Prop :=
  0 < chart.radius ∧ 0 < chart.fieldBound ∧
    (∀ x : E, chart.linear x = x + i (fderiv ℝ K x₀ x)) ∧
    (∀ y : E, chart.linear.symm y = y + i (fderiv ℝ Kinv (T x₀) y)) ∧
    chart.e₂ = -chart.e₁ + K x₀ + fderiv ℝ Kinv (T x₀) (T x₀) ∧
    (∀ y : E,
      chart.linear.symm (T (y - i chart.e₁)) - i chart.e₂ =
        y + i (normalizedField c s hs T K Kinv x₀ chart y)) ∧
    ‖x₀ + i chart.e₁‖ < chart.radius / 2 ∧
    normalizedField c s hs T K Kinv x₀ chart (x₀ + i chart.e₁) = 0 ∧
    HDeriv i (normalizedField c s hs T K Kinv x₀ chart)
      (x₀ + i chart.e₁) = 0 ∧
    (∀ y ∈ ball (0 : E) chart.radius,
      ‖normalizedField c s hs T K Kinv x₀ chart y‖ < chart.fieldBound ∧
      ‖hsDerivH c s hs (normalizedField c s hs T K Kinv x₀ chart) y‖ <
        chart.fieldBound ∧
      ‖hsDerivH c s hs (normalizedField c s hs T K Kinv x₀ chart) y‖ <
        (1 / 8 : ℝ))

def EventuallyTruncNullPreserving (K : E → H) (U : Set E) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    ∀ A : Set E, μ A = 0 →
      μ (U ∩ (Smap (projField c s N K)) ⁻¹' A) = 0

def cylindricalDensity (K : E → H) (N : ℕ) (x : E) : ℝ :=
  NlsGge.Ramer.finiteRamerDensity
    (fun v : NlsGge.Ramer.actualCMHead c N =>
      v + NlsGge.Ramer.truncField c s K N v)
    (NlsGge.Ramer.headPt c N (NlsGge.Ramer.coordE c s x))

def jacobianWithDiv (K : E → H) (d : E → ℝ) (x : E) : ℝ :=
  |NlsGge.Analysis.RegularizedDeterminant.det2 (hsDerivH c s hs K x)| *
    Real.exp (-d x - ‖K x‖ ^ 2 / 2)

end ActualRamerSetting

def NullPreservingOn
    {X : Type*} [MeasurableSpace X]
    (γ : Measure X) (T : X → X) (U : Set X) : Prop :=
  ∀ A : Set X, γ A = 0 → γ (U ∩ T ⁻¹' A) = 0

def C1DiffeomorphOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V → V) (U W : Set V) : Prop :=
  IsOpen U ∧ IsOpen W ∧ Set.BijOn T U W ∧
    ContDiffOn ℝ 1 T U ∧
    ∀ x ∈ U, IsUnit (fderiv ℝ T x)

def gaussianIntegral
    (d : ℕ) (U : Set (GaussianFiniteCarrier d))
    (f : GaussianFiniteCarrier d → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in U, ENNReal.ofReal (f x)
    ∂NlsGge.Ramer.finiteStdGaussian (GaussianFiniteCarrier d)

def CountableLocalDensityConvergence
    {X : Type*} [MeasurableSpace X] (γ : Measure X)
    (JN : ℕ → X → ℝ) (Jlim : X → ℝ) : Prop :=
  ∃ U : ℕ → Set X,
    (∀ k : ℕ, MeasurableSet (U k)) ∧
    γ ((⋃ k : ℕ, U k)ᶜ) = 0 ∧
    ∀ k : ℕ, TendstoInMeasure (γ.restrict (U k)) JN atTop Jlim

end
end NlsGge.ThirdConsultation.R
