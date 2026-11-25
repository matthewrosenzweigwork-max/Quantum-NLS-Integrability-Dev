import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.KSPS.Round5

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.Common NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSRiccati
noncomputable section

def sidePotential {N : ℕ} (φ : SobolevC N) (b : Bool) : PhysicalL2 :=
  if b then (toPotPair φ).2 else (toPotPair φ).1

def sideInput {N : ℕ} (φ : SobolevC N) (b : Bool) : PhysicalL2 :=
  if b then (toPotPair φ).1 else (toPotPair φ).2

def coefficient {N : ℕ} (φ : SobolevC N) (b : Bool) (k : ℕ) : PhysicalL2 :=
  if b then
    ((-1 : ℂ) ^ (k + 1)) •
      wkbR ((toPotPair φ).2, (toPotPair φ).1) k
  else wkbR (toPotPair φ) k

def left {N : ℕ} (φ : SobolevC N) (k : ℕ) : PhysicalL2 :=
  coefficient φ false k

def right {N : ℕ} (φ : SobolevC N) (k : ℕ) : PhysicalL2 :=
  coefficient φ true k

def signedDerivative (b : Bool) (f : PhysicalL2) : PhysicalL2 :=
  if b then -weakDerivative f else weakDerivative f

def recurrenceProduct {N : ℕ} (φ : SobolevC N) (b : Bool) (k : ℕ) : PhysicalL2 :=
  ∑ j ∈ Finset.Icc 1 (k - 1),
    physicalProduct (coefficient φ b j) (coefficient φ b (k - j))

def nonlinearTop {N : ℕ} (φ : SobolevC N) (b : Bool) : PhysicalL2 :=
  coefficient φ b (N + 1) -
    (if b then ((-1 : ℂ) ^ (N + 1)) • physicalSobolevDerivative38 N φ.1
     else -physicalSobolevDerivative38 N φ.2)

def «partial» {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) : PhysicalL2 :=
  ∑ k ∈ Finset.Icc 1 N,
    ((2 * Complex.I * lam) ^ k)⁻¹ • coefficient φ b k

def rho {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) : PhysicalL2 :=
  signedDerivative b («partial» φ b lam) -
    (2 * Complex.I * lam) • «partial» φ b lam +
    physicalProduct (sidePotential φ b)
      (physicalProduct («partial» φ b lam) («partial» φ b lam)) - sideInput φ b

def quadratic {N : ℕ} (φ : SobolevC N) (b : Bool) (j : ℕ) : PhysicalL2 :=
  physicalProduct (sidePotential φ b)
    (∑ k ∈ Finset.Icc 1 N, ∑ l ∈ Finset.Icc 1 N,
      if k + l = j then
        physicalProduct (coefficient φ b k) (coefficient φ b l)
      else 0)

def rhoTail {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) : PhysicalL2 :=
  ((2 * Complex.I * lam) ^ N)⁻¹ • coefficient φ b (N + 1) +
    ∑ j ∈ Finset.Icc (N + 1) (2 * N),
      ((2 * Complex.I * lam) ^ j)⁻¹ • quadratic φ b j

def «prefix» {N : ℕ} (φ : SobolevC N) (b : Bool) (k : ℕ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..x,
    coverRep38 (sidePotential φ b) t * coverRep38 (coefficient φ b k) t

def massPrefix {N : ℕ} (φ : SobolevC N) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..x,
    potRepFst38 (toPotPair φ) t * potRepSnd38 (toPotPair φ) t

def phaseFactor {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((if b then (-1 : ℂ) else 1) *
    ∑ k ∈ Finset.Icc 1 N,
      ((2 * Complex.I * lam) ^ k)⁻¹ * «prefix» φ b k x)

def forcing {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ) : ℂ :=
  (2 * Complex.I * lam) ^ N * phaseFactor φ b lam x * coverRep38 (rho φ b lam) x

def a1 {N : ℕ} (φ : SobolevC N) (b : Bool) (x : ℝ) : ℂ :=
  coverRep38 (quadratic φ b (N + 1)) x +
    (if b then (1 : ℂ) else -1) *
      coverRep38 (coefficient φ b (N + 1)) x * massPrefix φ x

def a2 {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) (x : ℝ) : ℂ :=
  (2 * Complex.I * lam) ^ 2 *
    (forcing φ b lam x - coverRep38 (coefficient φ b (N + 1)) x -
      (2 * Complex.I * lam)⁻¹ * a1 φ b x)

def intervalMeasure : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

end
end NlsGge.ThirdConsultation.KSPSRiccati
