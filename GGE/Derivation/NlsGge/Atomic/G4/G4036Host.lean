import Mathlib
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.Atomic.G4.G4017
import NlsGge.Atomic.G4.G4024
import NlsGge.Atomic.G4.G4027
import NlsGge.ThirdConsultation.G4.Basic
import NlsGge.Atomic.G5.G5001Host

/- G4036 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4036Host.lean.
   Bodies from Pro round 9 section 11 (DEFINITIONS/G4.lean.md, unchanged in round 10 section 9) with one lexical
   edit (binder `λ` renamed `lam`: `λ` is a Lean keyword). `terminalRoot` is already landed byte-identically in
   NlsGge/Atomic/G5/G5001Host.lean (imported, not redeclared). normalizedZeta/localRoot (G4NormalizedHost),
   sheetSign (G4017), slitRoot/slitPrimitive (G4024), elementarySlitIntegral (G4027), elementaryEtaIntegral
   (ThirdConsultation/G4/Basic) are landed and imported. Pro round 10 section 9: the landed public
   `cartesianX`/`cartesianY` (G5033Host) are preserved; the section 11 assembly is hosted under the distinct names
   `cartesianXNative`/`cartesianYNative`. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def zetaDividedDifference (n : ℤ) (φ : PotPair) (lam : ℂ) : ℂ :=
  if lam = tauN φ n then deriv (normalizedZeta n φ) (tauN φ n)
  else (normalizedZeta n φ (tauN φ n) - normalizedZeta n φ lam) /
    (tauN φ n - lam)

def constantEtaCorrection (n : ℤ) (φ : PotPair) : ℂ :=
  (normalizedZeta n φ (tauN φ n) - 1) * elementaryEtaIntegral n φ

def localRootAtDirichlet (n : ℤ) (φ : PotPair) : ℂ :=
  if h : lamPlus φ n = lamMinus φ n then tauN φ n - muSeq φ n
  else (lamPlus φ n - lamMinus φ n) / 2 *
    slitRoot (2 * (muSeq φ n - tauN φ n) /
      (lamPlus φ n - lamMinus φ n))

-- Compact, nested Cauchy integral: no chosen antiderivative or improper
-- integral is hidden in the definition.
def ownCorrection (n : ℤ) (φ : PotPair) (lam : ℂ) : ℂ :=
  let c : ℂ := discC φ n
  let r : ℝ := discR φ n
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi,
      (((∫ t : ℝ in (0 : ℝ)..θ,
          deriv (circleMap c r) t *
            ((normalizedZeta n φ (circleMap c r t) - 1) /
              standardRoot φ n (circleMap c r t))) /
          standardRoot φ n (circleMap c r θ)) *
        deriv (circleMap c r) θ / (circleMap c r θ - lam)))

def regularEtaIntegral (n : ℤ) (φ : PotPair) : ℂ :=
  localRootAtDirichlet n φ * ownCorrection n φ (muSeq φ n) -
    constantEtaCorrection n φ

def cartesianZExtended (n : ℤ) (a : ℤ) (φ : PotPair) : ℂ :=
  if a = 1 then
    (2 * (tauN φ n - muSeq φ n) + 2 * terminalRoot n φ) *
      Complex.exp (-(terminalRoot n φ *
        ownCorrection n φ (muSeq φ n)))
  else
    (2 * (tauN φ n - muSeq φ n) - 2 * terminalRoot n φ) *
      Complex.exp (terminalRoot n φ *
        ownCorrection n φ (muSeq φ n))

abbrev cartesianZ := cartesianZExtended

def cartesianXNative (n : ℤ) (φ : PotPair) : ℂ :=
  (xiN38 n φ / (Real.sqrt 8 : ℂ)) *
    (cartesianZExtended n 1 φ * Complex.exp (Complex.I * betaSum n φ) +
      cartesianZExtended n (-1) φ * Complex.exp (-Complex.I * betaSum n φ))

def cartesianYNative (n : ℤ) (φ : PotPair) : ℂ :=
  (xiN38 n φ / ((Real.sqrt 8 : ℂ) * Complex.I)) *
    (cartesianZExtended n 1 φ * Complex.exp (Complex.I * betaSum n φ) -
      cartesianZExtended n (-1) φ * Complex.exp (-Complex.I * betaSum n φ))

end
end NlsGge.GKDefinitionDesign
