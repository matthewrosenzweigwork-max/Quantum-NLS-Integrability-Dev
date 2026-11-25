import NlsGge.Atomic.KST.KST006
import NlsGge.GK38.Defs

/-!
# M-021 host: section-8 objects (proof development, author; not self-reviewed)

Definitions only, copied from Pro rounds 7-8 section 8
(`PRO_DEFINITION_RESPONSE_FP80_07_08.md`, M-021). The single lexical addition is
`open NlsGge.Analysis`, which `naturalPhysicalCoverL2` needs. No hypothesis is added.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open NlsGge.Pilot NlsGge.GK38 NlsGge.Schur
open NlsGge.Analysis
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004

namespace NlsGge.ThirdConsultation.MTwoMode
noncomputable section

abbrev CoefficientPair := Bool → ℤ → ℂ

def coefficientPair (f : KSTPairL2) : CoefficientPair :=
  fun b k => fourierCoeff (f b) k

def potentialCoefficientPair (φ : PotPair) : CoefficientPair :=
  fun b k => fourierCoeff
    (naturalPhysicalCoverL2 (if b then φ.1 else φ.2)) k

def T (φ : PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    KSTPairL2 →L[ℂ] KSTPairL2 :=
  NlsGge.Atomic.KST006.qOperator
    (WithLp.toLp 2 (fun b : Bool => if b then φ.1 else φ.2))
    n lam hlam

def Tcoeff (φ : PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (f : KSTPairL2) : CoefficientPair :=
  coefficientPair (T φ n lam hlam f)

def potentialCoefficientEnergy (w : ℤ → ℝ) (φ : PotPair) : ℝ≥0∞ :=
  ∑' k : ℤ, ENNReal.ofReal
    (w k ^ 2 *
      (‖potentialCoefficientPair φ true k‖^2 +
        ‖potentialCoefficientPair φ false k‖^2))

def potentialCoefficientNorm (w : ℤ → ℝ) (φ : PotPair) : ℝ :=
  Real.sqrt (potentialCoefficientEnergy w φ).toReal

def shiftedPairEnergy (w : ℤ → ℝ) (n : ℤ) (i : Bool)
    (f : CoefficientPair) : ℝ≥0∞ :=
  let s : ℤ := if i then n else -n
  ∑' k : ℤ, ENNReal.ofReal
    (w (k+s)^2 * ‖f true k‖^2 +
      w (k-s)^2 * ‖f false k‖^2)

def shiftedPairNorm (w : ℤ → ℝ) (n : ℤ) (i : Bool)
    (f : CoefficientPair) : ℝ :=
  Real.sqrt (shiftedPairEnergy w n i f).toReal

end
end NlsGge.ThirdConsultation.MTwoMode
