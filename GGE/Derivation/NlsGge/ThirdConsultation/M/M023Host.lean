import Mathlib
import NlsGge.Atomic.KST.KST003
import NlsGge.Atomic.KST.KST004
import NlsGge.GK38.Defs
import NlsGge.Atomic.M.M054
import NlsGge.ThirdConsultation.M.M021Host

/-!
# M-023 host: weighted Fourier-coordinate carrier bodies (proof development, AUTHOR; not self-reviewed)

Literal copy of the Pro round 10 section 3 "Literal scalar and coordinate bodies"
(`PRO_DEFINITION_RESPONSE_FP80_10.md`, commit 178f84d6; also DEFINITIONS/M.lean.md, round 10 section).
Definitions only; no hypothesis, no proof content.
-/

set_option autoImplicit false

open scoped ENNReal BigOperators

namespace NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
noncomputable section

-- Distinct roles; both are ordinary fixed complete complex Hilbert spaces.
abbrev PotentialCode (_w : ℤ → ℝ) :=
  lp (fun _ : Bool × ℤ => ℂ) 2

abbrev SourceCode (_w : ℤ → ℝ) (_n : ℤ) :=
  lp (fun _ : Bool × ℤ => ℂ) 2

-- The source ;n norm is the round-9 false branch.
def shiftWeight (w : ℤ → ℝ) (n : ℤ) (b : Bool) (k : ℤ) : ℝ :=
  if b then w (k - n) else w (k + n)

-- a(b,k) is w(2k) times the ordinary period-one coefficient.
-- Its genuine doubled-circle coefficient vanishes at every odd mode.
def potentialRaw (w : ℤ → ℝ) (a : PotentialCode w)
    (b : Bool) (k : ℤ) : ℂ :=
  if Even k then a (b, k / 2) / (w k : ℂ) else 0

def RepresentsPotential (w : ℤ → ℝ) (a : PotentialCode w)
    (φ : NlsGge.GK38.PotPair) : Prop :=
  ∀ b : Bool, ∀ k : ℤ,
    a (b, k) = (w (2 * k) : ℂ) *
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientPair
        φ b (2 * k)

def RepresentsSource (w : ℤ → ℝ) (n : ℤ) (x : SourceCode w n)
    (f : NlsGge.Atomic.KST003.KSTPairL2) : Prop :=
  ∀ b : Bool, ∀ k : ℤ,
    x (b, k) = (shiftWeight w n b k : ℂ) *
      NlsGge.ThirdConsultation.MTwoMode.coefficientPair f b k

def kernel (w : ℤ → ℝ) (n : ℤ) (lam : ℂ)
    (a : PotentialCode w) (x : SourceCode w n) (j : Bool × ℤ) : ℂ :=
  (shiftWeight w n j.1 j.2 : ℂ) *
    ∑' l : ℤ, potentialRaw w a j.1 (j.2 - l) *
      (NlsGge.Atomic.KST004.complementaryResolventCoeff
        n lam (if j.1 then l else -l) *
          (x (!j.1, l) / (shiftWeight w n (!j.1) l : ℂ)))

def evenNeumann {w : ℤ → ℝ} {n : ℤ}
    (T : SourceCode w n →L[ℂ] SourceCode w n) :
    SourceCode w n →L[ℂ] SourceCode w n :=
  ∑' j : ℕ, (T * T) ^ j

def fullNeumann {w : ℤ → ℝ} {n : ℤ}
    (T : SourceCode w n →L[ℂ] SourceCode w n) :
    SourceCode w n →L[ℂ] SourceCode w n :=
  (1 + T) * evenNeumann T

def strictDomain (w : ℤ → ℝ) (n : ℤ) :
    Set (ℂ × PotentialCode w) :=
  {p | p.1 ∈ NlsGge.Atomic.KST004.spectralStrip n ∧
    8 * ‖p.2‖ ^ 2 < NlsGge.Atomic.M.M054.indexWeight n}

end
end NlsGge.ThirdConsultation.MTwoMode.WeightedInverse
