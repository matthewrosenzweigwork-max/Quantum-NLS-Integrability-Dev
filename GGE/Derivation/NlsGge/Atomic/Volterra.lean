import NlsGge.GK38.PairVolterraDefs

/-! Homogeneous free-kernel Volterra terms on arbitrary finite intervals.
Each matrix entry is integrated as a complex scalar, following the existing
unit-interval implementation. The actual potential specialization uses exactly
its existing chosen representatives and coefficient signs. Integrability and
norm estimates are separate proof obligations. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace NlsGge.Atomic.Volterra

open NlsGge.GK38 NlsGge.SpectralFoundations

/-- The source potential coefficient after solving the ZS equation for the derivative. -/
def rawPotCoeff38 (a b : ℝ → ℂ) (s : ℝ) : PairMat38 :=
  !![0, Complex.I * a s; -(Complex.I * b s), 0]

/-- The n-th homogeneous term, recursively integrating its scalar entries. -/
def freeKernelVolterraTerm38 (a b : ℝ → ℂ) (z : ℂ) : ℕ → ℝ → PairMat38
  | 0, t => freeZsFundamentalComplex z t
  | n + 1, t => fun i j => ∫ s in (0 : ℝ)..t,
      (freeZsFundamentalComplex z (t - s) * rawPotCoeff38 a b s *
        freeKernelVolterraTerm38 a b z n s) i j

/-- The local source L2 pair norm; its use as a norm requires t>=0 and L2 integrability. -/
def pairL2NormOn38 (a b : ℝ → ℂ) (t : ℝ) : ℝ :=
  Real.sqrt (∫ s in (0 : ℝ)..t, ‖a s‖ ^ 2 + ‖b s‖ ^ 2)

/-- Actual PotPair specialization, with the same representatives as potCoeff38. -/
def potentialVolterraTerm38 (φ : PotPair) (z : ℂ) (n : ℕ) (t : ℝ) : PairMat38 :=
  freeKernelVolterraTerm38 (potRepFst38 φ) (potRepSnd38 φ) z n t

/-- Local L2 norm of the same actual potential pair representatives. -/
def potentialL2NormOn38 (φ : PotPair) (t : ℝ) : ℝ :=
  pairL2NormOn38 (potRepFst38 φ) (potRepSnd38 φ) t

end NlsGge.Atomic.Volterra
