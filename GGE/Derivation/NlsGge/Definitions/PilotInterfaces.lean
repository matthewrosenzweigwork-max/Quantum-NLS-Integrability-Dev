import Mathlib

/-!
Concrete conventions for the first cloud pilot. These declarations do not assert
the existence of the NLS Birkhoff map, spectral data, a Gibbs law, or a limit.
In particular the weighted membership predicates below are not Hilbert spaces;
their norms, completeness and Fourier realization remain separate obligations.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NlsGge.Pilot

/-- The physical circle has period one. -/
abbrev PhysicalCircle := AddCircle (1 : ℝ)

/-- Spatial integration uses the normalized Haar probability measure. -/
def spatialMeasure : Measure PhysicalCircle := AddCircle.haarAddCircle

/-- Actual equivalence classes of square-integrable physical fields. -/
abbrev PhysicalL2 : Type := Lp ℂ 2 spatialMeasure

/-- The ordinary Fourier coefficient uses the negative exponent in the integral.
Identities using this integral still require the relevant integrability proofs. -/
def physicalFourier (u : PhysicalCircle → ℂ) (n : ℤ) : ℂ :=
  fourierCoeff u n

/-- The linearized Birkhoff convention is minus the reflected Fourier coefficient. -/
def reflectedFourier (u : PhysicalCircle → ℂ) (n : ℤ) : ℂ :=
  -physicalFourier u (-n)

/-- All modes from -N through N, including the zero mode. -/
abbrev FourierPlane (N : ℕ) := Fin (2 * N + 1) → ℂ

def modeIndex (N : ℕ) (i : Fin (2 * N + 1)) : ℤ :=
  (i.val : ℤ) - (N : ℤ)

theorem modeIndex_bounds (N : ℕ) (i : Fin (2 * N + 1)) :
    -(N : ℤ) ≤ modeIndex N i ∧ modeIndex N i ≤ (N : ℤ) := by
  have hi := i.isLt
  dsimp [modeIndex]
  omega

theorem modeIndex_injective (N : ℕ) : Function.Injective (modeIndex N) := by
  intro i j hij
  apply Fin.ext
  dsimp [modeIndex] at hij
  omega

theorem modeIndex_covers (N : ℕ) (n : ℤ)
    (hlo : -(N : ℤ) ≤ n) (hhi : n ≤ (N : ℤ)) :
    ∃ i : Fin (2 * N + 1), modeIndex N i = n := by
  have hn : 0 ≤ n + (N : ℤ) := by omega
  refine ⟨⟨(n + (N : ℤ)).toNat, ?_⟩, ?_⟩
  · omega
  · dsimp [modeIndex]
    omega

def zeroMode (N : ℕ) : Fin (2 * N + 1) := ⟨N, by omega⟩

theorem modeIndex_zero (N : ℕ) : modeIndex N (zeroMode N) = 0 := by
  simp [modeIndex, zeroMode]

def reflectMode (N : ℕ) (i : Fin (2 * N + 1)) : Fin (2 * N + 1) :=
  ⟨2 * N - i.val, by have hi := i.isLt; omega⟩

theorem modeIndex_reflect (N : ℕ) (i : Fin (2 * N + 1)) :
    modeIndex N (reflectMode N i) = -modeIndex N i := by
  have hi := i.isLt
  dsimp [modeIndex, reflectMode]
  omega

theorem reflectMode_involutive (N : ℕ) : Function.Involutive (reflectMode N) := by
  intro i
  apply Fin.ext
  have hi := i.isLt
  dsimp [reflectMode]
  omega

/-- Minus reflection preserves the exact symmetric Fourier plane. -/
def reflectPlane (N : ℕ) (z : FourierPlane N) : FourierPlane N :=
  fun i => -z (reflectMode N i)

theorem reflectPlane_involutive (N : ℕ) : Function.Involutive (reflectPlane N) := by
  intro z
  funext i
  simp [reflectPlane, reflectMode_involutive N i]

/-- The concrete smooth trigonometric polynomial represented by these coordinates. -/
def planeField (N : ℕ) (z : FourierPlane N) (x : PhysicalCircle) : ℂ :=
  ∑ i : Fin (2 * N + 1), z i * fourier (modeIndex N i) x

/-- Ordinary product complex volume; no rescaling of planar Lebesgue measure. -/
def planeVolume (N : ℕ) : Measure (FourierPlane N) :=
  Measure.pi (fun _ : Fin (2 * N + 1) => (volume : Measure ℂ))

/-- Fixed interval parameters precede the coefficient sequence in uniform contracts. -/
def AdmittedCoefficients (cminus cplus : ℝ) (c : ℕ → ℝ) : Prop :=
  0 < cminus ∧ cminus ≤ cplus ∧ ∀ j : ℕ, cminus ≤ c j ∧ c j ≤ cplus

def japaneseBracket (n : ℤ) : ℝ := Real.sqrt (1 + (n : ℝ) ^ 2)

/-- Nonnegative full series retains infinity rather than totalizing it to zero. -/
def nonnegativeSeries (term : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∑' j : ℕ, term j

/-- A real value can only be obtained after proving finiteness. -/
def finiteSeriesValue (term : ℕ → ℝ≥0∞)
    (_hfinite : nonnegativeSeries term ≠ ⊤) : ℝ :=
  (nonnegativeSeries term).toReal

/-- Genuine weighted square-summability membership, with no fictitious norm.
Positivity of the supplied mode weights is a separate use-site obligation. -/
def WeightedSquareSummable (a : ℤ → ℝ) (s : ℝ) (x : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ =>
    a n * Real.rpow (japaneseBracket n) (-2 * s) * ‖x n‖ ^ 2)

/-- Ordinary sequence Sobolev membership for arbitrary real order. -/
def SobolevSquareSummable (r : ℝ) (x : ℤ → ℂ) : Prop :=
  Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * r) * ‖x n‖ ^ 2)

end NlsGge.Pilot
