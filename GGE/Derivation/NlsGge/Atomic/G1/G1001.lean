import NlsGge.Spectral.FreeZakharovShabatFundamentalComplexV4
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
The alternating phase on a finite ordered time simplex lies in the original
time interval.  The corresponding free Zakharov--Shabat propagator therefore
has the source exponential bound in the matrix `L²` operator norm.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.L2Operator

namespace NlsGge.Atomic.G1

/-- A descending finite list of times in `[0, upper]`. -/
def OrderedSimplexFrom (upper : ℝ) : List ℝ → Prop
  | [] => True
  | x :: xs => 0 ≤ x ∧ x ≤ upper ∧ OrderedSimplexFrom x xs

/-- The times `ts` satisfy `0 ≤ tₙ ≤ ⋯ ≤ t₁ ≤ t`. -/
def OrderedSimplex (t : ℝ) (ts : List ℝ) : Prop :=
  0 ≤ t ∧ OrderedSimplexFrom t ts

/-- The nested alternating sum `2t₁ - 2t₂ + ⋯` for a descending list. -/
def alternatingTail : List ℝ → ℝ
  | [] => 0
  | x :: xs => 2 * x - alternatingTail xs

/-- The source phase `t - 2t₁ + 2t₂ - ⋯` of a Volterra iterate. -/
def alternatingPhase (t : ℝ) (ts : List ℝ) : ℝ :=
  t - alternatingTail ts

theorem alternatingTail_bounds {upper : ℝ} {ts : List ℝ}
    (hupper : 0 ≤ upper) (h : OrderedSimplexFrom upper ts) :
    0 ≤ alternatingTail ts ∧ alternatingTail ts ≤ 2 * upper := by
  induction ts generalizing upper with
  | nil => simp [alternatingTail, hupper]
  | cons x xs ih =>
      rcases h with ⟨hx0, hxUpper, hxs⟩
      have htail := ih hx0 hxs
      constructor <;> simp only [alternatingTail] <;> nlinarith

/-- The alternating Volterra phase remains in `[-t,t]`. -/
theorem simplex_phase_bound {t : ℝ} {ts : List ℝ}
    (hord : OrderedSimplex t ts) : |alternatingPhase t ts| ≤ t := by
  rcases hord with ⟨ht, hts⟩
  rcases alternatingTail_bounds ht hts with ⟨hlo, hhi⟩
  rw [abs_le]
  constructor <;> dsimp [alternatingPhase] <;> nlinarith

/-- The free propagator evaluated at the alternating simplex phase. -/
def freeSimplexPropagator (z : ℂ) (t : ℝ) (ts : List ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  NlsGge.SpectralFoundations.freeZsFundamentalComplex z
    (alternatingPhase t ts)

private theorem freeSimplexExpBound {z : ℂ} {t phase : ℝ}
    (hphase : |phase| ≤ t) :
    ‖Complex.exp (phase • (-Complex.I * z))‖ ≤ Real.exp (|z.im| * t) ∧
      ‖Complex.exp (phase • (Complex.I * z))‖ ≤ Real.exp (|z.im| * t) := by
  have hfirst : (phase • (-Complex.I * z)).re ≤ |z.im| * t := by
    have hmul : phase * z.im ≤ |phase| * |z.im| := by
      calc
        phase * z.im ≤ |phase * z.im| := le_abs_self _
        _ = |phase| * |z.im| := abs_mul phase z.im
    have hscale : |phase| * |z.im| ≤ t * |z.im| :=
      mul_le_mul_of_nonneg_right hphase (abs_nonneg _)
    have hre : (phase • (-Complex.I * z)).re = phase * z.im := by
      simp [Complex.mul_re]
    rw [hre]
    nlinarith [hscale]
  have hsecond : (phase • (Complex.I * z)).re ≤ |z.im| * t := by
    have hmul : -(phase * z.im) ≤ |phase| * |z.im| := by
      calc
        -(phase * z.im) ≤ |phase * z.im| := neg_le_abs _
        _ = |phase| * |z.im| := abs_mul phase z.im
    have hscale : |phase| * |z.im| ≤ t * |z.im| :=
      mul_le_mul_of_nonneg_right hphase (abs_nonneg _)
    have hre : (phase • (Complex.I * z)).re = -(phase * z.im) := by
      simp [Complex.mul_re]
    rw [hre]
    nlinarith [hscale]
  constructor <;> rw [Complex.norm_exp] <;>
    exact Real.exp_le_exp.mpr (by assumption)

/-- The free matrix propagator has norm at most `exp (|Im z| t)` on the
ordered simplex. The norm is the standard matrix `L²` operator norm. -/
theorem freeSimplexPropagator_norm_le {z : ℂ} {t : ℝ} {ts : List ℝ}
    (hord : OrderedSimplex t ts) :
    ‖freeSimplexPropagator z t ts‖ ≤ Real.exp (|z.im| * t) := by
  have hphase := simplex_phase_bound hord
  rcases freeSimplexExpBound hphase with ⟨h00, h11⟩
  rw [freeSimplexPropagator,
    NlsGge.SpectralFoundations.freeZsFundamentalComplex,
    NlsGge.SpectralFoundations.freeDiagonalCandidate,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).2
  intro i
  fin_cases i
  · simpa [Matrix.diagonal] using h00
  · simpa [Matrix.diagonal] using h11

end NlsGge.Atomic.G1
