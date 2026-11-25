import Mathlib
import QuantumNLS.ResetNormalizationBinding

/-!
# LOCAL-022: uniqueness of the reset normalization

Source: `source-text/chapters/local/local_covariance.tex`,
`thm:reset-normalization-uniqueness` (statement and proof beginning at line 219).

This is the source-facing statement on the physical `L²` ball.  The exact indexed
mass is represented by a functional `q n u`; its zero-field value and its two
chart identities are stated explicitly so this theorem does not depend on the
in-progress strict-phase to monotone-phase bridge for DEF-014.  The accepted
Fourier isometry, sequence space, real symplectic form, and physical map
`Cphys L u = conj (u (-·))` are reused from the existing interfaces.

`IsStronglySymplecticOn` records the canonical diffeomorphism on the two open
balls.  Real analyticity is stated, as in the source.  The proof uses the
differentiability supplied by the canonical structure; it does not need higher
smoothness.  The imported rigidity proof follows the source: the transition
preserves each coordinate action; symplectic differentiation intertwines its
Hamiltonian vector field; uniqueness of the coordinate-rotation ODE gives
rotation commutation; conjugation and the derivative at zero fix the
nonnegative real sequences; finite-coordinate rotations and `ℓ²` density give
the result everywhere in the ball.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory AddCircle InnerProductSpace ComplexConjugate

namespace QuantumNLS.ResetNormalizationUniquenessLOCAL022

open QuantumNLS.ResetNormalizationUniqueness

/-- **LOCAL-022 `thm:reset-normalization-uniqueness`.**

Let `q n u` be the DEF-014 indexed mass functional.  Two real-analytic
canonical maps from the same full physical `L²` ball onto the same sequence
ball, with squared coordinate moduli `q n u`, Fourier derivative at zero, and
the source reflection-conjugation symmetry, agree on that ball.  The only
mass-side interface used here is `q n 0 = 0` and the two exact modulus
identities; no compatibility theorem is assumed.
-/
theorem thm_reset_normalization_uniqueness
    (L : ℝ) [Fact (0 < L)] {r : ℝ} (hr : 0 < r)
    (q : ℤ → Lp ℂ 2 (volume : Measure (AddCircle L)) → ℝ)
    (hq0 : ∀ n, q n 0 = 0)
    (Φ₁ Φ₂ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ)
    (hΦ₁ : IsStronglySymplecticOn
      (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₁)
    (hΦ₂ : IsStronglySymplecticOn
      (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₂)
    (han₁ : AnalyticOnNhd ℝ Φ₁
      (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (han₂ : AnalyticOnNhd ℝ Φ₂
      (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (hm₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      ∀ n, ‖Φ₁ u n‖ ^ 2 = q n u)
    (hm₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      ∀ n, ‖Φ₂ u n‖ ^ 2 = q n u)
    (hD₁ : ∀ h, fderiv ℝ Φ₁ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hD₂ : ∀ h, fderiv ℝ Φ₂ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hsym₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₁ (Cphys L u) = star (Φ₁ u))
    (hsym₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₂ (Cphys L u) = star (Φ₂ u)) :
    ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₁ u = Φ₂ u := by
  exact reset_normalization_uniqueness_phys L hr q hq0 Φ₁ Φ₂ hΦ₁ hΦ₂
    han₁ han₂ hm₁ hm₂ hD₁ hD₂ hsym₁ hsym₂

end QuantumNLS.ResetNormalizationUniquenessLOCAL022

#print axioms QuantumNLS.ResetNormalizationUniquenessLOCAL022.thm_reset_normalization_uniqueness
