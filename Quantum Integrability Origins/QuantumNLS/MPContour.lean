import Mathlib

/-!
# PROP-026 `lem:MP-linearization`: the contour family as a parameter space, weights and the uniform contour bookkeeping

New module.  Pure real/complex analysis.  The combined generator integrates over a finite union of C¹ contour pieces:

`Σ_i ∮_{piece i} ω_i(z) F(z) dz = Σ_i ∫_0^1 ω_i(γ_i τ) F(γ_i τ) γ_i'(τ) dτ`,

with `ω_i = p_t` on the pieces of the large contour `Γ_a` and `ω_i ≡ θ_n` on the pieces of the fixed contour `Γ_n`.
The parameter space is `Θ = Fin m × [0,1]` with `ν = count ⊗ Lebesgue` (finite measure, `Θ` compact), the contour point is
`z_θ = γ_i(τ)` and the complex weight of the operator integral is `u_θ = -(2πκ)⁻¹ ω_i(z_θ) γ_i'(τ)` (so that
`C_{0,N} = Re ∫ u_θ f_{z_θ}(S_N(z_θ)) dν`, `eq:MP-C0`).

* `Piece`, `ThetaSpace`, `nu`, `zθ`, `uθ`, `wθ = ‖uθ‖` and their continuity;
* `integral_theta`: `∫ g dν = Σ_i ∫_0^1 g(i,τ) dτ` for nonnegative bounded continuous `g`;
* **rectangle `Γ_a`**: the six affine pieces of the positively oriented rectangle with corners `±a`, heights `±h`, split at
  the real axis (where the background Cauchy transform jumps); `rect_weighted_length_le`: for `p_t(z) = Σ_{r∈R} t_r z^r`,
  `|t_r| ≤ T_r`, `r ≤ d`: `Σ_i ∫_0^1 |p_t(γ_i τ)| |γ_i'(τ)| dτ ≤ C_p (1+a)^{d+1}` with `C_p = 4 (Σ T_r)(1+h)^{d+1}`;
  this is the `W_a = (1+a)^{d+1}` growth of the source.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open MeasureTheory Set Filter unitInterval
open scoped Real

namespace QuantumNLS.MPContour

/-- One C¹ contour piece, parametrized by `τ ∈ [0,1]`, carrying a continuous weight `ω` (`p_t` or `θ_n`). -/
structure Piece where
  γ : ℝ → ℂ
  γ' : ℝ → ℂ
  ω : ℂ → ℂ
  hγ : ∀ τ, HasDerivAt γ (γ' τ) τ
  hγ' : Continuous γ'
  hω : Continuous ω

theorem Piece.continuous_γ (P : Piece) : Continuous P.γ :=
  continuous_iff_continuousAt.2 fun τ => (P.hγ τ).continuousAt

/-- The parameter space of `m` pieces. -/
abbrev ThetaSpace (m : ℕ) := Fin m × I

/-- `ν = count ⊗ Lebesgue`. -/
def nu (m : ℕ) : Measure (ThetaSpace m) := (Measure.count : Measure (Fin m)).prod (volume : Measure I)

instance (m : ℕ) : IsFiniteMeasure (nu m) := by
  unfold nu
  have : IsFiniteMeasure (Measure.count : Measure (Fin m)) := ⟨by simp⟩
  infer_instance

variable {m : ℕ}

def zθ (P : Fin m → Piece) (θ : ThetaSpace m) : ℂ := (P θ.1).γ θ.2

def uθ (κ : ℝ) (P : Fin m → Piece) (θ : ThetaSpace m) : ℂ :=
  -((((2 * Real.pi * κ)⁻¹ : ℝ) : ℂ)) * (P θ.1).ω (zθ P θ) * (P θ.1).γ' θ.2

def wθ (κ : ℝ) (P : Fin m → Piece) (θ : ThetaSpace m) : ℝ := ‖uθ κ P θ‖

theorem continuous_zθ (P : Fin m → Piece) : Continuous (zθ P) := by
  unfold zθ
  refine continuous_prod_of_discrete_left.2 (fun i => ?_)
  exact (P i).continuous_γ.comp continuous_subtype_val

theorem continuous_uθ (κ : ℝ) (P : Fin m → Piece) : Continuous (uθ κ P) := by
  unfold uθ
  refine continuous_prod_of_discrete_left.2 (fun i => ?_)
  have h1 : Continuous fun τ : I => (P i).γ τ := (P i).continuous_γ.comp continuous_subtype_val
  have h2 : Continuous fun τ : I => (P i).ω ((P i).γ τ) := (P i).hω.comp h1
  have h3 : Continuous fun τ : I => (P i).γ' τ := (P i).hγ'.comp continuous_subtype_val
  exact (continuous_const.mul h2).mul h3

theorem continuous_wθ (κ : ℝ) (P : Fin m → Piece) : Continuous (wθ κ P) :=
  (continuous_uθ κ P).norm

theorem integrable_of_continuous {g : ThetaSpace m → ℝ} (hg : Continuous g) : Integrable g (nu m) :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

/-- Integration over the parameter space is the sum over pieces of `∫_0^1`. -/
theorem integral_theta {g : ThetaSpace m → ℝ} (hg : Continuous g) :
    ∫ θ, g θ ∂(nu m) = ∑ i : Fin m, ∫ τ : I, g (i, τ) := by
  unfold nu
  rw [integral_prod _ (by simpa [nu] using integrable_of_continuous hg)]
  rw [integral_count]

/-! ### The rectangle `Γ_a` -/

/-- Affine piece `τ ↦ p + τ (q - p)` with weight `ω`. -/
def affinePiece (p q : ℂ) (ω : ℂ → ℂ) (hω : Continuous ω) : Piece where
  γ := fun τ => p + (τ : ℂ) * (q - p)
  γ' := fun _ => q - p
  ω := ω
  hγ := fun τ => by
    have h := ((hasDerivAt_id τ).ofReal_comp.mul_const (q - p)).const_add p
    simpa using h
  hγ' := continuous_const
  hω := hω

/-- The six pieces of the positively oriented rectangle `Γ_a` with corners `±a ± ih`, split at the real axis
(bottom, lower right, upper right, top, upper left, lower left), all with the weight `ω`. -/
def rectPieces (a h : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω) : Fin 6 → Piece :=
  ![affinePiece ((-a : ℂ) - h * Complex.I) ((a : ℂ) - h * Complex.I) ω hω,
    affinePiece ((a : ℂ) - h * Complex.I) (a : ℂ) ω hω,
    affinePiece (a : ℂ) ((a : ℂ) + h * Complex.I) ω hω,
    affinePiece ((a : ℂ) + h * Complex.I) ((-a : ℂ) + h * Complex.I) ω hω,
    affinePiece ((-a : ℂ) + h * Complex.I) (-a : ℂ) ω hω,
    affinePiece (-a : ℂ) ((-a : ℂ) - h * Complex.I) ω hω]

/-- Points of an affine piece between two points of the box `|Re| ≤ a, |Im| ≤ h` stay in the box, hence have norm `≤ a + h`. -/
theorem norm_affine_le {p q : ℂ} {a h : ℝ} (hp1 : |p.re| ≤ a) (hp2 : |p.im| ≤ h) (hq1 : |q.re| ≤ a)
    (hq2 : |q.im| ≤ h) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : ‖p + (τ : ℂ) * (q - p)‖ ≤ a + h := by
  have hre : |(p + (τ : ℂ) * (q - p)).re| ≤ a := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.sub_re]
    rw [abs_le] at *
    constructor <;> nlinarith [hp1.1, hp1.2, hq1.1, hq1.2]
  have him : |(p + (τ : ℂ) * (q - p)).im| ≤ h := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.sub_im]
    rw [abs_le] at *
    constructor <;> nlinarith [hp2.1, hp2.2, hq2.1, hq2.2]
  calc ‖p + (τ : ℂ) * (q - p)‖ ≤ |(p + (τ : ℂ) * (q - p)).re| + |(p + (τ : ℂ) * (q - p)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ a + h := add_le_add hre him

end QuantumNLS.MPContour

#print axioms QuantumNLS.MPContour.integral_theta
#print axioms QuantumNLS.MPContour.norm_affine_le
