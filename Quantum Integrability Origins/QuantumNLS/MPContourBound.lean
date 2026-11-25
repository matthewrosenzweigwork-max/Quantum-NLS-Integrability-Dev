import Mathlib
import QuantumNLS.MPContour

/-!
# PROP-026: the uniform contour bookkeeping `∫ w δ ≤ C (W_a Δ_N + ρ^I_N)`

New module (continuation of `MPContour`).  With `W_a = (1+a)^{d+1}`:

* `rect_weighted_length_le`: the weighted length of the rectangle `Γ_a`,
  `Σ_{i<6} ∫_0^1 |p_t(γ_i τ)| |γ_i'(τ)| dτ ≤ 4 (Σ_r T_r)(1+h)^{d+1} (1+a)^{d+1}` for `p_t(z) = Σ_{r∈R} t_r z^r`, `|t_r| ≤ T_r`, `r ≤ d`;
* `integral_w_delta_le`: for piecewise constant deviations `δ(i,τ) = ε_i` (`ε_i ≤ ε_a` on the large contour, `ε_i ≤ ε_f` on the fixed ones),
  `∫ w δ dν ≤ (2πκ)⁻¹ (ε_a · (weighted length of Γ_a) + ε_f · Λ)` where `Λ` bounds the weighted length of the fixed contours.
  In particular the fixed-contour deviation `ε_f = ρ^I_N` enters only through the fixed constant `Λ`, unamplified by `W_a`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

open MeasureTheory Set Filter unitInterval
open scoped Real

namespace QuantumNLS.MPContour

/-- Weighted length of one piece. -/
def wlen (P : Piece) : ℝ := ∫ τ : I, ‖P.ω (P.γ τ)‖ * ‖P.γ' τ‖

theorem wlen_nonneg (P : Piece) : 0 ≤ wlen P :=
  integral_nonneg (fun τ => mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem continuous_wlen_integrand (P : Piece) : Continuous fun τ : I => ‖P.ω (P.γ τ)‖ * ‖P.γ' τ‖ := by
  have h1 : Continuous fun τ : I => P.γ τ := P.continuous_γ.comp continuous_subtype_val
  exact ((P.hω.comp h1).norm).mul ((P.hγ'.comp continuous_subtype_val).norm)

/-- `∫ w δ dν` for a piecewise-constant deviation. -/
theorem integral_w_delta {m : ℕ} {κ : ℝ} (hκ : 0 < κ) (P : Fin m → Piece) (ε : Fin m → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    ∫ θ, wθ κ P θ * ε θ.1 ∂(nu m) = ((2 * Real.pi * κ)⁻¹) * ∑ i : Fin m, ε i * wlen (P i) := by
  have hc : Continuous fun θ : ThetaSpace m => wθ κ P θ * ε θ.1 :=
    (continuous_wθ κ P).mul (continuous_of_discreteTopology.comp continuous_fst)
  rw [integral_theta hc]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hw : ∀ τ : I, wθ κ P (i, τ) * ε i = ((2 * Real.pi * κ)⁻¹ * ε i) * (‖(P i).ω ((P i).γ τ)‖ * ‖(P i).γ' τ‖) := by
    intro τ
    unfold wθ uθ zθ
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by have := Real.pi_pos; positivity : 0 ≤ (2 * Real.pi * κ)⁻¹)]
    ring
  simp_rw [hw]
  rw [integral_const_mul]
  unfold wlen
  ring

section Rect

/-- `p_t(z) = Σ_{r∈R} t_r z^r`. -/
def polyT (R : Finset ℕ) (t : ℕ → ℝ) (z : ℂ) : ℂ := ∑ r ∈ R, (t r : ℂ) * z ^ r

theorem continuous_polyT (R : Finset ℕ) (t : ℕ → ℝ) : Continuous (polyT R t) := by
  unfold polyT
  exact continuous_finsetSum _ (fun r _ => continuous_const.mul (continuous_pow r))

theorem norm_polyT_le (R : Finset ℕ) (t T : ℕ → ℝ) {d : ℕ} (hR : ∀ r ∈ R, r ≤ d)
    (hT : ∀ r ∈ R, |t r| ≤ T r) {z : ℂ} {B : ℝ} (hz : ‖z‖ ≤ B) (hB : 1 ≤ B) :
    ‖polyT R t z‖ ≤ (∑ r ∈ R, T r) * B ^ d := by
  unfold polyT
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun r hr => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hTr : 0 ≤ T r := (abs_nonneg _).trans (hT r hr)
  have h1 : ‖z‖ ^ r ≤ B ^ r := pow_le_pow_left₀ (norm_nonneg _) hz r
  have h2 : B ^ r ≤ B ^ d := pow_le_pow_right₀ hB (hR r hr)
  calc |t r| * ‖z‖ ^ r ≤ T r * B ^ d :=
        mul_le_mul (hT r hr) (h1.trans h2) (by positivity) hTr

theorem wlen_le (P : Piece) {M c : ℝ} (hM : 0 ≤ M) (hP : ∀ τ ∈ Icc (0 : ℝ) 1, ‖P.ω (P.γ τ)‖ ≤ M)
    (hc : ∀ τ, ‖P.γ' τ‖ ≤ c) : wlen P ≤ M * c := by
  unfold wlen
  have hint : Integrable (fun τ : I => ‖P.ω (P.γ τ)‖ * ‖P.γ' τ‖) volume :=
    (continuous_wlen_integrand P).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ τ : I, ‖P.ω (P.γ τ)‖ * ‖P.γ' τ‖ ≤ ∫ _τ : I, M * c :=
        integral_mono hint (integrable_const _)
          (fun τ => mul_le_mul (hP τ τ.2) (hc τ) (norm_nonneg _) hM)
    _ = M * c := by simp

theorem affine_wlen_le {p q : ℂ} {a h : ℝ} (hp1 : |p.re| ≤ a) (hp2 : |p.im| ≤ h) (hq1 : |q.re| ≤ a)
    (hq2 : |q.im| ≤ h) (ha : 0 ≤ a) (hh : 0 ≤ h) (R : Finset ℕ) (t T : ℕ → ℝ) {d : ℕ}
    (hR : ∀ r ∈ R, r ≤ d) (hT : ∀ r ∈ R, |t r| ≤ T r) :
    wlen (affinePiece p q (polyT R t) (continuous_polyT R t)) ≤
      (∑ r ∈ R, T r) * (1 + a + h) ^ d * ‖q - p‖ := by
  have hsum0 : 0 ≤ ∑ r ∈ R, T r := Finset.sum_nonneg (fun r hr => (abs_nonneg _).trans (hT r hr))
  refine wlen_le _ (by positivity) (fun τ hτ => ?_) (fun τ => le_rfl)
  have hz := norm_affine_le hp1 hp2 hq1 hq2 hτ.1 hτ.2
  exact norm_polyT_le R t T hR hT (B := 1 + a + h) (by simp only [affinePiece]; linarith) (by linarith)

theorem rect_weighted_length_le {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (R : Finset ℕ) (t T : ℕ → ℝ) {d : ℕ}
    (hR : ∀ r ∈ R, r ≤ d) (hT : ∀ r ∈ R, |t r| ≤ T r) :
    ∑ i : Fin 6, wlen (rectPieces a h (polyT R t) (continuous_polyT R t) i) ≤
      4 * (∑ r ∈ R, T r) * (1 + h) ^ (d + 1) * (1 + a) ^ (d + 1) := by
  have hsum0 : 0 ≤ ∑ r ∈ R, T r := Finset.sum_nonneg (fun r hr => (abs_nonneg _).trans (hT r hr))
  set M : ℝ := (∑ r ∈ R, T r) * (1 + a + h) ^ d with hM
  have hI : ∀ x : ℝ, ‖(x : ℂ)‖ = |x| := fun x => by simp
  have b1 : |((-a : ℂ) - h * Complex.I).re| ≤ a := by simp [abs_of_nonneg ha, ha]
  have b2 : |((-a : ℂ) - h * Complex.I).im| ≤ h := by simp [abs_of_nonneg hh, hh]
  have b3 : |((a : ℂ) - h * Complex.I).re| ≤ a := by simp [abs_of_nonneg ha, ha]
  have b4 : |((a : ℂ) - h * Complex.I).im| ≤ h := by simp [abs_of_nonneg hh, hh]
  have b5 : |((a : ℂ)).re| ≤ a := by simp [abs_of_nonneg ha, ha]
  have b6 : |((a : ℂ)).im| ≤ h := by simp [abs_of_nonneg hh, hh]
  have b7 : |((a : ℂ) + h * Complex.I).re| ≤ a := by simp [abs_of_nonneg ha, ha]
  have b8 : |((a : ℂ) + h * Complex.I).im| ≤ h := by simp [abs_of_nonneg hh, hh]
  have b9 : |((-a : ℂ) + h * Complex.I).re| ≤ a := by simp [abs_of_nonneg ha, ha]
  have b10 : |((-a : ℂ) + h * Complex.I).im| ≤ h := by simp [abs_of_nonneg hh, hh]
  have b11 : |((-a : ℂ)).re| ≤ a := by simp [abs_of_nonneg ha, ha]
  have b12 : |((-a : ℂ)).im| ≤ h := by simp [abs_of_nonneg hh, hh]
  have w0 := affine_wlen_le b1 b2 b3 b4 ha hh R t T hR hT
  have w1 := affine_wlen_le b3 b4 b5 b6 ha hh R t T hR hT
  have w2 := affine_wlen_le b5 b6 b7 b8 ha hh R t T hR hT
  have w3 := affine_wlen_le b7 b8 b9 b10 ha hh R t T hR hT
  have w4 := affine_wlen_le b9 b10 b11 b12 ha hh R t T hR hT
  have w5 := affine_wlen_le b11 b12 b1 b2 ha hh R t T hR hT
  have n0 : ‖((a : ℂ) - h * Complex.I) - ((-a : ℂ) - h * Complex.I)‖ = 2 * a := by
    have : ((a : ℂ) - h * Complex.I) - ((-a : ℂ) - h * Complex.I) = ((2 * a : ℝ) : ℂ) := by push_cast; ring
    rw [this, hI, abs_of_nonneg (by linarith)]
  have n1 : ‖(a : ℂ) - ((a : ℂ) - h * Complex.I)‖ = h := by
    have : (a : ℂ) - ((a : ℂ) - h * Complex.I) = ((h : ℝ) : ℂ) * Complex.I := by ring
    rw [this, norm_mul, hI, abs_of_nonneg hh]; simp
  have n2 : ‖((a : ℂ) + h * Complex.I) - (a : ℂ)‖ = h := by
    have : ((a : ℂ) + h * Complex.I) - (a : ℂ) = ((h : ℝ) : ℂ) * Complex.I := by ring
    rw [this, norm_mul, hI, abs_of_nonneg hh]; simp
  have n3 : ‖((-a : ℂ) + h * Complex.I) - ((a : ℂ) + h * Complex.I)‖ = 2 * a := by
    have : ((-a : ℂ) + h * Complex.I) - ((a : ℂ) + h * Complex.I) = ((-(2 * a) : ℝ) : ℂ) := by push_cast; ring
    rw [this, hI, abs_neg, abs_of_nonneg (by linarith)]
  have n4 : ‖(-a : ℂ) - ((-a : ℂ) + h * Complex.I)‖ = h := by
    have : (-a : ℂ) - ((-a : ℂ) + h * Complex.I) = -(((h : ℝ) : ℂ) * Complex.I) := by ring
    rw [this, norm_neg, norm_mul, hI, abs_of_nonneg hh]; simp
  have n5 : ‖((-a : ℂ) - h * Complex.I) - (-a : ℂ)‖ = h := by
    have : ((-a : ℂ) - h * Complex.I) - (-a : ℂ) = -(((h : ℝ) : ℂ) * Complex.I) := by ring
    rw [this, norm_neg, norm_mul, hI, abs_of_nonneg hh]; simp
  rw [Fin.sum_univ_six]
  have e0 : rectPieces a h (polyT R t) (continuous_polyT R t) 0 =
      affinePiece ((-a : ℂ) - h * Complex.I) ((a : ℂ) - h * Complex.I) (polyT R t) (continuous_polyT R t) := rfl
  have e1 : rectPieces a h (polyT R t) (continuous_polyT R t) 1 =
      affinePiece ((a : ℂ) - h * Complex.I) (a : ℂ) (polyT R t) (continuous_polyT R t) := rfl
  have e2 : rectPieces a h (polyT R t) (continuous_polyT R t) 2 =
      affinePiece (a : ℂ) ((a : ℂ) + h * Complex.I) (polyT R t) (continuous_polyT R t) := rfl
  have e3 : rectPieces a h (polyT R t) (continuous_polyT R t) 3 =
      affinePiece ((a : ℂ) + h * Complex.I) ((-a : ℂ) + h * Complex.I) (polyT R t) (continuous_polyT R t) := rfl
  have e4 : rectPieces a h (polyT R t) (continuous_polyT R t) 4 =
      affinePiece ((-a : ℂ) + h * Complex.I) (-a : ℂ) (polyT R t) (continuous_polyT R t) := rfl
  have e5 : rectPieces a h (polyT R t) (continuous_polyT R t) 5 =
      affinePiece (-a : ℂ) ((-a : ℂ) - h * Complex.I) (polyT R t) (continuous_polyT R t) := rfl
  rw [e0, e1, e2, e3, e4, e5]
  rw [n0] at w0; rw [n1] at w1; rw [n2] at w2; rw [n3] at w3; rw [n4] at w4; rw [n5] at w5
  have hsplit : 1 + a + h ≤ (1 + a) * (1 + h) := by nlinarith [mul_nonneg ha hh]
  have hsplit2 : a + h ≤ (1 + a) * (1 + h) := by nlinarith [mul_nonneg ha hh]
  have hpow : (1 + a + h) ^ d ≤ ((1 + a) * (1 + h)) ^ d := pow_le_pow_left₀ (by linarith) hsplit d
  calc _ ≤ (∑ r ∈ R, T r) * (1 + a + h) ^ d * (2 * a) + (∑ r ∈ R, T r) * (1 + a + h) ^ d * h +
        (∑ r ∈ R, T r) * (1 + a + h) ^ d * h + (∑ r ∈ R, T r) * (1 + a + h) ^ d * (2 * a) +
        (∑ r ∈ R, T r) * (1 + a + h) ^ d * h + (∑ r ∈ R, T r) * (1 + a + h) ^ d * h := by linarith
    _ = (∑ r ∈ R, T r) * (1 + a + h) ^ d * (4 * (a + h)) := by ring
    _ ≤ (∑ r ∈ R, T r) * ((1 + a) * (1 + h)) ^ d * (4 * ((1 + a) * (1 + h))) := by
        gcongr
    _ = 4 * (∑ r ∈ R, T r) * (1 + h) ^ (d + 1) * (1 + a) ^ (d + 1) := by
        rw [mul_pow, pow_succ (1 + h), pow_succ (1 + a)]; ring

end Rect

end QuantumNLS.MPContour

#print axioms QuantumNLS.MPContour.integral_w_delta
#print axioms QuantumNLS.MPContour.rect_weighted_length_le
