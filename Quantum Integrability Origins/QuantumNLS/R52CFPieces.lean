import QuantumNLS.MPContour
import QuantumNLS.LabelExactPeriod

/-!
# R-52CF5DA1 stage 6: the fixed rectangles as weighted contour pieces

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101): the fixed contours `Γ_n`, `n ∈ F`, carry the
constant weights `t_n` in the combined generators `Σ_n t_n C^{(0)}_{N,n}` and `Σ_n t_n L^v_{N,n}`.

The positively oriented rectangle `∂([a,b]×[-h,h])` is written as four affine pieces (bottom, right, top, left) with
the constant weight `c` (`rect4`), and a finite family of rectangles is concatenated into one piece family over the
parameter space `Θ = Fin (m*4) × [0,1]` of `MPContour` (`rectFam`).  For every function `f` continuous on the
rectangles,
* `side_bottom`, `side_right`, `side_top`, `side_left`, `sum_rect4`: the four affine pieces with weight `c`
  reproduce `c · rectIntegral f a b h` (the literal rectangle integral of `LabelExactPeriod`);
* **`integral_rectFam`**: for every `f` with `θ ↦ u_θ f(z_θ)` continuous,
  `∫_Θ u_θ f(z_θ) dν = Σ_k -(2πκ)⁻¹ c_k ∮_{Γ_k} f`.
Pure real/complex analysis; no hypothesis is added.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped BigOperators

namespace QuantumNLS.R52CFPieces

open QuantumNLS.MPContour
open LabelExactPeriod (rectIntegral)

/-- The four affine sides of `∂([a,b]×[-h,h])`, positively oriented, with constant weight `c`. -/
def rect4 (a b h : ℝ) (c : ℂ) : Fin 4 → Piece :=
  ![affinePiece ((a : ℂ) - h * I) ((b : ℂ) - h * I) (fun _ => c) continuous_const,
    affinePiece ((b : ℂ) - h * I) ((b : ℂ) + h * I) (fun _ => c) continuous_const,
    affinePiece ((b : ℂ) + h * I) ((a : ℂ) + h * I) (fun _ => c) continuous_const,
    affinePiece ((a : ℂ) + h * I) ((a : ℂ) - h * I) (fun _ => c) continuous_const]

/-- `∫_0^1 f(p + τ(q-p))(q-p) dτ` for an affine segment. -/
theorem affine_integral (p q : ℂ) (f : ℂ → ℂ) :
    (∫ τ in (0 : ℝ)..1, f (p + (τ : ℂ) * (q - p)) * (q - p)) =
      (q - p) * ∫ τ in (0 : ℝ)..1, f (p + (τ : ℂ) * (q - p)) := by
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext τ
  ring

/-- The bottom side: `∫_0^1 f(a - ih + τ(b-a))(b-a) dτ = ∫_a^b f(x - ih) dx`. -/
theorem side_bottom (a b h : ℝ) (f : ℂ → ℂ) :
    (∫ τ in (0 : ℝ)..1, f (((a : ℂ) - h * I) + (τ : ℂ) * (((b : ℂ) - h * I) - ((a : ℂ) - h * I))) *
      (((b : ℂ) - h * I) - ((a : ℂ) - h * I))) =
      ∫ x in a..b, f (x + ((-h : ℝ) : ℂ) * I) := by
  have hx := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    (fun x : ℝ => f (x + ((-h : ℝ) : ℂ) * I)) (b - a) a
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at hx
  rw [← hx, Complex.real_smul, ← intervalIntegral.integral_const_mul]
  congr 1
  funext τ
  have harg : ((a : ℂ) - h * I) + (τ : ℂ) * (((b : ℂ) - h * I) - ((a : ℂ) - h * I)) =
      (((b - a) * τ + a : ℝ) : ℂ) + ((-h : ℝ) : ℂ) * I := by push_cast; ring
  rw [harg]
  generalize f ((((b - a) * τ + a : ℝ) : ℂ) + ((-h : ℝ) : ℂ) * I) = F
  push_cast
  ring

/-- The right side: `∫_0^1 f(b - ih + τ·2ih)(2ih) dτ = I ∫_{-h}^h f(b + iy) dy`. -/
theorem side_right (b h : ℝ) (f : ℂ → ℂ) :
    (∫ τ in (0 : ℝ)..1, f (((b : ℂ) - h * I) + (τ : ℂ) * (((b : ℂ) + h * I) - ((b : ℂ) - h * I))) *
      (((b : ℂ) + h * I) - ((b : ℂ) - h * I))) =
      I • ∫ y in (-h)..h, f (b + y * I) := by
  have hx := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    (fun y : ℝ => f (b + y * I)) (h - -h) (-h)
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at hx
  rw [smul_eq_mul, ← hx, Complex.real_smul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext τ
  have harg : ((b : ℂ) - h * I) + (τ : ℂ) * (((b : ℂ) + h * I) - ((b : ℂ) - h * I)) =
      (b : ℂ) + (((h - -h) * τ + -h : ℝ) : ℂ) * I := by push_cast; ring
  rw [harg]
  generalize f ((b : ℂ) + (((h - -h) * τ + -h : ℝ) : ℂ) * I) = F
  push_cast
  ring

/-- The top side (reversed): `∫_0^1 f(b + ih + τ(a-b))(a-b) dτ = -∫_a^b f(x + ih) dx`. -/
theorem side_top (a b h : ℝ) (f : ℂ → ℂ) :
    (∫ τ in (0 : ℝ)..1, f (((b : ℂ) + h * I) + (τ : ℂ) * (((a : ℂ) + h * I) - ((b : ℂ) + h * I))) *
      (((a : ℂ) + h * I) - ((b : ℂ) + h * I))) =
      -∫ x in a..b, f (x + h * I) := by
  have hx := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    (fun x : ℝ => f (x + h * I)) (a - b) b
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at hx
  rw [intervalIntegral.integral_symm a b] at hx
  rw [← hx, Complex.real_smul, ← intervalIntegral.integral_const_mul]
  congr 1
  funext τ
  have harg : ((b : ℂ) + h * I) + (τ : ℂ) * (((a : ℂ) + h * I) - ((b : ℂ) + h * I)) =
      (((a - b) * τ + b : ℝ) : ℂ) + (h : ℂ) * I := by push_cast; ring
  rw [harg]
  generalize f ((((a - b) * τ + b : ℝ) : ℂ) + (h : ℂ) * I) = F
  push_cast
  ring

/-- The left side (reversed): `∫_0^1 f(a + ih - τ·2ih)(-2ih) dτ = -I ∫_{-h}^h f(a + iy) dy`. -/
theorem side_left (a h : ℝ) (f : ℂ → ℂ) :
    (∫ τ in (0 : ℝ)..1, f (((a : ℂ) + h * I) + (τ : ℂ) * (((a : ℂ) - h * I) - ((a : ℂ) + h * I))) *
      (((a : ℂ) - h * I) - ((a : ℂ) + h * I))) =
      -(I • ∫ y in (-h)..h, f (a + y * I)) := by
  have hx := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    (fun y : ℝ => f (a + y * I)) (-h - h) h
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at hx
  rw [intervalIntegral.integral_symm (-h) h] at hx
  have hx' : (∫ y in (-h)..h, f (a + y * I)) =
      -((-h - h) • ∫ y in (0 : ℝ)..1, f (a + (((-h - h) * y + h : ℝ) : ℂ) * I)) := by
    rw [hx, neg_neg]
  rw [hx', smul_neg, neg_neg, smul_eq_mul, Complex.real_smul,
    ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  congr 1
  funext τ
  have harg : ((a : ℂ) + h * I) + (τ : ℂ) * (((a : ℂ) - h * I) - ((a : ℂ) + h * I)) =
      (a : ℂ) + (((-h - h) * τ + h : ℝ) : ℂ) * I := by push_cast; ring
  rw [harg]
  generalize f ((a : ℂ) + (((-h - h) * τ + h : ℝ) : ℂ) * I) = F
  push_cast
  ring

/-- The four pieces reproduce the literal rectangle integral, times the weight. -/
theorem sum_rect4 (a b h : ℝ) (c : ℂ) (f : ℂ → ℂ) :
    ∑ i : Fin 4, (∫ τ in (0 : ℝ)..1, (rect4 a b h c i).ω ((rect4 a b h c i).γ τ) *
      f ((rect4 a b h c i).γ τ) * (rect4 a b h c i).γ' τ) = c * rectIntegral f a b h := by
  simp only [Fin.sum_univ_four, rect4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, affinePiece]
  have e : ∀ (p q : ℂ), (∫ τ in (0 : ℝ)..1, c * f (p + (τ : ℂ) * (q - p)) * (q - p)) =
      c * ∫ τ in (0 : ℝ)..1, f (p + (τ : ℂ) * (q - p)) * (q - p) := by
    intro p q
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext τ; ring
  rw [e, e, e, e, side_bottom, side_right, side_top, side_left]
  unfold rectIntegral
  ring

/-- The unit-interval integral as an interval integral. -/
theorem integral_I (f : ℝ → ℂ) : ∫ τ : unitInterval, f τ = ∫ τ in (0 : ℝ)..1, f τ := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact integral_subtype_comap measurableSet_Icc f

/-- Integration over the parameter space as a sum over pieces (Banach-valued). -/
theorem integral_nu {M : ℕ} {g : ThetaSpace M → ℂ} (hg : Continuous g) :
    ∫ θ, g θ ∂(nu M) = ∑ i : Fin M, ∫ τ : unitInterval, g (i, τ) := by
  unfold nu
  rw [integral_prod _ (by simpa [nu] using
    (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g) :
      Integrable g (nu M)))]
  rw [integral_count]

/-- A finite family of weighted rectangles as one piece family over `Fin (m*4)`. -/
def rectFam {m : ℕ} (a b h : Fin m → ℝ) (c : Fin m → ℂ) : Fin (m * 4) → Piece :=
  fun k => rect4 (a (finProdFinEquiv.symm k).1) (b (finProdFinEquiv.symm k).1) (h (finProdFinEquiv.symm k).1)
    (c (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2

/-- **The weighted contour integral over the concatenated family is the weighted sum of the literal
rectangle integrals.** -/
theorem integral_rectFam (κ : ℝ) {m : ℕ} (a b h : Fin m → ℝ) (c : Fin m → ℂ) (f : ℂ → ℂ)
    (hcont : Continuous (fun θ => uθ κ (rectFam a b h c) θ * f (zθ (rectFam a b h c) θ))) :
    ∫ θ, uθ κ (rectFam a b h c) θ * f (zθ (rectFam a b h c) θ) ∂(nu (m * 4)) =
      ∑ i : Fin m, -((((2 * Real.pi * κ)⁻¹ : ℝ) : ℂ)) * (c i * rectIntegral f (a i) (b i) (h i)) := by
  rw [integral_nu hcont]
  rw [← (finProdFinEquiv : Fin m × Fin 4 ≃ Fin (m * 4)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sum_rect4 (a i) (b i) (h i) (c i) f, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set P := rect4 (a i) (b i) (h i) (c i) j with hPdef
  have hP : rectFam a b h c (finProdFinEquiv (i, j)) = P := by
    simp [rectFam, hPdef]
  have he : (∫ τ : unitInterval, uθ κ (rectFam a b h c) (finProdFinEquiv (i, j), τ) *
      f (zθ (rectFam a b h c) (finProdFinEquiv (i, j), τ))) =
      ∫ τ : unitInterval, (fun t : ℝ => -((((2 * Real.pi * κ)⁻¹ : ℝ) : ℂ)) * P.ω (P.γ t) * P.γ' t * f (P.γ t)) τ := by
    simp only [uθ, zθ, hP]
  have h2 := integral_I (fun t : ℝ => -((((2 * Real.pi * κ)⁻¹ : ℝ) : ℂ)) * P.ω (P.γ t) * P.γ' t * f (P.γ t))
  rw [he]
  refine h2.trans ?_
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  ring

end QuantumNLS.R52CFPieces

#print axioms QuantumNLS.R52CFPieces.sum_rect4
#print axioms QuantumNLS.R52CFPieces.integral_rectFam
