import Mathlib
import QuantumNLS.RootEvent
import QuantumNLS.ResolventNeighborhood
import QuantumNLS.NonvanishingD
import QuantumNLS.PROP017Source

/-!
# Propagation contour: scalar rectangle contour estimate consuming PROP-017

Owner: haiku_inventory (round 15). Source: `window_reconstruction.tex` lines 206–207, the scalar
contour functional `L_{N,p} = −(1/(2πκ)) Re ∮_{Γ_N} p(z) S_N(z)/D(z) dz` (`Γ_N` the positively oriented
rectangle with endpoints `±a` and heights `±h`, `D = A − e/A`), and the PROP-017 inputs
(`Q7A:eq:derivative` at `n = 0`, and the `|D|` lower bound on the neighbourhood).

Proved (no duplication of accepted lemmas; the PROP-017 outputs enter as hypotheses of exactly the
conclusion shapes of `PROP017Source.prop017_source`):

* `rectContour a h f`: the positively oriented rectangle integral (four interval integrals);
* `norm_rectContour_le`: `‖∮_{Γ_N} f‖ ≤ 4(a+h)·sup_{Γ_N}|f|`;
* `contour_bound_PROP017`: for `f = p·g/D` with `|p| ≤ P`, `|g| ≤ C` on `Γ_N`, `|D| ≥ d₀/2` on
  `Γ_N`, the contour error `‖∮_{Γ_N} p g/D‖ ≤ 4(a+h)·P·C/(d₀/2)`.

Not claimed: the Re/prefactor identification of `L_{N,p}`, operator functional calculus of `S_N`,
or the polynomial class of `p` (here `p` is any function bounded on `Γ_N`).
-/

namespace QuantumNLS.PropagationContour

open MeasureTheory Set Metric intervalIntegral
open QuantumNLS.ResolventNeighborhood QuantumNLS.NonvanishingD

/-- Positively oriented rectangle integral over the boundary of `Γ_N`: bottom `−a→a` at `−ih`,
right `−h→h` at `a`, top `a→−a` at `+ih`, left `h→−h` at `−a`. -/
noncomputable def rectContour (a h : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x in (-a)..a, f ((x : ℂ) - (h : ℂ) * Complex.I))
    + (∫ y in (-h)..h, f ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
    - (∫ x in (-a)..a, f ((x : ℂ) + (h : ℂ) * Complex.I))
    - (∫ y in (-h)..h, f ((-a : ℝ) + (y : ℂ) * Complex.I) * Complex.I)

lemma mem_GammaN_of_im {a h : ℝ} {w : ℂ} (hi : w.im = h ∨ w.im = -h) (hr : |w.re| ≤ a) :
    w ∈ GammaN a h :=
  Or.inr ⟨hi, hr⟩

lemma mem_GammaN_of_re {a h : ℝ} {w : ℂ} (hr : w.re = a ∨ w.re = -a) (hi : |w.im| ≤ h) :
    w ∈ GammaN a h :=
  Or.inl ⟨hr, hi⟩

/-- **Rectangle contour estimate.** If `‖f‖ ≤ M` on `Γ_N`, then `‖∮_{Γ_N} f‖ ≤ 4(a+h)M`. -/
theorem norm_rectContour_le {a h M : ℝ} (f : ℂ → ℂ) (ha : 0 ≤ a) (hh : 0 ≤ h) (hM0 : 0 ≤ M)
    (hM : ∀ z ∈ GammaN a h, ‖f z‖ ≤ M) : ‖rectContour a h f‖ ≤ 4 * (a + h) * M := by
  have hlen_a : |a - -a| = 2 * a := by
    rw [show a - -a = 2 * a by ring, abs_of_nonneg (by linarith)]
  have hlen_h : |h - -h| = 2 * h := by
    rw [show h - -h = 2 * h by ring, abs_of_nonneg (by linarith)]
  have hlen_a' : |-a - a| = 2 * a := by
    rw [show -a - a = -(2 * a) by ring, abs_neg, abs_of_nonneg (by linarith)]
  have hlen_h' : |-h - h| = 2 * h := by
    rw [show -h - h = -(2 * h) by ring, abs_neg, abs_of_nonneg (by linarith)]
  -- bottom side: points `x − ih`, `im = −h`, `|x| ≤ a`
  have hbot : ‖∫ x in (-a)..a, f ((x : ℂ) - (h : ℂ) * Complex.I)‖ ≤ M * (2 * a) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -a) (b := a) (C := M)
      (f := fun x : ℝ => f ((x : ℂ) - (h : ℂ) * Complex.I)) (by
        intro x hx
        rw [uIoc_of_le (by linarith)] at hx
        apply hM
        apply mem_GammaN_of_im
        · right
          simp
        · have hre : ((x : ℂ) - (h : ℂ) * Complex.I).re = x := by simp
          rw [hre, abs_le]
          constructor <;> linarith [hx.1, hx.2])
    rw [hlen_a] at this
    exact this
  -- right side: points `a + iy`, `re = a`, `|y| ≤ h`
  have hright : ‖∫ y in (-h)..h, f ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I‖ ≤ M * (2 * h) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -h) (b := h) (C := M)
      (f := fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I) (by
        intro y hy
        rw [uIoc_of_le (by linarith)] at hy
        rw [norm_mul, Complex.norm_I, mul_one]
        apply hM
        apply mem_GammaN_of_re
        · left
          simp
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
            Complex.I_re, Complex.ofReal_re, mul_one, zero_add, mul_zero, add_zero]
          rw [abs_le]
          constructor <;> linarith [hy.1, hy.2])
    rw [hlen_h] at this
    exact this
  -- top side: points `x + ih`, `im = h`, `|x| ≤ a`
  have htop : ‖∫ x in (-a)..a, f ((x : ℂ) + (h : ℂ) * Complex.I)‖ ≤ M * (2 * a) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -a) (b := a) (C := M)
      (f := fun x : ℝ => f ((x : ℂ) + (h : ℂ) * Complex.I)) (by
        intro x hx
        rw [uIoc_of_le (by linarith)] at hx
        apply hM
        apply mem_GammaN_of_im
        · left
          simp
        · have hre : ((x : ℂ) + (h : ℂ) * Complex.I).re = x := by simp
          rw [hre, abs_le]
          constructor <;> linarith [hx.1, hx.2])
    rw [hlen_a] at this
    exact this
  -- left side: points `−a + iy`, `re = −a`, `|y| ≤ h`
  have hleft : ‖∫ y in (-h)..h, f ((-a : ℝ) + (y : ℂ) * Complex.I) * Complex.I‖ ≤ M * (2 * h) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -h) (b := h) (C := M)
      (f := fun y : ℝ => f ((-a : ℝ) + (y : ℂ) * Complex.I) * Complex.I) (by
        intro y hy
        rw [uIoc_of_le (by linarith)] at hy
        rw [norm_mul, Complex.norm_I, mul_one]
        apply hM
        apply mem_GammaN_of_re
        · right
          simp
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
            Complex.I_re, Complex.ofReal_re, mul_one, zero_add, mul_zero, add_zero]
          rw [abs_le]
          constructor <;> linarith [hy.1, hy.2])
    rw [hlen_h] at this
    exact this
  unfold rectContour
  have htri := norm_sub_le
    ((∫ x in (-a)..a, f ((x : ℂ) - (h : ℂ) * Complex.I))
      + (∫ y in (-h)..h, f ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
      - (∫ x in (-a)..a, f ((x : ℂ) + (h : ℂ) * Complex.I)))
    (∫ y in (-h)..h, f ((-a : ℝ) + (y : ℂ) * Complex.I) * Complex.I)
  have htri2 := norm_sub_le
    ((∫ x in (-a)..a, f ((x : ℂ) - (h : ℂ) * Complex.I))
      + (∫ y in (-h)..h, f ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I))
    (∫ x in (-a)..a, f ((x : ℂ) + (h : ℂ) * Complex.I))
  have htri3 := norm_add_le (∫ x in (-a)..a, f ((x : ℂ) - (h : ℂ) * Complex.I))
    (∫ y in (-h)..h, f ((a : ℂ) + (y : ℂ) * Complex.I) * Complex.I)
  have e : 4 * (a + h) * M = M * (2 * a) + M * (2 * h) + M * (2 * a) + M * (2 * h) := by ring
  rw [e]
  linarith [htri, htri2, htri3, hbot, hright, htop, hleft]

/-- **Consumer of PROP-017: the contour error.** With `|g| ≤ C` on `Γ_N` (the `n = 0` case of
`Q7A:eq:derivative`, where `Γ_N ⊆ NbhdN(ρ/2)`), `|D| ≥ d₀/2` on `Γ_N` (`Q7A:eq:Gneighbor`-side
nonvanishing on `NbhdN(ρ/4)`), and `|p| ≤ P` on `Γ_N`:
`‖∮_{Γ_N} p·g/D‖ ≤ 4(a+h)·P·C/(d₀/2)`. -/
theorem contour_bound_PROP017 {a h ρ d0 C P : ℝ} (g D p : ℂ → ℂ)
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hρ : 0 ≤ ρ) (hd0 : 0 < d0) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hg : ∀ z ∈ NbhdN a h (ρ / 2), ‖g z‖ ≤ C)
    (hD : ∀ z ∈ NbhdN a h (ρ / 4), d0 / 2 ≤ ‖D z‖)
    (hp : ∀ z ∈ GammaN a h, ‖p z‖ ≤ P) :
    ‖rectContour a h (fun z => p z * g z / D z)‖ ≤ 4 * (a + h) * (P * C / (d0 / 2)) := by
  apply norm_rectContour_le _ ha hh (div_nonneg (mul_nonneg hP hC) (by linarith))
  intro z hz
  have hzg : z ∈ NbhdN a h (ρ / 2) := GammaN_subset_NbhdN hz (by linarith)
  have hzD : z ∈ NbhdN a h (ρ / 4) := GammaN_subset_NbhdN hz (by linarith)
  have hDz := hD z hzD
  have hgz := hg z hzg
  have hpz := hp z hz
  have hdpos : 0 < d0 / 2 := by linarith
  rw [norm_div, norm_mul]
  have hnum : ‖p z‖ * ‖g z‖ ≤ P * C := mul_le_mul hpz hgz (norm_nonneg _) hP
  calc ‖p z‖ * ‖g z‖ / ‖D z‖ ≤ P * C / ‖D z‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ P * C / (d0 / 2) := div_le_div_of_nonneg_left (mul_nonneg hP hC) hdpos hDz

end QuantumNLS.PropagationContour
