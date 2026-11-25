import Mathlib
import QuantumNLS.MPLinearization

/-!
# PROP-026 `lem:MP-linearization`: the uniform contour bookkeeping `C (W_a Δ_N + ρ^I_N)`

New module.  Specializes `MPLinearization.mp_linearization` to the source's combined contour
`Γ_a ∪ ⋃_{n∈I} Γ_n`: the six pieces of the positively oriented rectangle `Γ_a` (corners `±a ± ih`, split at the real axis, weight
`p_t(z) = Σ_{r∈R} t_r z^r`, `|t_r| ≤ T_r`, `r ≤ d`) followed by `n` fixed C¹ pieces `Pf` (weights `θ_m`).  With
`W_a = (1+a)^{d+1}`, `ε_a` the growing-window deviation (`eq:MP-growing-deviation`, `= CΔ_N`) on `Γ_a` and `ε_f` the fixed-contour
deviation (`eq:MP-fixed-deviation`, `= ρ^I_N`) on the fixed contours,

`‖γ^{(k)}_{e^{-iNC_{0,N}}φ} - γ^{(k)}_{e^{-iNL_N}φ}‖₁ ≤ C (2πκ)⁻¹ (ε_a · 4(ΣT)(1+h)^{d+1} W_a + ε_f · Λ)`,

`Λ ≥ Σ_j wlen(Pf_j)` the fixed weighted length of the fixed contours: the fixed-contour deviation is NOT multiplied by `W_a`.
`C` does not depend on `q, a, t, n, Pf`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.MPLinearizationContours

open QuantumNLS.MPContour QuantumNLS.MPFamily QuantumNLS.MPOps QuantumNLS.MPLinearization
open QuantumNLS.FunctionalLinearization
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.NormalizedTransfer

theorem im_affine (p q : ℂ) (τ : ℝ) : (p + (τ : ℂ) * (q - p)).im = p.im + τ * (q.im - p.im) := by
  simp [Complex.mul_im]

theorem rect_im (a h : ℝ) (hh : 0 < h) (ha : 0 ≤ a) (ω : ℂ → ℂ) (hω : Continuous ω) :
    (∀ i : Fin 6, ∀ τ ∈ Icc (0 : ℝ) 1, |((rectPieces a h ω hω i).γ τ).im| ≤ h) ∧
    (∀ i : Fin 6, ∀ τ ∈ Ioo (0 : ℝ) 1, ((rectPieces a h ω hω i).γ τ).im ≠ 0) := by
  constructor
  · intro i τ hτ
    have p1 := mul_nonneg hh.le hτ.1
    have p2 := mul_nonneg hh.le (sub_nonneg.2 hτ.2)
    fin_cases i <;>
      (simp only [rectPieces, affinePiece, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, im_affine, Complex.sub_im,
        Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im]
       <;> rw [abs_le] <;> constructor <;> nlinarith [hτ.1, hτ.2, hh])
  · intro i τ hτ
    have p1 := mul_pos hh hτ.1
    have p2 := mul_pos hh (sub_pos.2 hτ.2)
    fin_cases i <;>
      (simp only [rectPieces, affinePiece, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, im_affine, Complex.sub_im,
        Complex.add_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im]
       <;> intro h0 <;> nlinarith [hτ.1, hτ.2, hh])

theorem mp_linearization_contours (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (h : ℝ) (hh : 0 < h) (k : ℕ)
    (d₀ s₁ a₀ c₁ : ℝ) (hd0 : 0 < d₀) (hs0 : 0 ≤ s₁) (ha0 : 0 < a₀) (hc1 : 0 ≤ c₁)
    (d : ℕ) (R : Finset ℕ) (hRd : ∀ r ∈ R, r ≤ d) (T : ℕ → ℝ) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ) (hN : 1 ≤ k + q) (a : ℝ) (ha : 0 ≤ a) (t : ℕ → ℝ) (ht : ∀ r ∈ R, |t r| ≤ T r)
        {n : ℕ} (Pf : Fin n → Piece) (hΛ : ∑ j, wlen (Pf j) ≤ Λ) (Z : Set ℂ)
        (hZr : ∀ i : Fin 6, ∀ τ ∈ Icc (0 : ℝ) 1,
          ((rectPieces a h (polyT R t) (continuous_polyT R t)) i).γ τ ∈ Z)
        (hZf : ∀ j, ∀ τ ∈ Icc (0 : ℝ) 1, (Pf j).γ τ ∈ Z)
        (hImf : ∀ j, ∀ τ ∈ Icc (0 : ℝ) 1, |((Pf j).γ τ).im| ≤ h)
        (hrealf : ∀ j, ∀ τ ∈ Ioo (0 : ℝ) 1, ((Pf j).γ τ).im ≠ 0)
        (B : BgFam Z d₀ s₁ a₀ c₁)
        (phi : SymSector ℂ (L2T L) (k + q)) (hphi : ‖phi‖ = 1) (εa εf : ℝ) (hεa : 0 ≤ εa) (hεf : 0 ≤ εf)
        (hdeva : ∀ i : Fin 6, ∀ τ ∈ Icc (0 : ℝ) 1,
          ‖(normalizedTransfer L κ (k + q) (((rectPieces a h (polyT R t) (continuous_polyT R t)) i).γ τ) -
            B.s (((rectPieces a h (polyT R t) (continuous_polyT R t)) i).γ τ) •
            (1 : SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q))) phi‖ ≤ εa)
        (hdevf : ∀ j, ∀ τ ∈ Icc (0 : ℝ) 1,
          ‖(normalizedTransfer L κ (k + q) ((Pf j).γ τ) - B.s ((Pf j).γ τ) •
            (1 : SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q))) phi‖ ≤ εf),
        QuantumNLS.TraceClass.traceNorm
          (reducedDensityPower k q
              ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
                C0op (nu (6 + n)) (fun θ => normalizedTransfer L κ (k + q)
                  (zθ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf) θ))
                  (uθ κ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf))
                  (gθ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf) B)) 1 phi :
                SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
            reducedDensityPower k q
              ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
                Lop (nu (6 + n)) (fun θ => normalizedTransfer L κ (k + q)
                  (zθ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf) θ))
                  (uθ κ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf))
                  (dθ (Fin.append (rectPieces a h (polyT R t) (continuous_polyT R t)) Pf) B)) 1 phi :
                SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))) ≤
          ENNReal.ofReal (C * ((2 * Real.pi * κ)⁻¹ *
            (εa * (4 * (∑ r ∈ R, T r) * (1 + h) ^ (d + 1) * (1 + a) ^ (d + 1)) + εf * Λ))) := by
  obtain ⟨C, hC0, hmain⟩ := mp_linearization L κ hκ h k d₀ s₁ a₀ c₁ hd0 hs0 ha0 hc1
  refine ⟨C, hC0, ?_⟩
  intro q hN a ha t ht n Pf hΛ Z hZr hZf hImf hrealf B phi hphi εa εf hεa hεf hdeva hdevf
  set A := rectPieces a h (polyT R t) (continuous_polyT R t) with hA
  obtain ⟨him, hre⟩ := rect_im a h hh ha (polyT R t) (continuous_polyT R t)
  have hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (Fin.append A Pf i).γ τ ∈ Z := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · intro τ hτ; simpa [Fin.append_left] using hZr i τ hτ
    · intro τ hτ; simpa [Fin.append_right] using hZf j τ hτ
  have hIm : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, |((Fin.append A Pf i).γ τ).im| ≤ h := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · intro τ hτ; simpa [Fin.append_left] using him i τ hτ
    · intro τ hτ; simpa [Fin.append_right] using hImf j τ hτ
  have hreal : ∀ i, ∀ τ ∈ Ioo (0 : ℝ) 1, ((Fin.append A Pf i).γ τ).im ≠ 0 := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · intro τ hτ; simpa [Fin.append_left] using hre i τ hτ
    · intro τ hτ; simpa [Fin.append_right] using hrealf j τ hτ
  have hεapp : ∀ i, 0 ≤ (Fin.append (fun _ : Fin 6 => εa) (fun _ : Fin n => εf) : Fin (6 + n) → ℝ) i := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa [Fin.append_left] using hεa
    · simpa [Fin.append_right] using hεf
  have hdev : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1,
      ‖(normalizedTransfer L κ (k + q) ((Fin.append A Pf i).γ τ) - B.s ((Fin.append A Pf i).γ τ) •
        (1 : SymSector ℂ (L2T L) (k + q) →L[ℂ] SymSector ℂ (L2T L) (k + q))) phi‖ ≤
      (Fin.append (fun _ : Fin 6 => εa) (fun _ : Fin n => εf) : Fin (6 + n) → ℝ) i := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · intro τ hτ; simpa [Fin.append_left] using hdeva i τ hτ
    · intro τ hτ; simpa [Fin.append_right] using hdevf j τ hτ
  refine (hmain q hN Z (Fin.append A Pf) hZ hIm hreal B phi hphi _ hεapp hdev).trans ?_
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC0)
  have hpi : 0 ≤ (2 * Real.pi * κ)⁻¹ := by have := Real.pi_pos; positivity
  refine mul_le_mul_of_nonneg_left ?_ hpi
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have h1 := rect_weighted_length_le ha hh.le R t T hRd ht
  have hw := fun i => wlen_nonneg (A i)
  calc ∑ i : Fin 6, εa * wlen (A i) + ∑ j : Fin n, εf * wlen (Pf j)
      = εa * ∑ i : Fin 6, wlen (A i) + εf * ∑ j : Fin n, wlen (Pf j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ εa * (4 * (∑ r ∈ R, T r) * (1 + h) ^ (d + 1) * (1 + a) ^ (d + 1)) + εf * Λ :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hεa) (mul_le_mul_of_nonneg_left hΛ hεf)

end QuantumNLS.MPLinearizationContours

#print axioms QuantumNLS.MPLinearizationContours.mp_linearization_contours
