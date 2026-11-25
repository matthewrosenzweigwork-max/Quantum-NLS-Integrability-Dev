import NlsGge.Hierarchy.ALMoments38
import NlsGge.Hierarchy.ALMomentsBridge38
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.Measure.ComplexGaussian
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open Finset MeasureTheory
open scoped ENNReal

section Fourier

variable {L : ℕ} [NeZero L]

theorem stdAddChar_conj38 (x : ZMod L) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hn : ‖(ZMod.stdAddChar x : ℂ)‖ = 1 := by
    rw [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

theorem stdAddChar_sum38 (x : ZMod L) :
    ∑ k : ZMod L, (ZMod.stdAddChar (k * x) : ℂ) = if x = 0 then (L : ℂ) else 0 := by
  classical
  have := AddChar.sum_mulShift (R := ZMod L) (R' := ℂ) (ψ := ZMod.stdAddChar) x
    (ZMod.isPrimitive_stdAddChar L)
  rw [this]
  simp [ZMod.card]

/-- Cross Parseval for the unnormalised DFT on `ZMod L`. -/
theorem dft_parseval38 (Φ Ψ : ZMod L → ℂ) :
    ∑ k, ZMod.dft Φ k * (starRingEnd ℂ) (ZMod.dft Ψ k) =
      (L : ℂ) * ∑ j, Φ j * (starRingEnd ℂ) (Ψ j) := by
  classical
  have h1 : ∀ k : ZMod L, ZMod.dft Φ k * (starRingEnd ℂ) (ZMod.dft Ψ k) =
      ∑ j : ZMod L, ∑ j' : ZMod L, (Φ j * (starRingEnd ℂ) (Ψ j')) *
        (ZMod.stdAddChar (k * (j' - j)) : ℂ) := by
    intro k
    simp only [ZMod.dft_apply, smul_eq_mul, map_sum, map_mul, stdAddChar_conj38, neg_neg]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    have : (ZMod.stdAddChar (k * (j' - j)) : ℂ) =
        ZMod.stdAddChar (-(j * k)) * ZMod.stdAddChar (j' * k) := by
      rw [← AddChar.map_add_eq_mul]; congr 1; ring
    rw [this]; ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j : ZMod L, ∑ k : ZMod L, ∑ j' : ZMod L, (Φ j * (starRingEnd ℂ) (Ψ j')) *
        (ZMod.stdAddChar (k * (j' - j)) : ℂ) = (L : ℂ) * (Φ j * (starRingEnd ℂ) (Ψ j)) := by
    intro j
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, stdAddChar_sum38]
    simp [sub_eq_zero, eq_comm]
    ring
  simp_rw [h2]
  rw [Finset.mul_sum]

/-- Real Parseval: `Σ_k |û_k|² = L Σ_j |Φ_j|²`. -/
theorem dft_parseval_norm38 (Φ : ZMod L → ℂ) :
    ∑ k, ‖ZMod.dft Φ k‖ ^ 2 = (L : ℝ) * ∑ j, ‖Φ j‖ ^ 2 := by
  have h := dft_parseval38 Φ Φ
  simp_rw [Complex.mul_conj'] at h
  exact_mod_cast h

/-- Cyclic shift `(S_s Φ)_i = Φ_{i-s}`. -/
def alShift38 (s : ZMod L) (Φ : ZMod L → ℂ) : ZMod L → ℂ := fun i => Φ (i - s)

theorem dft_shift38 (s : ZMod L) (Φ : ZMod L → ℂ) (k : ZMod L) :
    ZMod.dft (alShift38 s Φ) k = ZMod.stdAddChar (-(s * k)) * ZMod.dft Φ k := by
  simp only [ZMod.dft_apply, smul_eq_mul, alShift38, Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.addRight s)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Equiv.coe_addRight, add_sub_cancel_right]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2; ring

/-- Backward difference `(ΔΦ)_i = Φ_i - Φ_{i-1}`. -/
def alDelta38 (Φ : ZMod L → ℂ) : ZMod L → ℂ := fun i => Φ i - Φ (i - 1)

theorem dft_delta38 (Φ : ZMod L → ℂ) (k : ZMod L) :
    ZMod.dft (alDelta38 Φ) k = (1 - ZMod.stdAddChar (-k)) * ZMod.dft Φ k := by
  have h : alDelta38 Φ = Φ - alShift38 1 Φ := rfl
  rw [h, map_sub, Pi.sub_apply, dft_shift38]
  simp [sub_mul]

theorem dft_delta_iter38 (j : ℕ) (Φ : ZMod L → ℂ) (k : ZMod L) :
    ZMod.dft ((alDelta38)^[j] Φ) k = (1 - ZMod.stdAddChar (-k)) ^ j * ZMod.dft Φ k := by
  induction j generalizing Φ with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ, Function.comp_apply, ih, dft_delta38]
    ring

/-- `e(ν/L)` for a lifted integer frequency. -/
theorem stdAddChar_int38 (ν : ℤ) :
    (ZMod.stdAddChar (ν : ZMod L) : ℂ) = Complex.exp (((2 * Real.pi * ν / L : ℝ) : ℂ) * Complex.I) := by
  rw [ZMod.stdAddChar_coe]; push_cast; ring_nf

theorem re_stdAddChar_int38 (ν : ℤ) :
    (ZMod.stdAddChar (ν : ZMod L) : ℂ).re = Real.cos (2 * Real.pi * ν / L) := by
  rw [stdAddChar_int38, Complex.exp_ofReal_mul_I_re]

theorem im_stdAddChar_int38 (ν : ℤ) :
    (ZMod.stdAddChar (ν : ZMod L) : ℂ).im = Real.sin (2 * Real.pi * ν / L) := by
  rw [stdAddChar_int38, Complex.exp_ofReal_mul_I_im]

/-- `|1 - e(-ν/L)|² = (2 sin(πν/L))²`. -/
theorem norm_one_sub_stdAddChar38 (ν : ℤ) :
    ‖(1 : ℂ) - ZMod.stdAddChar (-(ν : ZMod L))‖ ^ 2 = (2 * Real.sin (Real.pi * ν / L)) ^ 2 := by
  have e : (-(ν : ZMod L)) = ((-ν : ℤ) : ZMod L) := by push_cast; rfl
  rw [e, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    re_stdAddChar_int38, im_stdAddChar_int38]
  rw [sin_sq_two38]
  have : 2 * Real.pi * ((-ν : ℤ) : ℝ) / L = -(2 * (Real.pi * ν / L)) := by push_cast; ring
  rw [this, Real.cos_neg, Real.sin_neg]
  have h2 := Real.sin_sq_add_cos_sq (2 * (Real.pi * ν / L))
  nlinarith [h2]

/-- The symbol `ω_{h,ν} = 2 sin(π ν h)/h` (`D:eq:omega`). -/
def alOmega38 (h : ℝ) (ν : ℤ) : ℝ := 2 * Real.sin (Real.pi * ν * h) / h

theorem alOmega38_sq (h : ℝ) (hh : h ≠ 0) (ν : ℤ) :
    alOmega38 h ν ^ 2 * h ^ 2 = (2 * Real.sin (Real.pi * ν * h)) ^ 2 := by
  unfold alOmega38; field_simp

/-- Fourier side of `Σ_i |(Δ^j α)_i|²` (Parseval): `L⁻¹ Σ_k (2 sin(π ν_k/L))^{2j} |û_k|²`. -/
theorem alDelta_parseval38 (j : ℕ) (α : ZMod L → ℂ) :
    ∑ i, ‖((alDelta38)^[j] α) i‖ ^ 2 =
      (L : ℝ)⁻¹ * ∑ k : ZMod L, (2 * Real.sin (Real.pi * (k.valMinAbs : ℝ) / L)) ^ (2 * j) *
        ‖ZMod.dft α k‖ ^ 2 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have h := dft_parseval_norm38 ((alDelta38)^[j] α)
  have h2 : ∀ k : ZMod L, ‖ZMod.dft ((alDelta38)^[j] α) k‖ ^ 2 =
      (2 * Real.sin (Real.pi * (k.valMinAbs : ℝ) / L)) ^ (2 * j) * ‖ZMod.dft α k‖ ^ 2 := by
    intro k
    have hk := norm_one_sub_stdAddChar38 (L := L) k.valMinAbs
    rw [ZMod.coe_valMinAbs] at hk
    rw [dft_delta_iter38, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm j 2, pow_mul, hk, ← pow_mul, mul_comm 2 j]
  simp_rw [h2] at h
  field_simp
  linarith


/-- Autocorrelation theorem: `L Σ_i α_i conj α_{i-m} = Σ_k e(mk) |û_k|²`. -/
theorem autocorr_dft38 (m : ℕ) (α : ZMod L → ℂ) :
    (L : ℂ) * ∑ i, α i * (starRingEnd ℂ) (α (i - (m : ZMod L))) =
      ∑ k : ZMod L, (ZMod.stdAddChar ((m : ZMod L) * k) : ℂ) * ((‖ZMod.dft α k‖ ^ 2 : ℝ) : ℂ) := by
  have h := dft_parseval38 α (alShift38 (m : ZMod L) α)
  simp only [alShift38] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [dft_shift38, map_mul, stdAddChar_conj38, neg_neg, Complex.ofReal_pow, ← Complex.mul_conj']
  ring

theorem re_autocorr_dft38 (m : ℕ) (α : ZMod L → ℂ) :
    (L : ℝ) * (∑ i, α i * (starRingEnd ℂ) (α (i - (m : ZMod L)))).re =
      ∑ k : ZMod L, Real.cos (2 * Real.pi * ((m : ℤ) * k.valMinAbs : ℤ) / L) * ‖ZMod.dft α k‖ ^ 2 := by
  have h := congrArg Complex.re (autocorr_dft38 m α)
  rw [show (L : ℂ) = ((L : ℝ) : ℂ) by simp, Complex.re_ofReal_mul] at h
  simp only [Complex.re_sum] at h
  have e : ∀ k : ZMod L, ((ZMod.stdAddChar ((m : ZMod L) * k) : ℂ) * ((‖ZMod.dft α k‖ ^ 2 : ℝ) : ℂ)).re
      = Real.cos (2 * Real.pi * ((m : ℤ) * k.valMinAbs : ℤ) / L) * ‖ZMod.dft α k‖ ^ 2 := by
    intro k
    have hk : (m : ZMod L) * k = (((m : ℤ) * k.valMinAbs : ℤ) : ZMod L) := by
      simp
    rw [Complex.re_mul_ofReal, hk, re_stdAddChar_int38]
  simp_rw [e] at h
  rw [Complex.re_sum]
  exact h

/-- The quadratic part of `K_j` (`D:eq:Kj` with `M_d`, `C_k` replaced by their quadratic parts). -/
def alKQuad38 (α : ZMod L → ℂ) (j : ℕ) : ℝ :=
  (Nat.choose (2 * j) j : ℝ) * ∑ i, ‖α i‖ ^ 2 +
    2 * ∑ m ∈ Icc 1 j, (-1 : ℝ) ^ m * (Nat.choose (2 * j) (j - m) : ℝ) *
      (∑ i, α i * (starRingEnd ℂ) (α (i - (m : ZMod L)))).re

theorem alKQuad_fourier38 (α : ZMod L → ℂ) (j : ℕ) :
    alKQuad38 α j = (L : ℝ)⁻¹ * ∑ k : ZMod L,
      (2 * Real.sin (Real.pi * (k.valMinAbs : ℝ) / L)) ^ (2 * j) * ‖ZMod.dft α k‖ ^ 2 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hb : ∀ k : ZMod L, (2 * Real.sin (Real.pi * (k.valMinAbs : ℝ) / L)) ^ (2 * j) =
      (Nat.choose (2 * j) j : ℝ) + 2 * ∑ m ∈ Icc 1 j, (-1 : ℝ) ^ m * (Nat.choose (2 * j) (j - m) : ℝ) *
        Real.cos (2 * Real.pi * ((m : ℤ) * k.valMinAbs : ℤ) / L) := by
    intro k
    rw [pow_mul, sin_sq_two38 (Real.pi * (k.valMinAbs : ℝ) / L), cos_binomial38 j]
    refine congrArg₂ _ rfl (congrArg _ (Finset.sum_congr rfl fun m _ => ?_))
    congr 2
    push_cast; ring
  have hN := dft_parseval_norm38 α
  have hC := fun m : ℕ => re_autocorr_dft38 m α
  set cs : ZMod L → ℕ → ℝ := fun k m =>
    Real.cos (2 * Real.pi * ((m : ℤ) * k.valMinAbs : ℤ) / L) with hcs
  set n : ZMod L → ℝ := fun k => ‖ZMod.dft α k‖ ^ 2 with hn
  set c : ℕ → ℝ := fun m => (-1 : ℝ) ^ m * (Nat.choose (2 * j) (j - m) : ℝ) with hc
  have e1 : ∑ k : ZMod L, (2 * Real.sin (Real.pi * (k.valMinAbs : ℝ) / L)) ^ (2 * j) * n k =
      ∑ k : ZMod L, ((Nat.choose (2 * j) j : ℝ) * n k +
        2 * ∑ m ∈ Icc 1 j, c m * (cs k m * n k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb k, add_mul, mul_assoc, Finset.sum_mul]
    congr 2
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hc, hcs]; ring
  have e2 : ∑ k : ZMod L, ((Nat.choose (2 * j) j : ℝ) * n k +
        2 * ∑ m ∈ Icc 1 j, c m * (cs k m * n k)) =
      (Nat.choose (2 * j) j : ℝ) * ∑ k, n k + 2 * ∑ m ∈ Icc 1 j, c m * ∑ k : ZMod L, cs k m * n k := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [e1, e2, hN]
  unfold alKQuad38
  have e3 : ∀ m ∈ Icc 1 j, c m * ∑ k : ZMod L, cs k m * n k =
      (L : ℝ) * ((-1 : ℝ) ^ m * (Nat.choose (2 * j) (j - m) : ℝ) *
        (∑ i, α i * (starRingEnd ℂ) (α (i - (m : ZMod L)))).re) := by
    intro m _
    simp only [hc]
    rw [← hC m]
    ring
  rw [Finset.sum_congr rfl e3, ← Finset.mul_sum]
  field_simp

/-- `Σ_i |(Δ^j α)_i|²` equals the quadratic part of `K_j`. -/
theorem alKQuad_eq_delta38 (α : ZMod L → ℂ) (j : ℕ) :
    alKQuad38 α j = ∑ i, ‖((alDelta38)^[j] α) i‖ ^ 2 := by
  rw [alKQuad_fourier38, alDelta_parseval38]

theorem exists_pos_le_finset38 (s : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ m ∈ s, 0 < f m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m ∈ s, δ ≤ f m := by
  have hS : 0 ≤ ∑ m ∈ s, (f m)⁻¹ := Finset.sum_nonneg (fun m hm => inv_nonneg.2 (hf m hm).le)
  refine ⟨(1 + ∑ m ∈ s, (f m)⁻¹)⁻¹, by positivity, fun m hm => ?_⟩
  have h1 : (f m)⁻¹ ≤ ∑ m ∈ s, (f m)⁻¹ :=
    Finset.single_le_sum (f := fun m => (f m)⁻¹) (fun m hm => inv_nonneg.2 (hf m hm).le) hm
  rw [inv_le_comm₀ (by positivity) (hf m hm)]
  linarith

/-- **Quadratic part of `K_j` (`D:eq:Kj`, `D:eq:Cquadratic`)**: for admissible `α`, as `t → 0`,
`K_j(tα) = t² Σ_i |(Δ^j α)_i|² + O(t⁴)`, with `(Δα)_i = α_i - α_{i-1}` (cyclic). -/
theorem alK38_quadratic_delta38 {α : ZMod L → ℂ} (hα : IsALField38 α) (j : ℕ) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
      |alK38 (t • α) j - t ^ 2 * ∑ i, ‖((alDelta38)^[j] α) i‖ ^ 2| ≤ C * t ^ 4 := by
  obtain ⟨C0, δ0, hC0, hδ0, h0⟩ := alMass38_quadratic38 hα
  choose! Cf δf hCf hδf hbf using fun (m : ℕ) (hm : m ∈ Icc 1 j) =>
    alC38_quadratic38 hα (Finset.mem_Icc.1 hm).1
  obtain ⟨δ1, hδ1, hδ1f⟩ := exists_pos_le_finset38 (Icc 1 j) δf hδf
  refine ⟨(Nat.choose (2 * j) j : ℝ) * C0 + 1 + 2 * ∑ m ∈ Icc 1 j,
      (Nat.choose (2 * j) (j - m) : ℝ) * Cf m, min δ0 δ1, by
    have : 0 ≤ ∑ m ∈ Icc 1 j, (Nat.choose (2 * j) (j - m) : ℝ) * Cf m :=
      Finset.sum_nonneg fun m hm => mul_nonneg (Nat.cast_nonneg _) (hCf m hm).le
    have : 0 ≤ (Nat.choose (2 * j) j : ℝ) * C0 := mul_nonneg (Nat.cast_nonneg _) hC0.le
    positivity, lt_min hδ0 hδ1, fun t ht htd => ?_⟩
  have htd0 : |t| < δ0 := lt_of_lt_of_le htd (min_le_left _ _)
  have htd1 : |t| < δ1 := lt_of_lt_of_le htd (min_le_right _ _)
  have hM := h0 t ht htd0
  have hm_aux : ∀ m ∈ Icc 1 j, ‖alC38 (t • α) m - (t : ℂ) ^ 2 *
      ∑ i : ZMod L, α i * (starRingEnd ℂ) (α (i - (m : ZMod L)))‖ ≤ Cf m * t ^ 4 :=
    fun m hm => hbf m hm t ht (lt_of_lt_of_le htd1 (hδ1f m hm))
  rw [← alKQuad_eq_delta38]
  unfold alKQuad38 alK38
  set cm : ℕ → ℝ := fun m => (-1 : ℝ) ^ m * (Nat.choose (2 * j) (j - m) : ℝ) with hcm
  set A : ℕ → ℂ := fun m => ∑ i, α i * (starRingEnd ℂ) (α (i - (m : ZMod L))) with hA
  have hcmb : ∀ m, |cm m| = (Nat.choose (2 * j) (j - m) : ℝ) := fun m => by
    simp only [hcm, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  have e : (Nat.choose (2 * j) j : ℝ) * alMass38 L (t • α) +
        2 * ∑ k ∈ Icc 1 j, cm k * (alC38 (t • α) k).re -
      t ^ 2 * ((Nat.choose (2 * j) j : ℝ) * ∑ i, ‖α i‖ ^ 2 +
        2 * ∑ m ∈ Icc 1 j, cm m * (A m).re) =
      (Nat.choose (2 * j) j : ℝ) * (alMass38 L (t • α) - t ^ 2 * ∑ i, ‖α i‖ ^ 2) +
        2 * ∑ m ∈ Icc 1 j, cm m * ((alC38 (t • α) m).re - t ^ 2 * (A m).re) := by
    have : ∑ m ∈ Icc 1 j, cm m * ((alC38 (t • α) m).re - t ^ 2 * (A m).re) =
        ∑ k ∈ Icc 1 j, cm k * (alC38 (t • α) k).re - t ^ 2 * ∑ m ∈ Icc 1 j, cm m * (A m).re := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [this]; ring
  have hre : ∀ m ∈ Icc 1 j, |(alC38 (t • α) m).re - t ^ 2 * (A m).re| ≤ Cf m * t ^ 4 := by
    intro m hm
    have h1 := hm_aux m hm
    have h2 : (alC38 (t • α) m).re - t ^ 2 * (A m).re =
        (alC38 (t • α) m - (t : ℂ) ^ 2 * A m).re := by
      rw [Complex.sub_re, show (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [h2]
    exact (Complex.abs_re_le_norm _).trans h1
  rw [e]
  have hT : 0 ≤ t ^ 4 := by positivity
  have hsum : |∑ m ∈ Icc 1 j, cm m * ((alC38 (t • α) m).re - t ^ 2 * (A m).re)| ≤
      ∑ m ∈ Icc 1 j, (Nat.choose (2 * j) (j - m) : ℝ) * (Cf m * t ^ 4) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    rw [abs_mul, hcmb]
    exact mul_le_mul_of_nonneg_left (hre m hm) (Nat.cast_nonneg _)
  have hmass : |(Nat.choose (2 * j) j : ℝ) * (alMass38 L (t • α) - t ^ 2 * ∑ i, ‖α i‖ ^ 2)| ≤
      (Nat.choose (2 * j) j : ℝ) * (C0 * t ^ 4) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _)
  have hsum' : ∑ m ∈ Icc 1 j, (Nat.choose (2 * j) (j - m) : ℝ) * (Cf m * t ^ 4) =
      (∑ m ∈ Icc 1 j, (Nat.choose (2 * j) (j - m) : ℝ) * Cf m) * t ^ 4 := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
  calc _ ≤ |(Nat.choose (2 * j) j : ℝ) * (alMass38 L (t • α) - t ^ 2 * ∑ i, ‖α i‖ ^ 2)| +
        |2 * ∑ m ∈ Icc 1 j, cm m * ((alC38 (t • α) m).re - t ^ 2 * (A m).re)| := abs_add_le _ _
    _ ≤ (Nat.choose (2 * j) j : ℝ) * (C0 * t ^ 4) +
        2 * ∑ m ∈ Icc 1 j, (Nat.choose (2 * j) (j - m) : ℝ) * (Cf m * t ^ 4) := by
      have h2 : |2 * ∑ m ∈ Icc 1 j, cm m * ((alC38 (t • α) m).re - t ^ 2 * (A m).re)| =
          2 * |∑ m ∈ Icc 1 j, cm m * ((alC38 (t • α) m).re - t ^ 2 * (A m).re)| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      rw [h2]; linarith
    _ ≤ _ := by rw [hsum']; nlinarith [hT]

end Fourier

/-! ### The real Jacobian of the inverse DFT -/

section Jacobian

variable {L : ℕ} [NeZero L]

/-- The DFT as an `ℝ`-linear map of `ℂ^L ≅ ℝ^{2L}`. -/
def dftR38 : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ) :=
  (ZMod.dft : (ZMod L → ℂ) ≃ₗ[ℂ] (ZMod L → ℂ)).toLinearMap.restrictScalars ℝ

def reflR38 : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ) := LinearMap.funLeft ℝ ℂ (fun j : ZMod L => -j)

theorem finrank_pi38 : Module.finrank ℝ (ZMod L → ℂ) = 2 * L := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, ZMod.card]; ring

theorem abs_det_reflR38 : |LinearMap.det (reflR38 (L := L))| = 1 := by
  have h : reflR38 (L := L) ∘ₗ reflR38 = LinearMap.id := by
    ext Φ j; simp [reflR38]
  have h2 := congrArg LinearMap.det h
  rw [LinearMap.det_comp, LinearMap.det_id] at h2
  have h3 : |LinearMap.det (reflR38 (L := L))| * |LinearMap.det (reflR38 (L := L))| = 1 := by
    rw [← abs_mul, h2]; simp
  nlinarith [abs_nonneg (LinearMap.det (reflR38 (L := L)))]

theorem abs_det_dftR38 : |LinearMap.det (dftR38 (L := L))| = (L : ℝ) ^ L := by
  have h : dftR38 (L := L) ∘ₗ dftR38 = (L : ℝ) • reflR38 := by
    ext Φ j
    simp [dftR38, reflR38, ZMod.dft_dft, Complex.real_smul]
  have h2 := congrArg LinearMap.det h
  rw [LinearMap.det_comp, LinearMap.det_smul, finrank_pi38] at h2
  have h3 : |LinearMap.det (dftR38 (L := L))| ^ 2 = ((L : ℝ) ^ L) ^ 2 := by
    have hLn : |(L : ℝ)| = L := abs_of_nonneg (by positivity)
    have := congrArg abs h2
    rw [abs_mul, abs_mul, abs_pow, hLn, abs_det_reflR38,
      mul_one] at this
    rw [← pow_mul, pow_two, this, mul_comm L 2]
  have hL : (0 : ℝ) ≤ (L : ℝ) ^ L := by positivity
  exact (sq_eq_sq₀ (abs_nonneg _) hL).1 h3

/-- ℝ-linear inverse DFT -/
def synthR38 : (ZMod L → ℂ) ≃ₗ[ℝ] (ZMod L → ℂ) :=
  (ZMod.dft : (ZMod L → ℂ) ≃ₗ[ℂ] (ZMod L → ℂ)).symm.restrictScalars ℝ

theorem det_synth_mul38 : LinearMap.det (synthR38 (L := L) : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ)) *
    LinearMap.det (dftR38 (L := L)) = 1 := by
  rw [← LinearMap.det_comp]
  have : (synthR38 (L := L) : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ)) ∘ₗ dftR38 = LinearMap.id := by
    ext Φ j; simp [synthR38, dftR38]
  rw [this, LinearMap.det_id]

theorem det_synth_ne38 : LinearMap.det (synthR38 (L := L) : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ)) ≠ 0 := by
  intro h; have := det_synth_mul38 (L := L); rw [h, zero_mul] at this; exact zero_ne_one this

/-- The real Jacobian of `û ↦ α = 𝓕⁻ û`. -/
theorem map_synth_volume38 :
    Measure.map (synthR38 (L := L)) (volume : Measure (ZMod L → ℂ)) =
      ENNReal.ofReal ((L : ℝ) ^ L) • (volume : Measure (ZMod L → ℂ)) := by
  rw [show (⇑(synthR38 (L := L))) = ⇑(synthR38 (L := L) : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ)) from rfl,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume det_synth_ne38]
  congr 2
  have h := det_synth_mul38 (L := L)
  have hT : LinearMap.det (dftR38 (L := L)) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h; exact zero_ne_one h
  have : (LinearMap.det (synthR38 (L := L) : (ZMod L → ℂ) →ₗ[ℝ] (ZMod L → ℂ)))⁻¹ =
      LinearMap.det (dftR38 (L := L)) := by
    exact inv_eq_of_mul_eq_one_right h
  rw [this, abs_det_dftR38]

theorem integral_synth38 (F : (ZMod L → ℂ) → ℝ) :
    ∫ α, F α = ((L : ℝ) ^ L)⁻¹ * ∫ û, F (ZMod.dft.symm û) := by
  have hme : MeasurableEmbedding (synthR38 (L := L)) :=
    (synthR38 (L := L)).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have h1 := hme.integral_map (μ := (volume : Measure (ZMod L → ℂ))) F
  rw [map_synth_volume38, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h1
  have e : ∀ û, synthR38 (L := L) û = ZMod.dft.symm û := fun û => rfl
  simp_rw [e] at h1
  rw [← h1, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne L))), one_mul]

end Jacobian

/-! ### Complex Gaussian products as Lebesgue densities -/

section GaussianProduct

open NlsGge.Measure

variable {ι : Type} [Fintype ι]

def gDens38 (a : ℝ) (z : ℂ) : ℝ := (a / Real.pi) * Real.exp (-a * ‖z‖ ^ 2)

theorem gDens_nonneg38 {a : ℝ} (ha : 0 < a) (z : ℂ) : 0 ≤ gDens38 a z := by
  unfold gDens38; positivity

theorem gDens_integrable38 {a : ℝ} (ha : 0 < a) : Integrable (gDens38 a) := by
  unfold gDens38
  exact (integrable_complexGaussianKernel a ha).const_mul _

theorem gDens_meas38 (a : ℝ) : Measurable (gDens38 a) := by
  unfold gDens38; fun_prop

theorem pi_complexGaussian_eq38 (a : ι → ℝ) (ha : ∀ k, 0 < a k) :
    Measure.pi (fun k => complexGaussian (a k)) =
      (volume : Measure (ι → ℂ)).withDensity
        (fun x => ENNReal.ofReal (∏ k, gDens38 (a k) (x k))) := by
  refine Measure.pi_eq fun s hs => ?_
  have hcg : ∀ k, complexGaussian (a k) = (volume : Measure ℂ).withDensity
      (fun z => ENNReal.ofReal (gDens38 (a k) z)) := fun k => complexGaussian_density (a k) (ha k)
  have hmeasR : Measurable (fun x : ι → ℂ => ENNReal.ofReal (∏ k, gDens38 (a k) (x k))) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun k _ => ?_)
    exact (gDens_meas38 (a k)).comp (measurable_pi_apply k)
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  simp_rw [hcg, withDensity_apply _ (hs _)]
  set g : ι → ℂ → ℝ := fun k => (s k).indicator (gDens38 (a k)) with hg
  have hgi : ∀ k, Integrable (g k) := fun k => (gDens_integrable38 (ha k)).indicator (hs k)
  have hg0 : ∀ k z, 0 ≤ g k z := fun k z => by
    simp only [hg]; exact Set.indicator_nonneg (fun z _ => gDens_nonneg38 (ha k) z) z
  have h1 : ∫⁻ x : ι → ℂ in Set.pi Set.univ s, ENNReal.ofReal (∏ k, gDens38 (a k) (x k)) =
      ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ k, g k (x k)) := by
    rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Set.pi Set.univ s
    · rw [Set.indicator_of_mem hx]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [hg]; rw [Set.indicator_of_mem (hx k (Set.mem_univ k))]
    · rw [Set.indicator_of_notMem hx]
      have : ∃ k, x k ∉ s k := by
        by_contra hcon; push Not at hcon
        exact hx (fun k _ => hcon k)
      obtain ⟨k, hk⟩ := this
      have : ∏ k, g k (x k) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) (by simp only [hg]; rw [Set.indicator_of_notMem hk])
      rw [this]; simp
  rw [h1]
  have hint : Integrable (fun x : ι → ℂ => ∏ k, g k (x k)) (Measure.pi fun _ => (volume : Measure ℂ)) :=
    Integrable.fintype_prod (fun k => hgi k)
  have h2 := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun k _ => hg0 k (x k))
  have h3 : ∫⁻ x : ι → ℂ, ENNReal.ofReal (∏ k, g k (x k)) = ENNReal.ofReal (∏ k, ∫ z, g k z) := by
    rw [← integral_fintype_prod_eq_prod (fun k z => g k z)]
    exact h2.symm
  rw [h3, ENNReal.ofReal_prod_of_nonneg (fun k _ => integral_nonneg (hg0 k))]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hgi k) (Filter.Eventually.of_forall (hg0 k))]
  simp only [hg]
  rw [← lintegral_indicator (hs k)]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ s k <;> simp [Set.indicator, hz]
  

theorem integral_gauss_pi38 (a : ι → ℝ) (ha : ∀ k, 0 < a k) (F : (ι → ℂ) → ℝ) :
    ∫ x, F x ∂(Measure.pi fun k => complexGaussian (a k)) =
      (∏ k, a k / Real.pi) * ∫ x, Real.exp (-∑ k, a k * ‖x k‖ ^ 2) * F x := by
  rw [pi_complexGaussian_eq38 a ha]
  have hmeas : Measurable (fun x : ι → ℂ => (∏ k, gDens38 (a k) (x k)).toNNReal) := by
    refine Measurable.real_toNNReal (Finset.measurable_prod _ fun k _ => ?_)
    exact (gDens_meas38 (a k)).comp (measurable_pi_apply k)
  have := integral_withDensity_eq_integral_smul (μ := (volume : Measure (ι → ℂ))) hmeas F
  have e : (fun x : ι → ℂ => ENNReal.ofReal (∏ k, gDens38 (a k) (x k))) =
      fun x => ((∏ k, gDens38 (a k) (x k)).toNNReal : ENNReal) := rfl
  rw [e, this]
  have hp : ∀ x : ι → ℂ, ∏ k, gDens38 (a k) (x k) =
      (∏ k, a k / Real.pi) * Real.exp (-∑ k, a k * ‖x k‖ ^ 2) := by
    intro x
    unfold gDens38
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 2
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ ∏ k, gDens38 (a k) (x k) := Finset.prod_nonneg fun k _ => gDens_nonneg38 (ha k) _
  beta_reduce
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ h0, hp]
  ring


end GaussianProduct


/-! ### The quadratic symbol `W(ω_{h,k})` and the Gaussian rates -/

section Symbol

variable {L : ℕ} [NeZero L] {lo up : ℝ} {c : ℕ → ℝ}

/-- Parseval for the mass: `Σ_i |α_i|² = h Σ_k |û_k|²` for `h = 1/L`. -/
theorem sum_norm_sq_eq_dft38 (α : ZMod L → ℂ) {h : ℝ} (hh : h = (L : ℝ)⁻¹) :
    ∑ i, ‖α i‖ ^ 2 = h * ∑ k, ‖ZMod.dft α k‖ ^ 2 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [dft_parseval_norm38, hh]; field_simp

/-- The interpolant: `h · u(jh) = α_j` with `u(jh) = Σ_k û(k) e^{2πi k j h}`, `h = 1/L`. -/
theorem dft_symm_eq_interp38 (û : ZMod L → ℂ) (j : ZMod L) {h : ℝ} (hh : h = (L : ℝ)⁻¹) :
    ZMod.dft.symm û j = (h : ℂ) * ∑ k, û k * ZMod.stdAddChar (k * j) := by
  rw [ZMod.invDFT_apply, hh]
  simp only [smul_eq_mul, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm k j]; ring

/-- The `j`-th term of the quadratic part of `E_{W,h}`: `β_j h^{-2j-1} Σ_i |(Δ^j α)_i|²`. -/
def alEnergyQuadTerm38 (c : ℕ → ℝ) (h : ℝ) (α : ZMod L → ℂ) (j : ℕ) : ℝ :=
  NlsGge.coefficient c j * ((h⁻¹) ^ (2 * j + 1) * ∑ i, ‖((alDelta38)^[j] α) i‖ ^ 2)

/-- The quadratic part of `E_{W,h}` is a termwise sum of quadratic parts of `K_j`
(`alK38_quadratic_delta38`), `Q_{2j,h} = h^{-2j-1} K_j`. -/
theorem alEnergyQuadTerm_eq38 (α : ZMod L → ℂ) {h : ℝ} (hh : h = (L : ℝ)⁻¹) (j : ℕ) :
    alEnergyQuadTerm38 c h α j =
      ∑ k : ZMod L, NlsGge.weightTerm c (alOmega38 h k.valMinAbs) j * ‖ZMod.dft α k‖ ^ 2 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hh0 : h ≠ 0 := by rw [hh]; exact inv_ne_zero hL
  unfold alEnergyQuadTerm38
  rw [alDelta_parseval38, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold NlsGge.weightTerm alOmega38
  have e1 : Real.pi * (k.valMinAbs : ℝ) * h = Real.pi * (k.valMinAbs : ℝ) / L := by
    rw [hh]; ring
  rw [e1, hh]
  field_simp
  ring

/-- **Quadratic symbol of `E_{W,h}`** (`D:eq:omega`): the series of quadratic parts of the
`β_j Q_{2j,h}` converges and sums to `Σ_k W(ω_{h,k}) |û_k|²`, `ω_{h,k} = 2 sin(πkh)/h`,
`k = valMinAbs`. -/
theorem alEnergyQuad_hasSum38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c)
    (α : ZMod L → ℂ) {h : ℝ} (hh : h = (L : ℝ)⁻¹) :
    HasSum (alEnergyQuadTerm38 c h α)
      (∑ k : ZMod L, NlsGge.Weights.weight c (alOmega38 h k.valMinAbs) * ‖ZMod.dft α k‖ ^ 2) := by
  have : alEnergyQuadTerm38 c h α = fun j => ∑ k : ZMod L,
      NlsGge.weightTerm c (alOmega38 h k.valMinAbs) j * ‖ZMod.dft α k‖ ^ 2 :=
    funext (alEnergyQuadTerm_eq38 α hh)
  rw [this]
  refine hasSum_sum fun k _ => ?_
  exact (NlsGge.Weights.weightTerm_summable lo up c hc.1 (fun i => (hc.2.2 i).1)
    (fun i => (hc.2.2 i).2) _).hasSum.mul_right _

/-- The Gaussian rate `a_{h,k} = W(ω_{h,k}) - h` (`D:eq:ALrates`) at the integer frequency `ν`. -/
def alRate38 (c : ℕ → ℝ) (h : ℝ) (ν : ℤ) : ℝ :=
  NlsGge.Weights.weight c (alOmega38 h ν) - h

/-- Quadratic part of `E_{W,h} - M_d` has symbol `a_{h,k}`: `Σ_k W(ω_k)|û_k|² - Σ_i |α_i|²
= Σ_k a_{h,k} |û_k|²`. -/
theorem alRate_quadratic38 (α : ZMod L → ℂ) {h : ℝ} (hh : h = (L : ℝ)⁻¹) :
    ∑ k : ZMod L, NlsGge.Weights.weight c (alOmega38 h k.valMinAbs) * ‖ZMod.dft α k‖ ^ 2 -
        ∑ i, ‖α i‖ ^ 2 =
      ∑ k : ZMod L, alRate38 c h k.valMinAbs * ‖ZMod.dft α k‖ ^ 2 := by
  rw [sum_norm_sq_eq_dft38 α hh, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by unfold alRate38; ring

/-- Every rate is positive as soon as `h < β_0`-lower bound `lo` (`h` small). -/
theorem alRate38_pos (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ} (hh : h < lo)
    (ν : ℤ) : 0 < alRate38 c h ν := by
  have := NlsGge.Weights.weight_lower lo up c hc.1 (fun i => (hc.2.2 i).1)
    (fun i => (hc.2.2 i).2) (alOmega38 h ν)
  unfold alRate38; linarith

omit [NeZero L] in
/-- Threshold: for `h = 1/L` with `L > 1/lo`, all rates are positive. -/
theorem alRate38_pos_of_mesh38 (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) {h : ℝ}
    (hh : h = (L : ℝ)⁻¹) (hL : lo⁻¹ < (L : ℝ)) (ν : ℤ) : 0 < alRate38 c h ν := by
  refine alRate38_pos hc ?_ ν
  rw [hh]
  have hlo := hc.1
  have hL0 : 0 < (L : ℝ) := lt_trans (inv_pos.2 hlo) hL
  rw [inv_lt_comm₀ hL0 hlo]; exact hL

end Symbol


/-! ### The exact partition identity `D:eq:ALnormalizer` -/

section Normalizer

open ProbabilityTheory NlsGge.Measure

variable (L : ℕ) [NeZero L]

open Classical in
/-- The canonical partition function `𝒵_h = ∫_{𝔻^L} e^{-E_{W,h}(α)} ∏_j (1-|α_j|²)^{-1} d²α`
(`D:eq:ALfullmeasure`), `d²α` the product of planar Lebesgue measures. -/
def alPartition38 (c : ℕ → ℝ) (h : ℝ) : ℝ :=
  ∫ α : ZMod L → ℂ, if IsALField38 α then
    Real.exp (-alEnergy38 c h α) * ∏ j, (1 - ‖α j‖ ^ 2)⁻¹ else 0

variable {L}

/-- The nonlinear remainder `R_h` (`D:eq:ALR`) in Fourier coordinates `û`:
`R_h = E_{W,h}(α) - M_d(α) - Σ_k a_{h,k}|û_k|²`, `α = 𝓕⁻ û` (so `α_j = h u(jh)`). -/
def alRemainder38 (c : ℕ → ℝ) (h : ℝ) (û : ZMod L → ℂ) : ℝ :=
  alEnergy38 c h (ZMod.dft.symm û) - alMass38 L (ZMod.dft.symm û) -
    ∑ k : ZMod L, alRate38 c h k.valMinAbs * ‖û k‖ ^ 2

open Classical in
/-- `f_h = 1_{h max_j |u(jh)| < 1} e^{-R_h}` (`D:eq:ALf`). -/
def alReweight38 (c : ℕ → ℝ) (h : ℝ) (û : ZMod L → ℂ) : ℝ :=
  if IsALField38 (ZMod.dft.symm û) then Real.exp (-alRemainder38 c h û) else 0

/-- The Gaussian `γ_h` on the Fourier coordinates: independent proper complex Gaussians,
real-component variance `1/(2 a_{h,k})`. -/
def alGauss38 (c : ℕ → ℝ) (h : ℝ) : Measure (ZMod L → ℂ) :=
  Measure.pi fun k : ZMod L => complexGaussian (alRate38 c h k.valMinAbs)

/-- `Z_h = ∫ f_h dγ_h` (`D:eq:ALf`). -/
def alZ38 (c : ℕ → ℝ) (h : ℝ) : ℝ := ∫ û, alReweight38 c h û ∂(alGauss38 (L := L) c h)

theorem exp_alMass38 {α : ZMod L → ℂ} (hα : IsALField38 α) :
    Real.exp (alMass38 L α) = ∏ j, (1 - ‖α j‖ ^ 2)⁻¹ := by
  unfold alMass38
  rw [Real.exp_neg, Real.exp_sum, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have h1 : ‖α j‖ ^ 2 < 1 := by
    have := hα j; have := norm_nonneg (α j); nlinarith
  rw [Real.exp_log (by linarith)]

/-- **`D:eq:ALnormalizer`**: for `h = 1/L` and every rate positive (guaranteed by `h < β_0`-bound,
`alRate38_pos_of_mesh38`),
`𝒵_h = h^L ∏_{|k|≤N} (π / a_{h,k}) Z_h`. -/
theorem alGaussianNormalizer38 (c : ℕ → ℝ) {h : ℝ} (hh : h = (L : ℝ)⁻¹)
    (ha : ∀ ν : ℤ, 0 < alRate38 c h ν) :
    alPartition38 L c h =
      h ^ L * (∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs) * alZ38 (L := L) c h := by
  classical
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne L
  -- Step 1: real Jacobian of `û ↦ 𝓕⁻ û`.
  unfold alPartition38
  rw [integral_synth38]
  have hJ : ((L : ℝ) ^ L)⁻¹ = h ^ L := by rw [hh, inv_pow]
  rw [hJ]
  -- Step 2: pointwise factorization of the integrand.
  have hpt : ∀ û : ZMod L → ℂ,
      (if IsALField38 (ZMod.dft.symm û) then
        Real.exp (-alEnergy38 c h (ZMod.dft.symm û)) *
          ∏ j, (1 - ‖(ZMod.dft.symm û) j‖ ^ 2)⁻¹ else 0) =
      Real.exp (-∑ k : ZMod L, alRate38 c h k.valMinAbs * ‖û k‖ ^ 2) * alReweight38 c h û := by
    intro û
    unfold alReweight38
    by_cases hα : IsALField38 (ZMod.dft.symm û)
    · simp only [hα, ↓reduceIte]
      rw [← exp_alMass38 hα, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold alRemainder38; ring
    · simp only [hα, ↓reduceIte, mul_zero]
  simp_rw [hpt]
  -- Step 3: Gaussian integral.
  have hG := integral_gauss_pi38 (fun k : ZMod L => alRate38 c h k.valMinAbs)
    (fun k => ha _) (alReweight38 c h)
  have hprod : (∏ k : ZMod L, alRate38 c h k.valMinAbs / Real.pi) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => div_ne_zero (ha _).ne' Real.pi_ne_zero
  have hG' : ∫ û, Real.exp (-∑ k : ZMod L, alRate38 c h k.valMinAbs * ‖û k‖ ^ 2) *
      alReweight38 c h û = (∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs) *
        ∫ û, alReweight38 c h û ∂(alGauss38 (L := L) c h) := by
    have : (∏ k : ZMod L, Real.pi / alRate38 c h k.valMinAbs) =
        (∏ k : ZMod L, alRate38 c h k.valMinAbs / Real.pi)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [inv_div]
    rw [this]
    unfold alGauss38
    rw [hG]
    field_simp
  rw [hG']
  unfold alZ38
  ring

end Normalizer


/-! ### Paper form: frequencies `|k| ≤ N`, `L = 2N+1`, threshold on the mesh -/

section PaperForm

theorem prod_valMinAbs_eq_Icc38 (N : ℕ) (F : ℤ → ℝ) :
    ∏ k : ZMod (2 * N + 1), F k.valMinAbs = ∏ ν ∈ Finset.Icc (-(N : ℤ)) N, F ν := by
  have hmem : ∀ k : ZMod (2 * N + 1), k.valMinAbs ∈ Finset.Icc (-(N : ℤ)) N := by
    intro k
    have h1 := ZMod.natAbs_valMinAbs_le k
    have h2 : (2 * N + 1) / 2 = N := by omega
    rw [h2] at h1
    rw [Finset.mem_Icc]; omega
  have himg : (Finset.univ : Finset (ZMod (2 * N + 1))).image ZMod.valMinAbs =
      Finset.Icc (-(N : ℤ)) N := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx
      exact hmem k
    · rw [Finset.card_image_of_injective _ ZMod.injective_valMinAbs]
      simp [ZMod.card]
      omega
  rw [← himg, Finset.prod_image (fun a _ b _ h => ZMod.injective_valMinAbs h)]

/-- **`D:eq:ALnormalizer`, paper form.**  For `L = 2N+1`, `h = 1/L`, and `L > 1/lo` (so that
`h < lo ≤ β_0 ≤ W(·)` makes every rate `a_{h,k} = W(ω_{h,k}) - h` positive),
`𝒵_h = h^L ∏_{|k|≤N} (π/a_{h,k}) Z_h`, with `Z_h = ∫ f_h dγ_h`. -/
theorem alGaussianNormalizer_Icc38 {lo up : ℝ} {c : ℕ → ℝ}
    (hc : NlsGge.Pilot.AdmittedCoefficients lo up c) (N : ℕ) {h : ℝ}
    (hh : h = ((2 * N + 1 : ℕ) : ℝ)⁻¹) (hN : lo⁻¹ < ((2 * N + 1 : ℕ) : ℝ)) :
    alPartition38 (2 * N + 1) c h =
      h ^ (2 * N + 1) * (∏ ν ∈ Finset.Icc (-(N : ℤ)) N, Real.pi / alRate38 c h ν) *
        alZ38 (L := 2 * N + 1) c h := by
  rw [← prod_valMinAbs_eq_Icc38 N (fun ν => Real.pi / alRate38 c h ν)]
  exact alGaussianNormalizer38 c hh (alRate38_pos_of_mesh38 hc hh hN)

end PaperForm


end NlsGge.AblowitzLadik
end
