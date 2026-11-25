import NlsGge.Hierarchy.ALLaurent38
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Batch 38, E07-5a: the exact coefficients `C_1`, `C_2` of `D:eq:C12`
(paper/v2.tex l.1893-1897). -/

set_option autoImplicit false
noncomputable section
namespace NlsGge.AblowitzLadik
open Polynomial

structure ALSt38 where
  (a2 a4 b1 b3 c1 c3 d0 d2 d4 : ℂ)

def alStStep38 (u v : ℂ) (s : ALSt38) : ALSt38 where
  a2 := s.a2 + u * s.c1
  a4 := s.a4 + u * s.c3
  b1 := s.b1 + u * s.d0
  b3 := s.b3 + u * s.d2
  c1 := v
  c3 := v * s.a2 + s.c1
  d0 := 0
  d2 := v * s.b1 + s.d0
  d4 := v * s.b3 + s.d2

def alStInit38 : ALSt38 := ⟨0, 0, 0, 0, 0, 0, 1, 0, 0⟩

def alStSeq38 (u v : ℕ → ℂ) : ℕ → ALSt38
  | 0 => alStInit38
  | k + 1 => alStStep38 (u k) (v k) (alStSeq38 u v k)

def alCPoly38 (a b : ℂ) : Matrix (Fin 2) (Fin 2) ℂ[X] :=
  !![1, C a * X; C b * X, X ^ 2]

def alPolyPartial38 (u v : ℕ → ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ[X]
  | 0 => 1
  | k + 1 => alCPoly38 (u k) (v k) * alPolyPartial38 u v k

def ALInv38 (P : Matrix (Fin 2) (Fin 2) ℂ[X]) (s : ALSt38) : Prop :=
  (P 0 0).coeff 0 = 1 ∧ (P 0 0).coeff 2 = s.a2 ∧ (P 0 0).coeff 4 = s.a4 ∧
  (P 0 1).coeff 1 = s.b1 ∧ (P 0 1).coeff 3 = s.b3 ∧
  (P 1 0).coeff 1 = s.c1 ∧ (P 1 0).coeff 3 = s.c3 ∧
  (P 1 1).coeff 0 = s.d0 ∧ (P 1 1).coeff 2 = s.d2 ∧ (P 1 1).coeff 4 = s.d4

theorem alInv_step38 (a b : ℂ) (P : Matrix (Fin 2) (Fin 2) ℂ[X]) (s : ALSt38)
    (h : ALInv38 P s) : ALInv38 (alCPoly38 a b * P) (alStStep38 a b s) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  have e00 : (alCPoly38 a b * P) 0 0 = P 0 0 + X * (C a * P 1 0) := by
    simp [alCPoly38, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e01 : (alCPoly38 a b * P) 0 1 = P 0 1 + X * (C a * P 1 1) := by
    simp [alCPoly38, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e10 : (alCPoly38 a b * P) 1 0 = X * (C b * P 0 0) + X ^ 2 * P 1 0 := by
    simp [alCPoly38, Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e11 : (alCPoly38 a b * P) 1 1 = X * (C b * P 0 1) + X ^ 2 * P 1 1 := by
    simp [alCPoly38, Matrix.mul_apply, Fin.sum_univ_two]; ring
  unfold ALInv38
  rw [e00, e01, e10, e11]
  simp only [alStStep38, coeff_add, coeff_X_mul, coeff_C_mul, coeff_X_mul_zero,
    coeff_X_pow_mul', h1, h2, h3, h4, h5, h6, h7, h8, h9]
  norm_num

theorem alInv_all38 (u v : ℕ → ℂ) (k : ℕ) :
    ALInv38 (alPolyPartial38 u v k) (alStSeq38 u v k) := by
  induction k with
  | zero =>
    simp [ALInv38, alPolyPartial38, alStSeq38, alStInit38, Polynomial.coeff_one]
  | succ k ih => exact alInv_step38 _ _ _ _ ih

/-- `Σ_{1≤i<m+2} u_i v_{i-1}`. -/
def alA2_38 (u v : ℕ → ℂ) (m : ℕ) : ℂ := ∑ i ∈ Finset.range (m + 1), u (i + 1) * v i

theorem alSt_closed38 (u v : ℕ → ℂ) (m : ℕ) :
    (alStSeq38 u v (m + 2)).a2 = alA2_38 u v m ∧
    (alStSeq38 u v (m + 2)).a4 = (1 / 2) * alA2_38 u v m ^ 2
        - (1 / 2) * ∑ i ∈ Finset.range (m + 1), (u (i + 1) * v i) ^ 2
        + ∑ i ∈ Finset.range m, (1 - u (i + 1) * v (i + 1)) * (u (i + 2) * v i) ∧
    (alStSeq38 u v (m + 2)).c1 = v (m + 1) ∧
    (alStSeq38 u v (m + 2)).c3 = v (m + 1) * (∑ i ∈ Finset.range m, u (i + 1) * v i) + v m ∧
    (alStSeq38 u v (m + 2)).b1 = u 0 ∧
    (alStSeq38 u v (m + 2)).b3 = u 1 * (1 - u 0 * v 0) + u 0 * alA2_38 u v m ∧
    (alStSeq38 u v (m + 2)).d0 = 0 ∧
    (alStSeq38 u v (m + 2)).d2 = v (m + 1) * u 0 := by
  induction m with
  | zero =>
    simp [alStSeq38, alStStep38, alStInit38, alA2_38]
    ring
  | succ m ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih
    have e : alStSeq38 u v (m + 1 + 2) =
        alStStep38 (u (m + 2)) (v (m + 2)) (alStSeq38 u v (m + 2)) := rfl
    have hA : alA2_38 u v (m + 1) = alA2_38 u v m + u (m + 2) * v (m + 1) := by
      unfold alA2_38; rw [Finset.sum_range_succ]
    have hA' : alA2_38 u v m = (∑ i ∈ Finset.range m, u (i + 1) * v i) + u (m + 1) * v m := by
      unfold alA2_38; rw [Finset.sum_range_succ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e]; simp only [alStStep38, h1, h3, hA]
    · rw [e]
      simp only [alStStep38, h1, h2, h4, hA]
      rw [Finset.sum_range_succ (fun i => (u (i + 1) * v i) ^ 2) (m + 1),
        Finset.sum_range_succ (fun i => (1 - u (i + 1) * v (i + 1)) * (u (i + 2) * v i)) m, hA']
      ring
    · rw [e]; simp only [alStStep38]
    · rw [e]
      simp only [alStStep38, h1, h3]
      rw [Finset.sum_range_succ (fun i => u (i + 1) * v i) m, hA']
    · rw [e]; simp only [alStStep38, h5, h7]; ring
    · rw [e]; simp only [alStStep38, h6, h8, hA]; ring
    · rw [e]; simp only [alStStep38]
    · rw [e]; simp only [alStStep38, h5, h7]; ring


/-! ### Link to the actual monodromy -/

open scoped Matrix

theorem smul_alTransfer38 (a ζ : ℂ) (hζ : ζ ≠ 0) :
    ζ • alTransfer38 a ζ⁻¹ = ((Real.sqrt (1 - ‖a‖ ^ 2) : ℂ)⁻¹) •
      (alCPoly38 a (star a)).map (Polynomial.eval ζ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alTransfer38, alCPoly38] <;> field_simp

theorem alPartial_eval38 {L : ℕ} (α : ZMod L → ℂ) {ζ : ℂ} (hζ : ζ ≠ 0) (k : ℕ) :
    ζ ^ k • alPartial38 α ζ⁻¹ k = (∏ j ∈ Finset.range k, alScale38 α j) •
      (alPolyPartial38 (fun i => α (i : ZMod L)) (fun i => star (α (i : ZMod L))) k).map
        (Polynomial.eval ζ) := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [alPartial38, alPolyPartial38]
  | succ k ih =>
    have h1 : ζ ^ (k + 1) • alPartial38 α ζ⁻¹ (k + 1) =
        (ζ • alTransfer38 (α (k : ZMod L)) ζ⁻¹) * (ζ ^ k • alPartial38 α ζ⁻¹ k) := by
      rw [alPartial38, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ, mul_comm]
    rw [h1, ih, smul_alTransfer38 _ _ hζ]
    have hm : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ[X],
        (A * B).map (Polynomial.eval ζ) = A.map (Polynomial.eval ζ) * B.map (Polynomial.eval ζ) :=
      fun A B => Matrix.map_mul (f := Polynomial.evalRingHom ζ)
    rw [alPolyPartial38, hm, Finset.prod_range_succ, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, mul_comm]
    rfl

/-- The trace polynomial `tr ∏_j [[1, ζ α_j],[ζ ᾱ_j, ζ²]]`. -/
def alTracePoly38 {L : ℕ} (α : ZMod L → ℂ) : ℂ[X] :=
  (alPolyPartial38 (fun i => α (i : ZMod L)) (fun i => star (α (i : ZMod L))) L) 0 0 +
  (alPolyPartial38 (fun i => α (i : ZMod L)) (fun i => star (α (i : ZMod L))) L) 1 1

theorem alExtT38_eq_poly38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {ζ : ℂ}
    (hζ : ζ ≠ 0) :
    alExtT38 α ζ = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) * (alTracePoly38 α).eval ζ := by
  rw [alExtT38_eq hα hζ]
  have h := congrArg Matrix.trace (alPartial_eval38 α hζ L)
  rw [Matrix.trace_smul, Matrix.trace_smul, alScale38_prod hα] at h
  have h2 : Matrix.trace (alMonodromy38 α ζ⁻¹) = Matrix.trace (alPartial38 α ζ⁻¹ L) := rfl
  rw [h2]
  simp only [smul_eq_mul] at h
  rw [h]
  simp [alTracePoly38, Matrix.trace_fin_two]

theorem alExtTPoly38_eq {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    (∑ k ∈ Finset.range (L + 1), C (alExtCoeff38 α k) * X ^ (2 * k) : ℂ[X]) =
      C ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) * alTracePoly38 α := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_ ((Set.finite_singleton (0 : ℂ)).infinite_compl)
  intro ζ hζ
  have hζ' : ζ ≠ 0 := hζ
  have := alExtT38_eq_poly38 hα hζ'
  simp only [Set.mem_ofPred_eq, eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X]
  rw [← this]
  rfl

theorem alExtCoeff38_eq_coeff38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α)
    {k : ℕ} (hk : k ≤ L) :
    alExtCoeff38 α k = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) * (alTracePoly38 α).coeff (2 * k) := by
  have h := congrArg (fun p : ℂ[X] => p.coeff (2 * k)) (alExtTPoly38_eq hα)
  simp only [coeff_C_mul, finsetSum_coeff] at h
  rw [← h, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    have : 2 * k ≠ 2 * b := fun e => hb (by omega)
    simp [this]
  · intro hk'; exact absurd (Finset.mem_range.2 (by omega)) hk'

/-- Closed form of the low coefficients of the product, for `L = m + 3` factors. -/
theorem alQ_coeffs38 (u v : ℕ → ℂ) (m : ℕ) :
    ((alPolyPartial38 u v (m + 3)) 0 0 + (alPolyPartial38 u v (m + 3)) 1 1).coeff 0 = 1 ∧
    ((alPolyPartial38 u v (m + 3)) 0 0 + (alPolyPartial38 u v (m + 3)) 1 1).coeff 2 =
      ∑ i ∈ Finset.range (m + 2), u (i + 1) * v i + u 0 * v (m + 2) ∧
    ((alPolyPartial38 u v (m + 3)) 0 0 + (alPolyPartial38 u v (m + 3)) 1 1).coeff 4 =
      u 0 * v (m + 1) * (1 - u (m + 2) * v (m + 2)) + u 1 * v (m + 2) * (1 - u 0 * v 0)
      + ∑ i ∈ Finset.range (m + 1), (1 - u (i + 1) * v (i + 1)) * (u (i + 2) * v i)
      + (1 / 2) * (∑ i ∈ Finset.range (m + 2), u (i + 1) * v i + u 0 * v (m + 2)) ^ 2
      - (1 / 2) * ((u 0 * v (m + 2)) ^ 2 + ∑ i ∈ Finset.range (m + 2), (u (i + 1) * v i) ^ 2) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := alInv_all38 u v (m + 3)
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := alSt_closed38 u v (m + 1)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := alSt_closed38 u v m
  have hs : alStSeq38 u v (m + 3) = alStStep38 (u (m + 2)) (v (m + 2)) (alStSeq38 u v (m + 2)) := rfl
  have hA : alA2_38 u v (m + 1) = alA2_38 u v m + u (m + 2) * v (m + 1) := by
    unfold alA2_38; rw [Finset.sum_range_succ]
  have hA2 : alA2_38 u v (m + 1) = ∑ i ∈ Finset.range (m + 2), u (i + 1) * v i := rfl
  have hd0 : (alStSeq38 u v (m + 3)).d0 = 0 := rfl
  have hd4 : (alStSeq38 u v (m + 3)).d4 = v (m + 2) * (alStSeq38 u v (m + 2)).b3 +
      (alStSeq38 u v (m + 2)).d2 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [coeff_add, i1, i8, hd0]; ring
  · rw [coeff_add, i2, i9]
    have c1' : (alStSeq38 u v (m + 3)).a2 = alA2_38 u v (m + 1) := c1
    have c8' : (alStSeq38 u v (m + 3)).d2 = v (m + 2) * u 0 := c8
    rw [c1', c8', hA2]; ring
  · rw [coeff_add, i3, i10]
    have c2' := c2
    have c1' : (alStSeq38 u v (m + 3)).a4 = (1 / 2) * alA2_38 u v (m + 1) ^ 2
        - (1 / 2) * ∑ i ∈ Finset.range (m + 1 + 1), (u (i + 1) * v i) ^ 2
        + ∑ i ∈ Finset.range (m + 1), (1 - u (i + 1) * v (i + 1)) * (u (i + 2) * v i) := c2
    rw [c1', hd4, e6, e8, hA]
    have hA3 : ∑ i ∈ Finset.range (m + 1 + 1), (u (i + 1) * v i) ^ 2 =
        ∑ i ∈ Finset.range (m + 2), (u (i + 1) * v i) ^ 2 := rfl
    rw [hA3]
    have hA4 : alA2_38 u v m + u (m + 2) * v (m + 1) =
        ∑ i ∈ Finset.range (m + 2), u (i + 1) * v i := by rw [← hA]; rfl
    rw [← hA4]
    ring


theorem sum_zmod_range38 {L : ℕ} [NeZero L] (f : ZMod L → ℂ) :
    ∑ j : ZMod L, f j = ∑ i ∈ Finset.range L, f (i : ZMod L) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by have := NeZero.ne L; omega⟩
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => f (i : ZMod (n + 1))) (n + 1)]
  symm
  refine Finset.sum_congr rfl ?_
  intro j _
  have hj : (((j : ℕ) : ZMod (n + 1))) = (show ZMod (n + 1) from j) := Fin.cast_val_eq_self j
  rw [hj]

theorem alTracePoly_coeffs38 {L : ℕ} [NeZero L] (hL : 3 ≤ L) (α : ZMod L → ℂ) :
    (alTracePoly38 α).coeff 0 = 1 ∧
    (alTracePoly38 α).coeff 2 = ∑ j : ZMod L, α j * starRingEnd ℂ (α (j - 1)) ∧
    (alTracePoly38 α).coeff 4 =
      ∑ j : ZMod L, α j * starRingEnd ℂ (α (j - 2)) * (1 - α (j - 1) * starRingEnd ℂ (α (j - 1)))
      + (1 / 2) * (∑ j : ZMod L, α j * starRingEnd ℂ (α (j - 1))) ^ 2
      - (1 / 2) * ∑ j : ZMod L, (α j * starRingEnd ℂ (α (j - 1))) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 3 := ⟨L - 3, by omega⟩
  have h3 : ((m : ℕ) : ZMod (m + 3)) + 3 = 0 := by
    have := ZMod.natCast_self (m + 3)
    push_cast at this; exact this
  obtain ⟨q0, q2, q4⟩ := alQ_coeffs38 (fun i => α (i : ZMod (m + 3)))
    (fun i => star (α (i : ZMod (m + 3)))) m
  have hneg1 : ((m + 2 : ℕ) : ZMod (m + 3)) = 0 - 1 := by push_cast; linear_combination h3
  have hneg2 : ((m + 1 : ℕ) : ZMod (m + 3)) = 0 - 2 := by push_cast; linear_combination h3
  have hneg3 : ((m + 2 : ℕ) : ZMod (m + 3)) = 1 - 2 := by push_cast; linear_combination h3
  unfold alTracePoly38
  have hS1 : ∑ j : ZMod (m + 3), α j * starRingEnd ℂ (α (j - 1)) =
      ∑ i ∈ Finset.range (m + 2), α ((i + 1 : ℕ) : ZMod (m + 3)) * star (α (i : ZMod (m + 3)))
        + α ((0 : ℕ) : ZMod (m + 3)) * star (α ((m + 2 : ℕ) : ZMod (m + 3))) := by
    rw [sum_zmod_range38, Finset.sum_range_succ' _ (m + 2), hneg1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ((i + 1 : ℕ) : ZMod (m + 3)) - 1 = (i : ZMod (m + 3)) := by push_cast; ring
    rw [this]; rfl
  refine ⟨q0, ?_, ?_⟩
  · rw [q2, hS1]
  · have hT : ∑ j : ZMod (m + 3), α j * starRingEnd ℂ (α (j - 2)) *
        (1 - α (j - 1) * starRingEnd ℂ (α (j - 1))) =
        α ((0 : ℕ) : ZMod (m + 3)) * star (α ((m + 1 : ℕ) : ZMod (m + 3))) *
          (1 - α ((m + 2 : ℕ) : ZMod (m + 3)) * star (α ((m + 2 : ℕ) : ZMod (m + 3))))
        + α ((1 : ℕ) : ZMod (m + 3)) * star (α ((m + 2 : ℕ) : ZMod (m + 3))) *
          (1 - α ((0 : ℕ) : ZMod (m + 3)) * star (α ((0 : ℕ) : ZMod (m + 3))))
        + ∑ i ∈ Finset.range (m + 1), (1 - α ((i + 1 : ℕ) : ZMod (m + 3)) *
            star (α ((i + 1 : ℕ) : ZMod (m + 3)))) *
          (α ((i + 2 : ℕ) : ZMod (m + 3)) * star (α (i : ZMod (m + 3)))) := by
      have hst : ∀ z : ℂ, star z = starRingEnd ℂ z := fun z => rfl
      rw [sum_zmod_range38, Finset.sum_range_succ' _ (m + 2), Finset.sum_range_succ' _ (m + 1)]
      have e0 : ((0 : ℕ) : ZMod (m + 3)) - 2 = ((m + 1 : ℕ) : ZMod (m + 3)) := hneg2.symm
      have e0' : ((0 : ℕ) : ZMod (m + 3)) - 1 = ((m + 2 : ℕ) : ZMod (m + 3)) := by
        rw [hneg1]; simp
      have e1 : ((0 + 1 : ℕ) : ZMod (m + 3)) - 2 = ((m + 2 : ℕ) : ZMod (m + 3)) := by
        rw [hneg3]; simp
      have e1' : ((0 + 1 : ℕ) : ZMod (m + 3)) - 1 = ((0 : ℕ) : ZMod (m + 3)) := by simp
      rw [e0, e0', e1, e1']
      have e2 : ∑ i ∈ Finset.range (m + 1), α ((i + 1 + 1 : ℕ) : ZMod (m + 3)) *
            starRingEnd ℂ (α (((i + 1 + 1 : ℕ) : ZMod (m + 3)) - 2)) *
            (1 - α (((i + 1 + 1 : ℕ) : ZMod (m + 3)) - 1) *
              starRingEnd ℂ (α (((i + 1 + 1 : ℕ) : ZMod (m + 3)) - 1))) =
          ∑ i ∈ Finset.range (m + 1), (1 - α ((i + 1 : ℕ) : ZMod (m + 3)) *
            star (α ((i + 1 : ℕ) : ZMod (m + 3)))) *
          (α ((i + 2 : ℕ) : ZMod (m + 3)) * star (α (i : ZMod (m + 3)))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have a1 : ((i + 1 + 1 : ℕ) : ZMod (m + 3)) - 2 = (i : ZMod (m + 3)) := by
          push_cast; ring
        have a2 : ((i + 1 + 1 : ℕ) : ZMod (m + 3)) - 1 = ((i + 1 : ℕ) : ZMod (m + 3)) := by
          push_cast; ring
        have a3 : ((i + 1 + 1 : ℕ) : ZMod (m + 3)) = ((i + 2 : ℕ) : ZMod (m + 3)) := rfl
        rw [a1, a2, a3]; show _ = _; simp only [hst]; ring
      rw [e2]; simp; ring
    have hSq : ∑ j : ZMod (m + 3), (α j * starRingEnd ℂ (α (j - 1))) ^ 2 =
        (α ((0 : ℕ) : ZMod (m + 3)) * star (α ((m + 2 : ℕ) : ZMod (m + 3)))) ^ 2 +
        ∑ i ∈ Finset.range (m + 2),
          (α ((i + 1 : ℕ) : ZMod (m + 3)) * star (α (i : ZMod (m + 3)))) ^ 2 := by
      rw [sum_zmod_range38, Finset.sum_range_succ' _ (m + 2), hneg1, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have : ((i + 1 : ℕ) : ZMod (m + 3)) - 1 = (i : ZMod (m + 3)) := by push_cast; ring
      rw [this]; rfl
    rw [q4, hS1, hT, hSq]


/-! ### Taylor coefficients -/

open Filter Topology Metric NlsGge.Analysis

theorem iteratedDeriv_eval38 (p : ℂ[X]) (n : ℕ) :
    iteratedDeriv n (fun x : ℂ => p.eval x) 0 = (Nat.factorial n : ℂ) * p.coeff n := by
  induction n generalizing p with
  | zero => simp [coeff_zero_eq_eval_zero]
  | succ n ih =>
    have h : deriv (fun x : ℂ => p.eval x) = fun x => (derivative p).eval x := by
      funext x; exact Polynomial.deriv p
    rw [iteratedDeriv_succ', h, ih, coeff_derivative, Nat.factorial_succ]
    push_cast; ring

theorem iteratedDeriv_eq_of_sub38 {f g h : ℂ → ℂ} {m : ℕ} (hf : AnalyticAt ℂ f 0)
    (hg : AnalyticAt ℂ g 0) (hh : AnalyticAt ℂ h 0)
    (hfg : (fun z => f z - g z) =ᶠ[𝓝 0] fun z => z ^ m * h z) :
    ∀ i < m, iteratedDeriv i f 0 = iteratedDeriv i g 0 := by
  have hpow : AnalyticAt ℂ (fun z : ℂ => z ^ m) 0 := by fun_prop
  have hord : (m : ℕ∞) ≤ analyticOrderAt (fun z => f z - g z) 0 := by
    rw [analyticOrderAt_congr hfg]
    have h1 : analyticOrderAt (fun z : ℂ => z ^ m) 0 = m := by
      have := analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := 0) (n := m)
      simp only [sub_zero] at this
      exact this
    have h2 := analyticOrderAt_mul hpow hh
    have h3 : (fun z : ℂ => z ^ m * h z) = (fun z : ℂ => z ^ m) * h := rfl
    rw [h3, h2, h1]
    exact le_self_add
  have hfg' : AnalyticAt ℂ (fun z => f z - g z) 0 := hf.sub hg
  intro i hi
  have := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfg').1 hord i hi
  have e : (fun z => f z - g z) = f - g := rfl
  rw [e, iteratedDeriv_sub hf.contDiffAt hg.contDiffAt] at this
  exact sub_eq_zero.1 this

theorem iteratedDeriv_exp_log38 {g ℓ : ℂ → ℂ} (hℓ : AnalyticAt ℂ ℓ 0)
    (hg : g =ᶠ[𝓝 0] fun z => Complex.exp (ℓ z)) (h1 : iteratedDeriv 1 ℓ 0 = 0)
    (h3 : iteratedDeriv 3 ℓ 0 = 0) :
    iteratedDeriv 2 g 0 = iteratedDeriv 2 ℓ 0 * g 0 ∧
    iteratedDeriv 4 g 0 = (iteratedDeriv 4 ℓ 0 + 3 * iteratedDeriv 2 ℓ 0 ^ 2) * g 0 := by
  have hga : AnalyticAt ℂ g 0 := hℓ.cexp.congr hg.symm
  have hd : deriv g =ᶠ[𝓝 0] fun z => deriv ℓ z * g z := by
    filter_upwards [hg.eventually_nhds, hℓ.eventually_analyticAt] with y hy hya
    have hy' : g =ᶠ[𝓝 y] fun z => Complex.exp (ℓ z) := hy
    rw [hy'.deriv_eq, deriv_cexp hya.differentiableAt, hy'.eq_of_nhds]
    ring
  have key : ∀ n : ℕ, iteratedDeriv (n + 1) g 0 =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) * iteratedDeriv (i + 1) ℓ 0 *
        iteratedDeriv (n - i) g 0 := by
    intro n
    rw [iteratedDeriv_succ', hd.iteratedDeriv_eq]
    have := iteratedDeriv_mul (n := n) (x := (0 : ℂ)) (f := deriv ℓ) (g := g)
      hℓ.deriv.contDiffAt hga.contDiffAt
    simp only [Pi.mul_def] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedDeriv_succ']
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  have k3 := key 3
  simp [Finset.sum_range_succ, h1, h3] at k0 k1 k2 k3
  refine ⟨k1, ?_⟩
  rw [k3, k1]; ring


/-! ### `g ≡ T` modulo `ζ^{2L}` -/

theorem alExtT38_eq_eval38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alExtT38 α = fun x : ℂ => (C ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) * alTracePoly38 α).eval x := by
  funext x
  rw [← alExtTPoly38_eq hα]
  simp [alExtT38, eval_finsetSum]

/-- `g = (T+S)/2` and `T` have the same Taylor coefficients below order `2L`
(`g = T - ζ^{2L}/g`). -/
theorem alExteriorG38_iteratedDeriv_eq_T38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ}
    (hα : IsALField38 α) : ∀ n < 2 * L,
    iteratedDeriv n (alExteriorG38 α) 0 = iteratedDeriv n (alExtT38 α) 0 := by
  have hga : AnalyticAt ℂ (alExteriorG38 α) 0 :=
    (alExteriorG38_analytic hα) 0 (mem_ball_self one_pos)
  have hTa : AnalyticAt ℂ (alExtT38 α) 0 := (alExtT38_differentiable α).analyticAt 0
  have hg0 : alExteriorG38 α 0 ≠ 0 := alExteriorG38_ne_zero hα (mem_ball_self one_pos)
  have hha : AnalyticAt ℂ (fun z => -(alExteriorG38 α z)⁻¹) 0 := (hga.inv hg0).neg
  refine iteratedDeriv_eq_of_sub38 hga hTa hha ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (one_pos : (0:ℝ) < 1))] with z hz
  have hne := alExteriorG38_ne_zero hα hz
  have hsq := alExteriorG38_sq hα hz
  field_simp
  linear_combination hsq

theorem alC12_aux38 {L : ℕ} [NeZero L] (hL : 3 ≤ L) {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alC38 α 1 = (alTracePoly38 α).coeff 2 ∧
    alC38 α 2 = (alTracePoly38 α).coeff 4 - (1 / 2) * (alTracePoly38 α).coeff 2 ^ 2 := by
  obtain ⟨hsa, hsexp, hs0, hsev⟩ := alLog38_spec hα
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hℓ : AnalyticAt ℂ (alLog38 α) 0 := hsa 0 h0
  have hg : alExteriorG38 α =ᶠ[𝓝 0] fun z => Complex.exp (alLog38 α z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with z hz
    exact (hsexp z hz).symm
  have h1 : iteratedDeriv 1 (alLog38 α) 0 = 0 := iteratedDeriv_odd_eq_zero38 hsev 1 (by decide)
  have h3 : iteratedDeriv 3 (alLog38 α) 0 = 0 := iteratedDeriv_odd_eq_zero38 hsev 3 (by decide)
  obtain ⟨d2, d4⟩ := iteratedDeriv_exp_log38 hℓ hg h1 h3
  have e2 := alExteriorG38_iteratedDeriv_eq_T38 hα 2 (by omega)
  have e4 := alExteriorG38_iteratedDeriv_eq_T38 hα 4 (by omega)
  rw [alExtT38_eq_eval38 hα, iteratedDeriv_eval38, coeff_C_mul] at e2 e4
  rw [alExteriorG38_zero hα] at d2 d4
  set P : ℂ := ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) with hP
  have hP0 : P ≠ 0 := by rw [hP]; exact_mod_cast (Real.exp_pos _).ne'
  have c1 : alC38 α 1 = iteratedDeriv 2 (alLog38 α) 0 / 2 := by
    unfold alC38; norm_num [Nat.factorial]
  have c2 : alC38 α 2 = iteratedDeriv 4 (alLog38 α) 0 / 24 := by
    unfold alC38; norm_num [Nat.factorial]
  set l2 := iteratedDeriv 2 (alLog38 α) 0
  set l4 := iteratedDeriv 4 (alLog38 α) 0
  have q2 : l2 = 2 * (alTracePoly38 α).coeff 2 := by
    apply mul_right_cancel₀ hP0
    rw [← d2, e2]; norm_num [Nat.factorial]; ring
  have q4 : l4 = 24 * (alTracePoly38 α).coeff 4 - 3 * l2 ^ 2 := by
    apply mul_right_cancel₀ hP0
    have : l4 * P = iteratedDeriv 4 (alExteriorG38 α) 0 - 3 * l2 ^ 2 * P := by rw [d4]; ring
    rw [this, e4]; norm_num [Nat.factorial]; ring
  refine ⟨?_, ?_⟩
  · rw [c1, q2]; ring
  · rw [c2, q4, q2]; ring


/-- `log g ≡ log T (mod ζ^{2L})`: `ℓ + Log(1 + ζ^{2L}/g²)` is an analytic logarithm of the
polynomial `T` near `0`, and its Taylor coefficients of order `< 2L` are those of `ℓ`, so for
`k < L` the coefficient `alC38 α k` is the `ζ^{2k}` Taylor coefficient of `log T`. -/
theorem alC38_taylor_logT38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ∃ lam : ℂ → ℂ, AnalyticAt ℂ lam 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), Complex.exp (lam z) = alExtT38 α z) ∧
      lam 0 = ((alMass38 L α / 2 : ℝ) : ℂ) ∧
      ∀ k < L, alC38 α k = iteratedDeriv (2 * k) lam 0 / ((Nat.factorial (2 * k) : ℕ) : ℂ) := by
  obtain ⟨hsa, hsexp, hs0, hsev⟩ := alLog38_spec hα
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hℓ : AnalyticAt ℂ (alLog38 α) 0 := hsa 0 h0
  have hga : AnalyticAt ℂ (alExteriorG38 α) 0 := (alExteriorG38_analytic hα) 0 h0
  have hg0 : alExteriorG38 α 0 ≠ 0 := alExteriorG38_ne_zero hα h0
  obtain ⟨n, hn⟩ : ∃ n, 2 * L = n + 1 := ⟨2 * L - 1, by have := NeZero.ne L; omega⟩
  set u : ℂ → ℂ := fun z => (alExteriorG38 α z ^ 2)⁻¹ with hu_def
  have hu : AnalyticAt ℂ u 0 := (hga.pow 2).inv (pow_ne_zero 2 hg0)
  set w : ℂ → ℂ := fun z => z ^ (n + 1) * u z with hw_def
  have hw : AnalyticAt ℂ w 0 := (analyticAt_id.pow (n + 1)).mul hu
  have hw0 : w 0 = 0 := by simp [hw_def]
  have hslit0 : (1 + w 0) ∈ Complex.slitPlane := by rw [hw0]; simp
  have h1w : AnalyticAt ℂ (fun z => 1 + w z) 0 := analyticAt_const.add hw
  set D : ℂ → ℂ := fun z => Complex.log (1 + w z) with hD_def
  have hD : AnalyticAt ℂ D 0 := h1w.clog hslit0
  have hev_slit : ∀ᶠ z in 𝓝 (0 : ℂ), (1 + w z) ∈ Complex.slitPlane :=
    h1w.continuousAt.eventually_mem (Complex.isOpen_slitPlane.mem_nhds hslit0)
  refine ⟨fun z => alLog38 α z + D z, hℓ.add hD, ?_, ?_, ?_⟩
  · filter_upwards [Metric.isOpen_ball.mem_nhds h0, hev_slit] with z hz hzs
    have hne := alExteriorG38_ne_zero hα hz
    have hsq := alExteriorG38_sq hα hz
    have hpow : z ^ (2 * L) = z ^ (n + 1) := by rw [hn]
    rw [Complex.exp_add, hsexp z hz, hD_def]
    simp only
    rw [Complex.exp_log (Complex.slitPlane_ne_zero hzs)]
    simp only [hw_def, hu_def]
    rw [hpow] at hsq
    field_simp
    linear_combination hsq
  · simp [hD_def, hw0, hs0]
  · -- Taylor coefficients of `D` below order `2L` vanish
    have hdu : AnalyticAt ℂ (deriv u) 0 := hu.deriv
    set h2 : ℂ → ℂ := fun z => (((n + 1 : ℕ) : ℂ) * u z + z * deriv u z) / (1 + w z) with hh2
    have hh2a : AnalyticAt ℂ h2 0 :=
      ((analyticAt_const.mul hu).add (analyticAt_id.mul hdu)).div h1w
        (by rw [hw0]; simp)
    have hdD : (fun z => deriv D z - (fun _ : ℂ => (0 : ℂ)) z) =ᶠ[𝓝 0] fun z => z ^ n * h2 z := by
      filter_upwards [hev_slit, hw.eventually_analyticAt, hu.eventually_analyticAt] with z hzs hwa hua
      have hwd : HasDerivAt w (((n + 1 : ℕ) : ℂ) * z ^ n * u z + z ^ (n + 1) * deriv u z) z := by
        have h1 : HasDerivAt (fun z : ℂ => z ^ (n + 1)) (((n + 1 : ℕ) : ℂ) * z ^ n) z := by
          simpa using hasDerivAt_pow (n + 1) z
        exact h1.mul hua.differentiableAt.hasDerivAt
      have := (hwd.const_add 1).clog hzs
      have hDd : deriv D z = (((n + 1 : ℕ) : ℂ) * z ^ n * u z + z ^ (n + 1) * deriv u z) /
          (1 + w z) := this.deriv
      simp only [hDd, hh2]
      have hne : (1 + w z) ≠ 0 := Complex.slitPlane_ne_zero hzs
      field_simp
      ring
    have hz := iteratedDeriv_eq_of_sub38 hD.deriv analyticAt_const hh2a hdD
    intro k hk
    have hk2 : 2 * k < n + 1 := by omega
    have hDk : iteratedDeriv (2 * k) D 0 = 0 := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simp [hD_def, hw0]
      · obtain ⟨j, hj⟩ : ∃ j, 2 * k = j + 1 := ⟨2 * k - 1, by omega⟩
        rw [hj, iteratedDeriv_succ']
        have := hz j (by omega)
        simpa using this
    have hsum : iteratedDeriv (2 * k) (fun z => alLog38 α z + D z) 0 =
        iteratedDeriv (2 * k) (alLog38 α) 0 + iteratedDeriv (2 * k) D 0 := by
      have := iteratedDeriv_add (n := 2 * k) (x := (0 : ℂ)) (f := alLog38 α) (g := D)
        hℓ.contDiffAt hD.contDiffAt
      exact this
    rw [hsum, hDk, add_zero]
    rfl


/-! ### `D:eq:C12` -/

/-- `D:eq:C12`, first coefficient: `C₁ = Σ_j α_j conj(α_{j-1})` (indices in `ZMod L`; valid
for every `L ≥ 3`, in particular for the source range `L ≥ 5`). -/
theorem alC38_one38 {L : ℕ} [NeZero L] (hL : 3 ≤ L) {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alC38 α 1 = ∑ j : ZMod L, α j * starRingEnd ℂ (α (j - 1)) := by
  rw [(alC12_aux38 hL hα).1, (alTracePoly_coeffs38 hL α).2.1]

/-- `D:eq:C12`, second coefficient:
`C₂ = Σ_j α_j conj(α_{j-2}) (1 - r_{j-1}) - ½ Σ_j (α_j conj(α_{j-1}))²`, `r_j = |α_j|²`. -/
theorem alC38_two38 {L : ℕ} [NeZero L] (hL : 3 ≤ L) {α : ZMod L → ℂ} (hα : IsALField38 α) :
    alC38 α 2 =
      ∑ j : ZMod L, α j * starRingEnd ℂ (α (j - 2)) * (1 - ((‖α (j - 1)‖ ^ 2 : ℝ) : ℂ))
      - (1 / 2) * ∑ j : ZMod L, (α j * starRingEnd ℂ (α (j - 1))) ^ 2 := by
  obtain ⟨_, q2, q4⟩ := alTracePoly_coeffs38 hL α
  rw [(alC12_aux38 hL hα).2, q4, q2]
  have : ∀ j : ZMod L, α (j - 1) * starRingEnd ℂ (α (j - 1)) = ((‖α (j - 1)‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [Complex.mul_conj']; push_cast; ring
  simp only [this]
  ring

end NlsGge.AblowitzLadik

end
