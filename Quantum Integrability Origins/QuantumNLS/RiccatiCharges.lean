import Mathlib

/-!
# R-3FEAD88B stage E4-3a: the algebraic residual identity of the charge recursion

Source (`source/chapters/foundations/riccati_expansion.tex`, eq. riccati-residual, proof lines 32-38) and the
charge recursion (`source/chapters/core/model.tex`, eq:charges; `v_{j+1} = -i∂v_j + κ ū ∑_{a=1}^{j-1} v_a v_{j-a}`)
with `ū` replaced by the independent field `v`, `κ` the MODEL coupling (`κ_model = κ_phys / L`).

Setting (abstract, so that it applies to any model where `∂` and the product are linear/bilinear): `X` is a
`ℂ`-module, `D : X →ₗ X` plays `∂x`, `m : X →ₗ X →ₗ X` plays the product, `w : ℕ → X` the charges with
`w 1 = u` and, for `n ≥ 1`,
`w (n+1) = −i • D (w n) + κ • m v (∑_{a ∈ [1, n-1]} m (w a) (w (n-a)))`.
Write `ζ = z⁻¹` with `z ζ = 1`, so `z^{-n} = ζ^n` and `z^{1-n} = z ζ^n`.

Proved (no analysis here): with the residual
`E_M = ∑_{n≤M} z ζ^n w_n − u + i ∑_{n≤M} ζ^n D w_n − κ m(v, ∑_{b,d≤M} ζ^{b+d} w_b w_d)`,
for every `M ≥ 1`,
`E_M = (i ζ^M) • D w_M − κ • m v (T_M)`, `T_M = ∑_{b,d≤M} [M ≤ b+d] ζ^{b+d} w_b w_d`.

This is the source identity `E_M = i z^{-M} w_M' − κ v ∑_{b+d ≥ M} w_b w_d z^{-b-d}`. The bound
`‖E_M‖ ≤ C|z|^{-M}` (E4-3b, not in this module) follows from it with bounds on `w_M` and on the tail terms.

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Complex Finset

namespace QuantumNLS.RiccatiCharges

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- The residual `E_M` of the truncated expansion, with `ζ = z⁻¹` (source eq. riccati-residual). -/
def resid (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (D : X →ₗ[ℂ] X) (v u : X) (κ z ζ : ℂ) (w : ℕ → X) (M : ℕ) : X :=
  (∑ n ∈ Icc 1 M, (z * ζ ^ n) • w n) - u + (∑ n ∈ Icc 1 M, (Complex.I * ζ ^ n) • D (w n))
    - κ • m v (∑ b ∈ Icc 1 M, ∑ d ∈ Icc 1 M, (ζ ^ (b + d)) • m (w b) (w d))

/-- The tail `T_M` of the double sum: pairs with `M ≤ b + d`. -/
def tailT (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (ζ : ℂ) (w : ℕ → X) (M : ℕ) : X :=
  ∑ b ∈ Icc 1 M, ∑ d ∈ Icc 1 M, (if M ≤ b + d then (ζ ^ (b + d)) • m (w b) (w d) else 0)

/-- Adding the row and column `M+1` to a square box. -/
theorem dsum_succ (g : ℕ → ℕ → X) (M : ℕ) :
    ∑ b ∈ Icc 1 (M + 1), ∑ d ∈ Icc 1 (M + 1), g b d
      = (∑ b ∈ Icc 1 M, ∑ d ∈ Icc 1 M, g b d) + (∑ b ∈ Icc 1 M, g b (M + 1))
        + (∑ d ∈ Icc 1 (M + 1), g (M + 1) d) := by
  have h : 1 ≤ M + 1 := by omega
  simp only [Finset.sum_Icc_succ_top h, Finset.sum_add_distrib]

/-- Antidiagonal of the box `[1,M]²` as a sum over `a ∈ [1, M-1]`. -/
theorem antidiag_sum (F : ℕ → ℕ → X) (M : ℕ) :
    ∑ b ∈ Icc 1 M, ∑ d ∈ Icc 1 M, (if b + d = M then F b d else 0)
      = ∑ a ∈ Ico 1 M, F a (M - a) := by
  have h1 : ∑ b ∈ Icc 1 M, ∑ d ∈ Icc 1 M, (if b + d = M then F b d else 0)
      = ∑ p ∈ (Icc 1 M ×ˢ Icc 1 M).filter (fun p => p.1 + p.2 = M), F p.1 p.2 := by
    simp only [Finset.sum_filter, Finset.sum_product]
  rw [h1]
  -- the goal is `∑ over filter = ∑ over Ico`, so i := Prod.fst (filter → Ico), j := (a ↦ (a, M-a))
  refine Finset.sum_nbij' (Prod.fst : ℕ × ℕ → ℕ) (fun a : ℕ => ((a, M - a) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    simp only [Finset.mem_Ico]
    omega
  · intro a ha
    simp only [Finset.mem_Ico] at ha
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    omega
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    have hb : M - a = b := by omega
    simp [hb]
  · intro a _
    rfl
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    have hb : M - a = b := by omega
    simp [hb]

/-- Antidiagonal sum with the charge coefficients: `∑_{b+d=M} ζ^{b+d} w_b w_d = ζ^M ∑_{a<M} w_a w_{M-a}`. -/
theorem antidiag_G (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (ζ : ℂ) (w : ℕ → X) (M : ℕ) :
    ∑ b ∈ Icc 1 M, ∑ d ∈ Icc 1 M, (if b + d = M then (ζ ^ (b + d)) • m (w b) (w d) else 0)
      = ζ ^ M • ∑ a ∈ Ico 1 M, m (w a) (w (M - a)) := by
  have h := antidiag_sum (fun b d => (ζ ^ (b + d)) • m (w b) (w d)) M
  beta_reduce at h
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_Ico] at ha
  rw [show a + (M - a) = M by omega]

/-- Pointwise split of the tail indicator: `[M ≤ s] = [M+1 ≤ s] + [s = M]`. -/
theorem ite_split_le (M s : ℕ) (x : X) :
    (if M ≤ s then x else 0) = (if M + 1 ≤ s then x else 0) + (if s = M then x else 0) := by
  by_cases h1 : M + 1 ≤ s
  · have h2 : M ≤ s := by omega
    have h3 : s ≠ M := by omega
    simp [h1, h2, h3]
  · by_cases h2 : M ≤ s
    · have h3 : s = M := by omega
      simp [h1, h2, h3]
    · have h3 : s ≠ M := by omega
      simp [h1, h2, h3]

/-- Splitting the tail at level `M`: `T_M = ∑ [M+1 ≤ b+d] ζ^{b+d} w_b w_d + ζ^M ∑_{a<M} w_a w_{M-a}`. -/
theorem tail_split (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (ζ : ℂ) (w : ℕ → X) (M : ℕ) :
    tailT m ζ w M
      = (∑ b ∈ Icc 1 M, ∑ d ∈ Icc 1 M, (if M + 1 ≤ b + d then (ζ ^ (b + d)) • m (w b) (w d) else 0))
        + ζ ^ M • ∑ a ∈ Ico 1 M, m (w a) (w (M - a)) := by
  unfold tailT
  have hA : ∀ b d : ℕ, (if M ≤ b + d then (ζ ^ (b + d)) • m (w b) (w d) else 0)
      = (if M + 1 ≤ b + d then (ζ ^ (b + d)) • m (w b) (w d) else 0)
        + (if b + d = M then (ζ ^ (b + d)) • m (w b) (w d) else 0) :=
    fun b d => ite_split_le M (b + d) ((ζ ^ (b + d)) • m (w b) (w d))
  simp only [hA, Finset.sum_add_distrib]
  rw [antidiag_G m ζ w M]

/-- Tail recursion: `T_{M+1} = T_M − ζ^M S_M + (the row and column M+1)`. -/
theorem tail_succ (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (ζ : ℂ) (w : ℕ → X) (M : ℕ) :
    tailT m ζ w (M + 1)
      = tailT m ζ w M - ζ ^ M • (∑ a ∈ Ico 1 M, m (w a) (w (M - a)))
        + ((∑ b ∈ Icc 1 M, (ζ ^ (b + (M + 1))) • m (w b) (w (M + 1)))
          + ∑ d ∈ Icc 1 (M + 1), (ζ ^ (M + 1 + d)) • m (w (M + 1)) (w d)) := by
  have hD := dsum_succ (fun b d => if M + 1 ≤ b + d then (ζ ^ (b + d)) • m (w b) (w d) else 0) M
  beta_reduce at hD
  have e1 : ∀ b : ℕ, (if M + 1 ≤ b + (M + 1) then (ζ ^ (b + (M + 1))) • m (w b) (w (M + 1)) else 0)
      = (ζ ^ (b + (M + 1))) • m (w b) (w (M + 1)) := fun b => if_pos (by omega)
  have e2 : ∀ d : ℕ, (if M + 1 ≤ (M + 1) + d then (ζ ^ (M + 1 + d)) • m (w (M + 1)) (w d) else 0)
      = (ζ ^ (M + 1 + d)) • m (w (M + 1)) (w d) := fun d => if_pos (by omega)
  rw [tail_split m ζ w M]
  unfold tailT
  rw [hD]
  simp only [e1, e2]
  abel

/-- The residual recursion in one step. -/
theorem resid_succ (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (D : X →ₗ[ℂ] X) (v u : X) (κ z ζ : ℂ) (w : ℕ → X) (M : ℕ) :
    resid m D v u κ z ζ w (M + 1)
      = resid m D v u κ z ζ w M + (z * ζ ^ (M + 1)) • w (M + 1)
        + (Complex.I * ζ ^ (M + 1)) • D (w (M + 1))
        - κ • m v ((∑ b ∈ Icc 1 M, (ζ ^ (b + (M + 1))) • m (w b) (w (M + 1)))
          + ∑ d ∈ Icc 1 (M + 1), (ζ ^ (M + 1 + d)) • m (w (M + 1)) (w d)) := by
  have hD := dsum_succ (fun b d => (ζ ^ (b + d)) • m (w b) (w d)) M
  beta_reduce at hD
  unfold resid
  rw [hD]
  have h : 1 ≤ M + 1 := by omega
  simp only [Finset.sum_Icc_succ_top h, map_add, map_sub, smul_add, smul_sub]
  abel

/-- Base case `M = 1`. -/
theorem resid_one (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (D : X →ₗ[ℂ] X) (v u : X) (κ z ζ : ℂ) (w : ℕ → X)
    (hzζ : z * ζ = 1) (hw1 : w 1 = u) :
    resid m D v u κ z ζ w 1 = (Complex.I * ζ ^ 1) • D (w 1) - κ • m v (tailT m ζ w 1) := by
  simp [resid, tailT, hw1, hzζ]

/-- The truncated charge expansion of the Riccati residual: for every `M ≥ 1`,
`E_M = i ζ^M D w_M − κ m(v, T_M)`, i.e. `E_M = i z^{-M} ∂w_M − κ v ∑_{b+d ≥ M} w_b w_d z^{-b-d}`. -/
theorem resid_formula (m : X →ₗ[ℂ] X →ₗ[ℂ] X) (D : X →ₗ[ℂ] X) (v u : X) (κ z ζ : ℂ) (w : ℕ → X)
    (hzζ : z * ζ = 1) (hw1 : w 1 = u)
    (hrec : ∀ n : ℕ, 1 ≤ n → w (n + 1)
      = -(Complex.I • D (w n)) + κ • m v (∑ a ∈ Ico 1 n, m (w a) (w (n - a))))
    (M : ℕ) (hM : 1 ≤ M) :
    resid m D v u κ z ζ w M = (Complex.I * ζ ^ M) • D (w M) - κ • m v (tailT m ζ w M) := by
  induction M, hM using Nat.le_induction with
  | base => exact resid_one m D v u κ z ζ w hzζ hw1
  | succ M hM ih =>
    have hzz : z * ζ ^ (M + 1) = ζ ^ M := by
      linear_combination (ζ ^ M) * hzζ
    have hW : ζ ^ M • w (M + 1)
        = -(ζ ^ M • (Complex.I • D (w M))) + ζ ^ M • (κ • m v (∑ a ∈ Ico 1 M, m (w a) (w (M - a)))) := by
      rw [hrec M hM, smul_add, smul_neg]
    rw [resid_succ, ih, tail_succ, hzz, hW]
    simp only [map_add, map_sub, map_smul]
    module

end QuantumNLS.RiccatiCharges

#print axioms QuantumNLS.RiccatiCharges.dsum_succ
#print axioms QuantumNLS.RiccatiCharges.antidiag_sum
#print axioms QuantumNLS.RiccatiCharges.tail_succ
#print axioms QuantumNLS.RiccatiCharges.resid_succ
#print axioms QuantumNLS.RiccatiCharges.resid_formula
