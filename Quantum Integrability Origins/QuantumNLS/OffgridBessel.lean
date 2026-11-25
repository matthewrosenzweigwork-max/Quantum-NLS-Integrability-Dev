import Mathlib
import QuantumNLS.OffgridSums
import QuantumNLS.DiagonalBessel
import QuantumNLS.HaarEigenbasis

/-!
# R-F9AB39A7 `QG:lem:haar-offgrid-bessel` (kernel part, eq. `QG:eq:haar-kernel-bessel`)

(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:614-663`; imports the R-F611926F modules HaarEigenbasis `5976e63d…`
(`physBasis`, `eigen_all`, `lamTilde`, `lamTilde_eq`, `Lam`) and HaarKernelFactorizationSym read-only.)

* `Gamma0 L`: the square contour `Γ_0` centred at `0` with horizontal and vertical half-width `ω/4`, `ω = 2π/L`
  (as a set: `max(|Re w|,|Im w|) = ω/4`); `bR L r = (1+e^{π/2})√(16+π²)4^{r-1}/(r! ω^r)`.
* `far_of_gamma0`: for `w ∈ Γ_0` and `δ_r ∈ {0,1/2}`, `w/ω - δ_r` has distance `≥ 1/4` from `-ℤ`
  ("the distance from `w/ω` to both the integers and the half-integers is at least `1/4`").
* `norm_Lam_sq_sum_le`: `∑_{n∈F} |Λ_k(ωn+w)|² ≤ b_r²` for every finite `F ⊂ ℤ`, every `k` (the printed chain: `|1-ρ_r e^{iwL}|
  ≤ 1+e^{π/2}`, `e^{i(ωn+w)L} = e^{iwL}`, `∑_n ∏_j |n+w/ω-k_j-δ_r|^{-2} ≤ 16^{r-1}(16+π²)`).
* `no_pole`: `(-1)^n e^{i(ωn+w)L} ≠ 1` on `Γ_0` (all `ωn+w` avoid the resolvent poles).
* `bessel_K_finite`: for all finite `F` and `x ∈ Sym^r`, `∑_{n∈F}‖K_{r,ωn+w}x‖² ≤ b_r²‖x‖²` and
  `∑_{n∈F}‖K_{r,ωn+w}^* x‖² ≤ b_r²‖x‖²` (the two operator inequalities `∑K^*K, ∑KK^* ≤ b_r²`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped InnerProductSpace ComplexConjugate BigOperators
open QuantumNLS.Offgrid QuantumNLS.DiagonalBessel QuantumNLS.HaarEigenbasis
  QuantumNLS.HaarKernelFactorizationSym QuantumNLS.BethePhysicalTransfer QuantumNLS.PhysicalTensor
  QuantumNLS.HaarSlaterBasis QuantumNLS.TensorCarrier

namespace QuantumNLS.OffgridBessel

variable (L : ℝ) [Fact (0 < L)]

/-- The square contour `Γ_0`: boundary of the square centred at `0` with half-width `ω/4`. -/
def Gamma0 : Set ℂ := {w : ℂ | max |w.re| |w.im| = omegaL L / 4}

/-- The constant `b_r = (1+e^{π/2})√(16+π²)4^{r-1}/(r! ω^r)`. -/
def bR (r : ℕ) : ℝ :=
  (1 + Real.exp (Real.pi / 2)) * Real.sqrt (16 + Real.pi ^ 2) * 4 ^ (r - 1) /
    ((r.factorial : ℝ) * omegaL L ^ r)

theorem omega_pos : 0 < omegaL L := by
  unfold omegaL
  have : 0 < L := Fact.out
  positivity

theorem omega_mul_L : omegaL L * L = 2 * Real.pi := by
  have : 0 < L := Fact.out
  unfold omegaL
  field_simp

variable {L}

theorem abs_ge_quarter (x : ℝ) (j : ℤ) (hx : 4 * x = j) (hj : j ≠ 0) : 1 / 4 ≤ |x| := by
  have h1 : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
  have h2 : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast h1
  rw [← hx, abs_mul] at h2
  have : |(4 : ℝ)| = 4 := by norm_num
  rw [this] at h2
  linarith

theorem far_of_gamma0 {w : ℂ} (hw : w ∈ Gamma0 L) {δ : ℝ} (hδ : δ = 0 ∨ δ = 1 / 2) :
    Far (w / (omegaL L : ℂ) - (δ : ℂ)) := by
  have hω := omega_pos L
  intro m
  have hre : |w.re| ≤ omegaL L / 4 := by
    have : max |w.re| |w.im| = omegaL L / 4 := hw
    rw [← this]; exact le_max_left _ _
  have him : |w.im| ≤ omegaL L / 4 := by
    have : max |w.re| |w.im| = omegaL L / 4 := hw
    rw [← this]; exact le_max_right _ _
  have hcases : |w.re| = omegaL L / 4 ∨ |w.im| = omegaL L / 4 := by
    have : max |w.re| |w.im| = omegaL L / 4 := hw
    rcases max_choice |w.re| |w.im| with h | h
    · left; rw [← this, h]
    · right; rw [← this, h]
  rcases hcases with hr | hi
  · -- real part is ±ω/4
    have hnorm : |((m : ℂ) + (w / (omegaL L : ℂ) - (δ : ℂ))).re| ≤ ‖(m : ℂ) + (w / (omegaL L : ℂ) - (δ : ℂ))‖ :=
      Complex.abs_re_le_norm _
    refine le_trans ?_ hnorm
    have hre' : ((m : ℂ) + (w / (omegaL L : ℂ) - (δ : ℂ))).re = m + w.re / omegaL L - δ := by
      simp [Complex.div_ofReal_re]
      ring
    rw [hre']
    have hs : w.re / omegaL L = 1 / 4 ∨ w.re / omegaL L = -(1 / 4) := by
      rcases (abs_eq (by positivity : (0 : ℝ) ≤ omegaL L / 4)).mp hr with h | h
      · left; rw [h]; field_simp
      · right; rw [h]; field_simp
    rcases hs with hs | hs <;> rcases hδ with hδ | hδ <;> rw [hs, hδ]
    · exact abs_ge_quarter _ (4 * m + 1) (by push_cast; ring) (by omega)
    · exact abs_ge_quarter _ (4 * m - 1) (by push_cast; ring) (by omega)
    · exact abs_ge_quarter _ (4 * m - 1) (by push_cast; ring) (by omega)
    · exact abs_ge_quarter _ (4 * m - 3) (by push_cast; ring) (by omega)
  · have hnorm : |((m : ℂ) + (w / (omegaL L : ℂ) - (δ : ℂ))).im| ≤ ‖(m : ℂ) + (w / (omegaL L : ℂ) - (δ : ℂ))‖ :=
      Complex.abs_im_le_norm _
    refine le_trans ?_ hnorm
    have him' : ((m : ℂ) + (w / (omegaL L : ℂ) - (δ : ℂ))).im = w.im / omegaL L := by
      simp [Complex.div_ofReal_im]
    rw [him', abs_div, abs_of_pos hω, hi]
    field_simp
    rfl

theorem deltaR_cases (r : ℕ) : deltaR r = 0 ∨ deltaR r = 1 / 2 := by
  unfold deltaR; split_ifs
  · right; rfl
  · left; rfl

/-- `‖Λ‖²` as a product. -/
theorem norm_Lam_sq (n : ℕ) (z : ℂ) (k : Fin (n + 1) → ℤ) :
    ‖Lam L n z k‖ ^ 2 = ‖1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)‖ ^ 2 /
        (((n + 1).factorial : ℝ) ^ 2) * ∏ i, ‖lamFun L n z (k i)‖ ^ 2 := by
  unfold Lam
  rw [norm_mul, mul_pow, norm_div, div_pow, norm_prod, Finset.prod_pow]
  congr 2
  simp

theorem norm_lamFun_sq (n : ℕ) (z : ℂ) (m : ℤ) :
    ‖lamFun L n z m‖ ^ 2 = 1 / ‖z - ((omegaL L * ((m : ℝ) + deltaR (n + 1)) : ℝ) : ℂ)‖ ^ 2 := by
  unfold lamFun
  rw [norm_div, Complex.norm_I, div_pow, one_pow]

/-- On the contour: `z = ωj + w` gives `z - ω(m+δ) = ω((j-m) + (w/ω - δ))`. -/
theorem sub_pole_eq (w : ℂ) (j m : ℤ) (δ : ℝ) :
    ((omegaL L * (j : ℝ) : ℝ) : ℂ) + w - ((omegaL L * ((m : ℝ) + δ) : ℝ) : ℂ) =
      (omegaL L : ℂ) * ((j : ℂ) - (m : ℂ) + (w / (omegaL L : ℂ) - (δ : ℂ))) := by
  have hω : (omegaL L : ℂ) ≠ 0 := by exact_mod_cast (omega_pos L).ne'
  push_cast
  field_simp
  ring

theorem norm_exp_le {w : ℂ} (hw : w ∈ Gamma0 L) (j : ℤ) :
    ‖Complex.exp (Complex.I * (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) * L)‖ ≤ Real.exp (Real.pi / 2) := by
  have hL : 0 < L := Fact.out
  have him : |w.im| ≤ omegaL L / 4 := by
    have : max |w.re| |w.im| = omegaL L / 4 := hw
    rw [← this]; exact le_max_right _ _
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h1 : (Complex.I * (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) * (L : ℂ)).re = -(w.im * L) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h1]
  have h2 : w.im * L ≥ -(omegaL L / 4 * L) := by
    have := neg_abs_le w.im
    nlinarith [abs_nonneg w.im]
  have h3 : omegaL L / 4 * L = Real.pi / 2 := by
    have := omega_mul_L (L := L)
    nlinarith
  linarith

theorem no_pole {w : ℂ} (hw : w ∈ Gamma0 L) (n : ℕ) (j : ℤ) :
    (-1 : ℂ) ^ n * Complex.exp (Complex.I * (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) * L) ≠ 1 := by
  intro h
  have hL : 0 < L := Fact.out
  rw [q_eq_one_iff hL] at h
  obtain ⟨m, hm⟩ := h
  have hfar := far_of_gamma0 hw (deltaR_cases (n + 1))
  have h1 := sub_pole_eq (L := L) w j m (deltaR (n + 1))
  rw [← hm, sub_self] at h1
  have hω : (omegaL L : ℂ) ≠ 0 := by exact_mod_cast (omega_pos L).ne'
  have h2 := (mul_eq_zero.mp h1.symm).resolve_left hω
  have h3 := hfar (j - m)
  have : ((j - m : ℤ) : ℂ) + (w / (omegaL L : ℂ) - ((deltaR (n + 1) : ℝ) : ℂ)) = 0 := by
    rw [← h2]; push_cast; ring
  rw [this, norm_zero] at h3
  norm_num at h3

theorem norm_Lam_sq_sum_le {w : ℂ} (hw : w ∈ Gamma0 L) (n : ℕ) (k : Fin (n + 1) → ℤ) (F : Finset ℤ) :
    ∑ j ∈ F, ‖Lam L n (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) k‖ ^ 2 ≤ bR L (n + 1) ^ 2 := by
  have hω := omega_pos L
  set v : ℂ := w / (omegaL L : ℂ) - ((deltaR (n + 1) : ℝ) : ℂ) with hv
  have hfar : Far v := far_of_gamma0 hw (deltaR_cases (n + 1))
  have hq : ∀ j : ℤ, ‖1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) * L)‖ ≤
      1 + Real.exp (Real.pi / 2) := by
    intro j
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    linarith [norm_exp_le hw j]
  have hfac : ∀ j : ℤ, ∏ i : Fin (n + 1), ‖lamFun L n (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) (k i)‖ ^ 2 =
      (omegaL L ^ 2)⁻¹ ^ (n + 1) * ∏ i : Fin (n + 1), 1 / ‖(j : ℂ) - (k i : ℂ) + v‖ ^ 2 := by
    intro j
    have : ∀ i : Fin (n + 1), ‖lamFun L n (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) (k i)‖ ^ 2 =
        (omegaL L ^ 2)⁻¹ * (1 / ‖(j : ℂ) - (k i : ℂ) + v‖ ^ 2) := by
      intro i
      rw [norm_lamFun_sq, sub_pole_eq (L := L) w j (k i) (deltaR (n + 1)), norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hω, mul_pow, one_div, one_div, mul_inv]
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hpos : ∀ j : ℤ, ‖Lam L n (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) k‖ ^ 2 ≤
      (1 + Real.exp (Real.pi / 2)) ^ 2 / (((n + 1).factorial : ℝ) ^ 2) *
        ((omegaL L ^ 2)⁻¹ ^ (n + 1) * ∏ i : Fin (n + 1), 1 / ‖(j : ℂ) - (k i : ℂ) + v‖ ^ 2) := by
    intro j
    rw [norm_Lam_sq, hfac j]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) (hq j) 2
  calc ∑ j ∈ F, ‖Lam L n (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) k‖ ^ 2
      ≤ ∑ j ∈ F, (1 + Real.exp (Real.pi / 2)) ^ 2 / (((n + 1).factorial : ℝ) ^ 2) *
        ((omegaL L ^ 2)⁻¹ ^ (n + 1) * ∏ i : Fin (n + 1), 1 / ‖(j : ℂ) - (k i : ℂ) + v‖ ^ 2) :=
        Finset.sum_le_sum (fun j _ => hpos j)
    _ = (1 + Real.exp (Real.pi / 2)) ^ 2 / (((n + 1).factorial : ℝ) ^ 2) * ((omegaL L ^ 2)⁻¹ ^ (n + 1) *
        ∑ j ∈ F, ∏ i : Fin (n + 1), 1 / ‖(j : ℂ) - (k i : ℂ) + v‖ ^ 2) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (1 + Real.exp (Real.pi / 2)) ^ 2 / (((n + 1).factorial : ℝ) ^ 2) * ((omegaL L ^ 2)⁻¹ ^ (n + 1) *
        (16 ^ n * (16 + Real.pi ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        simpa using sum_prod_le (r := n + 1) (by omega) hfar k F
    _ = bR L (n + 1) ^ 2 := by
        unfold bR
        have h4 : (4 : ℝ) ^ (n + 1 - 1) = 4 ^ n := by simp
        rw [h4]
        have hs : Real.sqrt (16 + Real.pi ^ 2) ^ 2 = 16 + Real.pi ^ 2 := Real.sq_sqrt (by positivity)
        have h16 : ((4 : ℝ) ^ n) ^ 2 = 16 ^ n := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have e1 : ((1 + Real.exp (Real.pi / 2)) * Real.sqrt (16 + Real.pi ^ 2) * 4 ^ n /
            (((n + 1).factorial : ℝ) * omegaL L ^ (n + 1))) ^ 2 =
            (1 + Real.exp (Real.pi / 2)) ^ 2 * (Real.sqrt (16 + Real.pi ^ 2)) ^ 2 * ((4 : ℝ) ^ n) ^ 2 /
              ((((n + 1).factorial : ℝ)) ^ 2 * (omegaL L ^ (n + 1)) ^ 2) := by ring
        rw [e1, hs, h16]
        have hω' : omegaL L ≠ 0 := hω.ne'
        have e2 : ((omegaL L ^ 2)⁻¹ : ℝ) ^ (n + 1) = ((omegaL L ^ (n + 1)) ^ 2)⁻¹ := by
          rw [inv_pow]; congr 1; ring
        rw [e2]
        have ha : omegaL L ^ (n + 1) ≠ 0 := pow_ne_zero _ hω'
        have hr : (((n + 1).factorial : ℝ)) ≠ 0 := by positivity
        field_simp
        try ring

variable (L)

/-- The eigenvalue functions `Λ̃_k(ωj+w)` satisfy the per-`k` square-sum bound (finite sums over `j ∈ F`). -/
theorem lamTilde_sq_sum_le {w : ℂ} (hw : w ∈ Gamma0 L) (n : ℕ) (F : Finset ℤ) (k : Idx (n + 1)) :
    ∑ j ∈ F, ‖lamTilde L n k (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w)‖ ^ 2 ≤ bR L (n + 1) ^ 2 := by
  have : ∀ j ∈ F, ‖lamTilde L n k (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w)‖ ^ 2 =
      ‖Lam L n (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) k.1‖ ^ 2 := by
    intro j _
    rw [lamTilde_eq L n _ (no_pole hw n j) k]
  rw [Finset.sum_congr rfl this]
  exact norm_Lam_sq_sum_le hw n k.1 F

/-- **The Bessel inequalities for the kernels** (finite-sum form): for `w ∈ Γ_0` and every finite `F ⊂ ℤ`,
`∑_{n∈F} ‖K_{r,ωn+w} x‖² ≤ b_r² ‖x‖²` and `∑_{n∈F} ‖K_{r,ωn+w}^* x‖² ≤ b_r² ‖x‖²` on `Sym^r L²(𝕋_L)`. -/
theorem bessel_K_finite {w : ℂ} (hw : w ∈ Gamma0 L) (n : ℕ) (F : Finset ℤ)
    (x : SymSector ℂ (L2T L) (n + 1)) :
    (∑ j ∈ F, ‖physicalKernel L (n + 1) (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w) x‖ ^ 2 ≤
      bR L (n + 1) ^ 2 * ‖x‖ ^ 2) ∧
    (∑ j ∈ F, ‖ContinuousLinearMap.adjoint (physicalKernel L (n + 1)
      (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w)) x‖ ^ 2 ≤ bR L (n + 1) ^ 2 * ‖x‖ ^ 2) :=
  bessel_diag (physBasis L n) F
    (fun j : ℤ => physicalKernel L (n + 1) (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w))
    (fun j k => lamTilde L n k (((omegaL L * (j : ℝ) : ℝ) : ℂ) + w))
    (fun j k => eigen_all L n _ k) (fun k => lamTilde_sq_sum_le L hw n F k) x

#print axioms bessel_K_finite

end QuantumNLS.OffgridBessel
