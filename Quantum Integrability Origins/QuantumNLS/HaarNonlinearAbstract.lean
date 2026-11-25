import QuantumNLS.PeriodTwoTerm
import QuantumNLS.HilbertDiagOp

/-!
# R-9C3CC17D `QG:lem:haar-nonlinear-tail`, part 2: the commutator argument in a common eigenbasis

Source: `source-text/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:745-795` (the proof after the free expansion).

Abstract setting: a Hilbert basis `b` of a complex Hilbert space `E`; operators diagonal in `b`
(`IsDiagC b T μ`: `⟪b i, T v⟫ = μ i ⟪b i, v⟫`); a set `A` of basis labels (the energy-admissible labels) and a
vector `ψ` supported on `A` (`Supp b A ψ`).

* `IsDiagC.adjoint/.mul/.pow/.sub_smul_one/.supp/.norm_le/.pow_norm_le`: diagonal calculus; a diagonal operator
  whose eigenvalues are `≤ ρ` on `A` has norm `≤ ρ` on vectors supported on `A` (via `HilbertDiagOp.diag_exists`).
* `cJ`, `hasSum_cJ`: `⟪ψ, [T, J] ψ⟫ = Σ_m μ_m c_m` with
  `c_m = ⟪ψ, b_m⟫⟪b_m, Jψ⟫ − ⟪J^*ψ, b_m⟫⟪b_m, ψ⟫` (absolutely summable); `cJ_adjoint`: `c^{J^*} = −conj c^J`.
* `comm_pow_bound`: `|⟪u, [X^{d+1}, J] v⟫| ≤ (d+1) a c ρ^d ‖[X, J]‖` when `‖(X^*)^j u‖ ≤ aρ^j`, `‖X^j v‖ ≤ cρ^j`
  (the expansion of the power commutator into its `d` terms); `comm_sq_bound`: the quadratic term
  `|⟪ψ, [X², J] ψ⟫| ≤ ‖X^*ψ‖‖[X,J]ψ‖ + ‖[X^*,J^*]ψ‖‖Xψ‖`.
* `rect_hasSum`: interchange of a dominated series with the rectangle contour integral.
* `series_comm`: for one label `n` and one contour point: `Σ_m G(x_m) c_m = Σ_{d≥2} g_d ⟪ψ,[X^d,J]ψ⟫` with the
  printed bounds, `|·| ≤ Mσ^{-2} ρ (‖[X,J]ψ‖ + ‖[X^*,J^*]ψ‖) + 16 M σ^{-3} ρ² ‖[X,J]‖` for `ρ ≤ σ/2`.
* **`abstract_tail`**: for the diagonal operator `R` with eigenvalue `κ' Re ∮ Σ_{n∈I} t_n G_w(x_{n,m}(w)) dw` on
  `A`, `|⟪ψ, [R, J] ψ⟫| ≤ |κ'| · perimeter · (2Mσ^{-2}√Q β + 16Mσ^{-3} Q β)` whenever, for `J` and `J^*`, the
  individual commutators are `≤ β` and both square sums over `n ∈ I` are `≤ β²`, and `Σ_{n∈I} ρ_n² ≤ Q`.
  (Cauchy–Schwarz in the label for the quadratic term; individual commutator norms for `d ≥ 3`; the adjoint
  argument for the real part.)
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Complex Filter Topology Set

namespace QuantumNLS.HaarNonlinearAbstract

open QuantumNLS.PeriodReconstruction QuantumNLS.PeriodTwoTerm

/-! ## 1. Diagonal calculus -/

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma mul_ap (A B : E →L[ℂ] E) (v : E) : (A * B) v = A (B v) := rfl

lemma one_ap (v : E) : (1 : E →L[ℂ] E) v = v := rfl

end Basic

section Diag

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (b : HilbertBasis ι ℂ E)

/-- `T` is diagonal in `b` with eigenvalues `μ` (coefficient form). -/
abbrev IsDiagC (T : E →L[ℂ] E) (μ : ι → ℂ) : Prop := ∀ i v, ⟪b i, T v⟫_ℂ = μ i * ⟪b i, v⟫_ℂ

/-- `v` is supported on the label set `A`. -/
def Supp (A : Set ι) (v : E) : Prop := ∀ i, i ∉ A → ⟪b i, v⟫_ℂ = 0

variable {b}

lemma ext_coeff {u v : E} (h : ∀ i, ⟪b i, u⟫_ℂ = ⟪b i, v⟫_ℂ) : u = v := by
  apply b.repr.injective
  ext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, h]

lemma IsDiagC.apply_basis {T : E →L[ℂ] E} {μ : ι → ℂ} (h : IsDiagC b T μ) (i : ι) :
    T (b i) = μ i • b i := by
  refine ext_coeff (b := b) fun j => ?_
  rw [h, inner_smul_right]
  by_cases hj : j = i
  · subst hj; rfl
  · rw [b.orthonormal.inner_eq_zero hj, mul_zero, mul_zero]

lemma IsDiagC.adjoint {T : E →L[ℂ] E} {μ : ι → ℂ} (h : IsDiagC b T μ) :
    IsDiagC b (ContinuousLinearMap.adjoint T) (fun i => conj (μ i)) := by
  intro i v
  rw [ContinuousLinearMap.adjoint_inner_right, h.apply_basis, inner_smul_left]

lemma IsDiagC.mul {S T : E →L[ℂ] E} {μ ν : ι → ℂ} (hS : IsDiagC b S μ) (hT : IsDiagC b T ν) :
    IsDiagC b (S * T) (fun i => μ i * ν i) := by
  intro i v
  rw [mul_ap, hS, hT]; ring

lemma IsDiagC.pow {T : E →L[ℂ] E} {μ : ι → ℂ} (h : IsDiagC b T μ) (d : ℕ) :
    IsDiagC b (T ^ d) (fun i => μ i ^ d) := by
  induction d with
  | zero => intro i v; simp only [pow_zero, one_ap, one_mul]
  | succ d ih =>
    have := ih.mul h
    rw [pow_succ]
    intro i v; rw [this i v]; simp only [pow_succ]

lemma IsDiagC.sub_smul_one {S : E →L[ℂ] E} {μ : ι → ℂ} (h : IsDiagC b S μ) (c : ℂ) :
    IsDiagC b (S - c • (1 : E →L[ℂ] E)) (fun i => μ i - c) := by
  intro i v
  rw [sub_apply, smul_apply, one_ap,
    inner_sub_right, inner_smul_right, h]; ring

lemma IsDiagC.supp {T : E →L[ℂ] E} {μ : ι → ℂ} (h : IsDiagC b T μ) {A : Set ι} {v : E}
    (hv : Supp b A v) : Supp b A (T v) := fun i hi => by rw [h, hv i hi, mul_zero]

lemma IsDiagC.norm_le {T : E →L[ℂ] E} {μ : ι → ℂ} (h : IsDiagC b T μ) {A : Set ι} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ i ∈ A, ‖μ i‖ ≤ ρ) {v : E} (hv : Supp b A v) : ‖T v‖ ≤ ρ * ‖v‖ := by
  classical
  obtain ⟨T', hT', hn⟩ := QuantumNLS.HilbertDiagOp.diag_exists b
    (fun i => if i ∈ A then μ i else 0) ρ (fun i => by
      split_ifs with hi
      · exact hρ i hi
      · rw [norm_zero]; exact hρ0) hρ0
  have : T v = T' v := ext_coeff (b := b) fun i => by
    rw [h, hT']
    split_ifs with hi
    · rfl
    · rw [hv i hi, mul_zero, mul_zero]
  rw [this]
  exact (T'.le_opNorm v).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg v))

lemma IsDiagC.pow_norm_le {T : E →L[ℂ] E} {μ : ι → ℂ} (h : IsDiagC b T μ) {A : Set ι} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ : ∀ i ∈ A, ‖μ i‖ ≤ ρ) {v : E} (hv : Supp b A v) (j : ℕ) :
    ‖(T ^ j) v‖ ≤ ρ ^ j * ‖v‖ := by
  induction j with
  | zero => simp only [pow_zero, one_ap, one_mul, le_refl]
  | succ j ih =>
    rw [pow_succ', mul_ap, pow_succ]
    have hs : Supp b A ((T ^ j) v) := (h.pow j).supp hv
    calc ‖T ((T ^ j) v)‖ ≤ ρ * ‖(T ^ j) v‖ := h.norm_le hρ0 hρ hs
      _ ≤ ρ * (ρ ^ j * ‖v‖) := mul_le_mul_of_nonneg_left ih hρ0
      _ = ρ ^ j * ρ * ‖v‖ := by ring

end Diag

/-! ## 2. The commutator coefficients -/

section Coeff

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (b : HilbertBasis ι ℂ E)

/-- `c_m = ⟪ψ, b_m⟫⟪b_m, Jψ⟫ − ⟪J^*ψ, b_m⟫⟪b_m, ψ⟫`. -/
def cJ (J : E →L[ℂ] E) (ψ : E) (i : ι) : ℂ :=
  ⟪ψ, b i⟫_ℂ * ⟪b i, J ψ⟫_ℂ - ⟪ContinuousLinearMap.adjoint J ψ, b i⟫_ℂ * ⟪b i, ψ⟫_ℂ

variable {b}

/-- `⟪ψ, [T, J] ψ⟫ = Σ_m μ_m c_m` for `T` diagonal. -/
lemma hasSum_cJ {T : E →L[ℂ] E} {μ : ι → ℂ} (h : IsDiagC b T μ) (J : E →L[ℂ] E) (ψ : E) :
    HasSum (fun i => μ i * cJ b J ψ i) ⟪ψ, (T * J - J * T) ψ⟫_ℂ := by
  have h1 := b.hasSum_inner_mul_inner ψ (T (J ψ))
  have h2 := b.hasSum_inner_mul_inner (ContinuousLinearMap.adjoint J ψ) (T ψ)
  rw [ContinuousLinearMap.adjoint_inner_left] at h2
  have h3 := h1.sub h2
  rw [← inner_sub_right] at h3
  convert h3 using 1
  · funext i; simp only [cJ]; rw [h i (J ψ), h i ψ]; ring
  · rfl

lemma cJ_zero {A : Set ι} {ψ : E} (hψ : Supp b A ψ) (J : E →L[ℂ] E) {i : ι} (hi : i ∉ A) :
    cJ b J ψ i = 0 := by
  have h1 : ⟪ψ, b i⟫_ℂ = 0 := by rw [← inner_conj_symm, hψ i hi, map_zero]
  simp only [cJ, h1, hψ i hi, zero_mul, mul_zero, sub_zero]

/-- The dominating sequence `cs_m = |ψ_m|² + |(Jψ)_m|² + |(J^*ψ)_m|²`. -/
def cdom (b : HilbertBasis ι ℂ E) (J : E →L[ℂ] E) (ψ : E) (i : ι) : ℝ :=
  ‖⟪b i, ψ⟫_ℂ‖ ^ 2 + ‖⟪b i, J ψ⟫_ℂ‖ ^ 2 + ‖⟪b i, ContinuousLinearMap.adjoint J ψ⟫_ℂ‖ ^ 2

lemma cs_nonneg (J : E →L[ℂ] E) (ψ : E) (i : ι) : 0 ≤ cdom b J ψ i := by unfold cdom; positivity

lemma summable_cs (J : E →L[ℂ] E) (ψ : E) : Summable (cdom b J ψ) :=
  ((b.orthonormal.inner_products_summable ψ).add (b.orthonormal.inner_products_summable (J ψ))).add
    (b.orthonormal.inner_products_summable (ContinuousLinearMap.adjoint J ψ))

lemma norm_cJ_le (J : E →L[ℂ] E) (ψ : E) (i : ι) : ‖cJ b J ψ i‖ ≤ cdom b J ψ i := by
  unfold cJ cdom
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_inner_symm ψ (b i),
    norm_inner_symm (ContinuousLinearMap.adjoint J ψ) (b i)]
  have := norm_nonneg ⟪b i, ψ⟫_ℂ
  have := norm_nonneg ⟪b i, J ψ⟫_ℂ
  have := norm_nonneg ⟪b i, ContinuousLinearMap.adjoint J ψ⟫_ℂ
  nlinarith [sq_nonneg (‖⟪b i, ψ⟫_ℂ‖ - ‖⟪b i, J ψ⟫_ℂ‖),
    sq_nonneg (‖⟪b i, ψ⟫_ℂ‖ - ‖⟪b i, ContinuousLinearMap.adjoint J ψ⟫_ℂ‖)]

lemma cs_adjoint (J : E →L[ℂ] E) (ψ : E) (i : ι) :
    cdom b (ContinuousLinearMap.adjoint J) ψ i = cdom b J ψ i := by
  unfold cdom; rw [ContinuousLinearMap.adjoint_adjoint]; ring

lemma cJ_adjoint (J : E →L[ℂ] E) (ψ : E) (i : ι) :
    cJ b (ContinuousLinearMap.adjoint J) ψ i = -conj (cJ b J ψ i) := by
  simp only [cJ, ContinuousLinearMap.adjoint_adjoint, map_sub, map_mul, inner_conj_symm]
  ring

end Coeff

/-! ## 3. Commutators of powers -/

section Powers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma comm_pow_succ (X J : E →L[ℂ] E) (d : ℕ) :
    X ^ (d + 1) * J - J * X ^ (d + 1) = X * (X ^ d * J - J * X ^ d) + (X * J - J * X) * X ^ d := by
  rw [pow_succ']; noncomm_ring

/-- The power commutator expanded into its `d` terms. -/
lemma comm_pow_bound (X J : E →L[ℂ] E) {ρ : ℝ} (v : E) {c : ℝ}
    (hv : ∀ j, ‖(X ^ j) v‖ ≤ c * ρ ^ j) (d : ℕ) :
    ∀ (u : E) (a : ℝ), (∀ j, ‖(ContinuousLinearMap.adjoint X ^ j) u‖ ≤ a * ρ ^ j) →
      ‖⟪u, (X ^ (d + 1) * J - J * X ^ (d + 1)) v⟫_ℂ‖ ≤
        (d + 1) * a * c * ρ ^ d * ‖X * J - J * X‖ := by
  induction d with
  | zero =>
    intro u a hu
    have hu0 := hu 0
    have hv0 := hv 0
    simp only [pow_zero, one_ap, mul_one] at hu0 hv0
    rw [zero_add, pow_one]
    refine (norm_inner_le_norm _ _).trans ?_
    have h1 := (X * J - J * X).le_opNorm v
    have := norm_nonneg u
    have := norm_nonneg ((X * J - J * X) v)
    calc ‖u‖ * ‖(X * J - J * X) v‖ ≤ a * (‖X * J - J * X‖ * c) :=
          mul_le_mul hu0 (h1.trans (mul_le_mul_of_nonneg_left hv0 (norm_nonneg _)))
            (norm_nonneg _) (le_trans (norm_nonneg u) hu0)
      _ = ((0 : ℕ) + 1 : ℝ) * a * c * ρ ^ 0 * ‖X * J - J * X‖ := by push_cast; ring
  | succ d ih =>
    intro u a hu
    rw [comm_pow_succ X J (d + 1), add_apply, inner_add_right]
    refine (norm_add_le _ _).trans ?_
    have hu' : ∀ j, ‖(ContinuousLinearMap.adjoint X ^ j) (ContinuousLinearMap.adjoint X u)‖ ≤
        (a * ρ) * ρ ^ j := fun j => by
      have := hu (j + 1)
      rw [pow_succ, mul_ap] at this
      calc _ ≤ a * ρ ^ (j + 1) := this
        _ = a * ρ * ρ ^ j := by ring
    have t1 : ‖⟪u, (X * (X ^ (d + 1) * J - J * X ^ (d + 1))) v⟫_ℂ‖ ≤
        (d + 1) * (a * ρ) * c * ρ ^ d * ‖X * J - J * X‖ := by
      rw [mul_ap, ← ContinuousLinearMap.adjoint_inner_left]
      exact ih _ _ hu'
    have hu0 := hu 0
    simp only [pow_zero, one_ap, mul_one] at hu0
    have t2 : ‖⟪u, ((X * J - J * X) * X ^ (d + 1)) v⟫_ℂ‖ ≤
        a * (‖X * J - J * X‖ * (c * ρ ^ (d + 1))) := by
      rw [mul_ap]
      refine (norm_inner_le_norm _ _).trans ?_
      exact mul_le_mul hu0 (((X * J - J * X).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hv (d + 1)) (norm_nonneg _))) (norm_nonneg _)
        (le_trans (norm_nonneg u) hu0)
    calc _ ≤ (d + 1) * (a * ρ) * c * ρ ^ d * ‖X * J - J * X‖ +
          a * (‖X * J - J * X‖ * (c * ρ ^ (d + 1))) := add_le_add t1 t2
      _ = ((d + 1 : ℕ) + 1) * a * c * ρ ^ (d + 1) * ‖X * J - J * X‖ := by push_cast; ring

/-- The quadratic term. -/
lemma comm_sq_bound (X J : E →L[ℂ] E) (ψ : E) :
    ‖⟪ψ, (X ^ 2 * J - J * X ^ 2) ψ⟫_ℂ‖ ≤
      ‖ContinuousLinearMap.adjoint X ψ‖ * ‖(X * J - J * X) ψ‖ +
        ‖(ContinuousLinearMap.adjoint X * ContinuousLinearMap.adjoint J -
          ContinuousLinearMap.adjoint J * ContinuousLinearMap.adjoint X) ψ‖ * ‖X ψ‖ := by
  have e : X ^ 2 * J - J * X ^ 2 = X * (X * J - J * X) + (X * J - J * X) * X := by
    rw [pow_two]; noncomm_ring
  have eadj : ContinuousLinearMap.adjoint (X * J - J * X) =
      -(ContinuousLinearMap.adjoint X * ContinuousLinearMap.adjoint J -
        ContinuousLinearMap.adjoint J * ContinuousLinearMap.adjoint X) := by
    simp only [← ContinuousLinearMap.star_eq_adjoint, star_sub, star_mul]; abel
  have e1 : ⟪ψ, (X ^ 2 * J - J * X ^ 2) ψ⟫_ℂ =
      ⟪ContinuousLinearMap.adjoint X ψ, (X * J - J * X) ψ⟫_ℂ +
        ⟪ContinuousLinearMap.adjoint (X * J - J * X) ψ, X ψ⟫_ℂ := by
    rw [e, add_apply, inner_add_right, mul_ap, mul_ap, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left]
  rw [e1]
  refine (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) ?_)
  refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [eadj, neg_apply, norm_neg]

end Powers

/-! ## 4. Interchanging a dominated series with the contour integral -/

section Contour

lemma edge_hasSum {κ : Type*} [Countable κ] {F : κ → ℂ → ℂ} {B : κ → ℝ} {γ : ℝ → ℂ}
    (hγ : Continuous γ) {c d : ℝ} {S : Set ℂ} (hmem : ∀ t ∈ uIcc c d, γ t ∈ S)
    (hc : ∀ k, ∀ z ∈ S, ContinuousAt (F k) z) (hB : ∀ k, ∀ z ∈ S, ‖F k z‖ ≤ B k)
    (hBs : Summable B) :
    HasSum (fun k => ∫ t in c..d, F k (γ t)) (∫ t in c..d, ∑' k, F k (γ t)) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => B k)
    (fun k => ?_) (fun k => Eventually.of_forall fun t ht => hB k _ (hmem t (uIoc_subset_uIcc ht)))
    (Eventually.of_forall fun t _ => hBs) intervalIntegrable_const
    (Eventually.of_forall fun t ht => (Summable.of_norm_bounded hBs fun k =>
      hB k _ (hmem t (uIoc_subset_uIcc ht))).hasSum)
  have hcont : ContinuousOn (fun t => F k (γ t)) (uIcc c d) := fun t ht =>
    ((hc k _ (hmem t ht)).comp hγ.continuousAt).continuousWithinAt
  exact (hcont.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc

/-- `Σ_k ∮ F_k = ∮ Σ_k F_k` for a dominated series of functions continuous on the contour. -/
lemma rect_hasSum {κ : Type*} [Countable κ] {F : κ → ℂ → ℂ} {B : κ → ℝ} {a b h : ℝ}
    (hab : a ≤ b) (hh : 0 ≤ h) (hc : ∀ k, ∀ z ∈ Gam a b h, ContinuousAt (F k) z)
    (hB : ∀ k, ∀ z ∈ Gam a b h, ‖F k z‖ ≤ B k) (hBs : Summable B) :
    HasSum (fun k => LabelExactPeriod.rectIntegral (F k) a b h)
      (LabelExactPeriod.rectIntegral (fun z => ∑' k, F k z) a b h) := by
  have e1 := edge_hasSum (γ := fun x : ℝ => (x : ℂ) + ((-h : ℝ) : ℂ) * I) (by fun_prop)
    (fun x hx => bot_mem hab hx) hc hB hBs
  have e2 := edge_hasSum (γ := fun x : ℝ => (x : ℂ) + h * I) (by fun_prop)
    (fun x hx => top_mem hab hx) hc hB hBs
  have e3 := edge_hasSum (γ := fun y : ℝ => (b : ℂ) + y * I) (by fun_prop)
    (fun y hy => right_mem (a := a) hh hy) hc hB hBs
  have e4 := edge_hasSum (γ := fun y : ℝ => (a : ℂ) + y * I) (by fun_prop)
    (fun y hy => left_mem (b := b) hh hy) hc hB hBs
  unfold LabelExactPeriod.rectIntegral
  exact ((e1.sub e2).add (e3.const_smul I)).sub (e4.const_smul I)

lemma rect_congr_Gam {f g : ℂ → ℂ} {a b h : ℝ} (hab : a ≤ b) (hh : 0 ≤ h)
    (hfg : ∀ z ∈ Gam a b h, f z = g z) :
    LabelExactPeriod.rectIntegral f a b h = LabelExactPeriod.rectIntegral g a b h :=
  LabelExactPeriod.rectIntegral_congr (fun _ hx => hfg _ (bot_mem hab hx))
    (fun _ hx => hfg _ (top_mem hab hx)) (fun _ hy => hfg _ (right_mem hh hy))
    (fun _ hy => hfg _ (left_mem hh hy))

end Contour

/-! ## 5. One label and one contour point -/

section Series

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {b : HilbertBasis ι ℂ E}

lemma half_pow_bound {σ ρ : ℝ} (hσ : 0 < σ) (hρ0 : 0 ≤ ρ) (hρσ : ρ ≤ σ / 2) (d : ℕ) :
    σ⁻¹ ^ d * ρ ^ d ≤ (1 / 2) ^ d := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (mul_nonneg (inv_nonneg.2 hσ.le) hρ0) ?_ d
  rw [inv_mul_le_iff₀ hσ]; linarith

/-- **One label, one contour point.** -/
lemma series_comm {X : E →L[ℂ] E} {x : ι → ℂ} (hX : IsDiagC b X x) {A : Set ι} {ψ : E}
    (hψ : Supp b A ψ) (hψ1 : ‖ψ‖ = 1) (J : E →L[ℂ] E) {ρ σ M : ℝ} (hρ0 : 0 ≤ ρ)
    (hρσ : ρ ≤ σ / 2) (hσ : 0 < σ) (hM : 0 ≤ M) (hx : ∀ m ∈ A, ‖x m‖ ≤ ρ) (G : ℂ → ℂ)
    (g : ℕ → ℂ) (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hgM : ∀ d, ‖g d‖ ≤ M * σ⁻¹ ^ d)
    (hG : ∀ y, ‖y‖ ≤ σ / 2 → HasSum (fun d => g d * y ^ d) (G y)) :
    ∃ T : ℂ, HasSum (fun m => G (x m) * cJ b J ψ m) T ∧
      ‖T‖ ≤ M * σ⁻¹ ^ 2 * ρ * (‖(X * J - J * X) ψ‖ +
          ‖(ContinuousLinearMap.adjoint X * ContinuousLinearMap.adjoint J -
            ContinuousLinearMap.adjoint J * ContinuousLinearMap.adjoint X) ψ‖) +
        16 * M * σ⁻¹ ^ 3 * ρ ^ 2 * ‖X * J - J * X‖ := by
  set c := cJ b J ψ with hcdef
  set F : ι × ℕ → ℂ := fun p => g p.2 * x p.1 ^ p.2 * c p.1 with hF
  have hFb : ∀ p, ‖F p‖ ≤ cdom b J ψ p.1 * (M * (1 / 2) ^ p.2) := by
    rintro ⟨m, d⟩
    by_cases hm : m ∈ A
    · simp only [hF, norm_mul, norm_pow]
      have h1 := hgM d
      have h2 : ‖x m‖ ^ d ≤ ρ ^ d := pow_le_pow_left₀ (norm_nonneg _) (hx m hm) d
      have h3 := norm_cJ_le (b := b) J ψ m
      have h4 := half_pow_bound hσ hρ0 hρσ d
      have hσi : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
      calc ‖g d‖ * ‖x m‖ ^ d * ‖c m‖ ≤ (M * σ⁻¹ ^ d) * ρ ^ d * cdom b J ψ m :=
            mul_le_mul (mul_le_mul h1 h2 (by positivity) (mul_nonneg hM (pow_nonneg hσi d))) h3
              (norm_nonneg _) (mul_nonneg (mul_nonneg hM (pow_nonneg hσi d)) (pow_nonneg hρ0 d))
      _ = cdom b J ψ m * (M * (σ⁻¹ ^ d * ρ ^ d)) := by ring
      _ ≤ cdom b J ψ m * (M * (1 / 2) ^ d) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hM) (cs_nonneg J ψ m)
    · simp only [hF, hcdef, cJ_zero hψ J hm, mul_zero, norm_zero]
      exact mul_nonneg (cs_nonneg J ψ m) (mul_nonneg hM (by positivity))
  have hbs : Summable (fun p : ι × ℕ => cdom b J ψ p.1 * (M * (1 / 2) ^ p.2)) :=
    Summable.mul_of_nonneg (f := cdom b J ψ) (g := fun d : ℕ => M * (1 / 2 : ℝ) ^ d)
      (summable_cs J ψ) ((summable_geometric_two).mul_left M) (fun i => cs_nonneg J ψ i)
      (fun d => mul_nonneg hM (by positivity))
  obtain ⟨Tot, hTot⟩ : Summable F := Summable.of_norm_bounded hbs hFb
  refine ⟨Tot, ?_, ?_⟩
  · -- the fibres over `m`
    refine hTot.prod_fiberwise fun m => ?_
    by_cases hm : m ∈ A
    · have := (hG (x m) ((hx m hm).trans hρσ)).mul_right (c m)
      exact this
    · simp only [hF, hcdef, cJ_zero hψ J hm, mul_zero]
      exact hasSum_zero
  · -- the fibres over `d`
    have hswap : HasSum (F ∘ Prod.swap) Tot := (Equiv.prodComm ℕ ι).hasSum_iff.2 hTot
    have hd : ∀ d : ℕ, HasSum (fun m => (F ∘ Prod.swap) (d, m))
        (g d * ⟪ψ, (X ^ d * J - J * X ^ d) ψ⟫_ℂ) := fun d => by
      have := (hasSum_cJ (hX.pow d) J ψ).mul_left (g d)
      refine this.congr_fun fun m => ?_
      simp only [Function.comp, Prod.swap, hF, hcdef]; ring
    have hTd := hswap.prod_fiberwise hd
    -- the bound
    set K := X * J - J * X with hK
    set Kp := ContinuousLinearMap.adjoint X * ContinuousLinearMap.adjoint J -
      ContinuousLinearMap.adjoint J * ContinuousLinearMap.adjoint X with hKp
    have hXψ : ∀ j, ‖(X ^ j) ψ‖ ≤ 1 * ρ ^ j := fun j => by
      have := hX.pow_norm_le hρ0 hx hψ j; rw [hψ1] at this; linarith
    have hXaψ : ∀ j, ‖(ContinuousLinearMap.adjoint X ^ j) ψ‖ ≤ 1 * ρ ^ j := fun j => by
      have := hX.adjoint.pow_norm_le hρ0 (fun m hm => by rw [Complex.norm_conj]; exact hx m hm) hψ j
      rw [hψ1] at this; linarith
    set X2 := M * σ⁻¹ ^ 2 * ρ * (‖K ψ‖ + ‖Kp ψ‖) with hX2
    set K3 := 8 * M * σ⁻¹ ^ 3 * ρ ^ 2 * ‖K‖ with hK3
    have hσi : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
    have hX20 : 0 ≤ X2 :=
      mul_nonneg (mul_nonneg (mul_nonneg hM (by positivity)) hρ0) (by positivity)
    have hK30 : 0 ≤ K3 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hσi 3)) (by positivity))
        (norm_nonneg _)
    set bd : ℕ → ℝ := fun d => (if d = 2 then X2 else 0) + K3 * ((d : ℝ) * (1 / 2) ^ d) with hbd
    have hbd0 : ∀ d, 0 ≤ bd d := fun d => by
      have : 0 ≤ (if d = 2 then X2 else 0) := by split_ifs; exacts [hX20, le_rfl]
      exact add_nonneg this (mul_nonneg hK30 (by positivity))
    have hbdsum : HasSum bd (X2 + K3 * 2) := by
      have h1 := hasSum_ite_eq 2 X2
      have h2 := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ))
        (by rw [Real.norm_of_nonneg (by norm_num)]; norm_num)).mul_left K3
      have e : (1 / 2 : ℝ) / (1 - 1 / 2) ^ 2 = 2 := by norm_num
      rw [e] at h2
      exact h1.add h2
    have hpt : ∀ d, ‖g d * ⟪ψ, (X ^ d * J - J * X ^ d) ψ⟫_ℂ‖ ≤ bd d := by
      intro d
      match d with
      | 0 => rw [hg0, zero_mul, norm_zero]; exact hbd0 0
      | 1 => rw [hg1, zero_mul, norm_zero]; exact hbd0 1
      | 2 =>
        rw [norm_mul]
        have h1 := comm_sq_bound X J ψ
        have h2 : ‖ContinuousLinearMap.adjoint X ψ‖ ≤ ρ := by
          have := hXaψ 1; rwa [pow_one, pow_one, one_mul] at this
        have h3 : ‖X ψ‖ ≤ ρ := by have := hXψ 1; rwa [pow_one, pow_one, one_mul] at this
        have h4 : ‖⟪ψ, (X ^ 2 * J - J * X ^ 2) ψ⟫_ℂ‖ ≤ ρ * (‖K ψ‖ + ‖Kp ψ‖) := by
          refine h1.trans ?_
          have := norm_nonneg (K ψ); have := norm_nonneg (Kp ψ)
          nlinarith
        have h5 := hgM 2
        have e2 : bd 2 = X2 + K3 * (((2 : ℕ) : ℝ) * (1 / 2) ^ 2) := by
          simp only [hbd, ↓reduceIte]
        have h6 : 0 ≤ K3 * (((2 : ℕ) : ℝ) * (1 / 2) ^ 2) := mul_nonneg hK30 (by positivity)
        calc ‖g 2‖ * ‖⟪ψ, (X ^ 2 * J - J * X ^ 2) ψ⟫_ℂ‖ ≤ (M * σ⁻¹ ^ 2) * (ρ * (‖K ψ‖ + ‖Kp ψ‖)) :=
              mul_le_mul h5 h4 (norm_nonneg _) (mul_nonneg hM (by positivity))
          _ = X2 := by simp only [hX2]; ring
          _ ≤ bd 2 := by rw [e2]; linarith
      | k + 3 =>
        rw [norm_mul]
        have h1 := comm_pow_bound X J ψ hXψ (k + 2) ψ 1 hXaψ
        have h5 := hgM (k + 3)
        have h6 := half_pow_bound hσ hρ0 hρσ k
        have hσ0 : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
        calc ‖g (k + 3)‖ * ‖⟪ψ, (X ^ (k + 3) * J - J * X ^ (k + 3)) ψ⟫_ℂ‖
            ≤ (M * σ⁻¹ ^ (k + 3)) * (((k + 2 : ℕ) + 1) * 1 * 1 * ρ ^ (k + 2) * ‖K‖) :=
              mul_le_mul h5 h1 (norm_nonneg _) (mul_nonneg hM (pow_nonneg hσ0 _))
          _ = M * σ⁻¹ ^ 3 * ρ ^ 2 * ‖K‖ * ((k + 3 : ℕ) : ℝ) * (σ⁻¹ ^ k * ρ ^ k) := by
              push_cast; ring
          _ ≤ M * σ⁻¹ ^ 3 * ρ ^ 2 * ‖K‖ * ((k + 3 : ℕ) : ℝ) * (1 / 2) ^ k :=
              mul_le_mul_of_nonneg_left h6 (mul_nonneg (mul_nonneg (mul_nonneg
                (mul_nonneg hM (pow_nonneg hσ0 3)) (by positivity)) (norm_nonneg _)) (by positivity))
          _ = K3 * (((k + 3 : ℕ) : ℝ) * (1 / 2) ^ (k + 3)) := by
              simp only [hK3]; ring
          _ ≤ bd (k + 3) := by
              have e3 : bd (k + 3) = K3 * (((k + 3 : ℕ) : ℝ) * (1 / 2) ^ (k + 3)) := by
                simp only [hbd, show k + 3 ≠ 2 by omega, ↓reduceIte, zero_add]
              rw [e3]
    have := hTd.norm_le_of_bounded hbdsum hpt
    calc ‖Tot‖ ≤ X2 + K3 * 2 := this
      _ = _ := by simp only [hX2, hK3]; ring

end Series

/-! ## 6. The summed nonlinear remainder in a common eigenbasis -/

section Main

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {b : HilbertBasis ι ℂ E}

/-- The commutator hypotheses for `J'` (individual norms and both square sums over `n ∈ I`). -/
def CommBd (X : ℤ → ℂ → E →L[ℂ] E) (I : Finset ℤ) (S : Set ℂ) (ψ : E) (β : ℝ)
    (J' : E →L[ℂ] E) : Prop :=
  ∀ w ∈ S, (∀ n ∈ I, ‖X n w * J' - J' * X n w‖ ≤ β) ∧
    ∑ n ∈ I, ‖(X n w * J' - J' * X n w) ψ‖ ^ 2 ≤ β ^ 2 ∧
    ∑ n ∈ I, ‖(ContinuousLinearMap.adjoint (X n w) * ContinuousLinearMap.adjoint J' -
      ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (X n w)) ψ‖ ^ 2 ≤ β ^ 2

/-- The per-point bound summed over the labels (Cauchy–Schwarz for the quadratic term). -/
lemma point_bound {X : ℤ → ℂ → E →L[ℂ] E} {x : ℤ → ℂ → ι → ℂ}
    (hX : ∀ n w, IsDiagC b (X n w) (x n w)) {A : Set ι} {ψ : E} (hψ : Supp b A ψ)
    (hψ1 : ‖ψ‖ = 1) {I : Finset ℤ} {t : ℤ → ℝ} (ht : ∀ n, |t n| ≤ 1) {ρ : ℤ → ℝ}
    (hρ0 : ∀ n, 0 ≤ ρ n) {σ M β Q : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hρσ : ∀ n ∈ I, ρ n ≤ σ / 2) (hQ : ∑ n ∈ I, ρ n ^ 2 ≤ Q) {G : ℂ → ℂ → ℂ} {g : ℂ → ℕ → ℂ}
    {w : ℂ} (hg0 : g w 0 = 0) (hg1 : g w 1 = 0) (hgM : ∀ d, ‖g w d‖ ≤ M * σ⁻¹ ^ d)
    (hG : ∀ y, ‖y‖ ≤ σ / 2 → HasSum (fun d => g w d * y ^ d) (G w y))
    (hx : ∀ n ∈ I, ∀ m ∈ A, ‖x n w m‖ ≤ ρ n) {J' : E →L[ℂ] E}
    (hK : (∀ n ∈ I, ‖X n w * J' - J' * X n w‖ ≤ β) ∧
      ∑ n ∈ I, ‖(X n w * J' - J' * X n w) ψ‖ ^ 2 ≤ β ^ 2 ∧
      ∑ n ∈ I, ‖(ContinuousLinearMap.adjoint (X n w) * ContinuousLinearMap.adjoint J' -
        ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (X n w)) ψ‖ ^ 2 ≤ β ^ 2) :
    ∃ S : ℂ, HasSum (fun m => cJ b J' ψ m * ∑ n ∈ I, (t n : ℂ) * G w (x n w m)) S ∧
      ‖S‖ ≤ 2 * M * σ⁻¹ ^ 2 * Real.sqrt Q * β + 16 * M * σ⁻¹ ^ 3 * Q * β := by
  obtain ⟨hK1, hK2, hK3⟩ := hK
  have hser : ∀ n ∈ I, ∃ T : ℂ, HasSum (fun m => G w (x n w m) * cJ b J' ψ m) T ∧
      ‖T‖ ≤ M * σ⁻¹ ^ 2 * ρ n * (‖(X n w * J' - J' * X n w) ψ‖ +
          ‖(ContinuousLinearMap.adjoint (X n w) * ContinuousLinearMap.adjoint J' -
            ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (X n w)) ψ‖) +
        16 * M * σ⁻¹ ^ 3 * ρ n ^ 2 * ‖X n w * J' - J' * X n w‖ := fun n hn =>
    series_comm (hX n w) hψ hψ1 J' (hρ0 n) (hρσ n hn) hσ hM (hx n hn) (G w) (g w) hg0 hg1 hgM hG
  choose! T hT hTb using hser
  refine ⟨∑ n ∈ I, (t n : ℂ) * T n, ?_, ?_⟩
  · have := hasSum_sum (s := I) fun n hn => (hT n hn).mul_left (t n : ℂ)
    refine this.congr_fun fun m => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  · have hσi : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
    have hcs1 : ∑ n ∈ I, ρ n * ‖(X n w * J' - J' * X n w) ψ‖ ≤ Real.sqrt Q * β := by
      refine (Real.sum_mul_le_sqrt_mul_sqrt I ρ (fun n => ‖(X n w * J' - J' * X n w) ψ‖)).trans ?_
      exact mul_le_mul (Real.sqrt_le_sqrt hQ)
        ((Real.sqrt_le_sqrt hK2).trans (le_of_eq (Real.sqrt_sq hβ))) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    have hcs2 : ∑ n ∈ I, ρ n * ‖(ContinuousLinearMap.adjoint (X n w) * ContinuousLinearMap.adjoint J' -
        ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (X n w)) ψ‖ ≤ Real.sqrt Q * β := by
      refine (Real.sum_mul_le_sqrt_mul_sqrt I ρ (fun n => ‖(ContinuousLinearMap.adjoint (X n w) *
        ContinuousLinearMap.adjoint J' - ContinuousLinearMap.adjoint J' *
          ContinuousLinearMap.adjoint (X n w)) ψ‖)).trans ?_
      exact mul_le_mul (Real.sqrt_le_sqrt hQ)
        ((Real.sqrt_le_sqrt hK3).trans (le_of_eq (Real.sqrt_sq hβ))) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    have hM2 : 0 ≤ M * σ⁻¹ ^ 2 := mul_nonneg hM (by positivity)
    have hM3 : 0 ≤ 16 * M * σ⁻¹ ^ 3 := mul_nonneg (by linarith) (pow_nonneg hσi 3)
    have hstep : ∀ n ∈ I, ‖(t n : ℂ) * T n‖ ≤
        M * σ⁻¹ ^ 2 * (ρ n * ‖(X n w * J' - J' * X n w) ψ‖ +
          ρ n * ‖(ContinuousLinearMap.adjoint (X n w) * ContinuousLinearMap.adjoint J' -
            ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (X n w)) ψ‖) +
        16 * M * σ⁻¹ ^ 3 * β * ρ n ^ 2 := by
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hTb n hn
      have h2 : ‖X n w * J' - J' * X n w‖ ≤ β := hK1 n hn
      have h3 : 16 * M * σ⁻¹ ^ 3 * ρ n ^ 2 * ‖X n w * J' - J' * X n w‖ ≤
          16 * M * σ⁻¹ ^ 3 * β * ρ n ^ 2 := by
        have h7 : 0 ≤ 16 * M * σ⁻¹ ^ 3 * ρ n ^ 2 := mul_nonneg hM3 (by positivity)
        have := mul_le_mul_of_nonneg_left h2 h7
        linarith
      have h4 : ‖T n‖ ≤ M * σ⁻¹ ^ 2 * (ρ n * ‖(X n w * J' - J' * X n w) ψ‖ +
          ρ n * ‖(ContinuousLinearMap.adjoint (X n w) * ContinuousLinearMap.adjoint J' -
            ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (X n w)) ψ‖) +
          16 * M * σ⁻¹ ^ 3 * β * ρ n ^ 2 := by
        refine h1.trans ?_
        have e : M * σ⁻¹ ^ 2 * ρ n * (‖(X n w * J' - J' * X n w) ψ‖ +
            ‖(ContinuousLinearMap.adjoint (X n w) * ContinuousLinearMap.adjoint J' -
              ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (X n w)) ψ‖) =
            M * σ⁻¹ ^ 2 * (ρ n * ‖(X n w * J' - J' * X n w) ψ‖ +
              ρ n * ‖(ContinuousLinearMap.adjoint (X n w) * ContinuousLinearMap.adjoint J' -
                ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (X n w)) ψ‖) := by
          ring
        linarith
      calc |t n| * ‖T n‖ ≤ 1 * ‖T n‖ := mul_le_mul_of_nonneg_right (ht n) (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h4
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hstep).trans ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hM3' : 0 ≤ 16 * M * σ⁻¹ ^ 3 * β := mul_nonneg hM3 hβ
    calc M * σ⁻¹ ^ 2 * (∑ n ∈ I, ρ n * ‖(X n w * J' - J' * X n w) ψ‖ +
            ∑ n ∈ I, ρ n * ‖(ContinuousLinearMap.adjoint (X n w) * ContinuousLinearMap.adjoint J' -
              ContinuousLinearMap.adjoint J' * ContinuousLinearMap.adjoint (X n w)) ψ‖) +
          16 * M * σ⁻¹ ^ 3 * β * ∑ n ∈ I, ρ n ^ 2
        ≤ M * σ⁻¹ ^ 2 * (Real.sqrt Q * β + Real.sqrt Q * β) + 16 * M * σ⁻¹ ^ 3 * β * Q :=
          add_le_add (mul_le_mul_of_nonneg_left (add_le_add hcs1 hcs2) hM2)
            (mul_le_mul_of_nonneg_left hQ hM3')
      _ = _ := by ring

/-- **The summed nonlinear remainder, abstract form.** -/
theorem abstract_tail [Countable ι] {X : ℤ → ℂ → E →L[ℂ] E} {x : ℤ → ℂ → ι → ℂ}
    (hX : ∀ n w, IsDiagC b (X n w) (x n w)) {A : Set ι} {ψ : E} (hψ : Supp b A ψ)
    (hψ1 : ‖ψ‖ = 1) {I : Finset ℤ} {t : ℤ → ℝ} (ht : ∀ n, |t n| ≤ 1) {ρ : ℤ → ℝ}
    (hρ0 : ∀ n, 0 ≤ ρ n) {σ M β Q : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hρσ : ∀ n ∈ I, ρ n ≤ σ / 2) (hQ : ∑ n ∈ I, ρ n ^ 2 ≤ Q) {G : ℂ → ℂ → ℂ} {g : ℂ → ℕ → ℂ}
    {a b' h : ℝ} (hab : a ≤ b') (hh : 0 ≤ h)
    (hg0 : ∀ w ∈ Gam a b' h, g w 0 = 0) (hg1 : ∀ w ∈ Gam a b' h, g w 1 = 0)
    (hgM : ∀ w ∈ Gam a b' h, ∀ d, ‖g w d‖ ≤ M * σ⁻¹ ^ d)
    (hG : ∀ w ∈ Gam a b' h, ∀ y, ‖y‖ ≤ σ / 2 → HasSum (fun d => g w d * y ^ d) (G w y))
    (hx : ∀ n ∈ I, ∀ w ∈ Gam a b' h, ∀ m ∈ A, ‖x n w m‖ ≤ ρ n)
    (hGc : ∀ m ∈ A, ∀ n ∈ I, ∀ w ∈ Gam a b' h, ContinuousAt (fun w => G w (x n w m)) w)
    {J : E →L[ℂ] E} (hKJ : CommBd X I (Gam a b' h) ψ β J)
    (hKJa : CommBd X I (Gam a b' h) ψ β (ContinuousLinearMap.adjoint J))
    {R : E →L[ℂ] E} {r : ι → ℂ} (hR : IsDiagC b R r) (κ' : ℝ)
    (hr : ∀ m ∈ A, r m = ((κ' * (LabelExactPeriod.rectIntegral
      (fun w => ∑ n ∈ I, (t n : ℂ) * G w (x n w m)) a b' h).re : ℝ) : ℂ)) :
    ‖⟪ψ, (R * J - J * R) ψ⟫_ℂ‖ ≤
      |κ'| * ((2 * (b' - a) + 4 * h) *
        (2 * M * σ⁻¹ ^ 2 * Real.sqrt Q * β + 16 * M * σ⁻¹ ^ 3 * Q * β)) := by
  set Bnd := 2 * M * σ⁻¹ ^ 2 * Real.sqrt Q * β + 16 * M * σ⁻¹ ^ 3 * Q * β with hBnd
  set Ψ : ι → ℂ := fun m => LabelExactPeriod.rectIntegral
    (fun w => ∑ n ∈ I, (t n : ℂ) * G w (x n w m)) a b' h with hΨ
  -- a uniform bound for `G` on the small disc
  have hGb : ∀ w ∈ Gam a b' h, ∀ y, ‖y‖ ≤ σ / 2 → ‖G w y‖ ≤ 2 * M := by
    intro w hw y hy
    have hgs : HasSum (fun d : ℕ => M * (1 / 2 : ℝ) ^ d) (2 * M) := by
      have := hasSum_geometric_two.mul_left M; rwa [mul_comm] at this
    refine (hG w hw y hy).norm_le_of_bounded hgs fun d => ?_
    rw [norm_mul, norm_pow]
    have hσne := hσ.ne'
    calc ‖g w d‖ * ‖y‖ ^ d ≤ (M * σ⁻¹ ^ d) * (σ / 2) ^ d :=
          mul_le_mul (hgM w hw d) (pow_le_pow_left₀ (norm_nonneg _) hy d) (by positivity)
            (mul_nonneg hM (pow_nonneg (inv_nonneg.2 hσ.le) d))
      _ = M * (1 / 2) ^ d := by
          rw [mul_assoc, ← mul_pow]; congr 2; field_simp
  -- the contour sum for `J'`
  have hcont : ∀ J' : E →L[ℂ] E, CommBd X I (Gam a b' h) ψ β J' →
      ∃ V : ℂ, HasSum (fun m => Ψ m * cJ b J' ψ m) V ∧
        ‖V‖ ≤ (2 * (b' - a) + 4 * h) * Bnd := by
    intro J' hK
    set F : ι → ℂ → ℂ := fun m w => cJ b J' ψ m * ∑ n ∈ I, (t n : ℂ) * G w (x n w m) with hF
    have hFc : ∀ m, ∀ z ∈ Gam a b' h, ContinuousAt (F m) z := by
      intro m z hz
      by_cases hm : m ∈ A
      · exact continuousAt_const.mul (tendsto_finsetSum I fun n hn =>
          continuousAt_const.mul (hGc m hm n hn z hz))
      · have : F m = fun _ => 0 := by
          funext w; simp only [hF, cJ_zero hψ J' hm, zero_mul]
        rw [this]; exact continuousAt_const
    have hFb : ∀ m, ∀ z ∈ Gam a b' h, ‖F m z‖ ≤ cdom b J' ψ m * (I.card * (2 * M)) := by
      intro m z hz
      by_cases hm : m ∈ A
      · simp only [hF, norm_mul]
        refine mul_le_mul (norm_cJ_le J' ψ m) ?_ (norm_nonneg _) (cs_nonneg J' ψ m)
        refine (norm_sum_le _ _).trans ?_
        calc ∑ n ∈ I, ‖(t n : ℂ) * G z (x n z m)‖ ≤ ∑ _n ∈ I, 2 * M :=
              Finset.sum_le_sum fun n hn => by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                calc |t n| * ‖G z (x n z m)‖ ≤ 1 * (2 * M) :=
                      mul_le_mul (ht n) (hGb z hz _ ((hx n hn z hz m hm).trans (hρσ n hn)))
                        (norm_nonneg _) zero_le_one
                  _ = 2 * M := one_mul _
          _ = I.card * (2 * M) := by rw [Finset.sum_const, nsmul_eq_mul]
      · simp only [hF, cJ_zero hψ J' hm, zero_mul, norm_zero]
        exact mul_nonneg (cs_nonneg J' ψ m) (mul_nonneg (Nat.cast_nonneg _) (by linarith))
    have hsum := rect_hasSum hab hh hFc hFb ((summable_cs J' ψ).mul_right _)
    -- each term is `c_m Ψ_m`
    have hterm : ∀ m, LabelExactPeriod.rectIntegral (F m) a b' h = Ψ m * cJ b J' ψ m := fun m => by
      rw [show F m = fun w => cJ b J' ψ m * ∑ n ∈ I, (t n : ℂ) * G w (x n w m) from rfl,
        rectIntegral_const_mul, mul_comm]
    -- the pointwise sum
    have hpoint : ∀ z ∈ Gam a b' h, ∃ S : ℂ, HasSum (fun m => F m z) S ∧ ‖S‖ ≤ Bnd := fun z hz =>
      point_bound hX hψ hψ1 ht hρ0 hσ hM hβ hρσ hQ (hg0 z hz) (hg1 z hz) (hgM z hz) (hG z hz)
        (fun n hn m hm => hx n hn z hz m hm) (hK z hz)
    refine ⟨_, hsum.congr_fun fun m => (hterm m).symm, ?_⟩
    refine norm_rectIntegral_le hab hh fun z hz => ?_
    obtain ⟨S, hS, hSb⟩ := hpoint z hz
    rw [hS.tsum_eq]; exact hSb
  obtain ⟨V1, hV1, hV1b⟩ := hcont J hKJ
  obtain ⟨V2, hV2, hV2b⟩ := hcont (ContinuousLinearMap.adjoint J) hKJa
  -- `⟪ψ, [R, J] ψ⟫ = Σ_m r_m c_m = (κ'/2)(V1 − conj V2)`
  have hRJ := hasSum_cJ hR J ψ
  have hconj : HasSum (fun m => conj (Ψ m) * cJ b J ψ m) (-conj V2) := by
    have := (Complex.hasSum_conj'.2 hV2).neg
    refine this.congr_fun fun m => ?_
    rw [cJ_adjoint, map_mul, map_neg, Complex.conj_conj]; ring
  have hcomb : HasSum (fun m => r m * cJ b J ψ m) ((κ' : ℂ) / 2 * (V1 + -conj V2)) := by
    have := (hV1.add hconj).mul_left ((κ' : ℂ) / 2)
    refine this.congr_fun fun m => ?_
    by_cases hm : m ∈ A
    · rw [hr m hm]
      push_cast
      rw [Complex.re_eq_add_conj]
      simp only [hΨ]; ring
    · rw [cJ_zero hψ J hm]; ring
  rw [hRJ.unique hcomb, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_ofNat]
  have h1 : ‖V1 + -conj V2‖ ≤ ‖V1‖ + ‖V2‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, Complex.norm_conj]
  have h2 : ‖V1 + -conj V2‖ ≤ 2 * ((2 * (b' - a) + 4 * h) * Bnd) := by linarith
  calc |κ'| / 2 * ‖V1 + -conj V2‖ ≤ |κ'| / 2 * (2 * ((2 * (b' - a) + 4 * h) * Bnd)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end Main

end QuantumNLS.HaarNonlinearAbstract

#print axioms QuantumNLS.HaarNonlinearAbstract.comm_pow_bound
#print axioms QuantumNLS.HaarNonlinearAbstract.series_comm
#print axioms QuantumNLS.HaarNonlinearAbstract.abstract_tail
