import QuantumNLS.Fourier

/-!
# Positive Fourier multipliers: `A_k = 1 - Σ ∂²`, `A_k^{1/2}`, `A_k^{-1/2}`, the `H¹` form domain

Source anchors (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`):
* `source/chapters/definitions.tex:189` (DEF-031): "For fixed `k`, set `A_k = 1 - Σ_{j=1}^k ∂_{x_j}²`.
  The additive energy trace norm of a difference `D` is `‖A_k^{1/2} D A_k^{1/2}‖₁`, defined through the
  corresponding trace-class form realization."
* `source/chapters/energy_prepared/energy_trace.tex:14–25` (`A_k = 1 + Σ D_j²`, `D_j = -i∂_{x_j}`;
  `A_k^{1/2} ρ A_k^{1/2}` realized on a positive `ρ` with `Tr(A_k ρ) < ∞`, "does not require that the
  range of `ρ` lie in the operator domain of `A_k`"), and `:112–118` (`B = A_k^{-1/2} C A_k^{-1/2}`).

In the Fourier (momentum) representation on the `k`-torus `T_L^k`, `A_k` is the multiplication by
`a_k(n) = 1 + Σ_j (2π n_j / L)²` on `ℓ²(ℤ^k)` (indexed by `Fin k → ℤ`).  **Nothing about
self-adjointness or the form domain is assumed**: for an arbitrary index type `ι` and any real weight
`m ≥ 1`, the maximal multiplication operator `mulOp m` (a mathlib `LinearPMap`) is *proved*
densely defined, symmetric, self-adjoint (`LinearPMap.adjoint` equality), positive, closed, with a
bounded inverse `1/m` (norm `≤ 1`) mapping onto its domain.  `A_k` and `A_k^{1/2}` are the
instances `m = a_k` and `m = √a_k`; `A_k^{1/2}∘A_k^{1/2} = A_k` is proved with domains.

Scope: this is the multiplier side only, on the concrete space `ℓ²(ℤ^k)`; the identification of the
completed tensor power `L²(T_L)^{⊗̂k}` / `Sym^k` with `ℓ²(ℤ^k)` (U2/U3 chain) and the trace-class
form realization of `A_k^{1/2} ρ A_k^{1/2}` for general positive `ρ` (needs the spectral/trace-class
API of `TraceClass.lean`, owned elsewhere) are NOT done here.

No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal ComplexConjugate InnerProductSpace LinearPMap
open QuantumNLS.Fourier

namespace QuantumNLS.Energy

/-! ## `ℓ²(ι)` basics -/

section Basics

variable {ι : Type*}

/-- `ℓ²(ι; ℂ)`. -/
abbrev L2 (ι : Type*) : Type _ := lp (fun _ : ι => ℂ) 2

theorem memL2_iff {f : ι → ℂ} : Memℓp f 2 ↔ Summable fun n => ‖f n‖ ^ 2 := by
  constructor
  · intro h
    have := h.summable (by simp)
    simpa [Real.rpow_two] using this
  · intro h
    apply memℓp_gen
    simpa [Real.rpow_two] using h

theorem summable_sq (z : L2 ι) : Summable fun n => ‖(z : ι → ℂ) n‖ ^ 2 :=
  memL2_iff.1 (lp.memℓp z)

theorem norm_sq_eq_tsum (z : L2 ι) : ‖z‖ ^ 2 = ∑' n, ‖(z : ι → ℂ) n‖ ^ 2 := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by simp) z
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  exact h.tsum_eq.symm

theorem hasSum_norm_sq (z : L2 ι) : HasSum (fun n => ‖(z : ι → ℂ) n‖ ^ 2) (‖z‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by simp) z
  simpa [Real.rpow_two] using h

theorem inner_eq_tsum' (f g : L2 ι) :
    ⟪f, g⟫_ℂ = ∑' n, conj ((f : ι → ℂ) n) * (g : ι → ℂ) n := by
  rw [lp.inner_eq_tsum]
  exact tsum_congr fun n => by simp [mul_comm]

theorem hasSum_inner' (f g : L2 ι) :
    HasSum (fun n => conj ((f : ι → ℂ) n) * (g : ι → ℂ) n) ⟪f, g⟫_ℂ := by
  have h := lp.hasSum_inner (𝕜 := ℂ) f g
  convert h using 2 with n
  simp [mul_comm]

end Basics

/-! ## Bounded real multipliers -/

section Bounded

variable {ι : Type*}

theorem memL2_mul {c : ι → ℝ} {M : ℝ} (hc : ∀ n, |c n| ≤ M) (x : L2 ι) :
    Memℓp (fun n => (c n : ℂ) * (x : ι → ℂ) n) 2 := by
  rw [memL2_iff]
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    ((summable_sq x).mul_left (M ^ 2))
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_left₀ (abs_nonneg _) (hc n) 2)
    (sq_nonneg _)

/-- The bounded multiplication operator `x ↦ (c_n x_n)_n` on `ℓ²(ι)` for a real sequence `|c| ≤ M`. -/
def mulCLM (c : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ n, |c n| ≤ M) : L2 ι →L[ℂ] L2 ι :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => (c n : ℂ) * (x : ι → ℂ) n, memL2_mul hc x⟩
      map_add' := fun x y => by
        apply Subtype.ext; funext n
        exact mul_add _ _ _
      map_smul' := fun a x => by
        apply Subtype.ext; funext n
        show (c n : ℂ) * (a * (x : ι → ℂ) n) = a * ((c n : ℂ) * (x : ι → ℂ) n)
        ring }
    M (fun x => by
      have h1 : ‖(⟨fun n => (c n : ℂ) * (x : ι → ℂ) n, memL2_mul hc x⟩ : L2 ι)‖ ^ 2 ≤
          (M * ‖x‖) ^ 2 := by
        rw [norm_sq_eq_tsum, mul_pow, norm_sq_eq_tsum, ← tsum_mul_left]
        refine Summable.tsum_le_tsum (fun n => ?_) ((memL2_iff.1 (memL2_mul hc x))) 
          ((summable_sq x).mul_left (M ^ 2))
        show ‖(c n : ℂ) * (x : ι → ℂ) n‖ ^ 2 ≤ M ^ 2 * ‖(x : ι → ℂ) n‖ ^ 2
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
        exact mul_le_mul_of_nonneg_right (by simpa using pow_le_pow_left₀ (abs_nonneg _) (hc n) 2)
          (sq_nonneg _)
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).1 h1)

theorem mulCLM_apply (c : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ n, |c n| ≤ M) (x : L2 ι) (n : ι) :
    (mulCLM c M hM hc x : ι → ℂ) n = (c n : ℂ) * (x : ι → ℂ) n := rfl

/-- The bounded real multiplier is symmetric (hence self-adjoint). -/
theorem inner_mulCLM (c : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ n, |c n| ≤ M) (x y : L2 ι) :
    ⟪mulCLM c M hM hc x, y⟫_ℂ = ⟪x, mulCLM c M hM hc y⟫_ℂ := by
  rw [inner_eq_tsum', inner_eq_tsum']
  refine tsum_congr fun n => ?_
  simp only [mulCLM_apply, map_mul, Complex.conj_ofReal]
  ring

theorem mulCLM_isSelfAdjoint (c : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ n, |c n| ≤ M) :
    IsSelfAdjoint (mulCLM c M hM hc) :=
  (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 (fun x y => inner_mulCLM c M hM hc x y)

theorem inner_mulCLM_self (c : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ n, |c n| ≤ M) (x : L2 ι) :
    ⟪mulCLM c M hM hc x, x⟫_ℂ = ((∑' n, c n * ‖(x : ι → ℂ) n‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_eq_tsum', Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [mulCLM_apply, map_mul, Complex.conj_ofReal, mul_assoc, Complex.conj_mul']
  push_cast
  ring

/-- A nonnegative bounded multiplier is a positive operator. -/
theorem mulCLM_isPositive (c : ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ n, |c n| ≤ M)
    (hc0 : ∀ n, 0 ≤ c n) : (mulCLM c M hM hc).IsPositive := by
  refine ⟨fun x y => inner_mulCLM c M hM hc x y, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_mulCLM_self]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  exact tsum_nonneg fun n => mul_nonneg (hc0 n) (sq_nonneg _)

end Bounded

/-! ## The maximal multiplication operator `mulOp m` (unbounded, `m ≥ 1`) -/

section Unbounded

variable {ι : Type*} (m : ι → ℝ)

/-- Domain of the maximal multiplication operator: `{x ∈ ℓ² : m·x ∈ ℓ²}`. -/
def mulDomain : Submodule ℂ (L2 ι) where
  carrier := {x | Memℓp (fun n => (m n : ℂ) * (x : ι → ℂ) n) 2}
  zero_mem' := by
    have : (fun n => (m n : ℂ) * ((0 : L2 ι) : ι → ℂ) n) = 0 := by funext n; simp
    show Memℓp (fun n => (m n : ℂ) * ((0 : L2 ι) : ι → ℂ) n) 2
    rw [this]; exact zero_memℓp
  add_mem' := by
    intro x y hx hy
    have h := Memℓp.add hx hy
    have e : (fun n => (m n : ℂ) * ((x + y : L2 ι) : ι → ℂ) n) =
        (fun n => (m n : ℂ) * (x : ι → ℂ) n) + (fun n => (m n : ℂ) * (y : ι → ℂ) n) := by
      funext n; simp [mul_add]
    show Memℓp (fun n => (m n : ℂ) * ((x + y : L2 ι) : ι → ℂ) n) 2
    rw [e]; exact h
  smul_mem' := by
    intro c x hx
    have h := Memℓp.const_smul hx c
    have e : (fun n => (m n : ℂ) * ((c • x : L2 ι) : ι → ℂ) n) =
        c • (fun n => (m n : ℂ) * (x : ι → ℂ) n) := by
      funext n; simp [mul_left_comm]
    show Memℓp (fun n => (m n : ℂ) * ((c • x : L2 ι) : ι → ℂ) n) 2
    rw [e]; exact h

/-- The maximal multiplication operator `x ↦ m·x` on `ℓ²(ι)`, as a mathlib `LinearPMap`. -/
def mulOp : L2 ι →ₗ.[ℂ] L2 ι where
  domain := mulDomain m
  toFun :=
    { toFun := fun x => ⟨fun n => (m n : ℂ) * ((x : L2 ι) : ι → ℂ) n, x.2⟩
      map_add' := fun x y => by
        apply Subtype.ext; funext n
        show (m n : ℂ) * (((x : L2 ι) : ι → ℂ) n + ((y : L2 ι) : ι → ℂ) n) = _
        exact mul_add _ _ _
      map_smul' := fun a x => by
        apply Subtype.ext; funext n
        show (m n : ℂ) * (a * ((x : L2 ι) : ι → ℂ) n) = a * ((m n : ℂ) * ((x : L2 ι) : ι → ℂ) n)
        ring }

theorem mulOp_apply (x : (mulOp m).domain) (n : ι) :
    ((mulOp m x : L2 ι) : ι → ℂ) n = (m n : ℂ) * ((x : L2 ι) : ι → ℂ) n := rfl

variable {m}

theorem m_ne_zero (hm : ∀ n, 1 ≤ m n) (n : ι) : (m n : ℂ) ≠ 0 := by
  exact_mod_cast (by linarith [hm n] : m n ≠ 0)

/-- The bounded inverse `x ↦ x/m` (norm `≤ 1`). -/
def invCLM (m : ι → ℝ) (hm : ∀ n, 1 ≤ m n) : L2 ι →L[ℂ] L2 ι :=
  mulCLM (fun n => (m n)⁻¹) 1 zero_le_one (fun n => by
    rw [abs_of_pos (inv_pos.2 (by linarith [hm n]))]
    exact inv_le_one_of_one_le₀ (hm n))

theorem invCLM_apply (hm : ∀ n, 1 ≤ m n) (x : L2 ι) (n : ι) :
    (invCLM m hm x : ι → ℂ) n = ((m n)⁻¹ : ℝ) * (x : ι → ℂ) n := rfl

theorem inner_invCLM (hm : ∀ n, 1 ≤ m n) (x y : L2 ι) :
    ⟪invCLM m hm x, y⟫_ℂ = ⟪x, invCLM m hm y⟫_ℂ := inner_mulCLM _ _ _ _ x y

theorem invCLM_mem (hm : ∀ n, 1 ≤ m n) (y : L2 ι) : invCLM m hm y ∈ mulDomain m := by
  have e : (fun n => (m n : ℂ) * ((invCLM m hm y : L2 ι) : ι → ℂ) n) = (y : ι → ℂ) := by
    funext n
    rw [invCLM_apply]
    have := m_ne_zero hm n
    push_cast
    field_simp
  show Memℓp (fun n => (m n : ℂ) * ((invCLM m hm y : L2 ι) : ι → ℂ) n) 2
  rw [e]; exact lp.memℓp y

theorem mulOp_invCLM (hm : ∀ n, 1 ≤ m n) (y : L2 ι) :
    mulOp m ⟨invCLM m hm y, invCLM_mem hm y⟩ = y := by
  apply Subtype.ext; funext n
  show (m n : ℂ) * (((m n)⁻¹ : ℝ) * (y : ι → ℂ) n) = (y : ι → ℂ) n
  have := m_ne_zero hm n
  push_cast
  field_simp

theorem invCLM_mulOp (hm : ∀ n, 1 ≤ m n) (x : (mulOp m).domain) :
    invCLM m hm (mulOp m x) = (x : L2 ι) := by
  apply Subtype.ext; funext n
  show (((m n)⁻¹ : ℝ) : ℂ) * ((m n : ℂ) * ((x : L2 ι) : ι → ℂ) n) = ((x : L2 ι) : ι → ℂ) n
  have := m_ne_zero hm n
  push_cast
  field_simp

theorem mulOp_injective (hm : ∀ n, 1 ≤ m n) : Function.Injective (mulOp m) := by
  intro x y h
  apply Subtype.ext
  have := congrArg (invCLM m hm) h
  rwa [invCLM_mulOp, invCLM_mulOp] at this

/-- The multiplication operator is onto `ℓ²` (it has the bounded right inverse `invCLM`). -/
theorem mulOp_surjective (hm : ∀ n, 1 ≤ m n) : Function.Surjective (mulOp m) :=
  fun y => ⟨⟨invCLM m hm y, invCLM_mem hm y⟩, mulOp_invCLM hm y⟩

/-- The domain is dense. -/
theorem dense_mulDomain (hm : ∀ n, 1 ≤ m n) : Dense (mulDomain m : Set (L2 ι)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_orthogonal] at hy
  have h0 : ∀ w : L2 ι, ⟪w, invCLM m hm y⟫_ℂ = 0 := fun w => by
    rw [← inner_invCLM]
    exact hy _ (invCLM_mem hm w)
  have h1 : invCLM m hm y = 0 := inner_self_eq_zero.1 (h0 _)
  apply Subtype.ext; funext n
  have h2 := congrFun (congrArg Subtype.val h1) n
  rw [invCLM_apply] at h2
  have h3 : ((m n)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (by linarith [hm n])
  have h4 : (((m n)⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h3
  have h2' : (((m n)⁻¹ : ℝ) : ℂ) * (y : ι → ℂ) n = 0 := h2
  exact (mul_eq_zero.1 h2').resolve_left h4

/-- Symmetry: `⟪m x, y⟫ = ⟪x, m y⟫` on the domain. -/
theorem mulOp_formalAdjoint : (mulOp m).IsFormalAdjoint (mulOp m) := by
  intro x y
  show ⟪mulOp m x, (y : L2 ι)⟫_ℂ = ⟪(x : L2 ι), mulOp m y⟫_ℂ
  rw [inner_eq_tsum', inner_eq_tsum']
  refine tsum_congr fun n => ?_
  rw [mulOp_apply, mulOp_apply, map_mul, Complex.conj_ofReal]
  ring

/-- **Self-adjointness, proved**: `(mulOp m)† = mulOp m`, for every weight `m ≥ 1`. -/
theorem mulOp_adjoint_eq (hm : ∀ n, 1 ≤ m n) : (mulOp m)† = mulOp m := by
  have hd := dense_mulDomain hm
  have hle : mulOp m ≤ (mulOp m)† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hd (mulOp_formalAdjoint (m := m))
  have hdom : (mulOp m)†.domain ≤ (mulOp m).domain := by
    intro y hy
    set z := (mulOp m)† ⟨y, hy⟩ with hz
    have key : ∀ w : L2 ι, ⟪invCLM m hm z, w⟫_ℂ = ⟪y, w⟫_ℂ := fun w => by
      rw [inner_invCLM]
      have h2 := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩
        ⟨invCLM m hm w, invCLM_mem hm w⟩
      rw [mulOp_invCLM hm w] at h2
      exact h2
    have hy' : y = invCLM m hm z := (ext_inner_right ℂ key).symm
    rw [hy']
    exact invCLM_mem hm z
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

theorem mulOp_isSelfAdjoint (hm : ∀ n, 1 ≤ m n) : IsSelfAdjoint (mulOp m) :=
  (LinearPMap.isSelfAdjoint_def).2 (mulOp_adjoint_eq hm)

/-- A self-adjoint operator is closed (mathlib), so `mulOp m` is closed. -/
theorem mulOp_isClosed (hm : ∀ n, 1 ≤ m n) : (mulOp m).IsClosed :=
  (mulOp_isSelfAdjoint hm).isClosed

/-- On the domain, `m x ∈ ℓ²` gives a summable weighted square `Σ m|x|²` (as `m ≤ m²`). -/
theorem summable_weight_sq (hm : ∀ n, 1 ≤ m n) (x : (mulOp m).domain) :
    Summable fun n => m n * ‖((x : L2 ι) : ι → ℂ) n‖ ^ 2 := by
  have h := summable_sq (mulOp m x)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by linarith [hm n]) (sq_nonneg _))
    (fun n => ?_) h
  rw [mulOp_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have := hm n
  have h0 : 0 ≤ m n * (m n - 1) * ‖((x : L2 ι) : ι → ℂ) n‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  nlinarith [h0]

/-- **Positivity / form identity**: `⟪x, m x⟫ = Σ m |x|²` (real) on the domain. -/
theorem inner_mulOp_self (x : (mulOp m).domain) :
    ⟪(x : L2 ι), mulOp m x⟫_ℂ = ((∑' n, m n * ‖((x : L2 ι) : ι → ℂ) n‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_eq_tsum', Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [mulOp_apply]
  show conj (((x : L2 ι) : ι → ℂ) n) * ((m n : ℂ) * ((x : L2 ι) : ι → ℂ) n) = _
  rw [mul_left_comm, Complex.conj_mul']
  push_cast
  ring

/-- `‖x‖² ≤ Σ m|x|²` for `m ≥ 1`: the operator is bounded below by `1` (a positive operator). -/
theorem norm_sq_le_form (hm : ∀ n, 1 ≤ m n) (x : (mulOp m).domain) :
    ‖(x : L2 ι)‖ ^ 2 ≤ ∑' n, m n * ‖((x : L2 ι) : ι → ℂ) n‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_sq _) (summable_weight_sq hm x)
  have := hm n
  nlinarith [sq_nonneg ‖((x : L2 ι) : ι → ℂ) n‖]

/-- The range of the bounded inverse is exactly the domain. -/
theorem invCLM_range (hm : ∀ n, 1 ≤ m n) : Set.range (invCLM m hm) = (mulDomain m : Set (L2 ι)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩; exact invCLM_mem hm y
  · intro hx
    exact ⟨mulOp m ⟨x, hx⟩, invCLM_mulOp hm ⟨x, hx⟩⟩

/-- The bounded inverse is positive (nonnegative multiplier `1/m`). -/
theorem invCLM_isPositive (hm : ∀ n, 1 ≤ m n) : (invCLM m hm).IsPositive :=
  mulCLM_isPositive _ _ _ _ (fun n => (inv_pos.2 (by linarith [hm n])).le)

theorem invCLM_isSelfAdjoint (hm : ∀ n, 1 ≤ m n) : IsSelfAdjoint (invCLM m hm) :=
  mulCLM_isSelfAdjoint _ _ _ _

theorem norm_invCLM_le (hm : ∀ n, 1 ≤ m n) : ‖invCLM m hm‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  have h1 : ‖invCLM m hm x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq_tsum, norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ (summable_sq x)
    · rw [invCLM_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have h2 : ((m n)⁻¹) ^ 2 ≤ 1 := by
        have := inv_le_one_of_one_le₀ (hm n)
        have h0 : 0 ≤ (m n)⁻¹ := inv_nonneg.2 (by linarith [hm n])
        nlinarith
      exact mul_le_of_le_one_left (sq_nonneg _) h2
    · exact summable_sq _
  rw [one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

end Unbounded

/-! ## The form-domain Hilbert space `D(m)` with norm `‖m·x‖` -/

/-- A bundled multiplier weight `m ≥ 1`. -/
structure Mult (ι : Type*) where
  m : ι → ℝ
  one_le : ∀ n, 1 ≤ m n

namespace Mult

variable {ι : Type*} (M : Mult ι)

/-- The domain of `mulOp M.m`, as a space with norm `‖M.m · x‖`.  A `def` (not an `abbrev`) so that
the `ℓ²` norm of the ambient submodule is not inherited. -/
def DomSpace : Type _ := ↥(mulDomain M.m)

instance : AddCommGroup M.DomSpace := inferInstanceAs (AddCommGroup ↥(mulDomain M.m))
instance : Module ℂ M.DomSpace := inferInstanceAs (Module ℂ ↥(mulDomain M.m))

variable {M}

/-- The underlying `ℓ²` vector. -/
def DomSpace.val (x : M.DomSpace) : L2 ι := Subtype.val (show ↥(mulDomain M.m) from x)

def DomSpace.mk (x : L2 ι) (h : x ∈ mulDomain M.m) : M.DomSpace := (⟨x, h⟩ : ↥(mulDomain M.m))

theorem DomSpace.mem (x : M.DomSpace) : x.val ∈ mulDomain M.m :=
  (show ↥(mulDomain M.m) from x).2

theorem DomSpace.ext {x y : M.DomSpace} (h : x.val = y.val) : x = y := Subtype.ext h

@[simp] theorem DomSpace.val_mk (x : L2 ι) (h : x ∈ mulDomain M.m) : (DomSpace.mk x h).val = x := rfl
@[simp] theorem DomSpace.val_add (x y : M.DomSpace) : (x + y).val = x.val + y.val := rfl
@[simp] theorem DomSpace.val_smul (c : ℂ) (x : M.DomSpace) : (c • x).val = c • x.val := rfl

variable (M)

/-- The graph-type map `x ↦ M.m · x` into `ℓ²`. -/
def DomSpace.graph : M.DomSpace →ₗ[ℂ] L2 ι where
  toFun x := ⟨fun n => (M.m n : ℂ) * (x.val : ι → ℂ) n, x.mem⟩
  map_add' x y := by
    apply Subtype.ext; funext n
    show (M.m n : ℂ) * ((x.val : ι → ℂ) n + (y.val : ι → ℂ) n) =
      (M.m n : ℂ) * (x.val : ι → ℂ) n + (M.m n : ℂ) * (y.val : ι → ℂ) n
    exact mul_add _ _ _
  map_smul' c x := by
    apply Subtype.ext; funext n
    show (M.m n : ℂ) * (c * (x.val : ι → ℂ) n) = c * ((M.m n : ℂ) * (x.val : ι → ℂ) n)
    ring

theorem DomSpace.graph_apply (x : M.DomSpace) (n : ι) :
    (DomSpace.graph M x : ι → ℂ) n = (M.m n : ℂ) * (x.val : ι → ℂ) n := rfl

theorem DomSpace.graph_injective : Function.Injective (DomSpace.graph M) := by
  intro x y h
  apply DomSpace.ext
  have := mulOp_injective M.one_le (show mulOp M.m ⟨x.val, x.mem⟩ = mulOp M.m ⟨y.val, y.mem⟩ from h)
  exact congrArg Subtype.val this

instance : NormedAddCommGroup M.DomSpace :=
  NormedAddCommGroup.induced M.DomSpace (L2 ι) (DomSpace.graph M) (DomSpace.graph_injective M)

theorem DomSpace.norm_def (x : M.DomSpace) : ‖x‖ = ‖DomSpace.graph M x‖ := rfl

instance : NormedSpace ℂ M.DomSpace where
  norm_smul_le c x := by
    rw [DomSpace.norm_def, DomSpace.norm_def, map_smul, norm_smul]

instance : InnerProductSpace ℂ M.DomSpace where
  inner x y := inner ℂ (DomSpace.graph M x) (DomSpace.graph M y)
  norm_sq_eq_re_inner x := by exact norm_sq_eq_re_inner (DomSpace.graph M x)
  conj_inner_symm x y := by exact inner_conj_symm (DomSpace.graph M x) (DomSpace.graph M y)
  add_left x y z := by simp
  smul_left x y c := by simp [mul_comm]

theorem DomSpace.graph_surjective : Function.Surjective (DomSpace.graph M) := fun y =>
  ⟨DomSpace.mk (invCLM M.m M.one_le y) (invCLM_mem M.one_le y), mulOp_invCLM M.one_le y⟩

/-- **`A^{1/2}`-type unitary**: `D(m) ≃ₗᵢ ℓ²`, `x ↦ m·x`. -/
def DomSpace.unitary : M.DomSpace ≃ₗᵢ[ℂ] L2 ι where
  __ := LinearEquiv.ofBijective (DomSpace.graph M) ⟨DomSpace.graph_injective M, DomSpace.graph_surjective M⟩
  norm_map' _ := rfl

/-- **Completeness**: the form domain is a Hilbert space (not assumed: unitary equivalence with `ℓ²`). -/
instance : CompleteSpace M.DomSpace := (DomSpace.unitary M).toIsometryEquiv.completeSpace

theorem DomSpace.norm_sq_eq_tsum (x : M.DomSpace) :
    ‖x‖ ^ 2 = ∑' n, (M.m n) ^ 2 * ‖(x.val : ι → ℂ) n‖ ^ 2 := by
  rw [DomSpace.norm_def, QuantumNLS.Energy.norm_sq_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [DomSpace.graph_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Continuous inclusion `D(m) ↪ ℓ²`: `‖x‖_{ℓ²} ≤ ‖m x‖` (norm `≤ 1`, as `m ≥ 1`). -/
theorem DomSpace.norm_val_le (x : M.DomSpace) : ‖x.val‖ ≤ ‖x‖ := by
  have h1 : ‖x.val‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [DomSpace.norm_sq_eq_tsum, QuantumNLS.Energy.norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_sq _) ?_
    · have := M.one_le n
      have h0 : 0 ≤ (M.m n ^ 2 - 1) * ‖(x.val : ι → ℂ) n‖ ^ 2 :=
        mul_nonneg (by nlinarith) (sq_nonneg _)
      nlinarith [h0]
    · have h := summable_sq (DomSpace.graph M x)
      refine h.congr fun n => ?_
      rw [DomSpace.graph_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

end Mult

/-! ## Domains via summability -/

section DomainIff

variable {ι : Type*}

/-- `x ∈ D(m) ⟺ Σ m²|x|² < ∞`. -/
theorem mem_mulDomain_iff (m : ι → ℝ) (x : L2 ι) :
    x ∈ mulDomain m ↔ Summable fun n => (m n) ^ 2 * ‖(x : ι → ℂ) n‖ ^ 2 := by
  show Memℓp (fun n => (m n : ℂ) * (x : ι → ℂ) n) 2 ↔ _
  rw [memL2_iff]
  refine summable_congr fun n => ?_
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end DomainIff

/-! ## The kinetic multiplier `A_k = 1 + Σ_j D_j²` on `ℓ²(ℤ^k)` -/

section Kinetic

variable (L : ℝ) (k : ℕ)

/-- Momentum multi-indices for `k` particles: the Fourier side `ℤ^k` of `T_L^k`. -/
abbrev Mom (k : ℕ) : Type := Fin k → ℤ

/-- `a_k(n) = 1 + Σ_{j<k} (2π n_j / L)²`: the symbol of `A_k = 1 - Σ_j ∂_{x_j}²` (DEF-031). -/
def kinWeight (n : Mom k) : ℝ := 1 + ∑ j, freq L (n j) ^ 2

theorem one_le_kinWeight (n : Mom k) : 1 ≤ kinWeight L k n := by
  unfold kinWeight
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (freq L (n j)))
  linarith

/-- `√a_k`: the symbol of `A_k^{1/2}`. -/
def kinSqrt (n : Mom k) : ℝ := Real.sqrt (kinWeight L k n)

theorem one_le_kinSqrt (n : Mom k) : 1 ≤ kinSqrt L k n :=
  Real.one_le_sqrt.2 (one_le_kinWeight L k n)

theorem kinSqrt_sq (n : Mom k) : kinSqrt L k n ^ 2 = kinWeight L k n :=
  Real.sq_sqrt (by linarith [one_le_kinWeight L k n])

/-- At `k = 1` the symbol is F04's bracket `(1 + p_n²)` (`f04Weight L 1`). -/
theorem kinWeight_one (n : Mom 1) : kinWeight L 1 n = f04Weight L 1 (n 0) := by
  simp [kinWeight, f04Weight_one]

/-- Additivity over the particles (the sum of one-body symbols). -/
theorem kinWeight_eq_add (n : Mom k) :
    kinWeight L k n = 1 + ∑ j, (f04Weight L 1 (n j) - 1) := by
  simp [kinWeight, f04Weight_one]

/-- The multiplier `A_k` (weight `a_k ≥ 1`). -/
def kinMult : Mult (Mom k) := ⟨kinWeight L k, one_le_kinWeight L k⟩

/-- The multiplier `A_k^{1/2}` (weight `√a_k ≥ 1`). -/
def kinSqrtMult : Mult (Mom k) := ⟨kinSqrt L k, one_le_kinSqrt L k⟩

/-- `A_k = 1 - Σ_{j≤k} ∂_{x_j}²` in the Fourier representation (unbounded, maximal domain). -/
def Ak : L2 (Mom k) →ₗ.[ℂ] L2 (Mom k) := mulOp (kinWeight L k)

/-- `A_k^{1/2}` in the Fourier representation (unbounded, maximal domain). -/
def Ahalf : L2 (Mom k) →ₗ.[ℂ] L2 (Mom k) := mulOp (kinSqrt L k)

/-- `A_k^{-1}`: bounded, positive, self-adjoint, norm `≤ 1`. -/
def AkInv : L2 (Mom k) →L[ℂ] L2 (Mom k) := invCLM (kinWeight L k) (one_le_kinWeight L k)

/-- `A_k^{-1/2}`: bounded, positive, self-adjoint, norm `≤ 1`, range `D(A_k^{1/2}) = H¹`. -/
def AhalfInv : L2 (Mom k) →L[ℂ] L2 (Mom k) := invCLM (kinSqrt L k) (one_le_kinSqrt L k)

/-- `A_k` is self-adjoint (proved). -/
theorem Ak_isSelfAdjoint : IsSelfAdjoint (Ak L k) := mulOp_isSelfAdjoint (one_le_kinWeight L k)

/-- `A_k^{1/2}` is self-adjoint (proved). -/
theorem Ahalf_isSelfAdjoint : IsSelfAdjoint (Ahalf L k) := mulOp_isSelfAdjoint (one_le_kinSqrt L k)

theorem Ak_isClosed : (Ak L k).IsClosed := mulOp_isClosed (one_le_kinWeight L k)

theorem Ahalf_isClosed : (Ahalf L k).IsClosed := mulOp_isClosed (one_le_kinSqrt L k)

theorem AhalfInv_isPositive : (AhalfInv L k).IsPositive := invCLM_isPositive _

theorem AhalfInv_isSelfAdjoint : IsSelfAdjoint (AhalfInv L k) := invCLM_isSelfAdjoint _

theorem norm_AhalfInv_le : ‖AhalfInv L k‖ ≤ 1 := norm_invCLM_le _

theorem norm_AkInv_le : ‖AkInv L k‖ ≤ 1 := norm_invCLM_le _

/-- **`A_k^{1/2}` is a square root of `A_k`, with domains**: `x ∈ D(A_k) ⟺ x ∈ D(A_k^{1/2}) ∧
A_k^{1/2} x ∈ D(A_k^{1/2})`. -/
theorem mem_Ak_domain_iff (x : L2 (Mom k)) :
    x ∈ (Ak L k).domain ↔
      ∃ hx : x ∈ (Ahalf L k).domain, (Ahalf L k ⟨x, hx⟩ : L2 (Mom k)) ∈ (Ahalf L k).domain := by
  show x ∈ mulDomain (kinWeight L k) ↔
    ∃ hx : x ∈ mulDomain (kinSqrt L k), (mulOp (kinSqrt L k) ⟨x, hx⟩ : L2 (Mom k)) ∈
      mulDomain (kinSqrt L k)
  constructor
  · intro hx
    rw [mem_mulDomain_iff] at hx
    have hx' : x ∈ mulDomain (kinSqrt L k) := by
      rw [mem_mulDomain_iff]
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (fun n => ?_) hx
      rw [kinSqrt_sq]
      have := one_le_kinWeight L k n
      have h0 : 0 ≤ kinWeight L k n * (kinWeight L k n - 1) * ‖(x : Mom k → ℂ) n‖ ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
      nlinarith [h0]
    refine ⟨hx', ?_⟩
    rw [mem_mulDomain_iff]
    refine hx.congr fun n => ?_
    rw [mulOp_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← mul_assoc,
      ← pow_two, kinSqrt_sq]
  · rintro ⟨hx, hy⟩
    rw [mem_mulDomain_iff] at hy ⊢
    refine hy.congr fun n => ?_
    rw [mulOp_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← mul_assoc,
      ← pow_two, kinSqrt_sq]

/-- ... and `A_k x = A_k^{1/2}(A_k^{1/2} x)` there. -/
theorem Ak_eq_Ahalf_comp (x : L2 (Mom k)) (hx : x ∈ (Ak L k).domain) :
    Ak L k ⟨x, hx⟩ = Ahalf L k ⟨Ahalf L k ⟨x, ((mem_Ak_domain_iff L k x).1 hx).1⟩,
      ((mem_Ak_domain_iff L k x).1 hx).2⟩ := by
  apply Subtype.ext; funext n
  show (kinWeight L k n : ℂ) * (x : Mom k → ℂ) n =
    (kinSqrt L k n : ℂ) * ((kinSqrt L k n : ℂ) * (x : Mom k → ℂ) n)
  rw [← mul_assoc, ← Complex.ofReal_mul, ← pow_two, kinSqrt_sq]

/-! ### The `H¹` form domain `Q_k = D(A_k^{1/2})` with the energy norm -/

/-- `H¹(T_L^k)` in momentum representation: `D(A_k^{1/2})` with `‖x‖_Q = ‖A_k^{1/2}x‖`. -/
abbrev H1Dom : Type := (kinSqrtMult L k).DomSpace

variable {L k}

theorem summable_kin_form (x : H1Dom L k) :
    Summable fun n => kinWeight L k n * ‖(x.val : Mom k → ℂ) n‖ ^ 2 := by
  have := (mem_mulDomain_iff (kinSqrt L k) x.val).1 x.mem
  refine this.congr fun n => ?_
  rw [kinSqrt_sq]

/-- **Energy norm = the quadratic form of `A_k`**: `‖x‖²_Q = Σ a_k(n)|x_n|²`. -/
theorem H1Dom.norm_sq_eq (x : H1Dom L k) :
    ‖x‖ ^ 2 = ∑' n, kinWeight L k n * ‖(x.val : Mom k → ℂ) n‖ ^ 2 := by
  rw [Mult.DomSpace.norm_sq_eq_tsum]
  exact tsum_congr fun n => by
    show kinSqrt L k n ^ 2 * _ = _
    rw [kinSqrt_sq]

/-- Each one-body kinetic term is summable and bounded by the form. -/
theorem summable_kin_term (x : H1Dom L k) (j : Fin k) :
    Summable fun n => freq L (n j) ^ 2 * ‖(x.val : Mom k → ℂ) n‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (fun n => ?_)
    (summable_kin_form x)
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  unfold kinWeight
  have := Finset.single_le_sum (f := fun j => freq L (n j) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ j)
  linarith

/-- **`‖x‖²_{H¹_k} = ‖x‖²_{L²} + Σ_j ‖D_j x‖²`**, with `‖D_j x‖² = Σ_n (2πn_j/L)²|x_n|²`
(the source's `A_k = 1 + Σ D_j²`). -/
theorem H1Dom.kinetic_split (x : H1Dom L k) :
    ‖x‖ ^ 2 = ‖x.val‖ ^ 2 + ∑ j, ∑' n, freq L (n j) ^ 2 * ‖(x.val : Mom k → ℂ) n‖ ^ 2 := by
  rw [H1Dom.norm_sq_eq, QuantumNLS.Energy.norm_sq_eq_tsum]
  have e : ∀ n : Mom k, kinWeight L k n * ‖(x.val : Mom k → ℂ) n‖ ^ 2 =
      ‖(x.val : Mom k → ℂ) n‖ ^ 2 + ∑ j, freq L (n j) ^ 2 * ‖(x.val : Mom k → ℂ) n‖ ^ 2 :=
    fun n => by unfold kinWeight; rw [add_mul, one_mul, Finset.sum_mul]
  simp_rw [e]
  rw [(summable_sq x.val).tsum_add (summable_sum fun j _ => summable_kin_term x j),
    Summable.tsum_finsetSum (fun j _ => summable_kin_term x j)]

/-- Continuous inclusion `H¹_k ↪ L²` of norm `≤ 1`: `‖x‖_{L²} ≤ ‖x‖_{H¹}`. -/
theorem H1Dom.norm_val_le (x : H1Dom L k) : ‖x.val‖ ≤ ‖x‖ := Mult.DomSpace.norm_val_le (kinSqrtMult L k) x

/-- **Completeness of `H¹_k`** (Hilbert space; derived, not assumed). -/
example : CompleteSpace (H1Dom L k) := inferInstance

/-- `A_k^{-1/2}` is the inverse of the unitary `A_k^{1/2} : H¹ ≃ ℓ²` (range of `A_k^{-1/2}` = `H¹`). -/
theorem H1Dom.unitary_symm_val (y : L2 (Mom k)) :
    (((Mult.DomSpace.unitary (kinSqrtMult L k)).symm y : H1Dom L k).val : L2 (Mom k)) =
      AhalfInv L k y := by
  have h : Mult.DomSpace.unitary (kinSqrtMult L k)
      (Mult.DomSpace.mk (AhalfInv L k y) (invCLM_mem (one_le_kinSqrt L k) y)) = y :=
    mulOp_invCLM (one_le_kinSqrt L k) y
  have h2 := (LinearIsometryEquiv.symm_apply_eq _).2 h.symm
  rw [h2]; rfl

end Kinetic

/-! ## Forms bounded on the form domain ⟺ `B = A^{-1/2} C A^{-1/2}` bounded on `ℓ²`

Source (`energy_trace.tex:112`): "Boundedness of `C : H¹ → H^{-1}` means precisely that
`B = A_k^{-1/2} C A_k^{-1/2}` is bounded on `L²`."  Here a (possibly unbounded a priori) sesquilinear
form `c` on the form domain is bounded in the energy norm iff it is of the form
`c(f,g) = ⟨B A^{1/2} f, A^{1/2} g⟩` for a bounded operator `B` (the Riesz representation). -/

namespace Mult

variable {ι : Type*} {M : Mult ι}

/-- **Form-boundedness ⟺ bounded `B`**, for the form domain `D(m)` with norm `‖m·x‖`. -/
theorem form_bounded_iff (c : M.DomSpace →ₛₗ[starRingEnd ℂ] M.DomSpace →ₗ[ℂ] ℂ) :
    (∃ C : ℝ, ∀ f g : M.DomSpace, ‖c f g‖ ≤ C * ‖f‖ * ‖g‖) ↔
      ∃ B : L2 ι →L[ℂ] L2 ι, ∀ f g : M.DomSpace,
        c f g = ⟪B (DomSpace.unitary M f), DomSpace.unitary M g⟫_ℂ := by
  constructor
  · rintro ⟨C, hC⟩
    let ct : M.DomSpace →SL[starRingEnd ℂ] M.DomSpace →L[ℂ] ℂ := LinearMap.mkContinuous₂ c C hC
    let U' : L2 ι →L[ℂ] M.DomSpace :=
      (DomSpace.unitary M).symm.toContinuousLinearEquiv.toContinuousLinearMap
    let c' : L2 ι →SL[starRingEnd ℂ] L2 ι →L[ℂ] ℂ := ct.bilinearComp U' U'
    refine ⟨InnerProductSpace.continuousLinearMapOfBilin c', fun f g => ?_⟩
    have h1 := InnerProductSpace.continuousLinearMapOfBilin_apply c'
      (DomSpace.unitary M f) (DomSpace.unitary M g)
    rw [h1]
    show c f g = ct (U' (DomSpace.unitary M f)) (U' (DomSpace.unitary M g))
    have e1 : U' (DomSpace.unitary M f) = f := (DomSpace.unitary M).symm_apply_apply f
    have e2 : U' (DomSpace.unitary M g) = g := (DomSpace.unitary M).symm_apply_apply g
    rw [e1, e2]
    rfl
  · rintro ⟨B, hB⟩
    refine ⟨‖B‖, fun f g => ?_⟩
    rw [hB]
    calc ‖⟪B (DomSpace.unitary M f), DomSpace.unitary M g⟫_ℂ‖
        ≤ ‖B (DomSpace.unitary M f)‖ * ‖DomSpace.unitary M g‖ := norm_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖DomSpace.unitary M f‖) * ‖DomSpace.unitary M g‖ :=
          mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _)
      _ = ‖B‖ * ‖f‖ * ‖g‖ := by
          rw [(DomSpace.unitary M).norm_map, (DomSpace.unitary M).norm_map]

end Mult

/-! ## Rank-one energy realization `|A^{1/2} f⟩⟨A^{1/2} f|`

For `f` in the form domain `Q`, the sandwich of the rank-one density `|f⟩⟨f|` is realized *without
`f ∈ D(A)`* as the rank-one operator on `ℓ²` built from `A^{1/2} f ∈ ℓ²` (source `energy_trace.tex:19–25`:
"does not require that the range of `ρ` lie in the operator domain of `A_k`").  The countable
diagonalization `Σ λ_j |A^{1/2} f_j⟩⟨A^{1/2} f_j|` and its trace norm `Tr(A_k ρ)` need the trace-class API
(`TraceClass.lean`) and are NOT done here. -/

section RankOne

variable {ι : Type*} (M : Mult ι)

/-- `|M f⟩⟨M f|` for `f ∈ D(m)`; for `M = A_k^{1/2}` this is `A_k^{1/2}|f⟩⟨f|A_k^{1/2}`. -/
def energyRankOne (f : M.DomSpace) : L2 ι →L[ℂ] L2 ι :=
  InnerProductSpace.rankOne ℂ (Mult.DomSpace.unitary M f) (Mult.DomSpace.unitary M f)

theorem energyRankOne_isPositive (f : M.DomSpace) : (energyRankOne M f).IsPositive :=
  InnerProductSpace.isPositive_rankOne_self _

/-- Its operator norm is the squared energy norm `‖f‖²_Q`. -/
theorem norm_energyRankOne (f : M.DomSpace) : ‖energyRankOne M f‖ = ‖f‖ ^ 2 := by
  unfold energyRankOne
  rw [InnerProductSpace.norm_rankOne, (Mult.DomSpace.unitary M).norm_map, ← pow_two]

/-- Action: `|A^{1/2}f⟩⟨A^{1/2}f| g = ⟨A^{1/2}f, g⟩ A^{1/2}f`. -/
theorem energyRankOne_apply (f : M.DomSpace) (g : L2 ι) :
    energyRankOne M f g =
      ⟪Mult.DomSpace.unitary M f, g⟫_ℂ • Mult.DomSpace.unitary M f := by
  unfold energyRankOne
  rw [InnerProductSpace.rankOne_apply]

end RankOne

end QuantumNLS.Energy
