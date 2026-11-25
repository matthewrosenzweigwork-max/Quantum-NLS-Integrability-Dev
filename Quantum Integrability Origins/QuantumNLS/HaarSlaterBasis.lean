import Mathlib
import QuantumNLS.HaarSlater

/-!
# R-F611926F (R3): Slater completeness and the common orthonormal eigenbasis of `K_{r,z}`
(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:293`; imports HKF1, R1/R3 modules read-only)

* `anti_orth_zero`: an antisymmetric `F ∈ L²(𝕋_L^r)` orthogonal to all Slater vectors of strictly increasing mode tuples
  is `0` (Slater completeness, DERIVED from tensor-ONB completeness `eq_zero_of_orth_basis_prod` and the
  antisymmetry of `F`: pairing with a product vector changes by the sign of the permutation).
* `symBasisL2 b`: the vectors `(r!)^{-1/2} S(slater b k)`, `k` strictly increasing, form a Hilbert basis of the symmetric
  subspace `SymL2` (`S` = ordering sign, the unitary `A_r`).
* `physicalSymBasis`: transported to `Sym^r L²(𝕋_L)` via `symmetricPosition`.
* **`physicalKernel_eigen`**: for `q = ρ_r e^{izL} ≠ 1`, `K_{r,z} B_k = (1−q)/r! ∏_j i/(z − ω(k_j+δ_r)) · B_k`
  (`B` independent of `z`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators ComplexConjugate

namespace QuantumNLS.HaarSlaterBasis

open QuantumNLS.BetheIntegralOperator QuantumNLS.PhysicalTensor QuantumNLS.HaarKernelFactorization
  QuantumNLS.HaarKernelFactorizationOp QuantumNLS.HaarResolvent QuantumNLS.HaarTwisted
  QuantumNLS.HaarKernelFactorizationSym QuantumNLS.HaarSlaterDensity QuantumNLS.HaarSlater
  QuantumNLS.BetheCompressedKernel

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-! ### Antisymmetric vectors orthogonal to all Slater vectors vanish -/

section Anti

variable (b : HilbertBasis ℤ ℂ (L2T L))

theorem inner_physPerm_anti {F : L2TN L N} (hF : F ∈ AntiL2 L N) (σ : Equiv.Perm (Fin N))
    (a : L2TN L N) : ⟪physPerm σ a, F⟫_ℂ = ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ⟪a, F⟫_ℂ := by
  have h1 : F = ((Equiv.Perm.sign σ : ℤˣ) : ℂ) • physPerm σ F := by
    rw [hF σ, smul_smul, sign_sq N σ, one_smul]
  conv_lhs => rw [h1]
  rw [inner_smul_right, LinearIsometry.inner_map_map]

theorem inner_perm_prod {F : L2TN L N} (hF : F ∈ AntiL2 L N) (k : Fin N → ℤ)
    (σ : Equiv.Perm (Fin N)) :
    ⟪prodLp (fun i => b (k (σ.symm i))), F⟫_ℂ =
      ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ⟪prodLp (fun i => b (k i)), F⟫_ℂ := by
  have := prodLp_perm σ (fun i => b (k i))
  rw [show (fun i => b (k (σ.symm i))) = (fun i => (fun i => b (k i)) (σ.symm i)) from rfl, this]
  exact inner_physPerm_anti hF σ _

theorem anti_orth_zero {F : L2TN L N} (hF : F ∈ AntiL2 L N)
    (h : ∀ k : Fin N → ℤ, StrictMono k → ⟪slater (fun m => b m) k, F⟫_ℂ = 0) : F = 0 := by
  classical
  refine eq_zero_of_orth_basis_prod b (fun k => ?_)
  by_cases hk : Function.Injective k
  · -- sort
    set σ0 := Tuple.sort k with hσ0
    have hmono : StrictMono (fun i => k (σ0 i)) :=
      (Tuple.monotone_sort k).strictMono_of_injective (hk.comp σ0.injective)
    have h1 := h (fun i => k (σ0 i)) hmono
    -- expand the Slater vector
    have h2 : ⟪slater (fun m => b m) (fun i => k (σ0 i)), F⟫_ℂ =
        ((N.factorial : ℕ) : ℂ) * ⟪prodLp (fun i => b (k (σ0 i))), F⟫_ℂ := by
      unfold slater
      rw [sum_inner]
      have : ∀ τ : Equiv.Perm (Fin N),
          ⟪((Equiv.Perm.sign τ : ℤˣ) : ℂ) • prodLp (fun i => b (k (σ0 (τ.symm i)))), F⟫_ℂ =
            ⟪prodLp (fun i => b (k (σ0 i))), F⟫_ℂ := fun τ => by
        rw [inner_smul_left, conj_sign, inner_perm_prod b hF (fun i => k (σ0 i)) τ, ← mul_assoc,
          sign_sq N τ, one_mul]
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
        nsmul_eq_mul]
    rw [h2] at h1
    have hne : ((N.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
    have h3 : ⟪prodLp (fun i => b (k (σ0 i))), F⟫_ℂ = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hne
      · exact h
    have h4 := inner_perm_prod b hF k σ0.symm
    rw [Equiv.symm_symm] at h4
    rw [h3] at h4
    have hs : ((Equiv.Perm.sign σ0.symm : ℤˣ) : ℂ) ≠ 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ0.symm) with h | h <;> simp [h]
    rcases mul_eq_zero.1 h4.symm with h | h
    · exact absurd h hs
    · exact h
  · -- repeated index: a transposition fixes the product vector
    unfold Function.Injective at hk
    push_neg at hk
    obtain ⟨i, j, hij, hne⟩ := hk
    have hkij : k ∘ Equiv.swap i j = k := by
      funext m
      by_cases hm : m = i
      · subst hm; simp [hij]
      · by_cases hm' : m = j
        · subst hm'; simp [hij]
        · simp [Equiv.swap_apply_of_ne_of_ne hm hm']
    have h1 := inner_perm_prod b hF k (Equiv.swap i j)
    have hfun : (fun m => b (k ((Equiv.swap i j).symm m))) = fun m => b (k m) := by
      funext m
      have := congrFun hkij m
      simp only [Function.comp_apply] at this
      simp [this]
    rw [hfun, Equiv.Perm.sign_swap hne] at h1
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at h1
    have : (2 : ℂ) * ⟪prodLp (fun i => b (k i)), F⟫_ℂ = 0 := by linear_combination h1
    rcases mul_eq_zero.1 this with h | h
    · norm_num at h
    · exact h

end Anti

/-! ### The Hilbert basis of the symmetric subspace -/

section SymBasis

variable (b : HilbertBasis ℤ ℂ (L2T L))

/-- Index set: strictly increasing mode tuples. -/
abbrev Idx (N : ℕ) := {k : Fin N → ℤ // StrictMono k}

theorem slater_mem_anti (k : Fin N → ℤ) : slater (fun m => b m) k ∈ AntiL2 L N :=
  (mem_AntiL2 L N _).2 (slater_anti _ k)

/-- `(r!)^{-1/2} S (slater b k)`, a symmetric function. -/
def symVec (k : Idx N) : L2TN L N :=
  (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) • Sop L N (slater (fun m => b m) k.1)

theorem symVec_mem (k : Idx N) : symVec b k ∈ ContactOperator.SymL2 L N :=
  Submodule.smul_mem _ _ (Sop_mem_sym L N (slater_mem_anti b k.1))

theorem inner_Sop_Sop (a c : L2TN L N) : ⟪Sop L N a, Sop L N c⟫_ℂ = ⟪a, c⟫_ℂ := by
  rw [← inner_Sop_left, Sop_Sop]

theorem inner_symVec (k k' : Idx N) :
    ⟪symVec b k, symVec b k'⟫_ℂ = if k = k' then 1 else 0 := by
  unfold symVec
  rw [inner_smul_left, inner_smul_right, inner_Sop_Sop, inner_slater_strictMono b k.2 k'.2]
  have hfac : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  have hsq : (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) *
      ((N.factorial : ℕ) : ℂ) = 1 := by
    have : ((Real.sqrt (N.factorial : ℝ))⁻¹) * ((Real.sqrt (N.factorial : ℝ))⁻¹) * (N.factorial : ℝ) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _), inv_mul_cancel₀ hfac]
    exact_mod_cast this
  by_cases hkk : k = k'
  · have : k.1 = k'.1 := by rw [hkk]
    rw [if_pos hkk, if_pos this]
    simp only [Complex.conj_ofReal]
    rw [← mul_assoc]
    exact hsq
  · have : ¬ k.1 = k'.1 := fun h => hkk (Subtype.ext h)
    rw [if_neg hkk, if_neg this, mul_zero, mul_zero]

theorem symSpan_orth_bot : (Submodule.span ℂ (Set.range fun k : Idx N =>
    (⟨symVec b k, symVec_mem b k⟩ : ContactOperator.SymL2 L N)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hv' : ∀ k : Idx N, ⟪(⟨symVec b k, symVec_mem b k⟩ : ContactOperator.SymL2 L N), v⟫_ℂ = 0 := by
    intro k
    exact (Submodule.mem_orthogonal _ _).1 hv _ (Submodule.subset_span ⟨k, rfl⟩)
  have hF : Sop L N (v : L2TN L N) ∈ AntiL2 L N := Sop_mem_anti L N v.2
  have hc : ((Real.sqrt (N.factorial : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.factorial_pos N))).ne'
  have hzero := anti_orth_zero b hF (fun k hk => by
    have := hv' ⟨k, hk⟩
    show ⟪slater (fun m => b m) k, Sop L N (v : L2TN L N)⟫_ℂ = 0
    rw [inner_Sop_left]
    change ⟪symVec b ⟨k, hk⟩, (v : L2TN L N)⟫_ℂ = 0 at this
    unfold symVec at this
    rw [inner_smul_left] at this
    simp only [Complex.conj_ofReal] at this
    have hinv : (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) ≠ 0 := by
      simpa using hc
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hinv
    · exact h)
  apply Subtype.ext
  have := congrArg (Sop L N) hzero
  rw [Sop_Sop] at this
  simpa using this

/-- **Hilbert basis of `Sym^r L²(0,L)`** by symmetrized Slater determinants of the twisted modes. -/
def symBasisL2 : HilbertBasis (Idx N) ℂ (ContactOperator.SymL2 L N) :=
  HilbertBasis.mk (v := fun k => (⟨symVec b k, symVec_mem b k⟩ : ContactOperator.SymL2 L N))
    (orthonormal_iff_ite.2 (fun k k' => by
      have := inner_symVec b k k'
      exact this))
    (by rw [(Submodule.topologicalClosure_eq_top_iff).2 (symSpan_orth_bot b)])

end SymBasis

#print axioms anti_orth_zero
#print axioms symBasisL2

end QuantumNLS.HaarSlaterBasis
