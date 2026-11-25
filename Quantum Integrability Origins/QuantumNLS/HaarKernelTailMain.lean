import QuantumNLS.HaarKernelTailPointwise

/-!
# R-3B18A493 QG:prop:haar-kernel-tail, Part 3: the compact-uniform strong high-label tail

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:433-446`.

Statement (literal): for fixed `r` and every compact `C ⊆ Sym^r L²`,
`lim_{R→∞} sup_{‖t‖_∞ ≤ 1, t_n=0 (|n|≤R)} sup_{f∈C} ‖T_r(t) f‖ = 0`, given in the ε–N form
`∀ ε > 0, ∃ R₀, ∀ R ≥ R₀, ∀ t, ∀ f ∈ C, ‖T_r(t) f‖ ≤ ε` (equivalent to the displayed limit of suprema).
The odd-`r` vanishing and the even-`r` eigenvalue bound are included as the other two clauses.

Proved here, on top of the frozen Part 1 (`HaarKernelTailBounds`, 66cbcbcf) and Part 2 (`HaarKernelTailPointwise`,
47cd981f), with GridStrongSum, GridBounds, GridEigen, HilbertDiagOp read-only.

Standard axioms only. No `sorry`, no custom axioms.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology Finset Metric
open QuantumNLS.HaarEigenbasis QuantumNLS.HaarSlaterBasis QuantumNLS.HaarKernelFactorizationSym
open QuantumNLS.GridEigen QuantumNLS.GridBounds QuantumNLS.HilbertDiagOp QuantumNLS.GridStrongSum
open QuantumNLS.HaarKernelTailBounds QuantumNLS.HaarKernelTailPointwise
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BethePhysicalTransfer

namespace QuantumNLS.HaarKernelTailMain

variable (L : ℝ) [Fact (0 < L)]

/-- The eigenvalue identity: `T_r(t) B_k = μ_k(t) B_k` for a strong limit `T`. -/
theorem eigen_identity (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (T : Hn L n →L[ℂ] Hn L n)
    (hT : ∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v)))
    (k : Idx (n + 1)) :
    T (physBasis L n k) = muGrid L n t k • physBasis L n k := by
  have hc : ∀ j : Idx (n + 1),
      ⟪physBasis L n j, T (physBasis L n k) - muGrid L n t k • physBasis L n k⟫_ℂ = 0 := by
    intro j
    rw [inner_sub_right, inner_smul_right, strong_coeff L n t ht T hT j (physBasis L n k)]
    by_cases hjk : j = k
    · rw [hjk]
      ring
    · rw [(physBasis L n).orthonormal.inner_eq_zero hjk]
      ring
  have hsum := parseval_hasSum (physBasis L n)
    (T (physBasis L n k) - muGrid L n t k • physBasis L n k)
  have hz : (fun j : Idx (n + 1) => ‖⟪physBasis L n j,
      T (physBasis L n k) - muGrid L n t k • physBasis L n k⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) := by
    funext j
    rw [hc j]
    simp
  rw [hz] at hsum
  have h0 := hsum.unique hasSum_zero
  have h1 : T (physBasis L n k) - muGrid L n t k • physBasis L n k = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h0)
  exact sub_eq_zero.mp h1

/-- **Strong high-label tail, compact-uniform form.** For `C` compact and `ε > 0` there is `R₀` such that
`‖T_r(t) f‖ ≤ ε` for all `f ∈ C`, all `t` with `‖t‖_∞ ≤ 1` and `t_m = 0` for `|m| ≤ R`, whenever `R ≥ R₀`. -/
theorem haar_kernel_tail_compact (n : ℕ) (T : (ℤ → ℂ) → (Hn L n →L[ℂ] Hn L n))
    (hT : ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) → ∀ v,
      Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T t v)))
    (C : Set (Hn L n)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) →
      (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) → ∀ f ∈ C, ‖T t f‖ ≤ ε := by
  have hB0 : 0 ≤ Bd L (n + 1) := Bd_nonneg L (n + 1)
  set B := Bd L (n + 1) with hBdef
  set e : ℝ := ε / (2 * (B + 1)) with he_def
  have he : 0 < e := by positivity
  obtain ⟨u, huC, hufin, hcov⟩ := finite_cover_balls_of_compact hC he
  have hev : ∀ᶠ R : ℕ in atTop, ∀ x ∈ u, ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) →
      (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) → ‖T t x‖ ≤ ε / 2 := by
    refine (Filter.eventually_all_finite hufin).2 (fun x _ => ?_)
    obtain ⟨R₀, hR₀⟩ := pointwise_tail L n T hT x (ε / 2) (by positivity)
    exact Filter.eventually_atTop.2 ⟨R₀, fun R hR => hR₀ R hR⟩
  obtain ⟨R₁, hR₁⟩ := Filter.eventually_atTop.1 hev
  refine ⟨R₁, fun R hR t ht ht0 f hf => ?_⟩
  obtain ⟨x, hxu, hfx⟩ := Set.mem_iUnion₂.1 (hcov hf)
  have hdist : ‖f - x‖ < e := by
    rw [mem_ball, dist_eq_norm] at hfx
    exact hfx
  have hTx : ‖T t x‖ ≤ ε / 2 := hR₁ R hR x hxu t ht ht0
  have hnorm : ‖T t‖ ≤ B := strong_norm_le L n t ht (T t) (hT t ht)
  have hdecomp : T t f = T t x + T t (f - x) := by
    rw [← map_add, add_sub_cancel]
  have htri : ‖T t f‖ ≤ ‖T t x‖ + ‖T t (f - x)‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have h2 : ‖T t (f - x)‖ ≤ B * ‖f - x‖ :=
    (T t).le_opNorm (f - x) |>.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  have hBe : B * ‖f - x‖ ≤ ε / 2 := by
    have h3 : B * ‖f - x‖ ≤ B * e := mul_le_mul_of_nonneg_left hdist.le hB0
    have h4 : B * e = (ε / 2) * (B / (B + 1)) := by
      rw [he_def]
      field_simp
    have h5 : B / (B + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h6 : (ε / 2) * (B / (B + 1)) ≤ ε / 2 := mul_le_of_le_one_right (by positivity) h5
    linarith
  linarith

/-- **R-3B18A493 (`QG:prop:haar-kernel-tail`), all three clauses.**
(i) odd `r` (`n` even): if all labels of `B_k` lie in `[−R,R]` and `t_m = 0` for `|m| ≤ R`, then `T_r(t) B_k = 0`;
(ii) even `r` (`n` odd): if `|k_j+1/2| ≤ M` and `R > 2M+1`, the eigenvalue `μ_k(t)` of `T_r(t)` on `B_k` satisfies
`|μ_k(t)| ≤ 2^{r+2}/(r! ω^r (r−1)) (R−1)^{1−r}` for `‖t‖_∞ ≤ 1`, `t_m = 0` for `|m| ≤ R`;
(iii) for fixed `r` and compact `C`, the uniform tail `sup_t sup_{f∈C} ‖T_r(t) f‖ → 0` in ε–N form. -/
theorem R_3B18A493 (n : ℕ) (T : (ℤ → ℂ) → (Hn L n →L[ℂ] Hn L n))
    (hT : ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) → ∀ v,
      Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T t v))) :
    (Even n → ∀ (R : ℕ) (k : Idx (n + 1)), (∀ j : Fin (n + 1), |k.1 j| ≤ (R : ℤ)) →
        ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) → (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) →
        T t (physBasis L n k) = 0) ∧
    (Odd n → ∀ (k : Idx (n + 1)) (M : ℝ), (∀ j : Fin (n + 1), |(k.1 j : ℝ) + 1 / 2| ≤ M) →
        ∀ (R : ℕ), 2 * M + 1 < (R : ℝ) → ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) →
        (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) →
        ‖muGrid L n t k‖ ≤ 2 ^ (n + 1 + 2) / (((n + 1).factorial : ℝ) * (2 * Real.pi / L) ^ (n + 1) *
          (n : ℝ)) * ((R : ℝ) - 1) ^ (1 - ((n + 1 : ℕ) : ℤ))) ∧
    (∀ (C : Set (Hn L n)), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        ∀ t : ℤ → ℂ, (∀ m, ‖t m‖ ≤ 1) → (∀ m : ℤ, |m| ≤ (R : ℤ) → t m = 0) →
        ∀ f ∈ C, ‖T t f‖ ≤ ε) := by
  refine ⟨fun hn R k hk t ht ht0 => ?_, fun hn k M hM R hR t ht ht0 => ?_, fun C hC ε hε => ?_⟩
  · exact odd_tail_vanish L n hn R k hk t ht ht0 (T t) (hT t ht)
  · exact even_tail_eigen_bound L n hn k M hM R hR t ht ht0
  · exact haar_kernel_tail_compact L n T hT C hC ε hε

end QuantumNLS.HaarKernelTailMain

#print axioms QuantumNLS.HaarKernelTailMain.eigen_identity
#print axioms QuantumNLS.HaarKernelTailMain.haar_kernel_tail_compact
#print axioms QuantumNLS.HaarKernelTailMain.R_3B18A493
