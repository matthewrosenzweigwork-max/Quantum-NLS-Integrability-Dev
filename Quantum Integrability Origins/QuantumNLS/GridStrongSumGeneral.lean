import QuantumNLS.GridStrongSum

/-!
# R-E67FE3C4 general statement: bounded weights and every increasing finite exhaustion

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:365-420` (`QG:prop:haar-grid-weights`), statement
clause by clause:
1. For every bounded `t = (t_n)`, the symmetric partial sums of `Σ_n t_n K_{r,ω n}` converge strongly to a bounded
   operator `T_r(t)`, and `‖T_r(t)‖ ≤ (2π²/(3 r!)) (L/π)^r ‖t‖_∞` (`bounded_strong_limit`, with `‖t‖_∞ = ⨆ m ‖t m‖`).
   `T_r(t)` is the unique strong limit of the symmetric partial sums.
2. The same limit is obtained along every increasing finite exhaustion of `ℤ` (`exhaustion` clause).
3. For fixed `κ > 0`, `a ≥ 0`, `m ∈ ℕ`: `Σ_r r^m e^{ar} κ^{r-1} ‖T_r(t)‖ < ∞`, uniformly over `‖t‖_∞ ≤ 1`
   (frozen `GridStrongSum.R_E67FE3C4_strong_sum`, imported read-only).

Method: the coefficient-level dominated convergence of `GridStrongSum.strong_exists`, applied to an arbitrary
exhaustion; bounded `t` reduced to `‖u‖_∞ ≤ 1` by scaling with `M = ‖t‖_∞`.

Standard axioms only. No `sorry`, no custom axioms.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology Finset
open QuantumNLS.HaarEigenbasis QuantumNLS.HaarSlaterBasis QuantumNLS.HaarKernelFactorizationSym
open QuantumNLS.GridEigen QuantumNLS.GridBounds QuantumNLS.HilbertDiagOp QuantumNLS.GridStrongSum
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BethePhysicalTransfer

namespace QuantumNLS.GridStrongSumGeneral

variable (L : ℝ) [Fact (0 < L)]

/-- Partial sums of `Σ_m t_m K_{r,ω m}` along a finite exhaustion `F`. -/
def exSum (n : ℕ) (t : ℤ → ℂ) (F : ℕ → Finset ℤ) (N : ℕ) (v : Hn L n) : Hn L n :=
  ∑ m ∈ F N, t m • physicalKernel L (n + 1) (gridPt L m) v

/-- Coefficient partial sums `Σ_{m∈F N} t_m Λ̃_k(ω m)`. -/
def exCoef (n : ℕ) (t : ℤ → ℂ) (F : ℕ → Finset ℤ) (N : ℕ) (k : Idx (n + 1)) : ℂ :=
  ∑ m ∈ F N, t m * lamTilde L n k (gridPt L m)

/-- The symmetric exhaustion `N ↦ Icc (−N) N`. -/
def symF : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem symF_mono : ∀ N, symF N ⊆ symF (N + 1) := by
  intro N m hm
  simp only [symF, Finset.mem_Icc] at hm ⊢
  push_cast
  omega

theorem symF_cov : ∀ m : ℤ, ∃ N, m ∈ symF N := by
  intro m
  refine ⟨m.natAbs, ?_⟩
  simp only [symF, Finset.mem_Icc]
  rcases Int.natAbs_eq m with h | h <;> omega

/-- An increasing finite exhaustion tends to `atTop` in `Finset ℤ`. -/
theorem tendsto_of_exhaust (F : ℕ → Finset ℤ) (hmono : ∀ N, F N ⊆ F (N + 1))
    (hcov : ∀ m : ℤ, ∃ N, m ∈ F N) : Tendsto F atTop atTop := by
  have hmon : Monotone F := monotone_nat_of_le_succ hmono
  choose g hg using hcov
  refine Filter.tendsto_atTop_atTop.2 (fun s => ⟨s.sup g, fun N hN => ?_⟩)
  refine Finset.le_iff_subset.2 (fun m hm => ?_)
  have h1 : g m ≤ s.sup g := Finset.le_sup (f := g) hm
  exact (Finset.le_iff_subset.1 (hmon (le_trans h1 hN))) (hg m)

/-- Finite sums of a summable family along an exhaustion converge to its sum. -/
theorem tendsto_exh_sum (f : ℤ → ℂ) (hf : Summable f) (F : ℕ → Finset ℤ)
    (hF : Tendsto F atTop atTop) :
    Tendsto (fun N => ∑ m ∈ F N, f m) atTop (𝓝 (∑' m, f m)) := by
  have hS : Tendsto (fun s : Finset ℤ => ∑ m ∈ s, f m) atTop (𝓝 (∑' m, f m)) := hf.hasSum
  exact Filter.Tendsto.comp (g := fun s : Finset ℤ => ∑ m ∈ s, f m) hS hF

/-- Scaling of a partial sum: `exSum (c·u) = c • exSum u`. -/
theorem exSum_mul (n : ℕ) (c : ℂ) (t u : ℤ → ℂ) (h : ∀ m, t m = c * u m)
    (F : ℕ → Finset ℤ) (N : ℕ) (v : Hn L n) :
    exSum L n t F N v = c • exSum L n u F N v := by
  unfold exSum
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [h m, mul_smul]

/-- Strong convergence from coefficient-level convergence and a uniform coefficient bound
(dominated convergence in the square-summable basis coefficients). -/
theorem strong_of_coeff (n : ℕ) (u : ℤ → ℂ) (hu : ∀ m, ‖u m‖ ≤ 1) (T : Hn L n →L[ℂ] Hn L n)
    (hTcoef : ∀ (k : Idx (n + 1)) (v : Hn L n),
      ⟪physBasis L n k, T v⟫_ℂ = muGrid L n u k * ⟪physBasis L n k, v⟫_ℂ)
    (S : ℕ → Hn L n → Hn L n) (G : ℕ → Idx (n + 1) → ℂ)
    (hS : ∀ (N : ℕ) (v : Hn L n) (k : Idx (n + 1)),
      ⟪physBasis L n k, S N v⟫_ℂ = G N k * ⟪physBasis L n k, v⟫_ℂ)
    (hG : ∀ k : Idx (n + 1), Tendsto (fun N => G N k) atTop (𝓝 (muGrid L n u k)))
    (hGb : ∀ (N : ℕ) (k : Idx (n + 1)), ‖G N k‖ ≤ Bd L (n + 1)) :
    ∀ v, Tendsto (fun N => S N v) atTop (𝓝 (T v)) := by
  intro v
  refine tendsto_of_norm_sq_tendsto _ _ ?_
  have hw : ∀ N : ℕ, ‖S N v - T v‖ ^ 2 =
      ∑' k, ‖(G N k - muGrid L n u k) * ⟪physBasis L n k, v⟫_ℂ‖ ^ 2 := by
    intro N
    rw [← (parseval_hasSum (physBasis L n) (S N v - T v)).tsum_eq]
    refine tsum_congr (fun k => ?_)
    rw [inner_sub_right, hS, hTcoef, ← sub_mul]
  have hab : ∀ k : Idx (n + 1), Tendsto
      (fun N : ℕ => ‖(G N k - muGrid L n u k) * ⟪physBasis L n k, v⟫_ℂ‖ ^ 2) atTop (𝓝 0) := by
    intro k
    have h0 : Tendsto (fun N : ℕ => G N k - muGrid L n u k) atTop (𝓝 0) := by
      have := (hG k).sub_const (muGrid L n u k)
      rwa [sub_self] at this
    have h1 := ((h0.mul_const (⟪physBasis L n k, v⟫_ℂ)).norm).pow 2
    rwa [zero_mul, norm_zero, zero_pow two_ne_zero] at h1
  have hbd : ∀ᶠ N : ℕ in atTop, ∀ k : Idx (n + 1),
      ‖‖(G N k - muGrid L n u k) * ⟪physBasis L n k, v⟫_ℂ‖ ^ 2‖ ≤
        (2 * Bd L (n + 1)) ^ 2 * ‖⟪physBasis L n k, v⟫_ℂ‖ ^ 2 := by
    refine Filter.Eventually.of_forall (fun N k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply sq_norm_mul_le
    refine (norm_sub_le _ _).trans ?_
    linarith [hGb N k, norm_muGrid_le L n u hu k]
  have hsumB : Summable (fun k : Idx (n + 1) =>
      (2 * Bd L (n + 1)) ^ 2 * ‖⟪physBasis L n k, v⟫_ℂ‖ ^ 2) :=
    (parseval_hasSum (physBasis L n) v).summable.mul_left _
  have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N : ℕ) (k : Idx (n + 1)) =>
      ‖(G N k - muGrid L n u k) * ⟪physBasis L n k, v⟫_ℂ‖ ^ 2)
    (g := fun _ => (0 : ℝ)) (bound := fun k : Idx (n + 1) =>
      (2 * Bd L (n + 1)) ^ 2 * ‖⟪physBasis L n k, v⟫_ℂ‖ ^ 2) hsumB hab hbd
  rw [tsum_zero] at hdom
  exact hdom.congr (fun N => (hw N).symm)

/-- Strong convergence of the exhaustion partial sums of `Σ_m u_m K_{r,ω m}` (`‖u‖_∞ ≤ 1`) to the strong
limit `T` of the symmetric partial sums. -/
theorem exhaust_strong (n : ℕ) (u : ℤ → ℂ) (hu : ∀ m, ‖u m‖ ≤ 1) (F : ℕ → Finset ℤ)
    (hF : Tendsto F atTop atTop) (T : Hn L n →L[ℂ] Hn L n)
    (hTcoef : ∀ (k : Idx (n + 1)) (v : Hn L n),
      ⟪physBasis L n k, T v⟫_ℂ = muGrid L n u k * ⟪physBasis L n k, v⟫_ℂ) :
    ∀ v, Tendsto (fun N => exSum L n u F N v) atTop (𝓝 (T v)) := by
  refine strong_of_coeff L n u hu T hTcoef (fun N v => exSum L n u F N v)
    (fun N k => exCoef L n u F N k) ?_ ?_ ?_
  · intro N v k
    dsimp only [exSum, exCoef]
    rw [inner_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hc : ⟪physBasis L n k, physicalKernel L (n + 1) (gridPt L m) v⟫_ℂ =
        lamTilde L n k (gridPt L m) * ⟪physBasis L n k, v⟫_ℂ :=
      eig_coeff (physBasis L n) (physicalKernel L (n + 1) (gridPt L m))
        (fun k' => lamTilde L n k' (gridPt L m)) (fun i => eigen_all L n (gridPt L m) i) k v
    rw [inner_smul_right, hc]
    ring
  · intro k
    exact tendsto_exh_sum _ (summable_mul_grid L n u hu k) F hF
  · intro N k
    unfold exCoef
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_hasSum _ (fun m _ => norm_nonneg _)
      (summable_norm_mul_grid L n u hu k).hasSum).trans ?_
    exact (Summable.tsum_le_tsum (norm_mul_grid_le L n u hu k)
      (summable_norm_mul_grid L n u hu k) (grid_bound L n k).1).trans (grid_bound L n k).2

/-- Core statement for `‖u‖_∞ ≤ 1`: the symmetric strong limit `T`, its bound, and the strong limit along every
exhaustion with the same `T`. -/
theorem core_u (n : ℕ) (u : ℤ → ℂ) (hu : ∀ m, ‖u m‖ ≤ 1) :
    ∃ T : Hn L n →L[ℂ] Hn L n,
      (∀ v, Tendsto (fun N => exSum L n u symF N v) atTop (𝓝 (T v))) ∧ ‖T‖ ≤ Bd L (n + 1) ∧
      (∀ F : ℕ → Finset ℤ, Tendsto F atTop atTop →
        ∀ v, Tendsto (fun N => exSum L n u F N v) atTop (𝓝 (T v))) := by
  obtain ⟨T, hTsym, hTn, hTcoef⟩ := strong_exists L n u hu
  exact ⟨T, hTsym, hTn, fun F hF v => exhaust_strong L n u hu F hF T hTcoef v⟩

/-- **Clauses 1 and 2 of `QG:prop:haar-grid-weights`, for every bounded `t`.** -/
theorem bounded_strong_limit (n : ℕ) (t : ℤ → ℂ) (hb : BddAbove (Set.range fun m => ‖t m‖)) :
    ∃ T : Hn L n →L[ℂ] Hn L n,
      (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v))) ∧
      ‖T‖ ≤ Bd L (n + 1) * ⨆ m, ‖t m‖ ∧
      (∀ T' : Hn L n →L[ℂ] Hn L n,
        (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T' v))) → T' = T) ∧
      (∀ F : ℕ → Finset ℤ, (∀ N, F N ⊆ F (N + 1)) → (∀ m : ℤ, ∃ N, m ∈ F N) →
        ∀ v, Tendsto (fun N => ∑ m ∈ F N, t m • physicalKernel L (n + 1) (gridPt L m) v)
          atTop (𝓝 (T v))) := by
  set M : ℝ := ⨆ m, ‖t m‖ with hMdef
  have hM : ∀ m, ‖t m‖ ≤ M := fun m => le_ciSup hb m
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  set u : ℤ → ℂ := fun m => (M : ℂ)⁻¹ * t m with hudef
  have ht_eq : ∀ m, t m = (M : ℂ) * u m := by
    intro m
    by_cases h0 : M = 0
    · have htm : t m = 0 := norm_le_zero_iff.mp (by have := hM m; rw [h0] at this; exact this)
      simp [hudef, h0, htm]
    · have hMc : (M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0
      simp only [hudef]
      rw [← mul_assoc, mul_inv_cancel₀ hMc, one_mul]
  have hu : ∀ m, ‖u m‖ ≤ 1 := by
    intro m
    by_cases h0 : M = 0
    · have htm : t m = 0 := norm_le_zero_iff.mp (by have := hM m; rw [h0] at this; exact this)
      simp [hudef, htm]
    · have hpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm h0)
      rw [hudef]
      simp only
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM0,
        inv_mul_le_iff₀ hpos]
      linarith [hM m]
  obtain ⟨Tu, hTusym, hTun, hTuexh⟩ := core_u L n u hu
  have hTt : ∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (((M : ℂ) • Tu) v)) := by
    intro v
    have hc := (hTusym v).const_smul (M : ℂ)
    refine hc.congr (fun N => ?_)
    exact (exSum_mul L n (M : ℂ) t u ht_eq symF N v).symm
  refine ⟨(M : ℂ) • Tu, hTt, ?_, ?_, ?_⟩
  · calc ‖(M : ℂ) • Tu‖ ≤ ‖(M : ℂ)‖ * ‖Tu‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = M * ‖Tu‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hM0]
      _ ≤ M * Bd L (n + 1) := mul_le_mul_of_nonneg_left hTun hM0
      _ = Bd L (n + 1) * M := mul_comm _ _
  · intro T' hT'
    exact ContinuousLinearMap.ext (fun v => tendsto_nhds_unique (hT' v) (hTt v))
  · intro F hmono hcov v
    have hF := tendsto_of_exhaust F hmono hcov
    have hc := (hTuexh F hF v)
    have hc' := hc.const_smul (M : ℂ)
    refine hc'.congr (fun N => ?_)
    exact (exSum_mul L n (M : ℂ) t u ht_eq F N v).symm

/-- **Clause 3 of `QG:prop:haar-grid-weights`** (frozen `R_E67FE3C4_strong_sum`, `κ > 0`, `a ≥ 0`): the uniform
summability `Σ_r r^m e^{ar} κ^{r-1} ‖T_r(t)‖ < ∞` over `‖t‖_∞ ≤ 1`, in the frozen form. -/
theorem summability_clause (m : ℕ) (a κ : ℝ) (hκ : 0 < κ) (ha : 0 ≤ a) :
    ∃ S0 : ℝ, ∀ (t : ℤ → ℂ), (∀ j, ‖t j‖ ≤ 1) →
      ∀ T : (n : ℕ) → Hn L n →L[ℂ] Hn L n,
        (∀ n v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T n v))) →
        Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖) ∧
        ∑' n : ℕ, ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖ ≤ S0 :=
  (R_E67FE3C4_strong_sum L).2 m a κ hκ.le

/-- **R-E67FE3C4, full statement of `QG:prop:haar-grid-weights`.**
(1)–(2) for every bounded `t`: strong convergence of the symmetric partial sums to a bounded `T_r(t)` with
`‖T_r(t)‖ ≤ B_r(L) ‖t‖_∞`, the unique strong limit, and the same limit along every increasing finite
exhaustion; (3) the uniform summability for `κ > 0`, `a ≥ 0`, `m ∈ ℕ`. -/
theorem R_E67FE3C4_general :
    (∀ (n : ℕ) (t : ℤ → ℂ), BddAbove (Set.range fun m => ‖t m‖) →
      ∃ T : Hn L n →L[ℂ] Hn L n,
        (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v))) ∧
        ‖T‖ ≤ Bd L (n + 1) * ⨆ m, ‖t m‖ ∧
        (∀ T' : Hn L n →L[ℂ] Hn L n,
          (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T' v))) → T' = T) ∧
        (∀ F : ℕ → Finset ℤ, (∀ N, F N ⊆ F (N + 1)) → (∀ m : ℤ, ∃ N, m ∈ F N) →
          ∀ v, Tendsto (fun N => ∑ m ∈ F N, t m • physicalKernel L (n + 1) (gridPt L m) v)
            atTop (𝓝 (T v)))) ∧
    (∀ (m : ℕ) (a κ : ℝ), 0 < κ → 0 ≤ a → ∃ S0 : ℝ, ∀ (t : ℤ → ℂ), (∀ j, ‖t j‖ ≤ 1) →
      ∀ T : (n : ℕ) → Hn L n →L[ℂ] Hn L n,
        (∀ n v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T n v))) →
        Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖) ∧
        ∑' n : ℕ, ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖ ≤ S0) :=
  ⟨fun n t hb => bounded_strong_limit L n t hb, fun m a κ hκ ha => summability_clause L m a κ hκ ha⟩

end QuantumNLS.GridStrongSumGeneral

#print axioms QuantumNLS.GridStrongSumGeneral.bounded_strong_limit
#print axioms QuantumNLS.GridStrongSumGeneral.R_E67FE3C4_general
