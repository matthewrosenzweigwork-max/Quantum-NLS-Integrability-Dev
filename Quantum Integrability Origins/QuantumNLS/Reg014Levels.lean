import QuantumNLS.Reg014Residual

/-! REG-014 support: uniform bounds, in terms of an upper bound for the Fourier-coordinate
norm of the field, for the finite correlation remainders of one tree level of the
accepted REG-007 expansion. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set ComplexConjugate
namespace QuantumNLS.Reg014Levels
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev QuantumNLS.CorrelationTaylor
open QuantumNLS.TerraMultiRound49IntegratedLittleO QuantumNLS.TerraMultiRound51CorrelationExpansion
open QuantumNLS.TerraMultiRound51TaylorIntegral QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound55TreeFactors QuantumNLS.TerraMultiRound56FiniteRemainder
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.Reg014Residual

variable {L : ℝ} [Fact (0 < L)]

theorem vertexField_norm {k : ℕ} (x : Ell2) (t : BinaryTree Unit)
    (i : Fin (2 * t.numNodes + 1)) : ‖vertexField (L := L) k x t i‖ = ‖x‖ := by
  unfold vertexField
  split_ifs
  · rw [TerraMultiRound59PhysicalLinear.norm_physicalToHk, norm_jEll]
  · rw [TerraMultiRound59PhysicalLinear.norm_physicalToHk]

theorem factor_norm {k : ℕ} (x : Ell2) (t : BinaryTree Unit)
    (i : Fin (2 * t.numNodes + 1 + 1)) : ‖factorField (L := L) k x t i‖ = ‖x‖ := by
  unfold factorField
  split
  · rw [TerraMultiRound59PhysicalLinear.norm_physicalToHk, norm_jEll]
  · exact vertexField_norm x t _

theorem factor_norm_le {k : ℕ} (x : Ell2) (U : ℝ) (hx : ‖x‖ ≤ U) (t : BinaryTree Unit)
    (i : Fin (2 * t.numNodes + 1 + 1)) : ‖factorField (L := L) k x t i‖ ≤ U := by
  rw [factor_norm]; exact hx

/-- The per-tree constants (chosen once and for all). -/
def Kres {k d : ℕ} (hk : 1 ≤ k) (hd : d + 1 ≤ 2 * k) (j : ℕ) : ℝ :=
  Classical.choose (residual_uniform (L := L) (n := 2 * j + 1) (m := 2 * j) hk hd)

theorem Kres_spec {k d : ℕ} (hk : 1 ≤ k) (hd : d + 1 ≤ 2 * k) (j : ℕ) :
    0 ≤ Kres (L := L) hk hd j ∧ ∀ (U : ℝ), 0 ≤ U → ∀ (f : Fin (2 * j + 2) → Hk L k),
      (∀ i, ‖f i‖ ≤ U) → ∀ (paths : Fin (2 * j + 2) → Finset (Fin (2 * j + 1))) (z : ℝ),
      ‖integratedResidual f d paths z‖ ≤ |z| ^ (d + 1) * (Kres (L := L) hk hd j * U ^ (2 * j + 2)) :=
  Classical.choose_spec (residual_uniform (L := L) (n := 2 * j + 1) (m := 2 * j) hk hd)

def Kcor {k : ℕ} (hk : 1 ≤ k) (j : ℕ) : ℝ :=
  Classical.choose (correlation_uniform (L := L) (n := 2 * j + 1) (m := 2 * j) hk)

theorem Kcor_spec {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    0 ≤ Kcor (L := L) hk j ∧ ∀ (U : ℝ), 0 ≤ U → ∀ (f : Fin (2 * j + 2) → Hk L k),
      (∀ i, ‖f i‖ ≤ U) → ∀ (paths : Fin (2 * j + 2) → Finset (Fin (2 * j + 1))) (z : ℝ),
      ‖integratedCorrelation f paths z‖ ≤ Kcor (L := L) hk j * U ^ (2 * j + 2) :=
  Classical.choose_spec (correlation_uniform (L := L) (n := 2 * j + 1) (m := 2 * j) hk)

/-- One tree's positive-degree remainder term. -/
theorem tree_positive_term {k d : ℕ} (hk : 1 ≤ k) (hd : d + 1 ≤ 2 * k) (κ : ℝ)
    (U : ℝ) (hU : 0 ≤ U) (x : Ell2) (hx : ‖x‖ ≤ U) (Y : ℝ) (hY : 0 < Y)
    (t : BinaryTree Unit) :
    ‖(-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
      (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k x t)
        (finiteFactorPaths t) Y⁻¹ -
      ∑ j ∈ Finset.range (d + 2), (Y⁻¹ ^ j) •
        integratedCoeff (Cfun (factorField (L := L) k x t)) (finiteFactorPaths t) j))‖ ≤
    |κ| ^ t.numNodes * (Kres (L := L) hk hd t.numNodes * U ^ (2 * t.numNodes + 2)) *
      Y⁻¹ ^ (2 * t.numNodes + 1 + (d + 1)) := by
  have hres := residual_eq_difference (m := 2 * t.numNodes) hk (factorField (L := L) k x t)
    (finiteFactorPaths t) d Y⁻¹
  have hb := (Kres_spec (L := L) hk hd t.numNodes).2 U hU (factorField (L := L) k x t)
    (fun i => factor_norm_le x U hx t i) (finiteFactorPaths t) Y⁻¹
  have hYi : 0 ≤ Y⁻¹ := inv_nonneg.mpr hY.le
  rw [← hres]
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_smul, norm_pow,
    Real.norm_eq_abs, abs_of_nonneg hYi]
  rw [abs_of_nonneg hYi] at hb
  have hκ : 0 ≤ |κ| ^ t.numNodes := by positivity
  have hp : 0 ≤ Y⁻¹ ^ (2 * t.numNodes + 1) := by positivity
  calc |κ| ^ t.numNodes * (Y⁻¹ ^ (2 * t.numNodes + 1) *
        ‖integratedResidual (m := 2 * t.numNodes) (factorField (L := L) k x t) d (finiteFactorPaths t) Y⁻¹‖)
      ≤ |κ| ^ t.numNodes * (Y⁻¹ ^ (2 * t.numNodes + 1) *
        (Y⁻¹ ^ (d + 1) * (Kres (L := L) hk hd t.numNodes * U ^ (2 * t.numNodes + 2)))) := by
        gcongr
    _ = _ := by rw [show 2 * t.numNodes + 1 + (d + 1) = (2 * t.numNodes + 1) + (d + 1) from rfl, pow_add]; ring

/-- One tree level of the positive-degree remainders. -/
theorem positive_level_bound {k d : ℕ} (hk : 1 ≤ k) (hd : d + 1 ≤ 2 * k) (κ : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : ℝ), 0 ≤ U → ∀ x : Ell2, ‖x‖ ≤ U → ∀ Y : ℝ, 0 < Y →
      ‖positiveRemainder (L := L) (k := k) κ x n d Y‖ ≤
        K * U ^ (2 * n + 2) * Y⁻¹ ^ (2 * n + 1 + (d + 1)) := by
  refine ⟨((BinaryTree.treesOfNumNodesEq n).card : ℝ) *
    (|κ| ^ n * Kres (L := L) hk hd n), ?_, ?_⟩
  · have := (Kres_spec (L := L) hk hd n).1
    positivity
  intro U hU x hx Y hY
  unfold positiveRemainder
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ t ∈ BinaryTree.treesOfNumNodesEq n,
      ‖(-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
      (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k x t)
        (finiteFactorPaths t) Y⁻¹ -
      ∑ j ∈ Finset.range (d + 2), (Y⁻¹ ^ j) •
        integratedCoeff (Cfun (factorField (L := L) k x t)) (finiteFactorPaths t) j))‖ ≤
      (|κ| ^ n * Kres (L := L) hk hd n) * U ^ (2 * n + 2) * Y⁻¹ ^ (2 * n + 1 + (d + 1)) := by
    intro t ht
    have ht' : t.numNodes = n := BinaryTree.mem_treesOfNumNodesEq.mp ht
    have h := tree_positive_term (L := L) hk hd κ U hU x hx Y hY t
    have e : |κ| ^ t.numNodes * (Kres (L := L) hk hd t.numNodes * U ^ (2 * t.numNodes + 2)) *
        Y⁻¹ ^ (2 * t.numNodes + 1 + (d + 1)) =
        (|κ| ^ n * Kres (L := L) hk hd n) * U ^ (2 * n + 2) * Y⁻¹ ^ (2 * n + 1 + (d + 1)) := by
      rw [ht']; ring
    exact h.trans e.le
  calc _ ≤ ∑ _t ∈ BinaryTree.treesOfNumNodesEq n,
        (|κ| ^ n * Kres (L := L) hk hd n) * U ^ (2 * n + 2) * Y⁻¹ ^ (2 * n + 1 + (d + 1)) :=
        Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- One tree's degree-zero remainder term. -/
theorem tree_leading_term {k : ℕ} (hk : 1 ≤ k) (κ : ℝ)
    (U : ℝ) (hU : 0 ≤ U) (x : Ell2) (hx : ‖x‖ ≤ U) (Y : ℝ) (hY : 0 < Y)
    (t : BinaryTree Unit) :
    ‖(-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
      (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k x t)
        (finiteFactorPaths t) Y⁻¹ - Cfun (factorField (L := L) k x t) 0))‖ ≤
    |κ| ^ t.numNodes * (Kcor (L := L) hk t.numNodes * U ^ (2 * t.numNodes + 2) +
      L * Fourier.cL L ^ (2 * t.numNodes + 2) * U ^ (2 * t.numNodes + 2)) *
      Y⁻¹ ^ (2 * t.numNodes + 1) := by
  have hb := (Kcor_spec (L := L) hk t.numNodes).2 U hU (factorField (L := L) k x t)
    (fun i => factor_norm_le x U hx t i) (finiteFactorPaths t) Y⁻¹
  have hc : ‖Cfun (factorField (L := L) k x t) 0‖ ≤
      L * Fourier.cL L ^ (2 * t.numNodes + 2) * U ^ (2 * t.numNodes + 2) := by
    refine (norm_Cfun_le hk (factorField (L := L) k x t) _).trans ?_
    have hP := prod_norm_le (factorField (L := L) k x t) U (fun i => factor_norm_le x U hx t i)
    have hL : 0 < L := Fact.out
    have hcL : 0 ≤ Fourier.cL L := Real.sqrt_nonneg _
    exact mul_le_mul_of_nonneg_left hP (by positivity)
  have hYi : 0 ≤ Y⁻¹ := inv_nonneg.mpr hY.le
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_smul, norm_pow,
    Real.norm_eq_abs, abs_of_nonneg hYi]
  have hsub := norm_sub_le (integratedCorrelation (m := 2 * t.numNodes)
    (factorField (L := L) k x t) (finiteFactorPaths t) Y⁻¹) (Cfun (factorField (L := L) k x t) 0)
  have hp : 0 ≤ Y⁻¹ ^ (2 * t.numNodes + 1) := by positivity
  have hκ : 0 ≤ |κ| ^ t.numNodes := by positivity
  calc |κ| ^ t.numNodes * (Y⁻¹ ^ (2 * t.numNodes + 1) *
      ‖integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k x t)
        (finiteFactorPaths t) Y⁻¹ - Cfun (factorField (L := L) k x t) 0‖)
      ≤ |κ| ^ t.numNodes * (Y⁻¹ ^ (2 * t.numNodes + 1) *
        (Kcor (L := L) hk t.numNodes * U ^ (2 * t.numNodes + 2) +
          L * Fourier.cL L ^ (2 * t.numNodes + 2) * U ^ (2 * t.numNodes + 2))) := by
        gcongr
        exact hsub.trans (add_le_add hb hc)
    _ = _ := by ring

/-- One tree level of the degree-zero remainders. -/
theorem leading_level_bound {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : ℝ), 0 ≤ U → ∀ x : Ell2, ‖x‖ ≤ U → ∀ Y : ℝ, 0 < Y →
      ‖leadingRemainder (L := L) (k := k) κ x n Y‖ ≤
        K * U ^ (2 * n + 2) * Y⁻¹ ^ (2 * n + 1) := by
  have hL : 0 < L := Fact.out
  have hcL : 0 ≤ Fourier.cL L := Real.sqrt_nonneg _
  have hK := (Kcor_spec (L := L) hk n).1
  refine ⟨((BinaryTree.treesOfNumNodesEq n).card : ℝ) *
    (|κ| ^ n * (Kcor (L := L) hk n + L * Fourier.cL L ^ (2 * n + 2))), by positivity, ?_⟩
  intro U hU x hx Y hY
  unfold leadingRemainder
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ t ∈ BinaryTree.treesOfNumNodesEq n,
      ‖(-(κ : ℂ)) ^ t.numNodes * ((Y⁻¹ ^ (2 * t.numNodes + 1)) •
      (integratedCorrelation (m := 2 * t.numNodes) (factorField (L := L) k x t)
        (finiteFactorPaths t) Y⁻¹ - Cfun (factorField (L := L) k x t) 0))‖ ≤
      (|κ| ^ n * (Kcor (L := L) hk n + L * Fourier.cL L ^ (2 * n + 2))) * U ^ (2 * n + 2) *
        Y⁻¹ ^ (2 * n + 1) := by
    intro t ht
    have ht' : t.numNodes = n := BinaryTree.mem_treesOfNumNodesEq.mp ht
    have h := tree_leading_term (L := L) hk κ U hU x hx Y hY t
    have e : |κ| ^ t.numNodes * (Kcor (L := L) hk t.numNodes * U ^ (2 * t.numNodes + 2) +
        L * Fourier.cL L ^ (2 * t.numNodes + 2) * U ^ (2 * t.numNodes + 2)) *
        Y⁻¹ ^ (2 * t.numNodes + 1) =
        (|κ| ^ n * (Kcor (L := L) hk n + L * Fourier.cL L ^ (2 * n + 2))) * U ^ (2 * n + 2) *
        Y⁻¹ ^ (2 * n + 1) := by
      rw [ht']; ring
    exact h.trans e.le
  calc _ ≤ ∑ _t ∈ BinaryTree.treesOfNumNodesEq n,
        (|κ| ^ n * (Kcor (L := L) hk n + L * Fourier.cL L ^ (2 * n + 2))) * U ^ (2 * n + 2) *
          Y⁻¹ ^ (2 * n + 1) := Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

#print axioms positive_level_bound
#print axioms leading_level_bound
end QuantumNLS.Reg014Levels
