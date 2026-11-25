import Mathlib
import QuantumNLS.GridEigen
import QuantumNLS.GridBounds
import QuantumNLS.HilbertDiagOp

/-!
# R-E67FE3C4 item 2: strong sums `Σ_m t_m K_{r,ω m}` diagonal in the physical basis

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:365-420` (`QG:prop:haar-grid-weights`).

Realized objects used read-only: `physBasis` (Hilbert basis of `Sym^r L²`), `lamTilde` / `eigen_all`
(eigenbasis of `K_{r,z}`), the grid closed forms `lamTilde_grid_even`, `lamTilde_grid_odd_zero`,
`lamTilde_grid_odd_pole` (GridEigen, item 1), the sums `even_grid_sum`, `residue_sum_le` (GridBounds,
item 3), and the generic diagonal-operator lemmas (HilbertDiagOp).

Proved here:
* `grid_bound`: `Σ_m |Λ̃_k(ω m)| ≤ B_r(L) := (2π²/(3 r!)) (L/π)^r` uniformly in `k` (both parities);
* `strong_exists`: for `|t_m| ≤ 1`, the symmetric partial sums `Σ_{|m|≤N} t_m K_{r,ω m}` converge strongly to
  the operator `T` diagonal in `physBasis` with entries `μ_k(t) = Σ_m t_m Λ̃_k(ω m)`, and `‖T‖ ≤ B_r(L)`;
* `strong_norm_le`: every strong limit of the partial sums has norm at most `B_r(L)`;
* `R_E67FE3C4_strong_sum`: the combined statement, including summability of
  `Σ_r r^m e^{ar} κ^{r-1} ‖T_r(t)‖` with a bound independent of `t`.

Standard axioms only. No `sorry`, no custom axioms.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate
open Filter Topology Finset
open QuantumNLS.HaarEigenbasis QuantumNLS.HaarSlaterBasis QuantumNLS.HaarKernelFactorizationSym
open QuantumNLS.GridEigen QuantumNLS.GridBounds QuantumNLS.HilbertDiagOp
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BethePhysicalTransfer

namespace QuantumNLS.GridStrongSum

variable (L : ℝ) [Fact (0 < L)]

/-- The physical sector `Sym^r L²` with `r = n + 1`. -/
abbrev Hn (n : ℕ) : Type := SymSector ℂ (L2T L) (n + 1)

/-- The printed grid-sum constant `B_r(L) = (2π²/(3 r!)) (L/π)^r`. -/
def Bd (r : ℕ) : ℝ := 2 * Real.pi ^ 2 / (3 * (r.factorial : ℝ)) * (L / Real.pi) ^ r

theorem Bd_nonneg (r : ℕ) : 0 ≤ Bd L r := by
  have hL : (0 : ℝ) < L := Fact.out
  unfold Bd
  apply mul_nonneg
  · positivity
  · exact pow_nonneg (div_nonneg hL.le Real.pi_pos.le) r

/-- `‖x c‖² ≤ M² ‖c‖²` whenever `‖x‖ ≤ M`. -/
theorem sq_norm_mul_le (x c : ℂ) {M : ℝ} (hx : ‖x‖ ≤ M) : ‖x * c‖ ^ 2 ≤ M ^ 2 * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hx 2) (sq_nonneg _)

theorem norm_shift_factor (m a : ℤ) :
    ‖(1 : ℂ) / ((m : ℂ) - (a : ℂ) - 1 / 2)‖ = |(m : ℝ) - ((a : ℝ) + 1 / 2)|⁻¹ := by
  have e : (m : ℂ) - (a : ℂ) - 1 / 2 = (((m : ℝ) - ((a : ℝ) + 1 / 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, one_div]

theorem norm_int_diff_factor (a b : ℤ) :
    ‖(1 : ℂ) / ((a : ℂ) - (b : ℂ))‖ = |(a : ℝ) - (b : ℝ)|⁻¹ := by
  have e : (a : ℂ) - (b : ℂ) = (((a : ℝ) - (b : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, one_div]

theorem norm_omega_cast : ‖(omegaL L : ℂ)‖ = 2 * Real.pi / L := by
  have hω := omegaL_pos L
  rw [Complex.norm_real, Real.norm_of_nonneg hω.le]
  rfl

theorem norm_L_cast : ‖(L : ℂ)‖ = L := by
  have hL : (0 : ℝ) < L := Fact.out
  rw [Complex.norm_real, Real.norm_of_nonneg hL.le]

/-- Even `r = n+1`: the modulus of the grid eigenvalue. -/
theorem lam_norm_even {n : ℕ} (hn : Odd n) (k : Idx (n + 1)) (m : ℤ) :
    ‖lamTilde L n k (gridPt L m)‖ =
      2 / ((((n + 1).factorial : ℕ) : ℝ) * (2 * Real.pi / L) ^ (n + 1)) *
        ∏ i, |(m : ℝ) - ((k.1 i : ℝ) + 1 / 2)|⁻¹ := by
  have hprod : ‖∏ i, (1 : ℂ) / ((m : ℂ) - (k.1 i : ℂ) - 1 / 2)‖ =
      ∏ i, |(m : ℝ) - ((k.1 i : ℝ) + 1 / 2)|⁻¹ := by
    rw [norm_prod]
    exact Finset.prod_congr rfl (fun i _ => norm_shift_factor m (k.1 i))
  rw [lamTilde_grid_even L hn k m, norm_mul, hprod]
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_I, one_pow, Complex.norm_natCast,
    norm_omega_cast L, mul_one]
  try norm_num

/-- Odd `r = n+1`, at a pole `m = k_j`: the modulus of the grid eigenvalue. -/
theorem lam_norm_odd_pole {n : ℕ} (hn : Even n) (k : Idx (n + 1)) (j : Fin (n + 1)) :
    ‖lamTilde L n k (gridPt L (k.1 j))‖ =
      L / ((((n + 1).factorial : ℕ) : ℝ) * (2 * Real.pi / L) ^ n) *
        ∏ i ∈ Finset.univ.erase j, |((k.1 j : ℤ) : ℝ) - ((k.1 i : ℤ) : ℝ)|⁻¹ := by
  have hprod : ‖∏ i ∈ Finset.univ.erase j, (1 : ℂ) / ((k.1 j : ℂ) - (k.1 i : ℂ))‖ =
      ∏ i ∈ Finset.univ.erase j, |((k.1 j : ℤ) : ℝ) - ((k.1 i : ℤ) : ℝ)|⁻¹ := by
    rw [norm_prod]
    exact Finset.prod_congr rfl (fun i _ => norm_int_diff_factor (k.1 j) (k.1 i))
  rw [lamTilde_grid_odd_pole L hn k (k.1 j) j rfl, norm_mul, hprod]
  simp only [norm_div, norm_neg, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul,
    Complex.norm_natCast, norm_omega_cast L, norm_L_cast L]
  try norm_num

/-- Algebra for the odd case: `L/(F ω^n) · 2^n/n! ≤ B_{n+1}` with `F = (n+1)!`, `ω = 2π/L`. -/
theorem odd_const_le (n : ℕ) :
    L / ((((n + 1).factorial : ℕ) : ℝ) * (2 * Real.pi / L) ^ n) *
        (2 ^ n / ((n.factorial : ℕ) : ℝ)) ≤ Bd L (n + 1) := by
  have hL : (0 : ℝ) < L := Fact.out
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hF : (0 : ℝ) < (((n + 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hF0 : (((n + 1).factorial : ℕ) : ℝ) ≠ 0 := hF.ne'
  have hG : (1 : ℝ) ≤ ((n.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hG0 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hpow : (2 : ℝ) ^ n / (2 * Real.pi / L) ^ n = (L / Real.pi) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
  have key : L / ((((n + 1).factorial : ℕ) : ℝ) * (2 * Real.pi / L) ^ n) *
      (2 ^ n / ((n.factorial : ℕ) : ℝ)) =
      (L / Real.pi) ^ n * (L / ((((n + 1).factorial : ℕ) : ℝ) * ((n.factorial : ℕ) : ℝ))) := by
    rw [← hpow]
    field_simp
  have hBd : Bd L (n + 1) = (L / Real.pi) ^ n *
      (2 * Real.pi ^ 2 / (3 * (((n + 1).factorial : ℕ) : ℝ)) * (L / Real.pi)) := by
    unfold Bd
    rw [pow_succ]
    ring
  rw [key, hBd]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (div_nonneg hL.le hπ.le) n)
  have hdiv : L / ((((n + 1).factorial : ℕ) : ℝ) * ((n.factorial : ℕ) : ℝ)) ≤
      L / (((n + 1).factorial : ℕ) : ℝ) :=
    div_le_div_of_nonneg_left hL.le hF (le_mul_of_one_le_right hF.le hG)
  have h3 : L / (((n + 1).factorial : ℕ) : ℝ) ≤
      2 * Real.pi ^ 2 / (3 * (((n + 1).factorial : ℕ) : ℝ)) * (L / Real.pi) := by
    have e : 2 * Real.pi ^ 2 / (3 * (((n + 1).factorial : ℕ) : ℝ)) * (L / Real.pi) =
        (L / (((n + 1).factorial : ℕ) : ℝ)) * (2 * Real.pi / 3) := by
      field_simp <;> ring
    rw [e]
    exact le_mul_of_one_le_right (div_nonneg hL.le hF.le) (by linarith [Real.pi_gt_three])
  exact hdiv.trans h3

/-- Even-`r` constant identity: `2/(F ω^r) · (π²/3) 2^r = B_r(L)`. -/
theorem even_const_eq (n : ℕ) :
    2 / ((((n + 1).factorial : ℕ) : ℝ) * (2 * Real.pi / L) ^ (n + 1)) *
        ((Real.pi ^ 2 / 3) * 2 ^ (n + 1)) = Bd L (n + 1) := by
  have hL : (0 : ℝ) < L := Fact.out
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hF : (0 : ℝ) < (((n + 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hF0 : (((n + 1).factorial : ℕ) : ℝ) ≠ 0 := hF.ne'
  have hx0 : (2 * Real.pi / L) ^ (n + 1) ≠ 0 :=
    pow_ne_zero _ (div_ne_zero (mul_ne_zero two_ne_zero hπ0) hL0)
  have hLπ : (L / Real.pi) ^ (n + 1) = (2 : ℝ) ^ (n + 1) / (2 * Real.pi / L) ^ (n + 1) := by
    rw [← div_pow]
    congr 1
    field_simp <;> ring
  unfold Bd
  rw [hLπ]
  field_simp <;> ring

/-- **Uniform ℓ¹ bound on grid eigenvalues**, for every `k`, both parities of `r = n+1`. -/
theorem grid_bound (n : ℕ) (k : Idx (n + 1)) :
    Summable (fun m : ℤ => ‖lamTilde L n k (gridPt L m)‖) ∧
      ∑' m : ℤ, ‖lamTilde L n k (gridPt L m)‖ ≤ Bd L (n + 1) := by
  have hL : (0 : ℝ) < L := Fact.out
  rcases Nat.even_or_odd n with hn | hn
  · -- `n` even, `r = n+1` odd: only the grid points `m = k_j` contribute
    have hzero : ∀ m ∉ Finset.univ.image k.1, ‖lamTilde L n k (gridPt L m)‖ = 0 := by
      intro m hm
      rw [lamTilde_grid_odd_zero L hn k m ?_, norm_zero]
      intro i hi
      exact hm (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)
    refine ⟨summable_of_ne_finset_zero hzero, ?_⟩
    rw [tsum_eq_sum hzero, Finset.sum_image k.2.injective.injOn]
    rw [Finset.sum_congr rfl (fun j _ => lam_norm_odd_pole L hn k j), ← Finset.mul_sum]
    have hres := residue_sum_le (r := n + 1) (by omega) k.1 k.2
    simp only [Nat.add_sub_cancel] at hres
    have hc0 : (0 : ℝ) ≤ L / ((((n + 1).factorial : ℕ) : ℝ) * (2 * Real.pi / L) ^ n) :=
      div_nonneg hL.le (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg (by positivity) hL.le) _))
    exact (mul_le_mul_of_nonneg_left hres hc0).trans (odd_const_le L n)
  · -- `n` odd, `r = n+1` even: the printed product formula, summed via `even_grid_sum`
    have hr2 : 2 ≤ n + 1 := by
      obtain ⟨j, rfl⟩ := hn
      omega
    have hfun : (fun m : ℤ => ‖lamTilde L n k (gridPt L m)‖) = fun m : ℤ =>
        2 / ((((n + 1).factorial : ℕ) : ℝ) * (2 * Real.pi / L) ^ (n + 1)) *
          ∏ i, |(m : ℝ) - ((k.1 i : ℝ) + 1 / 2)|⁻¹ :=
      funext (fun m => lam_norm_even L hn k m)
    obtain ⟨hs, hsum⟩ := even_grid_sum hr2 k.1
    have hc0 : (0 : ℝ) ≤ 2 / ((((n + 1).factorial : ℕ) : ℝ) * (2 * Real.pi / L) ^ (n + 1)) :=
      div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (div_nonneg (by positivity) hL.le) _))
    rw [hfun]
    refine ⟨hs.mul_left _, ?_⟩
    rw [tsum_mul_left]
    calc _ ≤ 2 / ((((n + 1).factorial : ℕ) : ℝ) * (2 * Real.pi / L) ^ (n + 1)) *
            ((Real.pi ^ 2 / 3) * 2 ^ (n + 1)) := mul_le_mul_of_nonneg_left hsum hc0
      _ = Bd L (n + 1) := even_const_eq L n

/-- The grid-point coefficient `Λ̃_k(ω m)` times a bounded `t_m` is dominated by `‖Λ̃_k(ω m)‖`. -/
theorem norm_mul_grid_le (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (k : Idx (n + 1)) (m : ℤ) :
    ‖t m * lamTilde L n k (gridPt L m)‖ ≤ ‖lamTilde L n k (gridPt L m)‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ht m)

theorem summable_norm_mul_grid (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (k : Idx (n + 1)) :
    Summable (fun m : ℤ => ‖t m * lamTilde L n k (gridPt L m)‖) :=
  Summable.of_nonneg_of_le (fun m => norm_nonneg _) (norm_mul_grid_le L n t ht k)
    (grid_bound L n k).1

theorem summable_mul_grid (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (k : Idx (n + 1)) :
    Summable (fun m : ℤ => t m * lamTilde L n k (gridPt L m)) :=
  Summable.of_norm_bounded (grid_bound L n k).1 (norm_mul_grid_le L n t ht k)

/-- The symmetric partial coefficient `Σ_{|m|≤N} t_m Λ̃_k(ω m)`. -/
def partialCoef (n : ℕ) (t : ℤ → ℂ) (N : ℕ) (k : Idx (n + 1)) : ℂ :=
  ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), t m * lamTilde L n k (gridPt L m)

/-- The limit coefficient `μ_k(t) = Σ_m t_m Λ̃_k(ω m)`. -/
def muGrid (n : ℕ) (t : ℤ → ℂ) (k : Idx (n + 1)) : ℂ :=
  ∑' m : ℤ, t m * lamTilde L n k (gridPt L m)

/-- The symmetric partial sum `Σ_{|m|≤N} t_m K_{r, ω m}` applied to `v`. -/
def partialSum (n : ℕ) (t : ℤ → ℂ) (N : ℕ) (v : Hn L n) : Hn L n :=
  ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), t m • physicalKernel L (n + 1) (gridPt L m) v

theorem norm_partialCoef_le (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (N : ℕ) (k : Idx (n + 1)) :
    ‖partialCoef L n t N k‖ ≤ Bd L (n + 1) := by
  unfold partialCoef
  refine (norm_sum_le _ _).trans ?_
  refine (sum_le_hasSum _ (fun m _ => norm_nonneg _) (summable_norm_mul_grid L n t ht k).hasSum).trans ?_
  exact (Summable.tsum_le_tsum (norm_mul_grid_le L n t ht k) (summable_norm_mul_grid L n t ht k)
    (grid_bound L n k).1).trans (grid_bound L n k).2

theorem norm_muGrid_le (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (k : Idx (n + 1)) :
    ‖muGrid L n t k‖ ≤ Bd L (n + 1) := by
  unfold muGrid
  refine (norm_tsum_le_tsum_norm (summable_norm_mul_grid L n t ht k)).trans ?_
  exact (Summable.tsum_le_tsum (norm_mul_grid_le L n t ht k) (summable_norm_mul_grid L n t ht k)
    (grid_bound L n k).1).trans (grid_bound L n k).2

/-- Partial sums of a summable family converge to its sum along the symmetric exhaustion. -/
theorem tendsto_Icc_sum (f : ℤ → ℂ) (hf : Summable f) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f m) atTop (𝓝 (∑' m, f m)) := by
  have hI : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 (fun s => ⟨s.sup Int.natAbs,
      fun N hN => Finset.le_iff_subset.2 fun m hm => ?_⟩)
    have h1 : m.natAbs ≤ s.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hm
    rw [Finset.mem_Icc]
    rcases Int.natAbs_eq m with h | h <;> omega
  have hS : Tendsto (fun s : Finset ℤ => ∑ m ∈ s, f m) atTop (𝓝 (∑' m, f m)) := hf.hasSum
  exact Filter.Tendsto.comp (g := fun s : Finset ℤ => ∑ m ∈ s, f m) hS hI

/-- Coefficients of the partial sum: `⟪B_k, S_N v⟫ = (Σ_{|m|≤N} t_m Λ̃_k(ω m)) ⟪B_k, v⟫`. -/
theorem inner_partialSum (n : ℕ) (t : ℤ → ℂ) (N : ℕ) (k : Idx (n + 1)) (v : Hn L n) :
    ⟪physBasis L n k, partialSum L n t N v⟫_ℂ =
      partialCoef L n t N k * ⟪physBasis L n k, v⟫_ℂ := by
  unfold partialSum partialCoef
  rw [inner_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hc : ⟪physBasis L n k, physicalKernel L (n + 1) (gridPt L m) v⟫_ℂ =
      lamTilde L n k (gridPt L m) * ⟪physBasis L n k, v⟫_ℂ :=
    eig_coeff (physBasis L n) (physicalKernel L (n + 1) (gridPt L m))
      (fun k' => lamTilde L n k' (gridPt L m)) (fun i => eigen_all L n (gridPt L m) i) k v
  rw [inner_smul_right, hc]
  ring

theorem norm_partialSum_le (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (N : ℕ) (v : Hn L n) :
    ‖partialSum L n t N v‖ ≤ Bd L (n + 1) * ‖v‖ := by
  have hB0 := Bd_nonneg L (n + 1)
  have hA := parseval_hasSum (physBasis L n) (partialSum L n t N v)
  have hB : HasSum (fun k => Bd L (n + 1) ^ 2 * ‖⟪physBasis L n k, v⟫_ℂ‖ ^ 2)
      (Bd L (n + 1) ^ 2 * ‖v‖ ^ 2) :=
    (parseval_hasSum (physBasis L n) v).mul_left _
  have hle : ‖partialSum L n t N v‖ ^ 2 ≤ Bd L (n + 1) ^ 2 * ‖v‖ ^ 2 := by
    refine hasSum_le (fun k => ?_) hA hB
    show ‖⟪physBasis L n k, partialSum L n t N v⟫_ℂ‖ ^ 2 ≤
      Bd L (n + 1) ^ 2 * ‖⟪physBasis L n k, v⟫_ℂ‖ ^ 2
    rw [inner_partialSum]
    exact sq_norm_mul_le _ _ (norm_partialCoef_le L n t ht N k)
  exact le_of_sq_le_sq_nonneg (mul_nonneg hB0 (norm_nonneg v)) (by rw [mul_pow]; exact hle)

/-- Any strong limit of the symmetric partial sums has norm at most `B_{n+1}(L)`. -/
theorem strong_norm_le (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) (T : Hn L n →L[ℂ] Hn L n)
    (hT : ∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v))) :
    ‖T‖ ≤ Bd L (n + 1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Bd_nonneg L (n + 1))
  intro v
  exact le_of_tendsto' (hT v).norm (fun N => norm_partialSum_le L n t ht N v)

/-- **Strong convergence and norm bound.** For `|t_m| ≤ 1`, the symmetric partial sums converge strongly
to the operator `T` diagonal in `physBasis` with entries `μ_k(t)`, and `‖T‖ ≤ B_{n+1}(L)`. -/
theorem strong_exists (n : ℕ) (t : ℤ → ℂ) (ht : ∀ m, ‖t m‖ ≤ 1) :
    ∃ T : Hn L n →L[ℂ] Hn L n, (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v))) ∧
      ‖T‖ ≤ Bd L (n + 1) ∧ ∀ (k : Idx (n + 1)) (v : Hn L n),
        ⟪physBasis L n k, T v⟫_ℂ = muGrid L n t k * ⟪physBasis L n k, v⟫_ℂ := by
  obtain ⟨T, hT, hTn⟩ := diag_exists (physBasis L n) (muGrid L n t) (Bd L (n + 1))
    (fun k => norm_muGrid_le L n t ht k) (Bd_nonneg L (n + 1))
  refine ⟨T, fun v => ?_, hTn, hT⟩
  refine tendsto_of_norm_sq_tendsto _ _ ?_
  have hw : ∀ N : ℕ, ‖partialSum L n t N v - T v‖ ^ 2 =
      ∑' k, ‖(partialCoef L n t N k - muGrid L n t k) * ⟪physBasis L n k, v⟫_ℂ‖ ^ 2 := by
    intro N
    rw [← (parseval_hasSum (physBasis L n) (partialSum L n t N v - T v)).tsum_eq]
    refine tsum_congr (fun k => ?_)
    rw [inner_sub_right, inner_partialSum, hT k v, ← sub_mul]
  have hp : ∀ k : Idx (n + 1),
      Tendsto (fun N : ℕ => partialCoef L n t N k) atTop (𝓝 (muGrid L n t k)) :=
    fun k => tendsto_Icc_sum _ (summable_mul_grid L n t ht k)
  have hab : ∀ k : Idx (n + 1), Tendsto
      (fun N : ℕ => ‖(partialCoef L n t N k - muGrid L n t k) * ⟪physBasis L n k, v⟫_ℂ‖ ^ 2)
      atTop (𝓝 0) := by
    intro k
    have h0 : Tendsto (fun N : ℕ => partialCoef L n t N k - muGrid L n t k) atTop (𝓝 0) := by
      have := (hp k).sub_const (muGrid L n t k)
      rwa [sub_self] at this
    have h1 := ((h0.mul_const (⟪physBasis L n k, v⟫_ℂ)).norm).pow 2
    rwa [zero_mul, norm_zero, zero_pow two_ne_zero] at h1
  have hbd : ∀ᶠ N : ℕ in atTop, ∀ k : Idx (n + 1),
      ‖‖(partialCoef L n t N k - muGrid L n t k) * ⟪physBasis L n k, v⟫_ℂ‖ ^ 2‖ ≤
        (2 * Bd L (n + 1)) ^ 2 * ‖⟪physBasis L n k, v⟫_ℂ‖ ^ 2 := by
    refine Filter.Eventually.of_forall (fun N k => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply sq_norm_mul_le
    refine (norm_sub_le _ _).trans ?_
    linarith [norm_partialCoef_le L n t ht N k, norm_muGrid_le L n t ht k]
  have hsumB : Summable (fun k : Idx (n + 1) =>
      (2 * Bd L (n + 1)) ^ 2 * ‖⟪physBasis L n k, v⟫_ℂ‖ ^ 2) :=
    (parseval_hasSum (physBasis L n) v).summable.mul_left _
  have hdom := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (N : ℕ) (k : Idx (n + 1)) =>
      ‖(partialCoef L n t N k - muGrid L n t k) * ⟪physBasis L n k, v⟫_ℂ‖ ^ 2)
    (g := fun _ => (0 : ℝ)) (bound := fun k : Idx (n + 1) =>
      (2 * Bd L (n + 1)) ^ 2 * ‖⟪physBasis L n k, v⟫_ℂ‖ ^ 2) hsumB hab hbd
  rw [tsum_zero] at hdom
  exact hdom.congr (fun N => (hw N).symm)

/-- Summability of the grid-kernel tail: `Σ_n` of the summand is bounded in terms of `(e^a κ L/π)`. -/
theorem summand_key (m : ℕ) (a κ : ℝ) (hκ : 0 ≤ κ) (n : ℕ) :
    ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * (L / Real.pi) ^ (n + 1) ≤
      (m.factorial : ℝ) * (Real.exp 1 * Real.exp a * (L / Real.pi) * max κ 1) ^ (n + 1) := by
  have hL : (0 : ℝ) < L := Fact.out
  have hP : (0 : ℝ) ≤ L / Real.pi := div_nonneg hL.le Real.pi_pos.le
  have hx : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hA : ((n : ℝ) + 1) ^ m ≤ (m.factorial : ℝ) * Real.exp ((n : ℝ) + 1) := by
    have h := Real.pow_div_factorial_le_exp _ hx m
    have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hf] at h
    linarith [h, mul_comm (Real.exp ((n : ℝ) + 1)) (m.factorial : ℝ)]
  have hExp : Real.exp ((n : ℝ) + 1) = Real.exp 1 ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hExpA : Real.exp (a * ((n : ℝ) + 1)) = Real.exp a ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hκQ : κ ^ n ≤ (max κ 1) ^ (n + 1) :=
    (pow_le_pow_left₀ hκ (le_max_left κ 1) n).trans
      (pow_le_pow_right₀ (le_max_right κ 1) (Nat.le_succ n))
  have h1 : ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) ≤
      ((m.factorial : ℝ) * Real.exp ((n : ℝ) + 1)) * Real.exp (a * ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
  have h2 : ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n ≤
      ((m.factorial : ℝ) * Real.exp ((n : ℝ) + 1)) * Real.exp (a * ((n : ℝ) + 1)) *
        (max κ 1) ^ (n + 1) :=
    mul_le_mul h1 hκQ (pow_nonneg hκ _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _))
      (Real.exp_nonneg _))
  calc ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * (L / Real.pi) ^ (n + 1)
      ≤ ((m.factorial : ℝ) * Real.exp ((n : ℝ) + 1)) * Real.exp (a * ((n : ℝ) + 1)) *
          (max κ 1) ^ (n + 1) * (L / Real.pi) ^ (n + 1) :=
        mul_le_mul_of_nonneg_right h2 (pow_nonneg hP _)
    _ = (m.factorial : ℝ) * (Real.exp 1 * Real.exp a * (L / Real.pi) * max κ 1) ^ (n + 1) := by
        rw [hExp, hExpA]
        ring

/-- **Main statement of R-E67FE3C4 item 2.**
(i) For every `n` and every bounded `t` (`|t_m| ≤ 1`), the symmetric partial sums of `Σ_m t_m K_{r,ω m}`
converge strongly to an operator `T` with `‖T‖ ≤ B_r(L)`, diagonal in `physBasis` with entries `μ_k(t)`.
(ii) For `m : ℕ`, `a : ℝ`, `κ ≥ 0`, there is a constant `S0` such that for all bounded `t` and all families
`T_r(t)` of strong limits, `Σ_n (n+1)^m e^{a(n+1)} κ^n ‖T_n(t)‖` is summable with sum at most `S0`. -/
theorem R_E67FE3C4_strong_sum :
    (∀ (n : ℕ) (t : ℤ → ℂ), (∀ m, ‖t m‖ ≤ 1) → ∃ T : Hn L n →L[ℂ] Hn L n,
        (∀ v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T v))) ∧
        ‖T‖ ≤ Bd L (n + 1) ∧ ∀ (k : Idx (n + 1)) (v : Hn L n),
          ⟪physBasis L n k, T v⟫_ℂ = muGrid L n t k * ⟪physBasis L n k, v⟫_ℂ) ∧
    (∀ (m : ℕ) (a κ : ℝ), 0 ≤ κ → ∃ S0 : ℝ, ∀ (t : ℤ → ℂ), (∀ j, ‖t j‖ ≤ 1) →
        ∀ T : (n : ℕ) → Hn L n →L[ℂ] Hn L n,
          (∀ n v, Tendsto (fun N => partialSum L n t N v) atTop (𝓝 (T n v))) →
          Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖) ∧
          ∑' n : ℕ, ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖ ≤ S0) := by
  refine ⟨fun n t ht => strong_exists L n t ht, fun m a κ hκ => ?_⟩
  set E : ℝ := Real.exp 1 * Real.exp a * (L / Real.pi) * max κ 1 with hE
  have hs1 : Summable (fun n : ℕ => E ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
    (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial E)
  have hgs : Summable (fun n : ℕ => (2 * Real.pi ^ 2 / 3 * (m.factorial : ℝ)) *
      (E ^ (n + 1) / ((n + 1).factorial : ℝ))) := hs1.mul_left _
  refine ⟨∑' n : ℕ, (2 * Real.pi ^ 2 / 3 * (m.factorial : ℝ)) *
      (E ^ (n + 1) / ((n + 1).factorial : ℝ)), fun t ht T hT => ?_⟩
  have hbound : ∀ n : ℕ, ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖ ≤
      (2 * Real.pi ^ 2 / 3 * (m.factorial : ℝ)) * (E ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
    intro n
    have hTn : ‖T n‖ ≤ Bd L (n + 1) := strong_norm_le L n t ht (T n) (hT n)
    have hcoef : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n :=
      mul_nonneg (mul_nonneg (by positivity) (Real.exp_nonneg _)) (pow_nonneg hκ _)
    have hstep1 : ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖ ≤
        ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * Bd L (n + 1) :=
      mul_le_mul_of_nonneg_left hTn hcoef
    have hBd : Bd L (n + 1) = (2 * Real.pi ^ 2 / (3 * ((n + 1).factorial : ℝ))) *
        (L / Real.pi) ^ (n + 1) := by
      unfold Bd
      ring
    have hkey := summand_key L m a κ hκ n
    have hpre : (0 : ℝ) ≤ 2 * Real.pi ^ 2 / (3 * ((n + 1).factorial : ℝ)) := by positivity
    calc ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖
        ≤ ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * Bd L (n + 1) := hstep1
      _ = (2 * Real.pi ^ 2 / (3 * ((n + 1).factorial : ℝ))) *
          (((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * (L / Real.pi) ^ (n + 1)) := by
          rw [hBd]
          ring
      _ ≤ (2 * Real.pi ^ 2 / (3 * ((n + 1).factorial : ℝ))) *
          ((m.factorial : ℝ) * (Real.exp 1 * Real.exp a * (L / Real.pi) * max κ 1) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hkey hpre
      _ = (2 * Real.pi ^ 2 / 3 * (m.factorial : ℝ)) * (E ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
          rw [hE]
          field_simp
  have hsumf : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n * ‖T n‖) :=
    Summable.of_nonneg_of_le (fun n => by
      have hcoef : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ m * Real.exp (a * ((n : ℝ) + 1)) * κ ^ n :=
        mul_nonneg (mul_nonneg (by positivity) (Real.exp_nonneg _)) (pow_nonneg hκ _)
      exact mul_nonneg hcoef (norm_nonneg (T n))) hbound hgs
  exact ⟨hsumf, hsumf.tsum_le_tsum hbound hgs⟩

end QuantumNLS.GridStrongSum

#print axioms QuantumNLS.GridStrongSum.strong_exists
#print axioms QuantumNLS.GridStrongSum.R_E67FE3C4_strong_sum
