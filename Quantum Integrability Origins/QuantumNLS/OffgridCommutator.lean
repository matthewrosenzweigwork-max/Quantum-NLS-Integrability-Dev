import Mathlib
import QuantumNLS.PlacementCommutatorL2
import QuantumNLS.OffgridBessel
import QuantumNLS.DiagonalBesselStrong
import QuantumNLS.NormalizedTransfer
import QuantumNLS.BasisAdjoint

/-!
# R-F9AB39A7 `QG:lem:haar-offgrid-bessel` (`QUANTUM_GAUGE_COMPONENTS.tex:614-697`): the lemma

Statement formalized (`ω = 2π/L`, `Γ_0` the square contour of half-width `ω/4`, `z_n = ωn + w`):

(1) `haar_kernel_bessel` (eq. `QG:eq:haar-kernel-bessel`): for `w ∈ Γ_0`, `K_{r,z} = physicalKernel L r z`, `r = n+1`, both
    `∑_{j∈ℤ} K_{r,z_j}^* K_{r,z_j} ≤ b_r² 1` and `∑_j K_{r,z_j} K_{r,z_j}^* ≤ b_r² 1` hold as strong monotone sums:
    for each `x` the series converge unconditionally, to bounded positive operators `T, T'`, with
    `⟨x, T x⟩ = ∑_j ‖K_{r,z_j} x‖² ≤ b_r² ‖x‖²` (resp. with `K^*`), `b_r = (1+e^{π/2})√(16+π²)4^{r-1}/(r!ω^r)`.
(2) `haar_commutator_bessel` (eq. `QG:eq:haar-commutator-bessel`): for `1 ≤ k ≤ N`, bounded `J` on `Sym^k`, `J_N = U_{N,k}(J)`,
    `ψ ∈ Sym^N`, `κ ≥ 0`: `(∑_j ‖N[S_N(z_j), J_N]ψ‖²)^{1/2} ≤ B_k ‖J‖ ‖ψ‖`, `B_k = 2k∑_{r≥1} r κ^r b_r < ∞`,
    and the same for `S_N(z_j)^*`; uniform in `N ≥ k` and `w ∈ Γ_0`.
Here `S_N = normalizedTransfer` (DEF-048, the literal transfer with `ϑ_{N,r} = (N)_r/N^r`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementGrouping QuantumNLS.RootOverlapCommutator QuantumNLS.PlacementCommutatorL2

namespace QuantumNLS.OffgridCommutator

/-! ### Generic series commutator estimate -/

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι' : Type*}

/-- `c·1 + ∑_{j<N} a_j U_{N,j+1}(K_j)`. -/
def seriesOp (N : ℕ) (c : ℂ) (a : Fin N → ℂ)
    (K : (j : Fin N) → BoundedSymmetricKernel H (j.val + 1)) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  c • ContinuousLinearMap.id ℂ _ + ∑ j : Fin N, a j • genericU_N_r N (j.val + 1) j.2 (K j)

theorem l2_coe {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (S : Submodule ℂ V)
    (F : Finset ι') (v : ι' → S) : l2 F (fun m => (v m : V)) = l2 F v := by
  unfold l2
  simp [Submodule.coe_norm]

theorem seriesOp_comm_l2 (N k : ℕ) (hk : k ≤ N) (hN : 1 ≤ N) (F : Finset ι') (c : ι' → ℂ)
    (a : Fin N → ℂ) (K : (j : Fin N) → ι' → BoundedSymmetricKernel H (j.val + 1)) (b : Fin N → ℝ)
    (hb0 : ∀ j, 0 ≤ b j)
    (hb : ∀ (j : Fin N) (x : SymSector ℂ H (j.val + 1)), ∑ m ∈ F, ‖K j m x‖ ^ 2 ≤ b j ^ 2 * ‖x‖ ^ 2)
    (J : BoundedSymmetricKernel H k) (ψ : SymSector ℂ H N) :
    l2 F (fun m => (seriesOp N (c m) a (fun j => K j m) * genericU_N_r N k hk J -
        genericU_N_r N k hk J * seriesOp N (c m) a (fun j => K j m)) ψ) ≤
      2 * k * ‖J‖ * ‖ψ‖ / N * ∑ j : Fin N, ((j.val : ℝ) + 1) * ‖a j‖ * b j := by
  classical
  set X : (j : Fin N) → ι' → HilbertTensorPower ℂ H N := fun j m =>
    ((rawSubsetAverage N (j.val + 1) j.2 (K j m)).comp (rawSubsetAverage N k hk J) -
      (rawSubsetAverage N k hk J).comp (rawSubsetAverage N (j.val + 1) j.2 (K j m)))
      (ψ : HilbertTensorPower ℂ H N) with hX
  have hcomm : ∀ m, (((seriesOp N (c m) a (fun j => K j m) * genericU_N_r N k hk J -
        genericU_N_r N k hk J * seriesOp N (c m) a (fun j => K j m)) ψ : SymSector ℂ H N) :
          HilbertTensorPower ℂ H N) = ∑ j : Fin N, a j • X j m := by
    intro m
    have h1 : (seriesOp N (c m) a (fun j => K j m) * genericU_N_r N k hk J -
        genericU_N_r N k hk J * seriesOp N (c m) a (fun j => K j m)) ψ =
        ∑ j : Fin N, a j • (genericU_N_r N (j.val + 1) j.2 (K j m) (genericU_N_r N k hk J ψ) -
          genericU_N_r N k hk J (genericU_N_r N (j.val + 1) j.2 (K j m) ψ)) := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
      simp only [seriesOp, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.sum_apply,
        map_add, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [h1, Submodule.coe_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Submodule.coe_smul, Submodule.coe_sub]
    simp only [coe_genericU, hX, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  rw [← l2_coe]
  simp only [hcomm]
  refine (l2_sum_le F Finset.univ (fun j m => a j • X j m)).trans ?_
  have hj : ∀ j : Fin N, l2 F (fun m => a j • X j m) ≤
      ‖a j‖ * (2 * (b j * ‖J‖) * (((j.val + 1 : ℕ) : ℝ) * (k : ℝ) / N) * ‖ψ‖) := by
    intro j
    rw [l2_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have := average_commutator_l2_le N (j.val + 1) k j.2 hk hN F (K j) J (hb0 j) (hb j)
      (ψ : HilbertTensorPower ℂ H N)
    simpa [hX, Submodule.coe_norm] using this
  refine (Finset.sum_le_sum (fun j _ => hj j)).trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast
  ring

end Generic

/-! ### The concrete lemma -/

section Concrete

open QuantumNLS.OffgridBessel QuantumNLS.HaarEigenbasis QuantumNLS.HaarKernelFactorizationSym
  QuantumNLS.BethePhysicalTransfer QuantumNLS.PhysicalTensor QuantumNLS.NormalizedTransfer
  QuantumNLS.HighMomentsRank QuantumNLS.DiagonalBesselStrong QuantumNLS.HaarSlaterBasis

variable (L : ℝ) [Fact (0 < L)]

/-- The points `z_j = ωj + w`. -/
def zpt (w : ℂ) (j : ℤ) : ℂ := (omegaL L : ℂ) * (j : ℂ) + w

theorem zpt_eq (w : ℂ) (j : ℤ) : zpt L w j = ((omegaL L * (j : ℝ) : ℝ) : ℂ) + w := by
  simp [zpt]

/-- **`QG:eq:haar-kernel-bessel`** (strong monotone sums). -/
theorem haar_kernel_bessel {w : ℂ} (hw : w ∈ Gamma0 L) (n : ℕ) :
    (∃ T : SymSector ℂ (L2T L) (n + 1) →L[ℂ] SymSector ℂ (L2T L) (n + 1),
      (∀ x, HasSum (fun j : ℤ => (ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j)) ∘L
        physicalKernel L (n + 1) (zpt L w j)) x) (T x)) ∧
      (∀ x, ⟪x, T x⟫_ℂ = ((∑' j : ℤ, ‖physicalKernel L (n + 1) (zpt L w j) x‖ ^ 2 : ℝ) : ℂ)) ∧
      (∀ x, Summable (fun j : ℤ => ‖physicalKernel L (n + 1) (zpt L w j) x‖ ^ 2) ∧
        ∑' j : ℤ, ‖physicalKernel L (n + 1) (zpt L w j) x‖ ^ 2 ≤ bR L (n + 1) ^ 2 * ‖x‖ ^ 2) ∧
      T.IsPositive) ∧
    (∃ T : SymSector ℂ (L2T L) (n + 1) →L[ℂ] SymSector ℂ (L2T L) (n + 1),
      (∀ x, HasSum (fun j : ℤ => (physicalKernel L (n + 1) (zpt L w j) ∘L
        ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j))) x) (T x)) ∧
      (∀ x, ⟪x, T x⟫_ℂ = ((∑' j : ℤ, ‖ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j)) x‖ ^ 2 : ℝ) : ℂ)) ∧
      (∀ x, Summable (fun j : ℤ => ‖ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j)) x‖ ^ 2) ∧
        ∑' j : ℤ, ‖ContinuousLinearMap.adjoint (physicalKernel L (n + 1) (zpt L w j)) x‖ ^ 2 ≤
          bR L (n + 1) ^ 2 * ‖x‖ ^ 2) ∧
      T.IsPositive) := by
  have hb0 : 0 ≤ bR L (n + 1) := by
    unfold bR
    have := omega_pos L
    positivity
  have hK : ∀ (j : ℤ) (k : Idx (n + 1)), physicalKernel L (n + 1) (zpt L w j) (physBasis L n k) =
      lamTilde L n k (zpt L w j) • physBasis L n k := fun j k => eigen_all L n _ k
  have hB : ∀ (F : Finset ℤ) (k : Idx (n + 1)), ∑ j ∈ F, ‖lamTilde L n k (zpt L w j)‖ ^ 2 ≤ bR L (n + 1) ^ 2 := by
    intro F k
    simpa only [zpt_eq] using lamTilde_sq_sum_le L hw n F k
  exact ⟨strong_sum_diag (physBasis L n) (fun j : ℤ => physicalKernel L (n + 1) (zpt L w j))
      (fun j k => lamTilde L n k (zpt L w j)) hK hb0 hB,
    strong_sum_diag' (physBasis L n) (fun j : ℤ => physicalKernel L (n + 1) (zpt L w j))
      (fun j k => lamTilde L n k (zpt L w j)) hK hb0 hB⟩

/-- The constant `B_k = 2k ∑_{r≥1} r κ^r b_r`. -/
def Bk (κ : ℝ) (k : ℕ) : ℝ := 2 * k * ∑' j : ℕ, ((j : ℝ) + 1) * κ ^ (j + 1) * bR L (j + 1)

theorem summable_Bk (κ : ℝ) : Summable (fun j : ℕ => ((j : ℝ) + 1) * κ ^ (j + 1) * bR L (j + 1)) := by
  have hω := omega_pos L
  have hs := (Real.summable_pow_div_factorial (4 * κ / omegaL L)).mul_left
    ((1 + Real.exp (Real.pi / 2)) * Real.sqrt (16 + Real.pi ^ 2) * κ / omegaL L)
  refine hs.congr (fun j => ?_)
  unfold bR
  rw [Nat.factorial_succ]
  push_cast
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hω' : omegaL L ≠ 0 := hω.ne'
  try simp only [Nat.add_sub_cancel]
  have hinv : omegaL L ^ j * (omegaL L)⁻¹ ^ j = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hω', one_pow]
  field_simp
  linear_combination (κ * κ ^ j * omegaL L * 4 ^ j) * hinv

theorem Bk_nonneg {κ : ℝ} (hκ : 0 ≤ κ) (k : ℕ) : 0 ≤ Bk L κ k := by
  unfold Bk
  have := omega_pos L
  have : 0 ≤ ∑' j : ℕ, ((j : ℝ) + 1) * κ ^ (j + 1) * bR L (j + 1) := by
    refine tsum_nonneg (fun j => ?_)
    unfold bR
    positivity
  positivity


theorem normalizedTransfer_eq_seriesOp (κ : ℝ) (N : ℕ) (z : ℂ) :
    normalizedTransfer L κ N z =
      seriesOp N (1 + Complex.exp (Complex.I * z * L))
        (fun j : Fin N => (((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ))
        (fun j => physicalKernel L (j.val + 1) z) := rfl

theorem adjoint_seriesOp (N : ℕ) (c : ℂ) (a : Fin N → ℂ)
    (K : (j : Fin N) → BoundedSymmetricKernel (L2T L) (j.val + 1)) :
    ContinuousLinearMap.adjoint (seriesOp N c a K) =
      seriesOp N (conj c) (fun j => conj (a j)) (fun j => ContinuousLinearMap.adjoint (K j)) := by
  unfold seriesOp
  rw [map_add, map_sum, map_smulₛₗ, ContinuousLinearMap.adjoint_id]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_smulₛₗ, QuantumNLS.BasisAdjoint.placement_adjoint' L N (j.val + 1) j.2 (K j)]

theorem norm_coeff_le {κ : ℝ} (hκ : 0 ≤ κ) {N : ℕ} (hN : 1 ≤ N) (j : Fin N) :
    ‖(((κ ^ (j.val + 1) : ℝ) * fallR N (j.val + 1) : ℝ) : ℂ)‖ ≤ κ ^ (j.val + 1) := by
  have hb := fallR_bounds N hN (j.val + 1) j.2
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hκ _) hb.1)]
  calc κ ^ (j.val + 1) * fallR N (j.val + 1) ≤ κ ^ (j.val + 1) * 1 :=
        mul_le_mul_of_nonneg_left hb.2.2 (pow_nonneg hκ _)
    _ = κ ^ (j.val + 1) := mul_one _

/-- The finite-`F` form of the commutator estimate for a series of the shape of `S_N` or `S_N^*`. -/
theorem sum_weight_le {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ) :
    ∑ j : Fin N, ((j.val : ℝ) + 1) * κ ^ (j.val + 1) * bR L (j.val + 1) ≤
      ∑' j : ℕ, ((j : ℝ) + 1) * κ ^ (j + 1) * bR L (j + 1) := by
  have hnn : ∀ j : ℕ, 0 ≤ ((j : ℝ) + 1) * κ ^ (j + 1) * bR L (j + 1) := by
    intro j
    have := omega_pos L
    unfold bR
    positivity
  rw [Fin.sum_univ_eq_sum_range (fun j => ((j : ℝ) + 1) * κ ^ (j + 1) * bR L (j + 1)) N]
  exact (summable_Bk L κ).sum_le_tsum _ (fun j _ => hnn j)

/-- The abstract commutator bound for both `S_N` and `S_N^*`: given the Bessel hypotheses. -/
theorem commutator_bound_of_series {κ : ℝ} (hκ : 0 ≤ κ) {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (F : Finset ℤ) (c : ℤ → ℂ) (a : Fin N → ℂ)
    (ha : ∀ j : Fin N, ‖a j‖ ≤ κ ^ (j.val + 1))
    (K : (j : Fin N) → ℤ → BoundedSymmetricKernel (L2T L) (j.val + 1))
    (hb : ∀ (j : Fin N) (x : SymSector ℂ (L2T L) (j.val + 1)),
      ∑ m ∈ F, ‖K j m x‖ ^ 2 ≤ bR L (j.val + 1) ^ 2 * ‖x‖ ^ 2)
    (J : BoundedSymmetricKernel (L2T L) k) (ψ : SymSector ℂ (L2T L) N) :
    ∑ m ∈ F, ((N : ℝ) * ‖(seriesOp N (c m) a (fun j => K j m) * genericU_N_r N k hkN J -
        genericU_N_r N k hkN J * seriesOp N (c m) a (fun j => K j m)) ψ‖) ^ 2 ≤
      (Bk L κ k * ‖J‖ * ‖ψ‖) ^ 2 := by
  have hN : 1 ≤ N := hk1.trans hkN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb0 : ∀ j : Fin N, 0 ≤ bR L (j.val + 1) := by
    intro j; have := omega_pos L; unfold bR; positivity
  have h1 := seriesOp_comm_l2 N k hkN hN F c a K (fun j => bR L (j.val + 1)) hb0 hb J ψ
  set l := l2 F (fun m => (seriesOp N (c m) a (fun j => K j m) * genericU_N_r N k hkN J -
        genericU_N_r N k hkN J * seriesOp N (c m) a (fun j => K j m)) ψ) with hl
  have h2 : ∑ j : Fin N, ((j.val : ℝ) + 1) * ‖a j‖ * bR L (j.val + 1) ≤
      ∑' j : ℕ, ((j : ℝ) + 1) * κ ^ (j + 1) * bR L (j + 1) := by
    refine le_trans (Finset.sum_le_sum (fun j _ => ?_)) (sum_weight_le L hκ N)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha j) (by positivity)) (hb0 j)
  have h3 : (N : ℝ) * l ≤ Bk L κ k * ‖J‖ * ‖ψ‖ := by
    have e : (N : ℝ) * (2 * k * ‖J‖ * ‖ψ‖ / N * ∑ j : Fin N, ((j.val : ℝ) + 1) * ‖a j‖ * bR L (j.val + 1)) =
        2 * k * ‖J‖ * ‖ψ‖ * ∑ j : Fin N, ((j.val : ℝ) + 1) * ‖a j‖ * bR L (j.val + 1) := by
      field_simp
    calc (N : ℝ) * l ≤ (N : ℝ) * (2 * k * ‖J‖ * ‖ψ‖ / N *
          ∑ j : Fin N, ((j.val : ℝ) + 1) * ‖a j‖ * bR L (j.val + 1)) :=
          mul_le_mul_of_nonneg_left h1 hNr.le
      _ = 2 * k * ‖J‖ * ‖ψ‖ * ∑ j : Fin N, ((j.val : ℝ) + 1) * ‖a j‖ * bR L (j.val + 1) := e
      _ ≤ 2 * k * ‖J‖ * ‖ψ‖ * ∑' j : ℕ, ((j : ℝ) + 1) * κ ^ (j + 1) * bR L (j + 1) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Bk L κ k * ‖J‖ * ‖ψ‖ := by unfold Bk; ring
  have hsq : ∑ m ∈ F, ((N : ℝ) * ‖(seriesOp N (c m) a (fun j => K j m) * genericU_N_r N k hkN J -
        genericU_N_r N k hkN J * seriesOp N (c m) a (fun j => K j m)) ψ‖) ^ 2 = ((N : ℝ) * l) ^ 2 := by
    simp only [mul_pow, hl, l2_sq, Finset.mul_sum]
  rw [hsq]
  exact pow_le_pow_left₀ (mul_nonneg hNr.le (l2_nonneg _ _)) h3 2

/-- **`QG:eq:haar-commutator-bessel`**, for `S_N` (`normalizedTransfer`, DEF-048). -/
theorem haar_commutator_bessel {w : ℂ} (hw : w ∈ Gamma0 L) {κ : ℝ} (hκ : 0 ≤ κ) {N k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (J : BoundedSymmetricKernel (L2T L) k) (ψ : SymSector ℂ (L2T L) N) :
    Summable (fun j : ℤ => ((N : ℝ) * ‖(normalizedTransfer L κ N (zpt L w j) * genericU_N_r N k hkN J -
        genericU_N_r N k hkN J * normalizedTransfer L κ N (zpt L w j)) ψ‖) ^ 2) ∧
    Real.sqrt (∑' j : ℤ, ((N : ℝ) * ‖(normalizedTransfer L κ N (zpt L w j) * genericU_N_r N k hkN J -
        genericU_N_r N k hkN J * normalizedTransfer L κ N (zpt L w j)) ψ‖) ^ 2) ≤
      Bk L κ k * ‖J‖ * ‖ψ‖ := by
  have hN : 1 ≤ N := hk1.trans hkN
  have hfin : ∀ F : Finset ℤ, ∑ m ∈ F, ((N : ℝ) * ‖(normalizedTransfer L κ N (zpt L w m) *
      genericU_N_r N k hkN J - genericU_N_r N k hkN J * normalizedTransfer L κ N (zpt L w m)) ψ‖) ^ 2 ≤
      (Bk L κ k * ‖J‖ * ‖ψ‖) ^ 2 := by
    intro F
    simp only [normalizedTransfer_eq_seriesOp]
    refine commutator_bound_of_series L hκ hk1 hkN F _ _ (fun j => norm_coeff_le hκ hN j)
      (fun j m => physicalKernel L (j.val + 1) (zpt L w m)) (fun j x => ?_) J ψ
    have := (QuantumNLS.OffgridBessel.bessel_K_finite L hw j.val F x).1
    simpa only [zpt_eq] using this
  have hnn : ∀ m : ℤ, 0 ≤ ((N : ℝ) * ‖(normalizedTransfer L κ N (zpt L w m) *
      genericU_N_r N k hkN J - genericU_N_r N k hkN J * normalizedTransfer L κ N (zpt L w m)) ψ‖) ^ 2 :=
    fun m => by positivity
  have hsum := summable_of_sum_le hnn hfin
  refine ⟨hsum, ?_⟩
  exact Real.sqrt_le_iff.mpr ⟨mul_nonneg (mul_nonneg (Bk_nonneg L hκ k) (norm_nonneg J)) (norm_nonneg ψ),
    hsum.tsum_le_of_sum_le hfin⟩

/-- The same for the adjoint `S_N(z)^*`. -/
theorem haar_commutator_bessel_adjoint {w : ℂ} (hw : w ∈ Gamma0 L) {κ : ℝ} (hκ : 0 ≤ κ) {N k : ℕ}
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (J : BoundedSymmetricKernel (L2T L) k) (ψ : SymSector ℂ (L2T L) N) :
    Summable (fun j : ℤ => ((N : ℝ) * ‖(ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w j)) *
        genericU_N_r N k hkN J - genericU_N_r N k hkN J *
          ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w j))) ψ‖) ^ 2) ∧
    Real.sqrt (∑' j : ℤ, ((N : ℝ) * ‖(ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w j)) *
        genericU_N_r N k hkN J - genericU_N_r N k hkN J *
          ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w j))) ψ‖) ^ 2) ≤
      Bk L κ k * ‖J‖ * ‖ψ‖ := by
  have hN : 1 ≤ N := hk1.trans hkN
  have hfin : ∀ F : Finset ℤ, ∑ m ∈ F, ((N : ℝ) * ‖(ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w m)) *
      genericU_N_r N k hkN J - genericU_N_r N k hkN J *
        ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w m))) ψ‖) ^ 2 ≤
      (Bk L κ k * ‖J‖ * ‖ψ‖) ^ 2 := by
    intro F
    simp only [normalizedTransfer_eq_seriesOp, adjoint_seriesOp]
    refine commutator_bound_of_series L hκ hk1 hkN F _ _ (fun j => ?_)
      (fun j m => ContinuousLinearMap.adjoint (physicalKernel L (j.val + 1) (zpt L w m)))
      (fun j x => ?_) J ψ
    · rw [RCLike.norm_conj]; exact norm_coeff_le hκ hN j
    · have := (QuantumNLS.OffgridBessel.bessel_K_finite L hw j.val F x).2
      simpa only [zpt_eq] using this
  have hnn : ∀ m : ℤ, 0 ≤ ((N : ℝ) * ‖(ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w m)) *
      genericU_N_r N k hkN J - genericU_N_r N k hkN J *
        ContinuousLinearMap.adjoint (normalizedTransfer L κ N (zpt L w m))) ψ‖) ^ 2 :=
    fun m => by positivity
  have hsum := summable_of_sum_le hnn hfin
  refine ⟨hsum, ?_⟩
  exact Real.sqrt_le_iff.mpr ⟨mul_nonneg (mul_nonneg (Bk_nonneg L hκ k) (norm_nonneg J)) (norm_nonneg ψ),
    hsum.tsum_le_of_sum_le hfin⟩

#print axioms haar_kernel_bessel
#print axioms haar_commutator_bessel
#print axioms haar_commutator_bessel_adjoint

end Concrete

end QuantumNLS.OffgridCommutator
