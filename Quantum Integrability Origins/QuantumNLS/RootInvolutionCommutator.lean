import QuantumNLS.BoundedBetheTransfer
import QuantumNLS.NormalizedTransfer
import QuantumNLS.RootOverlapLimit
import QuantumNLS.RootOverlapCommutator
import QuantumNLS.HighMomentsRank

/-!
# R-C4F43CA8 `thm:root-involution`, part (2A): the finite commutator identity for the normalized transfers

Source: `source/chapters/foundations/ROOT_transfer_involution.tex:98` (zero Poisson bracket argument).
Realized inputs (read-only, frozen): `NormalizedTransfer.normalizedTransfer` (explicit expansion
`S_N(z) = (1+e^{izL}) Id + Σ_{j<N} κ^{j+1} θ_{N,j+1} U_{N,j+1}(K_{j+1,z})`), `BoundedBetheTransfer.transfer_consequences`
(accepted R-892D1666: `Commute (S_N z) (S_N w)`), `RootOverlapLimit.CommQ / ExN / limSeq` (scaled commutator expectation).

Proved here (standard axioms only):
* `commute_vec`: for every vector `x`, `Σ_{j,k<N} (c_j c_k) U_j(K_z) U_k(K_w) x = Σ_{k,j<N} (c_k c_j) U_k(K_w) U_j(K_z) x`,
  with `c_j = κ^{j+1} fallR N (j+1)` (from the commutation of the transfers; the constant `(1+e^{izL}) Id` drops out).
* `limSeq_sum_eq_zero`: for every unit `u`, `Σ_{j,k<N} c_j c_k limSeq_{j+1,k+1}(K_{j+1,z}, K_{k+1,w}) u N = 0`.

The vector-level route is used because `smul`-rewrites on `Sym^N →L Sym^N` have no instances in this repository.
Conjugate pairs (K_{q,w}^*) are NOT here (part 2D).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology

namespace QuantumNLS.RootInvolutionCommutator

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.NormalizedTransfer QuantumNLS.RootOverlapLimit QuantumNLS.RootOverlapCommutator
  QuantumNLS.HighMomentsRank

variable (L : ℝ) [Fact (0 < L)]

/-- `Sym^N` is closed: it is the fixed-point set of the continuous projection `symProj`. -/
theorem isClosed_symSector (N : ℕ) :
    IsClosed ((SymSector ℂ (L2T L) N : Submodule ℂ _) : Set (HilbertTensorPower ℂ (L2T L) N)) := by
  have hset : ((SymSector ℂ (L2T L) N : Submodule ℂ _) : Set (HilbertTensorPower ℂ (L2T L) N)) =
      {x | symProj ℂ (L2T L) N x = x} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_setOf_eq]
    rw [symProj_eq_starProjection N, Submodule.starProjection_eq_self_iff]
  rw [hset]
  exact isClosed_eq (symProj ℂ (L2T L) N).continuous continuous_id

/-- `Sym^N` is a complete space. -/
instance symSector_completeSpace (N : ℕ) : CompleteSpace (SymSector ℂ (L2T L) N) :=
  (isClosed_symSector L N).completeSpace_coe

/-- The complex coefficient `κ^{j+1} θ_{N,j+1}` of the `j`-th term of `S_N(z)`. -/
def cf (κ : ℝ) (N : ℕ) (j : ℕ) : ℂ := ((κ ^ (j + 1) * fallR N (j + 1) : ℝ) : ℂ)

/-- The generic term `U_{N,j+1}(K_{j+1,z})` of the expansion of `S_N(z)`. -/
def Gt (N : ℕ) (z : ℂ) (j : Fin N) : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (orderedKernel L (j.val + 1) z)

/-- The expansion of the normalized transfer, as a definitional identity. -/
theorem normalizedTransfer_eq_sum (κ : ℝ) (N : ℕ) (z : ℂ) :
    normalizedTransfer L κ N z =
      (1 + Complex.exp (Complex.I * z * L)) • ContinuousLinearMap.id ℂ _ +
        ∑ j : Fin N, cf κ N j • Gt L N z j := rfl

/-- Generic vector identity: the scalar parts commute, the operator parts give the commutator. -/
theorem comm_apply_eq (N : ℕ) (X Y : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) (a b : ℂ)
    (x : SymSector ℂ (L2T L) N) :
    ((a • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N) + X) * (b • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N) + Y)) x -
        ((b • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N) + Y) * (a • ContinuousLinearMap.id ℂ (SymSector ℂ (L2T L) N) + X)) x =
      (X * Y) x - (Y * X) x := by
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_add, map_smul]
  module

/-- Expansion of `X_z (X_w x)` (outer index `k` of `X_w`). -/
theorem sum_mul_apply_eq (κ : ℝ) (N : ℕ) (z w : ℂ) (x : SymSector ℂ (L2T L) N) :
    (∑ j : Fin N, cf κ N j • Gt L N z j) ((∑ k : Fin N, cf κ N k • Gt L N w k) x) =
      ∑ j : Fin N, ∑ k : Fin N, (cf κ N j * cf κ N k) • Gt L N z j (Gt L N w k x) := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [mul_comm]

/-- Expansion of `X_w (X_z x)`. -/
theorem sum_mul_apply_eq' (κ : ℝ) (N : ℕ) (z w : ℂ) (x : SymSector ℂ (L2T L) N) :
    (∑ k : Fin N, cf κ N k • Gt L N w k) ((∑ j : Fin N, cf κ N j • Gt L N z j) x) =
      ∑ j : Fin N, ∑ k : Fin N, (cf κ N j * cf κ N k) • Gt L N w k (Gt L N z j x) := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]

/-- **Vector commutator identity.** From the commutation of the normalized transfers (accepted):
`Σ_{j,k} (c_j c_k) U_j(z) U_k(w) x = Σ_{j,k} (c_j c_k) U_k(w) U_j(z) x`. -/
theorem commute_vec (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N) (z w : ℂ)
    (x : SymSector ℂ (L2T L) N) :
    ∑ j : Fin N, ∑ k : Fin N, (cf κ N j * cf κ N k) • Gt L N z j (Gt L N w k x) =
      ∑ j : Fin N, ∑ k : Fin N, (cf κ N j * cf κ N k) • Gt L N w k (Gt L N z j x) := by
  have hc : Commute (normalizedTransfer L κ N z) (normalizedTransfer L κ N w) :=
    (((QuantumNLS.BoundedBetheTransfer.transfer_consequences L hκ hN).2.1 z).2.1 w).1
  have h1 : (normalizedTransfer L κ N z * normalizedTransfer L κ N w) x =
      (normalizedTransfer L κ N w * normalizedTransfer L κ N z) x := by
    rw [hc.eq]
  rw [normalizedTransfer_eq_sum, normalizedTransfer_eq_sum] at h1
  have key := comm_apply_eq L N (∑ j : Fin N, cf κ N j • Gt L N z j)
    (∑ k : Fin N, cf κ N k • Gt L N w k) (1 + Complex.exp (Complex.I * z * L))
    (1 + Complex.exp (Complex.I * w * L)) x
  have h3 : ((∑ j : Fin N, cf κ N j • Gt L N z j) * (∑ k : Fin N, cf κ N k • Gt L N w k)) x -
      ((∑ k : Fin N, cf κ N k • Gt L N w k) * (∑ j : Fin N, cf κ N j • Gt L N z j)) x = 0 := by
    rw [← key]
    exact sub_eq_zero.mpr h1
  have h2 := sub_eq_zero.mp h3
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply] at h2
  rw [sum_mul_apply_eq, sum_mul_apply_eq'] at h2
  exact h2

/-- **Finite sum of the scaled commutator expectations vanishes** (for every unit `u`). -/
theorem limSeq_sum_eq_zero (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N) (z w : ℂ)
    (u : L2T L) (hu : ‖u‖ = 1) :
    ∑ j : Fin N, ∑ k : Fin N, (cf κ N j * cf κ N k) *
      limSeq (j.val + 1) (k.val + 1) (orderedKernel L (j.val + 1) z)
        (orderedKernel L (k.val + 1) w) u N = 0 := by
  classical
  set v : HilbertTensorPower ℂ (L2T L) N := (htpow N u : HilbertTensorPower ℂ (L2T L) N) with hv_def
  set x : SymSector ℂ (L2T L) N := ⟨v, htpow_mem_symSector N u⟩ with hx_def
  have hlim : ∀ j k : Fin N, limSeq (j.val + 1) (k.val + 1) (orderedKernel L (j.val + 1) z)
      (orderedKernel L (k.val + 1) w) u N =
      (-Complex.I) * (N : ℂ) *
        (⟪v, ((Gt L N z j (Gt L N w k x) : SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ -
          ⟪v, ((Gt L N w k (Gt L N z j x) : SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ) := by
    intro j k
    unfold limSeq
    rw [dif_pos ⟨Nat.succ_le_of_lt j.2, Nat.succ_le_of_lt k.2⟩]
    unfold ExN CommQ
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, Submodule.coe_sub,
      inner_sub_right]
    rfl
  have hP : ∑ j : Fin N, ∑ k : Fin N, (cf κ N j * cf κ N k) *
      ⟪v, ((Gt L N z j (Gt L N w k x) : SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ =
      ⟪v, ((∑ j : Fin N, ∑ k : Fin N, (cf κ N j * cf κ N k) • Gt L N z j (Gt L N w k x) :
        SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ := by
    simp [inner_sum, inner_smul_right, Submodule.coe_sum, Submodule.coe_smul]
  have hQ : ∑ j : Fin N, ∑ k : Fin N, (cf κ N j * cf κ N k) *
      ⟪v, ((Gt L N w k (Gt L N z j x) : SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ =
      ⟪v, ((∑ j : Fin N, ∑ k : Fin N, (cf κ N j * cf κ N k) • Gt L N w k (Gt L N z j x) :
        SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ := by
    simp [inner_sum, inner_smul_right, Submodule.coe_sum, Submodule.coe_smul]
  have hPQ := commute_vec L κ hκ N hN z w x
  have hstep : ∀ j k : Fin N, (cf κ N j * cf κ N k) * limSeq (j.val + 1) (k.val + 1)
      (orderedKernel L (j.val + 1) z) (orderedKernel L (k.val + 1) w) u N =
      (-Complex.I) * (N : ℂ) * ((cf κ N j * cf κ N k) *
        (⟪v, ((Gt L N z j (Gt L N w k x) : SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ -
          ⟪v, ((Gt L N w k (Gt L N z j x) : SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ)) := by
    intro j k
    rw [hlim j k]
    ring
  simp only [hstep, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hP, hQ, hPQ]
  simp

end QuantumNLS.RootInvolutionCommutator

#print axioms QuantumNLS.RootInvolutionCommutator.comm_apply_eq
#print axioms QuantumNLS.RootInvolutionCommutator.commute_vec
#print axioms QuantumNLS.RootInvolutionCommutator.limSeq_sum_eq_zero
#print axioms QuantumNLS.RootInvolutionCommutator.isClosed_symSector
