import QuantumNLS.RootInvolutionCommutator
import QuantumNLS.RootInvolutionLimit
import QuantumNLS.GenericUAdjoint

/-!
# R-C4F43CA8 `thm:root-involution`, part (2D): the conjugate pairs `{s_z, s̄_w} = 0`

Source: `source/chapters/foundations/ROOT_transfer_involution.tex:98` ("The same argument with `K_{q,w}^*` proves
`{s_z, s̄_w} = 0`").

Realized inputs (frozen): `RootInvolutionCommutator` (2A: `normalizedTransfer_eq_sum`, `comm_apply_eq`, `Gt`),
`RootInvolutionLimit` (2B: `norm_limSeq_le`, `cf_tendsto`), `GenericUAdjoint` (adjoint lemma
`adjoint_genericU_N_r`), accepted `BoundedBetheTransfer.transfer_consequences` (commutation of `S_N(z)` with `S_N(w)†`),
accepted `RootOverlapLimit.root_overlap_limit`, `RootPlacementBound.norm_physicalKernel_le`.

Proved here (standard axioms only):
* `adjoint_normalizedTransfer`: `S_N(w)† = conj(1+e^{iwL}) Id + Σ_k c_k Ũ_k(K_{k+1,w}†)` (c_k real).
* `comm_conj`: vector identity from `Commute S_N(z) S_N(w)†`.
* `zero_sum_gen`: generic finite-sum vanishing of the scaled commutator expectations.
* `tsum_Tn2_eq_zero`, `norm_Tn2_le`, `double_limit_conj`: the double limit of the conjugate-pair brackets.
* `kernelProductSymbol_adjoint`: `kernelProductSymbol A† u = conj (kernelProductSymbol A u)`.
* `double_limit_conj_symbol`: `Σ' κ^{n+1}κ^{m+1} pbC(s_{n+1,z}, s̄_{m+1,w})(u) = 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology

namespace QuantumNLS.RootInvolutionConj

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.KernelDefinition
  QuantumNLS.NormalizedTransfer QuantumNLS.RootOverlapLimit QuantumNLS.RootOverlapCommutator
  QuantumNLS.HighMomentsRank QuantumNLS.RootInvolutionCommutator QuantumNLS.RootInvolutionLimit
  QuantumNLS.RootPlacementBound QuantumNLS.GenericUAdjoint QuantumNLS.SymplecticBracket

variable (L : ℝ) [Fact (0 < L)]

/-- Expansion of `(Σ_j c_j F_j)((Σ_k d_k G_k) x)`. -/
theorem expand_app_left (N : ℕ) (c d : ℕ → ℂ)
    (F G : Fin N → SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) (x : SymSector ℂ (L2T L) N) :
    (∑ j : Fin N, c j.val • F j) ((∑ k : Fin N, d k.val • G k) x) =
      ∑ k : Fin N, ∑ j : Fin N, (d k.val * c j.val) • F j (G k x) := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]

/-- Expansion of `(Σ_k d_k G_k)((Σ_j c_j F_j) x)`. -/
theorem expand_app_right (N : ℕ) (c d : ℕ → ℂ)
    (F G : Fin N → SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N) (x : SymSector ℂ (L2T L) N) :
    (∑ k : Fin N, d k.val • G k) ((∑ j : Fin N, c j.val • F j) x) =
      ∑ j : Fin N, ∑ k : Fin N, (c j.val * d k.val) • G k (F j x) := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]

/-- Adjoint of a scalar multiple (conjugate-linear): `(c • A)† = conj c • A†`. -/
theorem adjoint_smul_CLM {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (c : ℂ)
    (A : E →L[ℂ] F) :
    ContinuousLinearMap.adjoint (c • A) = (starRingEnd ℂ c) • ContinuousLinearMap.adjoint A := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp [inner_smul_left, inner_smul_right, ContinuousLinearMap.adjoint_inner_left]

/-- The adjoint of the normalized transfer, in expansion form (`c_k` real, so `conj c_k = c_k`). -/
theorem adjoint_normalizedTransfer (κ : ℝ) (N : ℕ) (w : ℂ) :
    ContinuousLinearMap.adjoint (normalizedTransfer L κ N w) =
      star (1 + Complex.exp (Complex.I * w * L)) • ContinuousLinearMap.id ℂ _ +
        ∑ k : Fin N, cf κ N k.val •
          genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2)
            (ContinuousLinearMap.adjoint (orderedKernel L (k.val + 1) w)) := by
  rw [normalizedTransfer_eq_sum]
  simp [map_add, map_sum, adjoint_smul_CLM, ContinuousLinearMap.adjoint_id, Gt, adjoint_genericU_N_r, cf,
    Complex.star_def, Complex.conj_ofReal]

/-- **Vector identity from the commutation** `[S_N(z), S_N(w)†] = 0` (accepted). -/
theorem comm_conj (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N) (z w : ℂ)
    (x : SymSector ℂ (L2T L) N) :
    ∑ j : Fin N, ∑ k : Fin N, (cf κ N j.val * cf κ N k.val) •
        genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (orderedKernel L (j.val + 1) z)
          (genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2)
            (ContinuousLinearMap.adjoint (orderedKernel L (k.val + 1) w)) x) =
      ∑ j : Fin N, ∑ k : Fin N, (cf κ N j.val * cf κ N k.val) •
        genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2)
          (ContinuousLinearMap.adjoint (orderedKernel L (k.val + 1) w))
          (genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (orderedKernel L (j.val + 1) z) x) := by
  have hc : Commute (normalizedTransfer L κ N z)
      (ContinuousLinearMap.adjoint (normalizedTransfer L κ N w)) :=
    (((QuantumNLS.BoundedBetheTransfer.transfer_consequences L hκ hN).2.1 z).2.1 w).2
  have h1 : (normalizedTransfer L κ N z * ContinuousLinearMap.adjoint (normalizedTransfer L κ N w)) x =
      (ContinuousLinearMap.adjoint (normalizedTransfer L κ N w) * normalizedTransfer L κ N z) x := by
    rw [hc.eq]
  rw [adjoint_normalizedTransfer, normalizedTransfer_eq_sum] at h1
  have key := comm_apply_eq L N (∑ j : Fin N, cf κ N j.val • Gt L N z j)
    (∑ k : Fin N, cf κ N k.val • genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2)
      (ContinuousLinearMap.adjoint (orderedKernel L (k.val + 1) w)))
    (1 + Complex.exp (Complex.I * z * L)) (star (1 + Complex.exp (Complex.I * w * L))) x
  have h2 : ((∑ j : Fin N, cf κ N j.val • Gt L N z j) *
      (∑ k : Fin N, cf κ N k.val • genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2)
        (ContinuousLinearMap.adjoint (orderedKernel L (k.val + 1) w)))) x -
      ((∑ k : Fin N, cf κ N k.val • genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2)
        (ContinuousLinearMap.adjoint (orderedKernel L (k.val + 1) w))) *
        (∑ j : Fin N, cf κ N j.val • Gt L N z j)) x = 0 := by
    rw [← key]
    exact sub_eq_zero.mpr h1
  have h3 := sub_eq_zero.mp h2
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply] at h3
  rw [expand_app_left, expand_app_right] at h3
  have e1 : ∑ j : Fin N, ∑ k : Fin N, (cf κ N j.val * cf κ N k.val) •
        genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (orderedKernel L (j.val + 1) z)
          (genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2)
            (ContinuousLinearMap.adjoint (orderedKernel L (k.val + 1) w)) x) =
      ∑ k : Fin N, ∑ j : Fin N, (cf κ N k.val * cf κ N j.val) •
        genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (orderedKernel L (j.val + 1) z)
          (genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2)
            (ContinuousLinearMap.adjoint (orderedKernel L (k.val + 1) w)) x) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun j _ => by rw [mul_comm]))
  rw [e1]
  exact h3

/-- Finite sum of the scaled commutator expectations vanishes for a commuting pair of families. -/
theorem zero_sum_gen (KA KB : ∀ n : ℕ, BoundedSymmetricKernel (L2T L) n) (N : ℕ) (hN : 0 < N)
    (cc dd : ℕ → ℂ) (u : L2T L) (hu : ‖u‖ = 1)
    (hcomm : ∀ x : SymSector ℂ (L2T L) N,
      ∑ j : Fin N, ∑ k : Fin N, (cc j.val * dd k.val) •
          genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1))
            (genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1)) x) =
        ∑ j : Fin N, ∑ k : Fin N, (cc j.val * dd k.val) •
          genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1))
            (genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1)) x)) :
    ∑ j : Fin N, ∑ k : Fin N, (cc j.val * dd k.val) *
      limSeq (j.val + 1) (k.val + 1) (KA (j.val + 1)) (KB (k.val + 1)) u N = 0 := by
  classical
  set v : HilbertTensorPower ℂ (L2T L) N := (htpow N u : HilbertTensorPower ℂ (L2T L) N) with hv_def
  set x : SymSector ℂ (L2T L) N := ⟨v, htpow_mem_symSector N u⟩ with hx_def
  have hlim : ∀ j k : Fin N, limSeq (j.val + 1) (k.val + 1) (KA (j.val + 1)) (KB (k.val + 1)) u N =
      (-Complex.I) * (N : ℂ) *
        (⟪v, ((genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1))
            (genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1)) x) :
              SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ -
          ⟪v, ((genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1))
            (genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1)) x) :
              SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ) := by
    intro j k
    unfold limSeq
    rw [dif_pos ⟨Nat.succ_le_of_lt j.2, Nat.succ_le_of_lt k.2⟩]
    unfold ExN CommQ
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, Submodule.coe_sub,
      inner_sub_right]
    rfl
  have hP : ∑ j : Fin N, ∑ k : Fin N, (cc j.val * dd k.val) *
      ⟪v, ((genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1))
            (genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1)) x) :
              SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ =
      ⟪v, ((∑ j : Fin N, ∑ k : Fin N, (cc j.val * dd k.val) •
          genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1))
            (genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1)) x) :
              SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ := by
    simp [inner_sum, inner_smul_right, Submodule.coe_sum, Submodule.coe_smul]
  have hQ : ∑ j : Fin N, ∑ k : Fin N, (cc j.val * dd k.val) *
      ⟪v, ((genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1))
            (genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1)) x) :
              SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ =
      ⟪v, ((∑ j : Fin N, ∑ k : Fin N, (cc j.val * dd k.val) •
          genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1))
            (genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1)) x) :
              SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ := by
    simp [inner_sum, inner_smul_right, Submodule.coe_sum, Submodule.coe_smul]
  have hPQ := hcomm x
  have hstep : ∀ j k : Fin N, (cc j.val * dd k.val) * limSeq (j.val + 1) (k.val + 1)
      (KA (j.val + 1)) (KB (k.val + 1)) u N =
      (-Complex.I) * (N : ℂ) * ((cc j.val * dd k.val) *
        (⟪v, ((genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1))
            (genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1)) x) :
              SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ -
          ⟪v, ((genericU_N_r N (k.val + 1) (Nat.succ_le_of_lt k.2) (KB (k.val + 1))
            (genericU_N_r N (j.val + 1) (Nat.succ_le_of_lt j.2) (KA (j.val + 1)) x) :
              SymSector ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N)⟫_ℂ)) := by
    intro j k
    rw [hlim j k]
    ring
  simp only [hstep, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hP, hQ, hPQ]
  simp

/-- The `(n,m)` term of the conjugate-pair double series. -/
def Tn2 (κ : ℝ) (N : ℕ) (z w : ℂ) (u : L2T L) (nm : ℕ × ℕ) : ℂ :=
  cf κ N nm.1 * cf κ N nm.2 *
    limSeq (nm.1 + 1) (nm.2 + 1) (orderedKernel L (nm.1 + 1) z)
      (ContinuousLinearMap.adjoint (orderedKernel L (nm.2 + 1) w)) u N

/-- The finite sums of `Tn2` vanish for `N ≥ 1`. -/
theorem tsum_Tn2_eq_zero (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ)
    (hN : 0 < N) : ∑' nm : ℕ × ℕ, Tn2 L κ N z w u nm = 0 := by
  rw [tsum_eq_sum (s := Finset.range N ×ˢ Finset.range N)]
  · rw [Finset.sum_product]
    simp only [Finset.sum_range]
    exact zero_sum_gen L (fun n => orderedKernel L n z)
      (fun n => ContinuousLinearMap.adjoint (orderedKernel L n w)) N hN (fun j => cf κ N j)
      (fun j => cf κ N j) u hu (comm_conj L κ hκ N hN z w)
  · rintro ⟨n, m⟩ hnm
    have h1 : ¬ (n + 1 ≤ N ∧ m + 1 ≤ N) := by
      intro h
      apply hnm
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    unfold Tn2 limSeq
    rw [dif_neg h1, mul_zero]


/-- **Domination of the `(n,m)` term** (uniform in `N ≥ 1`):
`‖Tn_N(n,m)‖ ≤ 8 (n+1)(m+1) (κ/Im z)^{n+1} (κ/Im w)^{m+1}`. -/
theorem norm_Tn2_le (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ) (hN : 0 < N) (z w : ℂ) (hz : κ < z.im)
    (hw : κ < w.im) (u : L2T L) (hu : ‖u‖ = 1) (nm : ℕ × ℕ) :
    ‖Tn2 L κ N z w u nm‖ ≤
      8 * ((((nm.1 : ℝ) + 1) * (κ / z.im) ^ (nm.1 + 1)) *
        (((nm.2 : ℝ) + 1) * (κ / w.im) ^ (nm.2 + 1))) := by
  obtain ⟨n, m⟩ := nm
  have hη : 0 < z.im := lt_of_le_of_lt hκ hz
  have hη' : 0 < w.im := lt_of_le_of_lt hκ hw
  have hr : 0 ≤ κ / z.im := div_nonneg hκ hη.le
  have hr' : 0 ≤ κ / w.im := div_nonneg hκ hη'.le
  have hRHS : 0 ≤ 8 * ((((n : ℝ) + 1) * (κ / z.im) ^ (n + 1)) *
      (((m : ℝ) + 1) * (κ / w.im) ^ (m + 1))) :=
    mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hr _))
      (mul_nonneg (by positivity) (pow_nonneg hr' _)))
  by_cases h1 : n + 1 ≤ N ∧ m + 1 ≤ N
  · obtain ⟨hf0, -, hf1⟩ := fallR_bounds N hN (n + 1) h1.1
    obtain ⟨hg0, -, hg1⟩ := fallR_bounds N hN (m + 1) h1.2
    have hc1 : ‖cf κ N n‖ ≤ κ ^ (n + 1) := by
      unfold cf
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (pow_nonneg hκ _) hf0)]
      exact mul_le_of_le_one_right (pow_nonneg hκ _) hf1
    have hc2 : ‖cf κ N m‖ ≤ κ ^ (m + 1) := by
      unfold cf
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (pow_nonneg hκ _) hg0)]
      exact mul_le_of_le_one_right (pow_nonneg hκ _) hg1
    have hl := norm_limSeq_le L N (n + 1) (m + 1) h1.1 h1.2 (orderedKernel L (n + 1) z)
      (ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)) u hu
    have hA : ‖orderedKernel L (n + 1) z‖ ≤ 2 * (z.im)⁻¹ ^ (n + 1) :=
      norm_physicalKernel_le (L := L) (by omega) z hη
    have hB : ‖ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)‖ ≤ 2 * (w.im)⁻¹ ^ (m + 1) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact norm_physicalKernel_le (L := L) (by omega) w hη'
    have e1 : (κ / z.im) ^ (n + 1) = κ ^ (n + 1) * (z.im)⁻¹ ^ (n + 1) := by
      rw [div_eq_mul_inv, mul_pow]
    have e2 : (κ / w.im) ^ (m + 1) = κ ^ (m + 1) * (w.im)⁻¹ ^ (m + 1) := by
      rw [div_eq_mul_inv, mul_pow]
    have hα : κ ^ (n + 1) * ‖orderedKernel L (n + 1) z‖ ≤ 2 * (κ / z.im) ^ (n + 1) := by
      rw [e1]
      calc κ ^ (n + 1) * ‖orderedKernel L (n + 1) z‖
          ≤ κ ^ (n + 1) * (2 * (z.im)⁻¹ ^ (n + 1)) :=
            mul_le_mul_of_nonneg_left hA (pow_nonneg hκ _)
        _ = 2 * (κ ^ (n + 1) * (z.im)⁻¹ ^ (n + 1)) := by ring
    have hβ : κ ^ (m + 1) * ‖ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)‖ ≤ 2 * (κ / w.im) ^ (m + 1) := by
      rw [e2]
      calc κ ^ (m + 1) * ‖ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)‖
          ≤ κ ^ (m + 1) * (2 * (w.im)⁻¹ ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left hB (pow_nonneg hκ _)
        _ = 2 * (κ ^ (m + 1) * (w.im)⁻¹ ^ (m + 1)) := by ring
    have hnA : 0 ≤ κ ^ (n + 1) * ‖orderedKernel L (n + 1) z‖ := by positivity
    have hnB : 0 ≤ κ ^ (m + 1) * ‖ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)‖ := by positivity
    have hpq : (0 : ℝ) ≤ 2 * (((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) := by positivity
    calc ‖Tn2 L κ N z w u (n, m)‖
        = ‖cf κ N n‖ * ‖cf κ N m‖ *
            ‖limSeq (n + 1) (m + 1) (orderedKernel L (n + 1) z) (ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)) u N‖ := by
          unfold Tn2
          rw [norm_mul, norm_mul]
      _ ≤ κ ^ (n + 1) * κ ^ (m + 1) *
            (2 * (((n + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) * ‖orderedKernel L (n + 1) z‖ *
              ‖ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)‖) :=
          mul_le_mul (mul_le_mul hc1 hc2 (norm_nonneg _) (pow_nonneg hκ _)) hl
            (norm_nonneg _) (mul_nonneg (pow_nonneg hκ _) (pow_nonneg hκ _))
      _ = (κ ^ (n + 1) * ‖orderedKernel L (n + 1) z‖) * (κ ^ (m + 1) * ‖ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)‖) *
            (2 * (((n : ℝ) + 1)) * ((m : ℝ) + 1)) := by push_cast; ring
      _ ≤ (2 * (κ / z.im) ^ (n + 1)) * (2 * (κ / w.im) ^ (m + 1)) *
            (2 * (((n : ℝ) + 1)) * ((m : ℝ) + 1)) := by
          refine mul_le_mul (mul_le_mul hα hβ hnB (by positivity)) le_rfl ?_ (by positivity)
          positivity
      _ = 8 * ((((n : ℝ) + 1) * (κ / z.im) ^ (n + 1)) *
            (((m : ℝ) + 1) * (κ / w.im) ^ (m + 1))) := by ring
  · have h0 : Tn2 L κ N z w u (n, m) = 0 := by
      show cf κ N n * cf κ N m * limSeq (n + 1) (m + 1) (orderedKernel L (n + 1) z)
        (ContinuousLinearMap.adjoint (orderedKernel L (m + 1) w)) u N = 0
      unfold limSeq
      rw [dif_neg h1, mul_zero]
    rw [h0, norm_zero]
    exact hRHS


/-- Summability of the bound (as in 2B). -/
theorem summable_aux2 (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ (n + 1)) := by
  have hr' : ‖r‖ < 1 := by rw [Real.norm_of_nonneg h0]; exact h1
  have h2 : Summable (fun n : ℕ => (n : ℝ) ^ (1 : ℕ) * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr'
  have h3 : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 : ℕ) * r ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr h2
  refine h3.congr (fun n => ?_)
  push_cast
  ring

/-- **Double limit of the conjugate-pair scaled commutators.** For `0 < κ < Im z`, `κ < Im w`, unit `u`:
`Σ'_{(n,m)} κ^{n+1} κ^{m+1} pbC(K_{n+1,z}, (K_{m+1,w})†)(u) = 0`. -/
theorem double_limit_conj (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im)
    (u : L2T L) (hu : ‖u‖ = 1) :
    ∑' nm : ℕ × ℕ, ((κ ^ (nm.1 + 1) : ℝ) : ℂ) * ((κ ^ (nm.2 + 1) : ℝ) : ℂ) *
      pbC (kernelProductSymbol (orderedKernel L (nm.1 + 1) z))
        (kernelProductSymbol (ContinuousLinearMap.adjoint (orderedKernel L (nm.2 + 1) w))) u = 0 := by
  have hκ0 : 0 ≤ κ := hκ.le
  have hη : 0 < z.im := lt_of_le_of_lt hκ0 hz
  have hη' : 0 < w.im := lt_of_le_of_lt hκ0 hw
  have hr : 0 ≤ κ / z.im := div_nonneg hκ0 hη.le
  have hr' : 0 ≤ κ / w.im := div_nonneg hκ0 hη'.le
  have hr1 : κ / z.im < 1 := (div_lt_one hη).mpr hz
  have hr1' : κ / w.im < 1 := (div_lt_one hη').mpr hw
  have hsf := summable_aux2 (κ / z.im) hr hr1
  have hsg := summable_aux2 (κ / w.im) hr' hr1'
  have hsum : Summable (fun nm : ℕ × ℕ => 8 * ((((nm.1 : ℝ) + 1) * (κ / z.im) ^ (nm.1 + 1)) *
      (((nm.2 : ℝ) + 1) * (κ / w.im) ^ (nm.2 + 1)))) :=
    ((hsf.mul_of_nonneg hsg
      (fun n => mul_nonneg (by positivity) (pow_nonneg hr _))
      (fun m => mul_nonneg (by positivity) (pow_nonneg hr' _))).mul_left 8)
  have hpt : ∀ nm : ℕ × ℕ, Tendsto (fun N : ℕ => Tn2 L κ N z w u nm) atTop
      (𝓝 (((κ ^ (nm.1 + 1) : ℝ) : ℂ) * ((κ ^ (nm.2 + 1) : ℝ) : ℂ) *
        pbC (kernelProductSymbol (orderedKernel L (nm.1 + 1) z))
          (kernelProductSymbol (ContinuousLinearMap.adjoint (orderedKernel L (nm.2 + 1) w))) u)) := by
    intro nm
    exact ((cf_tendsto κ nm.1).mul (cf_tendsto κ nm.2)).mul
      (root_overlap_limit (nm.1 + 1) (nm.2 + 1) (orderedKernel L (nm.1 + 1) z)
        (ContinuousLinearMap.adjoint (orderedKernel L (nm.2 + 1) w)) u hu)
  have hbd : ∀ᶠ N : ℕ in atTop, ∀ nm : ℕ × ℕ, ‖Tn2 L κ N z w u nm‖ ≤
      8 * ((((nm.1 : ℝ) + 1) * (κ / z.im) ^ (nm.1 + 1)) *
        (((nm.2 : ℝ) + 1) * (κ / w.im) ^ (nm.2 + 1))) :=
    eventually_atTop.2 ⟨1, fun N hN nm => norm_Tn2_le L κ hκ0 N (by omega) z w hz hw u hu nm⟩
  have hlim := tendsto_tsum_of_dominated_convergence hsum hpt hbd
  have hz0 : Tendsto (fun N : ℕ => ∑' nm : ℕ × ℕ, Tn2 L κ N z w u nm) atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (tsum_Tn2_eq_zero L κ hκ z w u hu N (by omega)).symm
  exact (tendsto_nhds_unique hz0 hlim).symm

/-- **Conjugate symbol.** `s_{A†}(u) = conj s_A(u)` for the product symbol of a bounded symmetric kernel. -/
theorem kernelProductSymbol_adjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {r : ℕ} (A : BoundedSymmetricKernel H r) (u : H) :
    kernelProductSymbol (ContinuousLinearMap.adjoint A) u = conj (kernelProductSymbol A u) := by
  unfold kernelProductSymbol
  exact (ContinuousLinearMap.adjoint_inner_right A
    (⟨(htpow r u : HilbertTensorPower ℂ H r), htpow_mem_symSector r u⟩ : SymSector ℂ H r)
    (⟨(htpow r u : HilbertTensorPower ℂ H r), htpow_mem_symSector r u⟩ : SymSector ℂ H r)).trans
    (inner_conj_symm _ _).symm

/-- **R-C4F43CA8 part (2D): `{s_z, s̄_w} = 0` as the fixed-order-summed bracket identity.** -/
theorem double_limit_conj_symbol (κ : ℝ) (hκ : 0 < κ) (z w : ℂ) (hz : κ < z.im) (hw : κ < w.im)
    (u : L2T L) (hu : ‖u‖ = 1) :
    ∑' nm : ℕ × ℕ, ((κ ^ (nm.1 + 1) : ℝ) : ℂ) * ((κ ^ (nm.2 + 1) : ℝ) : ℂ) *
      pbC (kernelProductSymbol (orderedKernel L (nm.1 + 1) z))
        (fun v => conj (kernelProductSymbol (orderedKernel L (nm.2 + 1) w) v)) u = 0 := by
  have h := double_limit_conj L κ hκ z w hz hw u hu
  refine Eq.trans (tsum_congr (fun nm => ?_)) h
  rw [show (fun v => conj (kernelProductSymbol (orderedKernel L (nm.2 + 1) w) v)) =
      kernelProductSymbol (ContinuousLinearMap.adjoint (orderedKernel L (nm.2 + 1) w)) from
      funext fun v => (kernelProductSymbol_adjoint _ v).symm]

end QuantumNLS.RootInvolutionConj

#print axioms QuantumNLS.RootInvolutionConj.adjoint_normalizedTransfer
#print axioms QuantumNLS.RootInvolutionConj.comm_conj
#print axioms QuantumNLS.RootInvolutionConj.zero_sum_gen
#print axioms QuantumNLS.RootInvolutionConj.tsum_Tn2_eq_zero
#print axioms QuantumNLS.RootInvolutionConj.norm_Tn2_le
#print axioms QuantumNLS.RootInvolutionConj.double_limit_conj
#print axioms QuantumNLS.RootInvolutionConj.kernelProductSymbol_adjoint
#print axioms QuantumNLS.RootInvolutionConj.double_limit_conj_symbol
