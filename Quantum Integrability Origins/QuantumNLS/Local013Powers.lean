import QuantumNLS.Local013ProductLimit
import QuantumNLS.GenericPlacementsZero

/-!
# LOCAL-013 `reset:principal-calculus`, stage L3a: the identity family and powers

The functional-calculus clause of LOCAL-013 (`quantum_periods.tex:118-140`: "one first truncates
the scalar series uniformly in the kernel norm and then passes to the limit in each of its
finitely many products") uses the finitely many products `A_N^k`. This stage builds them as
iterated LOCAL-011 chosen products and applies the product clause (`product_converges`) `k` times.

Proved here (standard axioms only):
* `unitList N`: the kernel list with the identity in degree `0`; it represents `Id` on
  `Sym^N H` (`represented_unitList`), has radius bound `≤ 1`, converges to `unitLim`
  (`unit_converges`), and `symbol unitLim = 1`.
* `powList A k N` (`A_N^k` as iterated chosen products) and `powLim Alim k`
  (`powLim (k+1) = prodLim Alim (powLim k)`).
* `powList_radius_le`: `‖A_N^k‖_R ≤ ‖A_N‖_R^k` (LOCAL-011 product bound).
* `pow_converges`: on `R ≥ 1`, `A_N^k` converges with limits `powLim Alim k`, represents
  `(A_N)^k`, and has symbol `a^k` on `‖v‖² ≤ R`.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace BigOperators
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementProduct QuantumNLS.KernelConvergence QuantumNLS.LocalPlacement
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011 QuantumNLS.Local013ProductSymbol
  QuantumNLS.Local013ProductLimit

namespace QuantumNLS.Local013Powers

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The identity family -/

/-- The identity kernel list: the identity of `Sym^0 H` in degree `0`, zero elsewhere. -/
def unitList (N : ℕ) : KernelList (H := H) N :=
  kernelSpike (H := H) (n := 0) (ContinuousLinearMap.id ℂ (SymSector ℂ H 0))

/-- The limiting identity kernels. -/
def unitLim (p : ℕ) : BoundedSymmetricKernel H p :=
  if h : p = 0 then castSymSectorOperator h.symm (ContinuousLinearMap.id ℂ (SymSector ℂ H 0))
  else 0

theorem coeffAt_unitList {N p : ℕ} (hp : p ≤ N) :
    coeffAt (fun N => unitList (H := H) N) N p = unitLim p := by
  unfold coeffAt
  rw [dif_pos hp]
  rfl

theorem genericU_zero_kernel {N n : ℕ} (hn : n ≤ N) :
    genericU_N_r N n hn (0 : BoundedSymmetricKernel H n) = 0 := by
  calc genericU_N_r N n hn (0 : BoundedSymmetricKernel H n)
      = genericU_N_r N n hn ((0 : ℂ) • (0 : BoundedSymmetricKernel H n)) := by
        rw [zero_smul_kernel]
    _ = (0 : ℂ) • genericU_N_r N n hn (0 : BoundedSymmetricKernel H n) :=
        QuantumNLS.RootOverlapLimit.genericU_smul N n hn 0 0
    _ = 0 := by ext x; simp

omit [CompleteSpace H] in
theorem zeroKernelScalar_id :
    QuantumNLS.GenericPlacementsZero.zeroKernelScalar (H := H)
      (ContinuousLinearMap.id ℂ (SymSector ℂ H 0)) = 1 := by
  unfold QuantumNLS.GenericPlacementsZero.zeroKernelScalar
  simp

theorem represented_unitList (N : ℕ) :
    QuantumNLS.RadiusBound.represented (unitList (H := H) N) =
      ContinuousLinearMap.id ℂ (SymSector ℂ H N) := by
  classical
  unfold QuantumNLS.RadiusBound.represented
  rw [Finset.sum_eq_single (⟨0, Nat.succ_pos N⟩ : Fin (N + 1))]
  · rw [QuantumNLS.RadiusBound.Q_eq_genericU_N_r]
    have h := QuantumNLS.LocalPlacement.genericU_N_0_eq_scalar (H := H) N
      (ContinuousLinearMap.id ℂ (SymSector ℂ H 0))
    rw [zeroKernelScalar_id, one_smul] at h
    exact h
  · intro j _ hj
    have hj0 : j.1 ≠ 0 := fun h => hj (Fin.ext h)
    rw [QuantumNLS.RadiusBound.Q_eq_genericU_N_r]
    have hz : unitList (H := H) N j = 0 := by
      unfold unitList kernelSpike
      rw [dif_neg hj0]
    rw [hz]
    exact genericU_zero_kernel _
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem radiusBound_unitList {R : ℝ} (N : ℕ) :
    QuantumNLS.RadiusBound.radiusBound R (unitList (H := H) N) ≤ 1 := by
  classical
  unfold QuantumNLS.RadiusBound.radiusBound
  rw [Finset.sum_eq_single (⟨0, Nat.succ_pos N⟩ : Fin (N + 1))]
  · simp only [pow_zero, one_mul]
    unfold unitList kernelSpike
    rw [dif_pos rfl]
    exact ContinuousLinearMap.norm_id_le
  · intro j _ hj
    have hj0 : j.1 ≠ 0 := fun h => hj (Fin.ext h)
    unfold unitList kernelSpike
    rw [dif_neg hj0]
    simp [ContinuousLinearMap.opNorm_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem unit_converges (R : ℝ) :
    ConvergesOnRadius R (fun N => unitList (H := H) N) unitLim := by
  refine ⟨⟨1, fun N => radiusBound_unitList N⟩, fun p => ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop p] with N hN
  rw [coeffAt_unitList hN, sub_self]
  simp [ContinuousLinearMap.opNorm_zero]

theorem symbol_unitLim (v : H) : symbol (unitLim (H := H)) v = 1 := by
  unfold symbol
  rw [tsum_eq_single 0]
  · unfold unitLim
    rw [dif_pos rfl]
    unfold kernelProductSymbol
    have hn : ‖(htpow 0 v : HilbertTensorPower ℂ H 0)‖ = 1 := by rw [norm_htpow, pow_zero]
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (htpow 0 v : HilbertTensorPower ℂ H 0)
    rw [hn] at h2
    exact h2.trans (by norm_num)
  · intro p hp
    unfold unitLim
    rw [dif_neg hp]
    exact kps_zero v

/-! ### Powers -/

/-- `A_N^k` as iterated LOCAL-011 chosen products (`A_N^{k+1} = A_N · A_N^k`). -/
def powList (A : ∀ N : ℕ, KernelList (H := H) N) : ℕ → ∀ N : ℕ, KernelList (H := H) N
  | 0 => fun N => unitList N
  | k + 1 => fun N => chosenProductKernelList N (A N) (powList A k N)

/-- The limiting kernels of `A_N^k`. -/
def powLim (Alim : ∀ p : ℕ, BoundedSymmetricKernel H p) : ℕ → ∀ p : ℕ, BoundedSymmetricKernel H p
  | 0 => unitLim
  | k + 1 => prodLim Alim (powLim Alim k)

theorem powList_radius_le {R : ℝ} (hR : 1 ≤ R) (A : ∀ N : ℕ, KernelList (H := H) N) (k N : ℕ) :
    QuantumNLS.RadiusBound.radiusBound R (powList A k N) ≤
      (QuantumNLS.RadiusBound.radiusBound R (A N)) ^ k := by
  induction k with
  | zero => simpa [powList] using radiusBound_unitList (R := R) N
  | succ k ih =>
    have h0 : 0 ≤ QuantumNLS.RadiusBound.radiusBound R (A N) :=
      QuantumNLS.RadiusBound.radiusBound_nonneg (by linarith) (A N)
    calc QuantumNLS.RadiusBound.radiusBound R (powList A (k + 1) N)
        ≤ QuantumNLS.RadiusBound.radiusBound R (A N) *
            QuantumNLS.RadiusBound.radiusBound R (powList A k N) :=
          chosenProductKernelList_radius_le hR (A N) (powList A k N)
      _ ≤ QuantumNLS.RadiusBound.radiusBound R (A N) *
            (QuantumNLS.RadiusBound.radiusBound R (A N)) ^ k :=
          mul_le_mul_of_nonneg_left ih h0
      _ = _ := by rw [pow_succ']

/-- **Powers of a convergent family.** -/
theorem pow_converges {R : ℝ} (hR : 1 ≤ R) {A : ∀ N : ℕ, KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hA : ConvergesOnRadius R A Alim) (k : ℕ) :
    ConvergesOnRadius R (powList A k) (powLim Alim k) ∧
      (∀ N, QuantumNLS.RadiusBound.represented (powList A k N) =
        (QuantumNLS.RadiusBound.represented (A N)) ^ k) ∧
      ∀ v : H, ‖v‖ ^ 2 ≤ R → symbol (powLim Alim k) v = (symbol Alim v) ^ k := by
  induction k with
  | zero =>
    refine ⟨unit_converges R, fun N => ?_, fun v _ => ?_⟩
    · simp only [powList, pow_zero]
      exact represented_unitList N
    · simp only [powLim, pow_zero]
      exact symbol_unitLim v
  | succ k ih =>
    obtain ⟨hc, hrep, hsym⟩ := product_converges hR hA ih.1
    refine ⟨hc, fun N => ?_, fun v hv => ?_⟩
    · simp only [powList]
      rw [hrep N, ih.2.1 N, pow_succ']
      rfl
    · simp only [powLim]
      rw [hsym v hv, ih.2.2 v hv, pow_succ']

end QuantumNLS.Local013Powers

#print axioms QuantumNLS.Local013Powers.represented_unitList
#print axioms QuantumNLS.Local013Powers.unit_converges
#print axioms QuantumNLS.Local013Powers.symbol_unitLim
#print axioms QuantumNLS.Local013Powers.powList_radius_le
#print axioms QuantumNLS.Local013Powers.pow_converges
