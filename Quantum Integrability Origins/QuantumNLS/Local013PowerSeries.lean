import QuantumNLS.Local013Powers

/-!
# LOCAL-013 `reset:principal-calculus`, stage L3b: norm-convergent scalar power series
(`source-text/chapters/local/quantum_periods.tex:118-140`)

Source: "Convergent families are closed under ... norm-convergent scalar power series whose absolute
kernel norms lie strictly inside their convergence disks, after reducing the radius if necessary.
... The same argument, with the absolute scalar power-series majorant, proves the
functional-calculus assertion. For example, one first truncates the scalar series uniformly in the
kernel norm and then passes to the limit in each of its finitely many products. No interchange of
an unbounded word sum is used."

Formalization. `f(z) = Σ c_k z^k` with `Σ ‖c_k‖ ρ^k < ∞` (the disk of radius `ρ` lies in the disk
of convergence) and the absolute kernel norms `‖A_N‖_r = Σ_p r^p ‖A_{p,N}‖ ≤ M < ρ` on the radius
`r` (after radius reduction). The family is `f(A)_N = Σ_k c_k A_N^k` with `A_N^k` the iterated
LOCAL-011 chosen products (stage L3a), summed in the finite-dimensional space of kernel lists.

Proved here (standard axioms only):
* `psList c A N = Σ' k, c_k • powList A k N` represents `Σ' k, c_k (A_N)^k`
  (`represented_psList`), and has `‖f(A)_N‖_r ≤ Σ' ‖c_k‖ M^k` (`radiusBound_psList_le`).
* every fixed-degree coefficient converges (`tendsto_coeff_ps`, dominated convergence with the
  absolute majorant `‖c_k‖ M^k`; each truncation term is a finite product, stage L3a);
* `powerSeries_converges`: the family converges on `r` with limiting kernels
  `psLim c Alim j = Σ' k, c_k (powLim Alim k)_j`, and its symbol is `Σ' k, c_k a(v)^k` on
  `‖v‖² ≤ r`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.KernelConvergence
  QuantumNLS.LocalPlacement QuantumNLS.Local013ProductSymbol QuantumNLS.Local013Powers

namespace QuantumNLS.Local013PowerSeries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Norms of kernel lists -/

theorem norm_coeff_le_radiusBound {r : ℝ} (hr : 1 ≤ r) {N : ℕ} (L : KernelList (H := H) N)
    (p : Fin (N + 1)) : ‖L p‖ ≤ QuantumNLS.RadiusBound.radiusBound r L := by
  unfold QuantumNLS.RadiusBound.radiusBound
  calc ‖L p‖ ≤ r ^ p.1 * ‖L p‖ := le_mul_of_one_le_left (norm_nonneg (L p)) (one_le_pow₀ hr)
    _ ≤ ∑ q : Fin (N + 1), r ^ q.1 * ‖L q‖ :=
      Finset.single_le_sum (f := fun q : Fin (N + 1) => r ^ q.1 * ‖L q‖)
        (fun q _ => mul_nonneg (pow_nonneg (by linarith) _) (norm_nonneg (L q))) (Finset.mem_univ p)

theorem norm_coeffAt_le {r : ℝ} (hr : 1 ≤ r) (A : ∀ N : ℕ, KernelList (H := H) N) (N j : ℕ) :
    ‖coeffAt A N j‖ ≤ QuantumNLS.RadiusBound.radiusBound r (A N) := by
  unfold coeffAt
  split_ifs with h
  · exact norm_coeff_le_radiusBound hr (A N) _
  · rw [ContinuousLinearMap.opNorm_zero]
    exact QuantumNLS.RadiusBound.radiusBound_nonneg (by linarith) (A N)

/-! ### The power-series family -/

/-- `f(A)_N = Σ_k c_k A_N^k` as a kernel list. -/
def psList (c : ℕ → ℂ) (A : ∀ N : ℕ, KernelList (H := H) N) (N : ℕ) : KernelList (H := H) N :=
  fun p => ∑' k, c k • powList A k N p

/-- The limiting kernels `Σ_k c_k (A^k)_j`. -/
def psLim (c : ℕ → ℂ) (Alim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j : ℕ) :
    BoundedSymmetricKernel H j :=
  ∑' k, c k • powLim Alim k j

section Family

variable {r M ρ : ℝ} {c : ℕ → ℂ} {A : ∀ N : ℕ, KernelList (H := H) N}

theorem summable_majorant (hM0 : 0 ≤ M) (hMρ : M < ρ) (hc : Summable fun k => ‖c k‖ * ρ ^ k) :
    Summable fun k => ‖c k‖ * M ^ k :=
  Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hM0 hMρ.le k) (norm_nonneg _)) hc

theorem radiusBound_powList_le (hr : 1 ≤ r) (hM : ∀ N, QuantumNLS.RadiusBound.radiusBound r (A N) ≤ M)
    (k N : ℕ) : QuantumNLS.RadiusBound.radiusBound r (powList A k N) ≤ M ^ k :=
  (powList_radius_le hr A k N).trans
    (pow_le_pow_left₀ (QuantumNLS.RadiusBound.radiusBound_nonneg (by linarith) (A N)) (hM N) k)

set_option maxHeartbeats 1000000 in
theorem summable_psCoord (hr : 1 ≤ r) (hM : ∀ N, QuantumNLS.RadiusBound.radiusBound r (A N) ≤ M)
    (hb : Summable fun k => ‖c k‖ * M ^ k) (N : ℕ) (p : Fin (N + 1)) :
    Summable fun k => c k • powList A k N p :=
  Summable.of_norm_bounded (E := BoundedSymmetricKernel H p.1) hb
    (fun k => (QuantumNLS.RadiusBound.norm_smul_kernel (c k) (powList A k N p)).le.trans
    (mul_le_mul_of_nonneg_left ((norm_coeff_le_radiusBound hr (powList A k N) p).trans
      (radiusBound_powList_le hr hM k N)) (norm_nonneg (c k))))

theorem coeffAt_psList {N j : ℕ} (hjN : j ≤ N) :
    coeffAt (psList c A) N j = ∑' k, c k • coeffAt (powList A k) N j := by
  unfold coeffAt
  simp only [dif_pos hjN]
  rfl

end Family

/-! ### Uniform radius bound, coefficient limits, represented operator -/

section Family2

variable {r M : ℝ} {c : ℕ → ℂ} {A : ∀ N : ℕ, KernelList (H := H) N}
  {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p}

set_option maxHeartbeats 2000000 in
theorem radiusBound_psList_le (hr : 1 ≤ r)
    (hM : ∀ N, QuantumNLS.RadiusBound.radiusBound r (A N) ≤ M)
    (hb : Summable fun k => ‖c k‖ * M ^ k) (N : ℕ) :
    QuantumNLS.RadiusBound.radiusBound r (psList c A N) ≤ ∑' k, ‖c k‖ * M ^ k := by
  have hs_p : ∀ p : Fin (N + 1), Summable fun k => ‖c k‖ * ‖powList A k N p‖ := fun p =>
    Summable.of_nonneg_of_le (fun k => mul_nonneg (norm_nonneg (c k)) (norm_nonneg (powList A k N p)))
      (fun k => mul_le_mul_of_nonneg_left ((norm_coeff_le_radiusBound hr (powList A k N) p).trans
        (radiusBound_powList_le hr hM k N)) (norm_nonneg (c k))) hb
  have hcoord : ∀ p : Fin (N + 1),
      ‖psList c A N p‖ ≤ ∑' k, ‖c k‖ * ‖powList A k N p‖ := by
    intro p
    unfold psList
    have hle : ∀ k, ‖c k • powList A k N p‖ ≤ ‖c k‖ * ‖powList A k N p‖ := fun k =>
      (QuantumNLS.RadiusBound.norm_smul_kernel (c k) (powList A k N p)).le
    have hsn : Summable fun k => ‖c k • powList A k N p‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg (c k • powList A k N p)) hle (hs_p p)
    exact (norm_tsum_le_tsum_norm (E := BoundedSymmetricKernel H p.1) hsn).trans
      (Summable.tsum_le_tsum hle hsn (hs_p p))
  have hrow : ∀ k, ∑ p : Fin (N + 1), r ^ p.1 * (‖c k‖ * ‖powList A k N p‖) ≤ ‖c k‖ * M ^ k := by
    intro k
    calc ∑ p : Fin (N + 1), r ^ p.1 * (‖c k‖ * ‖powList A k N p‖)
        = ‖c k‖ * QuantumNLS.RadiusBound.radiusBound r (powList A k N) := by
          rw [QuantumNLS.RadiusBound.radiusBound, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)
      _ ≤ ‖c k‖ * M ^ k :=
          mul_le_mul_of_nonneg_left (radiusBound_powList_le hr hM k N) (norm_nonneg (c k))
  have hsum2 : ∀ p : Fin (N + 1), Summable fun k => r ^ p.1 * (‖c k‖ * ‖powList A k N p‖) :=
    fun p => (hs_p p).mul_left _
  calc QuantumNLS.RadiusBound.radiusBound r (psList c A N)
      = ∑ p : Fin (N + 1), r ^ p.1 * ‖psList c A N p‖ := rfl
    _ ≤ ∑ p : Fin (N + 1), r ^ p.1 * ∑' k, ‖c k‖ * ‖powList A k N p‖ :=
        Finset.sum_le_sum (fun p _ => mul_le_mul_of_nonneg_left (hcoord p)
          (pow_nonneg (by linarith) _))
    _ = ∑' k, ∑ p : Fin (N + 1), r ^ p.1 * (‖c k‖ * ‖powList A k N p‖) := by
        rw [Summable.tsum_finsetSum (fun p _ => hsum2 p)]
        exact Finset.sum_congr rfl (fun p _ => (tsum_mul_left).symm)
    _ ≤ ∑' k, ‖c k‖ * M ^ k := by
        refine Summable.tsum_le_tsum hrow ?_ hb
        exact Summable.of_nonneg_of_le
          (fun k => Finset.sum_nonneg (fun p _ => by positivity)) hrow hb

theorem tendsto_coeff_ps (hr : 1 ≤ r) (hA : ConvergesOnRadius r A Alim)
    (hM : ∀ N, QuantumNLS.RadiusBound.radiusBound r (A N) ≤ M)
    (hb : Summable fun k => ‖c k‖ * M ^ k) (j : ℕ) :
    Tendsto (fun N => coeffAt (psList c A) N j) atTop (𝓝 (psLim c Alim j)) := by
  have hk : ∀ k, Tendsto (fun N => c k • coeffAt (powList A k) N j) atTop
      (𝓝 (c k • powLim Alim k j)) := fun k =>
    ((tendsto_iff_norm_sub_tendsto_zero (E := BoundedSymmetricKernel H j)).mpr
      ((pow_converges hr hA k).1.2 j)).const_smul (c k)
  have hdom := tendsto_tsum_of_dominated_convergence (G := BoundedSymmetricKernel H j)
    (bound := fun k => ‖c k‖ * M ^ k) hb hk
    (Eventually.of_forall fun N k =>
      (QuantumNLS.RadiusBound.norm_smul_kernel (c k) (coeffAt (powList A k) N j)).le.trans
      (mul_le_mul_of_nonneg_left ((norm_coeffAt_le hr (powList A k) N j).trans
        (radiusBound_powList_le hr hM k N)) (norm_nonneg (c k))))
  unfold psLim
  apply hdom.congr'
  filter_upwards [eventually_ge_atTop j] with N hN
  exact (coeffAt_psList hN).symm

/-- The DEF-009 placement `K ↦ Q_{N,p}(K)` as a continuous additive map. -/
def qHom (N : ℕ) (p : Fin (N + 1)) :
    BoundedSymmetricKernel H p.1 →+ (SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :=
  AddMonoidHom.mk' (fun K => QuantumNLS.RadiusBound.Q N p.1 (Nat.lt_succ_iff.mp p.2) K)
    (fun K L => by
      simp only [QuantumNLS.RadiusBound.Q_eq_genericU_N_r]
      exact QuantumNLS.RootOverlapLimit.genericU_add N p.1 _ K L)

theorem continuous_qHom (N : ℕ) (p : Fin (N + 1)) : Continuous (qHom (H := H) N p) :=
  AddMonoidHomClass.continuous_of_bound (qHom (H := H) N p) 1 (fun K => by
    rw [one_mul]
    exact QuantumNLS.RadiusBound.norm_Q_le N p.1 (Nat.lt_succ_iff.mp p.2) K)

theorem represented_psList (hr : 1 ≤ r) (hA : ConvergesOnRadius r A Alim)
    (hM : ∀ N, QuantumNLS.RadiusBound.radiusBound r (A N) ≤ M)
    (hb : Summable fun k => ‖c k‖ * M ^ k) (N : ℕ) :
    QuantumNLS.RadiusBound.represented (psList c A N) =
      ∑' k, c k • (QuantumNLS.RadiusBound.represented (A N)) ^ k := by
  have hp : ∀ p : Fin (N + 1), HasSum
      (fun k => QuantumNLS.RadiusBound.Q N p.1 (Nat.lt_succ_iff.mp p.2) (c k • powList A k N p))
      (QuantumNLS.RadiusBound.Q N p.1 (Nat.lt_succ_iff.mp p.2) (psList c A N p)) := fun p =>
    ((summable_psCoord hr hM hb N p).hasSum.map (qHom N p) (continuous_qHom N p))
  have hsmul : ∀ (p : Fin (N + 1)) (k : ℕ),
      QuantumNLS.RadiusBound.Q N p.1 (Nat.lt_succ_iff.mp p.2) (c k • powList A k N p) =
        c k • QuantumNLS.RadiusBound.Q N p.1 (Nat.lt_succ_iff.mp p.2) (powList A k N p) := by
    intro p k
    simp only [QuantumNLS.RadiusBound.Q_eq_genericU_N_r]
    exact QuantumNLS.RootOverlapLimit.genericU_smul N p.1 _ (c k) _
  unfold QuantumNLS.RadiusBound.represented
  calc ∑ p : Fin (N + 1), QuantumNLS.RadiusBound.Q N p.1 (Nat.lt_succ_iff.mp p.2) (psList c A N p)
      = ∑ p : Fin (N + 1), ∑' k,
          c k • QuantumNLS.RadiusBound.Q N p.1 (Nat.lt_succ_iff.mp p.2) (powList A k N p) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [← (hp p).tsum_eq]
        exact tsum_congr (fun k => hsmul p k)
    _ = ∑' k, ∑ p : Fin (N + 1),
          c k • QuantumNLS.RadiusBound.Q N p.1 (Nat.lt_succ_iff.mp p.2) (powList A k N p) := by
        rw [Summable.tsum_finsetSum]
        intro p _
        exact ((hp p).summable).congr (fun k => hsmul p k)
    _ = ∑' k, c k • (QuantumNLS.RadiusBound.represented (A N)) ^ k := by
        refine tsum_congr (fun k => ?_)
        rw [← Finset.smul_sum, ← (pow_converges hr hA k).2.1 N]
        rfl

/-! ### The symbol -/

/-- `K ↦ ⟨v^{⊗n}, K v^{⊗n}⟩` as a continuous additive map. -/
def kpsHom (n : ℕ) (v : H) : BoundedSymmetricKernel H n →+ ℂ :=
  AddMonoidHom.mk' (fun K => kernelProductSymbol K v) (fun K L => by
    simp [kernelProductSymbol, inner_add_right])

theorem continuous_kpsHom (n : ℕ) (v : H) : Continuous (kpsHom (H := H) n v) :=
  AddMonoidHomClass.continuous_of_bound (kpsHom (H := H) n v) (‖v‖ ^ (2 * n)) (fun K => by
    rw [mul_comm]
    exact norm_kernelProductSymbol_le K v)

set_option maxHeartbeats 2000000 in
theorem symbol_psLim (hr : 1 ≤ r) (hA : ConvergesOnRadius r A Alim)
    (hM : ∀ N, QuantumNLS.RadiusBound.radiusBound r (A N) ≤ M)
    (hb : Summable fun k => ‖c k‖ * M ^ k) (v : H) (hv : ‖v‖ ^ 2 ≤ r) :
    symbol (psLim c Alim) v = ∑' k, c k * (symbol Alim v) ^ k := by
  have hr0 : 0 ≤ r := by linarith
  have hlimS : ∀ k, Summable fun j => r ^ j * ‖powLim Alim k j‖ := fun k =>
    radius_summable hr0 (radiusBound_powList_le hr hM k) (pow_converges hr hA k).1.2
  have hlimT : ∀ k, ∑' j, r ^ j * ‖powLim Alim k j‖ ≤ M ^ k := fun k =>
    Real.tsum_le_of_sum_range_le (fun j => mul_nonneg (pow_nonneg hr0 _)
      (norm_nonneg (powLim Alim k j)))
      (partial_sums_le hr0 (radiusBound_powList_le hr hM k) (pow_converges hr hA k).1.2)
  have hkj : ∀ k j, ‖powLim Alim k j‖ ≤ M ^ k := fun k j =>
    (le_mul_of_one_le_left (norm_nonneg (powLim Alim k j)) (one_le_pow₀ hr)).trans
      (((hlimS k).le_tsum j (fun i _ => mul_nonneg (pow_nonneg hr0 _)
        (norm_nonneg (powLim Alim k i)))).trans (hlimT k))
  have hsj : ∀ j, Summable fun k => c k • powLim Alim k j := fun j =>
    Summable.of_norm_bounded (E := BoundedSymmetricKernel H j) hb (fun k =>
      (QuantumNLS.RadiusBound.norm_smul_kernel (c k) (powLim Alim k j)).le.trans
      (mul_le_mul_of_nonneg_left (hkj k j) (norm_nonneg (c k))))
  have hterm : ∀ j, kernelProductSymbol (psLim c Alim j) v =
      ∑' k, c k * kernelProductSymbol (powLim Alim k j) v := by
    intro j
    unfold psLim
    have hmap : HasSum (fun k => kernelProductSymbol (c k • powLim Alim k j) v)
        (kernelProductSymbol (∑' k, c k • powLim Alim k j) v) :=
      (hsj j).hasSum.map (kpsHom j v) (continuous_kpsHom j v)
    rw [← hmap.tsum_eq]
    refine tsum_congr (fun k => ?_)
    show kernelProductSymbol (c k • powLim Alim k j) v = _
    simp [kernelProductSymbol, inner_smul_right]
  have hFb : ∀ x : ℕ × ℕ, ‖c x.1 * kernelProductSymbol (powLim Alim x.1 x.2) v‖ ≤
      ‖c x.1‖ * (r ^ x.2 * ‖powLim Alim x.1 x.2‖) := by
    intro x
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_kernelProductSymbol_le _ v).trans ?_)
      (norm_nonneg (c x.1))
    rw [pow_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hv _)
      (norm_nonneg (powLim Alim x.1 x.2))
  have hgs : Summable (fun x : ℕ × ℕ => ‖c x.1‖ * (r ^ x.2 * ‖powLim Alim x.1 x.2‖)) := by
    refine (summable_prod_of_nonneg (fun x => by positivity)).mpr ⟨fun k => show Summable fun y => ‖c k‖ * (r ^ y * ‖powLim Alim k y‖) from
      (hlimS k).mul_left ‖c k‖, ?_⟩
    refine Summable.of_nonneg_of_le (fun k => tsum_nonneg (fun j => by positivity)) (fun k => ?_) hb
    show ∑' y, ‖c k‖ * (r ^ y * ‖powLim Alim k y‖) ≤ ‖c k‖ * M ^ k
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hlimT k) (norm_nonneg (c k))
  have hF : Summable (fun x : ℕ × ℕ => c x.1 * kernelProductSymbol (powLim Alim x.1 x.2) v) :=
    Summable.of_norm_bounded hgs hFb
  unfold symbol
  simp only [hterm]
  rw [Summable.tsum_comm' (f := fun k j => c k * kernelProductSymbol (powLim Alim k j) v) hF
    (fun k => hF.prod_factor k)
    (fun j => hF.comp_injective (i := fun k => (k, j)) (fun a b h => by simpa using h))]
  refine tsum_congr (fun k => ?_)
  rw [tsum_mul_left]
  have := (pow_converges hr hA k).2.2 v hv
  unfold symbol at this
  rw [this]

/-- **LOCAL-013, functional-calculus clause.** On a radius `r ≥ 1` where the family converges and its
absolute kernel norms are `≤ M < ρ`, for every scalar series with `Σ ‖c_k‖ ρ^k < ∞` the family
`f(A)_N = Σ_k c_k A_N^k` converges on `r`, represents `Σ_k c_k (A_N)^k`, and has symbol
`Σ_k c_k a^k` on `‖v‖² ≤ r`. -/
theorem powerSeries_converges {ρ : ℝ} (hr : 1 ≤ r) (hA : ConvergesOnRadius r A Alim)
    (hM0 : 0 ≤ M) (hM : ∀ N, QuantumNLS.RadiusBound.radiusBound r (A N) ≤ M) (hMρ : M < ρ)
    (hc : Summable fun k => ‖c k‖ * ρ ^ k) :
    ConvergesOnRadius r (psList c A) (psLim c Alim) ∧
      (∀ N, QuantumNLS.RadiusBound.represented (psList c A N) =
        ∑' k, c k • (QuantumNLS.RadiusBound.represented (A N)) ^ k) ∧
      ∀ v : H, ‖v‖ ^ 2 ≤ r → symbol (psLim c Alim) v = ∑' k, c k * (symbol Alim v) ^ k := by
  have hb := summable_majorant hM0 hMρ hc
  refine ⟨⟨⟨∑' k, ‖c k‖ * M ^ k, radiusBound_psList_le hr hM hb⟩, fun j => ?_⟩,
    represented_psList hr hA hM hb, fun v hv => symbol_psLim hr hA hM hb v hv⟩
  exact (tendsto_iff_norm_sub_tendsto_zero (E := BoundedSymmetricKernel H j)).mp
    (tendsto_coeff_ps hr hA hM hb j)

end Family2

end QuantumNLS.Local013PowerSeries

#print axioms QuantumNLS.Local013PowerSeries.summable_psCoord
#print axioms QuantumNLS.Local013PowerSeries.radiusBound_psList_le
#print axioms QuantumNLS.Local013PowerSeries.tendsto_coeff_ps
#print axioms QuantumNLS.Local013PowerSeries.represented_psList
#print axioms QuantumNLS.Local013PowerSeries.symbol_psLim
#print axioms QuantumNLS.Local013PowerSeries.powerSeries_converges
