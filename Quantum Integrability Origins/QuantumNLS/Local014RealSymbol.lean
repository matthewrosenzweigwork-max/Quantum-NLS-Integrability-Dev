import QuantumNLS.Local014ClassicalSeries
import QuantumNLS.GenericUAdjoint

/-!
# LOCAL-014 stage E4a: the real symbol `h`

Source: `source-text/chapters/local/quantum_periods.tex:188-190` ("Suppose `H_N` is self-adjoint
and has convergent kernel expansions with uniformly bounded radius-`8` norm. Let `h` be its real
symbol.") integrator decision: realness of `h` is PROVED, through the expectation limit
`⟨u^{⊗N}, H_N u^{⊗N}⟩ → h(u)` on the unit sphere.

* `expect_represented`: `⟨u^{⊗N}, A_N u^{⊗N}⟩ = Σ_{p≤N} ⟨u^{⊗p}, A_{p,N} u^{⊗p}⟩` for unit `u`
  (frozen `inner_genericU_N_r_product_of_unit`);
* `tendsto_expect`: for a family converging on a radius `R > 1`, the product-state expectations
  converge to the symbol on the unit sphere (Tannery, majorant `C R^{-p}`);
* `symbol_im_eq_zero`: if every `H_N` is self-adjoint, the symbol is real on the unit sphere;
* `saKernel`, `saList`, `saLim`: the self-adjoint parts `(A + A†)/2` of the kernels. For
  self-adjoint `H_N` they are again an expansion of `H_N` (`represented_saList`, frozen
  `adjoint_genericU_N_r`), they converge on the same radius (`saList_converges`), and their symbol
  is `Re h` (`symbol_saLim`), equal to `h` on the unit sphere (`symbol_saLim_eq_on_sphere`).
  `hReal Hlim u = Re (symbol Hlim u)` is the real Hamiltonian whose flow the theorem uses; it is
  gauge invariant (`hReal_phase`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators Nat
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.KernelConvergence

namespace QuantumNLS.Local014RealSymbol

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "RB" => QuantumNLS.RadiusBound.radiusBound
local notation "REP" => QuantumNLS.RadiusBound.represented

/-- The product vector `u^{⊗N} ∈ Sym^N H`. -/
def prodVec (N : ℕ) (u : H) : SymSector ℂ H N := ⟨htpow N u, htpow_mem_symSector N u⟩

theorem coeffAt_fin (A : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) (N : ℕ)
    (p : Fin (N + 1)) : coeffAt A N p.1 = A N p := by
  unfold coeffAt
  rw [dif_pos (Nat.lt_succ_iff.mp p.2)]

theorem kps_sub {p : ℕ} (X Y : BoundedSymmetricKernel H p) (u : H) :
    kernelProductSymbol (X - Y) u = kernelProductSymbol X u - kernelProductSymbol Y u := by
  simp [kernelProductSymbol, inner_sub_right]

theorem norm_kps_le_of_unit {p : ℕ} (X : BoundedSymmetricKernel H p) {u : H} (hu : ‖u‖ = 1) :
    ‖kernelProductSymbol X u‖ ≤ ‖X‖ := by
  simpa [hu] using norm_kernelProductSymbol_le X u

/-- Product-state expectation of a represented operator. -/
theorem expect_represented (A : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) (N : ℕ)
    (u : H) (hu : ‖u‖ = 1) :
    ⟪prodVec N u, REP (A N) (prodVec N u)⟫_ℂ =
      ∑ p ∈ range (N + 1), kernelProductSymbol (coeffAt A N p) u := by
  unfold QuantumNLS.RadiusBound.represented
  rw [ContinuousLinearMap.sum_apply, inner_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun p => kernelProductSymbol (coeffAt A N p) u)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [coeffAt_fin A N p, QuantumNLS.RadiusBound.Q_eq_genericU_N_r]
  exact QuantumNLS.LocalPlacement.inner_genericU_N_r_product_of_unit N p.1 _ (A N p) u hu

theorem coeffAt_eq_zero (A : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) {N p : ℕ}
    (hp : N < p) : coeffAt A N p = 0 := by
  unfold coeffAt
  rw [dif_neg (by omega)]

theorem pow_mul_norm_coeffAt_le {R : ℝ} (hR : 0 ≤ R)
    (A : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) (N p : ℕ) :
    R ^ p * ‖coeffAt A N p‖ ≤ RB R (A N) := by
  by_cases hp : p ≤ N
  · have h := Finset.single_le_sum (f := fun q : Fin (N + 1) => R ^ q.1 * ‖A N q‖)
      (fun q _ => mul_nonneg (pow_nonneg hR _)
        (norm_nonneg (A N q : SymSector ℂ H q.1 →L[ℂ] SymSector ℂ H q.1)))
      (Finset.mem_univ ⟨p, Nat.lt_succ_of_le hp⟩)
    rw [← coeffAt_fin A N ⟨p, Nat.lt_succ_of_le hp⟩] at h
    exact h
  · rw [coeffAt_eq_zero A (by omega)]
    have h0 : ‖(0 : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)‖ = 0 :=
      norm_zero (E := SymSector ℂ H p →L[ℂ] SymSector ℂ H p)
    rw [h0, mul_zero]
    exact QuantumNLS.RadiusBound.radiusBound_nonneg hR (A N)

/-- **Expectation limit on the unit sphere**: `⟨u^{⊗N}, A_N u^{⊗N}⟩ → a(u)`. -/
theorem tendsto_expect {R : ℝ} (hR : 1 < R) {A : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hA : ConvergesOnRadius R A Alim) (u : H)
    (hu : ‖u‖ = 1) :
    Tendsto (fun N => ⟪prodVec N u, REP (A N) (prodVec N u)⟫_ℂ) atTop (𝓝 (symbol Alim u)) := by
  obtain ⟨⟨C, hC⟩, hl⟩ := hA
  have hR0 : 0 < R := by linarith
  have hseq : ∀ N, ⟪prodVec N u, REP (A N) (prodVec N u)⟫_ℂ =
      ∑' p, kernelProductSymbol (coeffAt A N p) u := by
    intro N
    rw [expect_represented A N u hu, tsum_eq_sum (s := range (N + 1))]
    · intro p hp
      rw [Finset.mem_range, not_lt] at hp
      rw [coeffAt_eq_zero A (by omega)]
      simp [kernelProductSymbol]
  simp_rw [hseq]
  have hbound : ∀ N p, ‖kernelProductSymbol (coeffAt A N p) u‖ ≤ C * (R⁻¹) ^ p := by
    intro N p
    refine (norm_kps_le_of_unit _ hu).trans ?_
    have h := (pow_mul_norm_coeffAt_le hR0.le A N p).trans (hC N)
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hR0 p), mul_comm]
    exact h
  have hsum : Summable fun p : ℕ => C * (R⁻¹) ^ p :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hR)).mul_left C
  refine tendsto_tsum_of_dominated_convergence (bound := fun p => C * (R⁻¹) ^ p) hsum
    (fun p => ?_) (Eventually.of_forall fun N p => hbound N p)
  have h := hl p
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) h
  rw [← kps_sub]
  exact norm_kps_le_of_unit _ hu

/-- **`h` is real on the unit sphere** when every `H_N` is self-adjoint. -/
theorem symbol_im_eq_zero {R : ℝ} (hR : 1 < R)
    {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hH : ConvergesOnRadius R Hk Hlim)
    (hsa : ∀ N, IsSelfAdjoint (REP (Hk N))) (u : H) (hu : ‖u‖ = 1) :
    (symbol Hlim u).im = 0 := by
  have hlim := (Complex.continuous_im.tendsto _).comp (tendsto_expect hR hH u hu)
  have hz : ∀ N, (⟪prodVec N u, REP (Hk N) (prodVec N u)⟫_ℂ).im = 0 := by
    intro N
    have hsym := (hsa N).isSymmetric
    have h1 : (starRingEnd ℂ) ⟪prodVec N u, REP (Hk N) (prodVec N u)⟫_ℂ =
        ⟪prodVec N u, REP (Hk N) (prodVec N u)⟫_ℂ := by
      rw [inner_conj_symm]
      exact hsym _ _
    exact Complex.conj_eq_iff_im.mp h1
  have h0 : Tendsto (fun N => (⟪prodVec N u, REP (Hk N) (prodVec N u)⟫_ℂ).im) atTop (𝓝 0) := by
    simp only [hz]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

/-! ## Self-adjoint parts of the kernels -/

/-- `(A + A†)/2`. -/
def saKernel {p : ℕ} (A : BoundedSymmetricKernel H p) : BoundedSymmetricKernel H p :=
  (1 / 2 : ℂ) • (A + ContinuousLinearMap.adjoint A)

def saList (Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) (N : ℕ) :
    LocalPlacement.KernelList (H := H) N := fun p => saKernel (Hk N p)

def saLim (Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p) (p : ℕ) : BoundedSymmetricKernel H p :=
  saKernel (Hlim p)

theorem saKernel_sub {p : ℕ} (X Y : BoundedSymmetricKernel H p) :
    saKernel X - saKernel Y = saKernel (X - Y) := by
  unfold saKernel
  rw [map_sub, show X - Y + (ContinuousLinearMap.adjoint X - ContinuousLinearMap.adjoint Y) =
      (X + ContinuousLinearMap.adjoint X) - (Y + ContinuousLinearMap.adjoint Y) by abel]
  exact (smul_sub (1 / 2 : ℂ) _ _).symm

theorem norm_saKernel_le {p : ℕ} (X : BoundedSymmetricKernel H p) : ‖saKernel X‖ ≤ ‖X‖ := by
  unfold saKernel
  rw [QuantumNLS.RadiusBound.norm_smul_kernel]
  have hn : ‖(ContinuousLinearMap.adjoint X : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)‖ = ‖X‖ :=
    (ContinuousLinearMap.adjoint : (SymSector ℂ H p →L[ℂ] SymSector ℂ H p) ≃ₗᵢ⋆[ℂ]
      (SymSector ℂ H p →L[ℂ] SymSector ℂ H p)).norm_map X
  have h1 : ‖X + ContinuousLinearMap.adjoint X‖ ≤ ‖X‖ + ‖X‖ := by
    refine (norm_add_le (X : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)
      (ContinuousLinearMap.adjoint X)).trans ?_
    rw [hn]
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h2]
  linarith

theorem coeffAt_saList (Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) (N p : ℕ) :
    coeffAt (saList Hk) N p = saKernel (coeffAt Hk N p) := by
  unfold coeffAt
  split_ifs
  · rfl
  · unfold saKernel
    ext x
    simp

theorem saList_converges {R : ℝ} (hR : 0 ≤ R)
    {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hH : ConvergesOnRadius R Hk Hlim) :
    ConvergesOnRadius R (saList Hk) (saLim Hlim) := by
  obtain ⟨⟨C, hC⟩, hl⟩ := hH
  refine ⟨⟨C, fun N => le_trans ?_ (hC N)⟩, fun p => ?_⟩
  · unfold QuantumNLS.RadiusBound.radiusBound
    exact Finset.sum_le_sum fun q _ =>
      mul_le_mul_of_nonneg_left (norm_saKernel_le _) (pow_nonneg hR _)
  · refine squeeze_zero (fun N => norm_nonneg (coeffAt (saList Hk) N p - saLim Hlim p :
      SymSector ℂ H p →L[ℂ] SymSector ℂ H p)) (fun N => ?_) (hl p)
    rw [coeffAt_saList, saLim, saKernel_sub]
    exact norm_saKernel_le _

/-- For self-adjoint `H_N`, the self-adjoint parts are again an expansion of `H_N`. -/
theorem represented_saList (Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) (N : ℕ)
    (hsa : IsSelfAdjoint (REP (Hk N))) : REP (saList Hk N) = REP (Hk N) := by
  have hadj : ContinuousLinearMap.adjoint (REP (Hk N)) =
      ∑ p : Fin (N + 1), QuantumNLS.RadiusBound.Q N p.1 (Nat.lt_succ_iff.mp p.2)
        (ContinuousLinearMap.adjoint (Hk N p)) := by
    unfold QuantumNLS.RadiusBound.represented
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [QuantumNLS.RadiusBound.Q_eq_genericU_N_r, QuantumNLS.RadiusBound.Q_eq_genericU_N_r]
    exact QuantumNLS.GenericUAdjoint.adjoint_genericU_N_r _ _ _ _
  have hstar : ContinuousLinearMap.adjoint (REP (Hk N)) = REP (Hk N) := hsa
  have hsplit : REP (saList Hk N) =
      (1 / 2 : ℂ) • (REP (Hk N) + ContinuousLinearMap.adjoint (REP (Hk N))) := by
    rw [hadj]
    unfold QuantumNLS.RadiusBound.represented saList saKernel
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [QuantumNLS.RadiusBound.Q_eq_genericU_N_r,
      QuantumNLS.RootOverlapLimit.genericU_smul, QuantumNLS.RootOverlapLimit.genericU_add]
  rw [hsplit, hstar, ← two_smul ℂ (REP (Hk N)), smul_smul]
  norm_num

theorem kps_adjoint {p : ℕ} (X : BoundedSymmetricKernel H p) (u : H) :
    kernelProductSymbol (ContinuousLinearMap.adjoint X) u =
      (starRingEnd ℂ) (kernelProductSymbol X u) := by
  unfold kernelProductSymbol
  change ⟪(⟨htpow p u, htpow_mem_symSector p u⟩ : SymSector ℂ H p),
      ContinuousLinearMap.adjoint X ⟨htpow p u, htpow_mem_symSector p u⟩⟫_ℂ =
    (starRingEnd ℂ) ⟪(⟨htpow p u, htpow_mem_symSector p u⟩ : SymSector ℂ H p),
      X ⟨htpow p u, htpow_mem_symSector p u⟩⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem kps_saKernel {p : ℕ} (X : BoundedSymmetricKernel H p) (u : H) :
    kernelProductSymbol (saKernel X) u = ((kernelProductSymbol X u).re : ℂ) := by
  have hsmul : kernelProductSymbol ((1 / 2 : ℂ) • (X + ContinuousLinearMap.adjoint X)) u =
      (1 / 2 : ℂ) * (kernelProductSymbol X u +
        kernelProductSymbol (ContinuousLinearMap.adjoint X) u) := by
    simp [kernelProductSymbol, inner_add_right, inner_smul_right]
    ring
  unfold saKernel
  rw [hsmul, kps_adjoint, Complex.add_conj]
  push_cast
  ring

/-- The symbol of the self-adjoint parts is `Re h`, on the whole convergence ball. -/
theorem symbol_saLim {R : ℝ} (hR : 0 ≤ R) {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hH : ConvergesOnRadius R Hk Hlim) (u : H)
    (hu : ‖u‖ ^ 2 ≤ R) :
    symbol (saLim Hlim) u = ((symbol Hlim u).re : ℂ) := by
  have hs := QuantumNLS.Local014IteratedSymbol.summable_of_converges hR hH
  have hsk : Summable fun p => kernelProductSymbol (Hlim p) u :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => QuantumNLS.Local013CommutatorSeries.norm_kps_le_radius (Hlim p) hu) hs)
  unfold symbol saLim
  simp_rw [kps_saKernel]
  rw [← Complex.ofReal_tsum]
  congr 1
  exact (Complex.reCLM.map_tsum hsk).symm

/-- On the unit sphere the real Hamiltonian is the symbol itself. -/
theorem symbol_saLim_eq_on_sphere {R : ℝ} (hR : 1 < R)
    {Hk : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hH : ConvergesOnRadius R Hk Hlim)
    (hsa : ∀ N, IsSelfAdjoint (REP (Hk N))) (u : H) (hu : ‖u‖ = 1) :
    symbol (saLim Hlim) u = symbol Hlim u := by
  rw [symbol_saLim (by linarith) hH u (by rw [hu]; norm_num; linarith)]
  apply Complex.ext
  · simp
  · simp [symbol_im_eq_zero hR hH hsa u hu]

/-- The real Hamiltonian `h = Re a_H`. -/
def hReal (Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p) (u : H) : ℝ := (symbol Hlim u).re

theorem hReal_phase (Hlim : ∀ p : ℕ, BoundedSymmetricKernel H p) (θ : ℝ) (u : H) :
    hReal Hlim (Complex.exp (θ * Complex.I) • u) = hReal Hlim u := by
  unfold hReal
  rw [QuantumNLS.Local014ClassicalSeries.symbol_phase Hlim (Complex.norm_exp_ofReal_mul_I θ) u]

end QuantumNLS.Local014RealSymbol

/-! Axiom audit. -/
#print axioms QuantumNLS.Local014RealSymbol.expect_represented
#print axioms QuantumNLS.Local014RealSymbol.tendsto_expect
#print axioms QuantumNLS.Local014RealSymbol.symbol_im_eq_zero
#print axioms QuantumNLS.Local014RealSymbol.saList_converges
#print axioms QuantumNLS.Local014RealSymbol.represented_saList
#print axioms QuantumNLS.Local014RealSymbol.symbol_saLim
#print axioms QuantumNLS.Local014RealSymbol.symbol_saLim_eq_on_sphere
#print axioms QuantumNLS.Local014RealSymbol.hReal_phase
