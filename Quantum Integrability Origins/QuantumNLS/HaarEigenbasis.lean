import Mathlib
import QuantumNLS.HaarSlaterBasis
import QuantumNLS.HighMomentsDerivative

/-!
# R-F611926F (R3 + R2): the common eigenbasis, its eigenvalues, and the removable singularities
(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:293`; imports HKF1, R1/R3 modules, HMD1 read-only)

For `r = n+1`, `ρ_r = (−1)^n`, `δ_r = deltaR r`, `q = ρ_r e^{izL}`:
* `physBasis n`: a Hilbert basis of `Sym^r L²(𝕋_L)` indexed by strictly increasing `k : Fin r → ℤ`
  (symmetrized Slater determinants of the twisted modes, ordering sign included), independent of `z`.
* **`physicalKernel_eigen`** (R3): for `q ≠ 1`, `K_{r,z} B_k = (1−q)/r! ∏_j i/(z − ω(k_j+δ_r)) · B_k`
  (`= i^r(1−q)/r! ∏_j 1/(z−ω(k_j+δ_r))`, eq. `QG:eq:haar-kernel-eigenvalue`).
* **R2 (removable singularities)**: `z ↦ K_{r,z}` is entire (`differentiable_physicalKernel`); the poles of the
  right side are the isolated zeros of `1 − q` (`eventually_not_pole`); at each pole the right side of the factorization
  tends to `K_{r,z₀}` (`removable_singularity`); each eigenvalue function extends to an entire function
  `Λ̃_k(z) = ⟨B_k, K_{r,z} B_k⟩` and `K_{r,z} B_k = Λ̃_k(z) B_k` holds for EVERY `z ∈ ℂ` (`eigen_all`), so the common
  eigenbasis persists at the poles (`eigenvalue_entire`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators ComplexConjugate

namespace QuantumNLS.HaarEigenbasis

open QuantumNLS.BetheIntegralOperator QuantumNLS.PhysicalTensor QuantumNLS.HaarKernelFactorization
  QuantumNLS.HaarKernelFactorizationOp QuantumNLS.HaarResolvent QuantumNLS.HaarTwisted
  QuantumNLS.HaarKernelFactorizationSym QuantumNLS.HaarSlaterDensity QuantumNLS.HaarSlater
  QuantumNLS.HaarSlaterBasis QuantumNLS.BetheCompressedKernel QuantumNLS.KernelDefinition
  QuantumNLS.TensorCarrier QuantumNLS.BethePhysicalTransfer

section Eigen

variable (L : ℝ) [Fact (0 < L)]

theorem rho_delta (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((deltaR (n + 1) : ℝ) : ℂ)) = (-1 : ℂ) ^ n := by
  rcases Nat.even_or_odd n with hn | hn
  · have h : deltaR (n + 1) = 0 := by
      unfold deltaR; rw [if_neg]; intro h; exact (Nat.not_even_iff_odd.2 hn.add_one) h
    rw [h, hn.neg_one_pow]; simp
  · have h : deltaR (n + 1) = 1 / 2 := by
      unfold deltaR; rw [if_pos]; exact hn.add_one
    rw [h, hn.neg_one_pow]
    have : (2 * (Real.pi : ℂ) * Complex.I * (((1 : ℝ) / 2 : ℝ) : ℂ)) = Real.pi * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_pi_mul_I]

theorem rho_sq (n : ℕ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← mul_pow]; simp

/-- The one-particle eigenvalue `i/(z − ω(m+δ_r))`. -/
def lamFun (n : ℕ) (z : ℂ) (m : ℤ) : ℂ :=
  Complex.I / (z - ((omegaL L * ((m : ℝ) + deltaR (n + 1)) : ℝ) : ℂ))

/-- The eigenvalue `(1−q)/r! ∏_j i/(z − ω(k_j+δ_r))` (`QG:eq:haar-kernel-eigenvalue`). -/
def Lam (n : ℕ) (z : ℂ) (k : Fin (n + 1) → ℤ) : ℂ :=
  (1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) / ((n + 1).factorial : ℂ) *
    ∏ i, lamFun L n z (k i)

theorem hlam (n : ℕ) (z : ℂ) (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1) (m : ℤ) :
    R1 L ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z (tbasis L (deltaR (n + 1)) m) =
      lamFun L n z m • tbasis L (deltaR (n + 1)) m := by
  rw [tbasis_apply]
  exact R1_tmode L (ρ := (-1 : ℂ) ^ n) (rho_sq n) (rho_delta n) hq m

theorem positionAverage_of_sym {N : ℕ} {F : L2TN L N} (hF : F ∈ ContactOperator.SymL2 L N) :
    positionAverage L N F = F := by
  rw [ContactOperator.mem_SymL2_iff] at hF
  unfold positionAverage
  have : ∀ σ : Equiv.Perm (Fin N), ((physPerm σ).toContinuousLinearMap) F = F := fun σ => hF σ
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, this]
  have hne : ((N.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The eigen-equation at the level of the explicit operator `(1−q)/r! · S R^{⊗r} S`. -/
theorem factor_eigen (n : ℕ) (z : ℂ) (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1)
    (k : Idx (n + 1)) :
    ((1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) / ((n + 1).factorial : ℂ)) •
        Sop L (n + 1) ((Rtens L (n + 1) ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z).operator
          (Sop L (n + 1) (symVec (tbasis L (deltaR (n + 1))) k))) =
      Lam L n z k.1 • symVec (tbasis L (deltaR (n + 1))) k := by
  set b := tbasis L (deltaR (n + 1)) with hb
  have hSV : Sop L (n + 1) (symVec b k) =
      (((Real.sqrt ((n + 1).factorial : ℝ))⁻¹ : ℝ) : ℂ) • slater (fun m => b m) k.1 := by
    unfold symVec
    rw [map_smul, Sop_Sop]
  have hR := Rtens_slater (fun m => b m) ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z
    (lamFun L n z) (hlam L n z hq) k.1
  rw [hSV, map_smul, hR, map_smul, map_smul, smul_smul]
  unfold Lam symVec
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- **R3, eigenvalue relation for the compressed kernel on `L²(𝕋_L^r)`**. -/
theorem compressed_eigen (n : ℕ) (z : ℂ) (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1)
    (k : Idx (n + 1)) :
    (compressedKernel L (n + 1) z).operator (symVec (tbasis L (deltaR (n + 1))) k) =
      Lam L n z k.1 • symVec (tbasis L (deltaR (n + 1))) k := by
  rw [compressed_operator_eq L n z hq,
    positionAverage_of_sym L (symVec_mem _ k)]
  exact factor_eigen L n z hq k

/-- **Hilbert basis of `Sym^r L²(𝕋_L)`** (symmetrized Slater determinants of the twisted modes). -/
def physBasis (n : ℕ) : HilbertBasis (Idx (n + 1)) ℂ (SymSector ℂ (L2T L) (n + 1)) :=
  HilbertBasis.ofRepr ((symmetricPosition L (n + 1)).trans
    (symBasisL2 (tbasis L (deltaR (n + 1)))).repr)

theorem physBasis_apply (n : ℕ) (k : Idx (n + 1)) :
    physUnitary (L := L) ((physBasis L n k : SymSector ℂ (L2T L) (n + 1)) :
      HilbertTensorPower ℂ (L2T L) (n + 1)) = symVec (tbasis L (deltaR (n + 1))) k := by
  classical
  have h1 : physBasis L n k = (symmetricPosition L (n + 1)).symm
      (symBasisL2 (tbasis L (deltaR (n + 1))) k) := by
    rw [← HilbertBasis.repr_symm_single]
    show ((symmetricPosition L (n + 1)).trans (symBasisL2 (tbasis L (deltaR (n + 1)))).repr).symm _ = _
    rw [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
      HilbertBasis.repr_symm_single]
  rw [h1]
  have h2 := congrArg Subtype.val ((symmetricPosition L (n + 1)).apply_symm_apply
    (symBasisL2 (tbasis L (deltaR (n + 1))) k))
  exact h2.trans (by rw [symBasisL2, HilbertBasis.coe_mk])

/-- **R3: the actual `K_{r,z}` is diagonal in the `z`-independent orthonormal basis `physBasis`**, with eigenvalue
`i^r(1−q)/r! ∏_j 1/(z − ω(k_j+δ_r))`, for `z` outside the resolvent poles. -/
theorem physicalKernel_eigen (n : ℕ) (z : ℂ)
    (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1) (k : Idx (n + 1)) :
    physicalKernel L (n + 1) z (physBasis L n k) = Lam L n z k.1 • physBasis L n k := by
  apply Subtype.ext
  apply (physUnitary (L := L) (N := n + 1)).injective
  rw [physicalKernel_factorization L n z hq, physBasis_apply]
  rw [Submodule.coe_smul, map_smul, physBasis_apply]
  exact factor_eigen L n z hq k

end Eigen

#print axioms physicalKernel_eigen

/-! ### R2: removable singularities -/

section R2

variable (L : ℝ) [Fact (0 < L)] (n : ℕ)

/-- The left side `z ↦ K_{r,z}` is entire (bounded integral-kernel definition). -/
theorem entire_physicalKernel :
    Differentiable ℂ (fun z : ℂ => physicalKernel L (n + 1) z) :=
  QuantumNLS.HighMomentsDerivative.differentiable_physicalKernel L (n + 1)

theorem im_eq_zero_of_pole {z : ℂ} (hz : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) = 1) :
    z.im = 0 := by
  have h1 := congrArg norm hz
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_exp] at h1
  have h2 : (Complex.I * z * (L : ℂ)).re = -(z.im * L) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [h2, Real.exp_eq_one_iff] at h1
  have hL : 0 < L := Fact.out
  have : z.im * L = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h hL.ne'

/-- The poles are isolated: `1 − q ≠ 0` on a punctured neighbourhood of every point. -/
theorem eventually_not_pole (z0 : ℂ) :
    ∀ᶠ z in 𝓝[≠] z0, (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1 := by
  have hf : AnalyticAt ℂ (fun z : ℂ => (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z0 := by
    have : Differentiable ℂ (fun z : ℂ => (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) := by
      fun_prop
    exact this.analyticAt z0
  rcases hf.eventually_eq_or_eventually_ne (analyticAt_const (v := (1 : ℂ))) with h | h
  · exfalso
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h
    have hz1 := im_eq_zero_of_pole L n (hball (y := z0 + ((ε / 2 : ℝ) : ℂ) * Complex.I) (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith))
    have hz2 := im_eq_zero_of_pole L n (hball (y := z0 + ((ε / 4 : ℝ) : ℂ) * Complex.I) (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith))
    simp at hz1 hz2
    linarith
  · exact h

/-- **Removable singularity of the right side** `(1−q)/r! · A_r^*(∧^r R_z)A_r`: at every point `z₀` (in particular at
every pole) its limit along `z → z₀`, `z ≠ z₀`, exists and equals `K_{r,z₀}` (in the position representation). -/
theorem removable_singularity (z0 : ℂ) (w : SymSector ℂ (L2T L) (n + 1)) :
    Tendsto (fun z : ℂ =>
      ((1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) / ((n + 1).factorial : ℂ)) •
        Sop L (n + 1) ((Rtens L (n + 1) ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z).operator
          (Sop L (n + 1) (physUnitary (L := L) (w : HilbertTensorPower ℂ (L2T L) (n + 1))))))
      (𝓝[≠] z0)
      (𝓝 (physUnitary (L := L) ((physicalKernel L (n + 1) z0 w : SymSector ℂ (L2T L) (n + 1)) :
        HilbertTensorPower ℂ (L2T L) (n + 1)))) := by
  have hcont : Continuous (fun z : ℂ => physUnitary (L := L)
      ((physicalKernel L (n + 1) z w : SymSector ℂ (L2T L) (n + 1)) :
        HilbertTensorPower ℂ (L2T L) (n + 1))) :=
    (physUnitary (L := L) (N := n + 1)).continuous.comp
      (continuous_subtype_val.comp ((entire_physicalKernel L n).continuous.clm_apply continuous_const))
  have ht := (hcont.tendsto z0).mono_left (nhdsWithin_le_nhds (s := {z0}ᶜ))
  refine ht.congr' ?_
  filter_upwards [eventually_not_pole L n z0] with z hz
  exact physicalKernel_factorization L n z hz w

/-- The eigenvalue as an entire function: `Λ̃_k(z) = ⟨B_k, K_{r,z} B_k⟩`. -/
def lamTilde (k : Idx (n + 1)) (z : ℂ) : ℂ :=
  ⟪physBasis L n k, physicalKernel L (n + 1) z (physBasis L n k)⟫_ℂ

theorem lamTilde_continuous (k : Idx (n + 1)) : Continuous (lamTilde L n k) := by
  unfold lamTilde
  exact continuous_const.inner ((entire_physicalKernel L n).continuous.clm_apply continuous_const)

theorem lamTilde_differentiable (k : Idx (n + 1)) : Differentiable ℂ (lamTilde L n k) := by
  have h1 : Differentiable ℂ (fun z : ℂ => physicalKernel L (n + 1) z (physBasis L n k)) :=
    (entire_physicalKernel L n).clm_apply (differentiable_const _)
  have h2 : Differentiable ℂ (innerSL ℂ (physBasis L n k)) := (innerSL ℂ (physBasis L n k)).differentiable
  have := h2.comp h1
  exact this

theorem lamTilde_eq (z : ℂ) (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1)
    (k : Idx (n + 1)) : lamTilde L n k z = Lam L n z k.1 := by
  unfold lamTilde
  rw [physicalKernel_eigen L n z hq k, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (physBasis L n).orthonormal.1 k]
  simp

/-- **The common orthonormal eigenbasis diagonalizes `K_{r,z}` for EVERY `z ∈ ℂ`, poles included.** -/
theorem eigen_all (z0 : ℂ) (k : Idx (n + 1)) :
    physicalKernel L (n + 1) z0 (physBasis L n k) = lamTilde L n k z0 • physBasis L n k := by
  set g : ℂ → SymSector ℂ (L2T L) (n + 1) := fun z =>
    physicalKernel L (n + 1) z (physBasis L n k) - lamTilde L n k z • physBasis L n k with hg
  have hgc : Continuous g :=
    ((entire_physicalKernel L n).continuous.clm_apply continuous_const).sub
      ((lamTilde_continuous L n k).smul continuous_const)
  have hzero : ∀ᶠ z in 𝓝[≠] z0, g z = 0 := by
    filter_upwards [eventually_not_pole L n z0] with z hz
    simp only [hg]
    rw [lamTilde_eq L n z hz k, physicalKernel_eigen L n z hz k, sub_self]
  have h1 := (hgc.tendsto z0).mono_left (nhdsWithin_le_nhds (s := {z0}ᶜ))
  have h2 : Tendsto g (𝓝[≠] z0) (𝓝 0) := tendsto_const_nhds.congr' (hzero.mono fun z hz => hz.symm)
  have := tendsto_nhds_unique h1 h2
  simp only [hg] at this
  exact sub_eq_zero.1 this

/-- **R2 (eigenvalues)**: each eigenvalue function extends to an entire function, equal to the printed formula
`i^r(1−q)/r! ∏ 1/(z − ω(k_j+δ_r))` off the poles, with `K_{r,z} B_k = Λ̃_k(z) B_k` for all `z ∈ ℂ`. -/
theorem eigenvalue_entire (k : Idx (n + 1)) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ z, physicalKernel L (n + 1) z (physBasis L n k) = Λ z • physBasis L n k) ∧
      (∀ z, (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1 → Λ z = Lam L n z k.1) :=
  ⟨lamTilde L n k, lamTilde_differentiable L n k, fun z => eigen_all L n z k,
    fun z hz => lamTilde_eq L n z hz k⟩

end R2

#print axioms removable_singularity
#print axioms eigen_all
#print axioms eigenvalue_entire

end QuantumNLS.HaarEigenbasis
