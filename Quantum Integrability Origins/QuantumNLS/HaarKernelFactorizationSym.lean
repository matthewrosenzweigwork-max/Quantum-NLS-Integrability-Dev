import Mathlib
import QuantumNLS.HaarKernelFactorizationOp

/-!
# R-F611926F `QG:prop:haar-kernel-factorization` (stage 3): `A_r`, `∧^r R`, poles, symmetric sector
(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:293`; imports stages 1 and 2 read-only)

* `AntiL2`: the antisymmetric subspace `{F | V_σ F = sgn σ · F}` of `L²(𝕋_L^r)`;
  `Sop_Sop` (`S² = 1`), `Sop_mem_anti`, `Sop_mem_sym`: `S` maps the symmetric subspace into the antisymmetric
  one and back (the unitary involution `A_r`, `A_r^* = S|_{anti}`); `Rtens_mem_anti`: `R_z^{⊗r}` preserves the
  antisymmetric subspace, so `S R^{⊗r} S |_{sym}` is literally `A_r^*(∧^r R)A_r` (with `∧^r R = R^{⊗r}|_{anti}`).
* `q_eq_one_iff`: `1 − ρ_r e^{izL} = 0` iff `z ∈ ω(ℤ + δ_r)`, `ω = 2π/L`: the resolvent poles of the source; so
  the hypothesis `q ≠ 1` of stage 2 is exactly "z outside the resolvent poles".
* `physicalKernel_factorization`: the exact factorization for the actual `K_{r,z} = physicalKernel L r z` on the
  symmetric sector `Sym^r L²(𝕋_L)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators InnerProductSpace ComplexConjugate Classical

namespace QuantumNLS.HaarKernelFactorizationSym

open QuantumNLS.BetheIntegralOperator QuantumNLS.PhysicalTensor QuantumNLS.BetheWeakGradient
  QuantumNLS.BetheCompressedKernel QuantumNLS.HaarKernelFactorization QuantumNLS.HaarKernelFactorizationOp

section Anti

variable (L : ℝ) [Fact (0 < L)] (m : ℕ)

/-- The antisymmetric subspace `{F | F(x∘σ) = sgn σ F(x)}` of `L²(𝕋_L^m)`. -/
def AntiL2 : Submodule ℂ (L2TN L m) where
  carrier := {F | ∀ σ : Equiv.Perm (Fin m), physPerm σ F = ((Equiv.Perm.sign σ : ℤˣ) : ℂ) • F}
  add_mem' := fun {F G} hF hG σ => by
    rw [map_add, hF σ, hG σ, smul_add]
  zero_mem' := fun σ => by simp
  smul_mem' := fun c F hF σ => by
    rw [map_smul, hF σ, smul_comm]

theorem mem_AntiL2 (F : L2TN L m) :
    F ∈ AntiL2 L m ↔ ∀ σ : Equiv.Perm (Fin m), physPerm σ F = ((Equiv.Perm.sign σ : ℤˣ) : ℂ) • F :=
  Iff.rfl

theorem sgnDec_sq (X : Fin m → ℝ) : sgnDec X * sgnDec X = 1 := by
  unfold sgnDec
  rcases Int.units_eq_one_or (Equiv.Perm.sign (sortPerm X)) with h | h <;> simp [h]

theorem sign_sq (σ : Equiv.Perm (Fin m)) :
    ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ((Equiv.Perm.sign σ : ℤˣ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- `S² = 1`: the ordering-sign multiplication is an involution. -/
theorem Sop_Sop (f : L2TN L m) : Sop L m (Sop L m f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_Sop L m (Sop L m f), coeFn_Sop L m f] with x h1 h2
  rw [h1, h2, ← mul_assoc, sgnDec_sq, one_mul]

/-- `S` maps symmetric functions to antisymmetric ones (`A_r : Sym → Anti`). -/
theorem Sop_mem_anti {F : L2TN L m} (hF : F ∈ ContactOperator.SymL2 L m) : Sop L m F ∈ AntiL2 L m := by
  rw [ContactOperator.mem_SymL2_iff] at hF
  intro σ
  refine Lp.ext ?_
  filter_upwards [coeFn_physPerm σ (Sop L m F),
    (measurePreserving_coordPerm (L := L) σ).quasiMeasurePreserving.ae_eq_comp (coeFn_Sop L m F),
    coeFn_physPerm σ F, Lp.coeFn_smul ((Equiv.Perm.sign σ : ℤˣ) : ℂ) (Sop L m F), coeFn_Sop L m F,
    QuantumNLS.BethePhysicalAssembly.torus_ae_injective L m] with x h1 h2 h3 h4 h5 h6
  rw [hF σ] at h3
  simp only [Function.comp_apply] at h2
  simp only [Pi.smul_apply, smul_eq_mul] at h4
  have hs : sgnDec (representatives L (coordPerm σ x)) =
      ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * sgnDec (representatives L x) :=
    sgnDec_comp (rep_injective L h6) σ
  rw [h1, h2, h4, h5, ← h3, hs]
  ring

/-- `S` maps antisymmetric functions to symmetric ones (`A_r^* : Anti → Sym`). -/
theorem Sop_mem_sym {F : L2TN L m} (hF : F ∈ AntiL2 L m) : Sop L m F ∈ ContactOperator.SymL2 L m := by
  rw [ContactOperator.mem_SymL2_iff]
  intro σ
  refine Lp.ext ?_
  filter_upwards [coeFn_physPerm σ (Sop L m F),
    (measurePreserving_coordPerm (L := L) σ).quasiMeasurePreserving.ae_eq_comp (coeFn_Sop L m F),
    coeFn_physPerm σ F, Lp.coeFn_smul ((Equiv.Perm.sign σ : ℤˣ) : ℂ) F, coeFn_Sop L m F,
    QuantumNLS.BethePhysicalAssembly.torus_ae_injective L m] with x h1 h2 h3 h4 h5 h6
  rw [hF σ] at h3
  simp only [Function.comp_apply] at h2
  simp only [Pi.smul_apply, smul_eq_mul] at h4
  have hs : sgnDec (representatives L (coordPerm σ x)) =
      ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * sgnDec (representatives L x) :=
    sgnDec_comp (rep_injective L h6) σ
  rw [h1, h2, h5, ← h3, h4, hs]
  have := sign_sq m σ
  calc ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * sgnDec (representatives L x) *
        (((Equiv.Perm.sign σ : ℤˣ) : ℂ) * F x)
      = (((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ((Equiv.Perm.sign σ : ℤˣ) : ℂ)) *
          (sgnDec (representatives L x) * F x) := by ring
    _ = sgnDec (representatives L x) * F x := by rw [this, one_mul]

variable (q z : ℂ)

/-- `R_z^{⊗r}` preserves the antisymmetric subspace: `∧^r R_z^ρ = R_z^{⊗r}|_{anti}` is a self-map of it. -/
theorem Rtens_mem_anti {F : L2TN L m} (hF : F ∈ AntiL2 L m) :
    (Rtens L m q z).operator F ∈ AntiL2 L m := by
  have hall : ∀ τ : Equiv.Perm (Fin m), physPerm τ⁻¹ ((Rtens L m q z).operator F) =
      ((Equiv.Perm.sign τ : ℤˣ) : ℂ) • (Rtens L m q z).operator F := by
    intro τ
    have hk : (permutedKernel L m (Rtens L m q z) τ⁻¹ τ⁻¹).operator = (Rtens L m q z).operator := by
      refine operator_congr_ae _ _ (Eventually.of_forall (fun p => ?_))
      show ∏ i, Rk q z (representatives L (coordPerm τ⁻¹ p.1) i)
          (representatives L (coordPerm τ⁻¹ p.2) i) =
        ∏ i, Rk q z (representatives L p.1 i) (representatives L p.2 i)
      exact Fintype.prod_equiv τ⁻¹ _ _ (fun i => rfl)
    have h0 := permutedKernel_operator L m (Rtens L m q z) τ⁻¹ τ⁻¹ F
    rw [hk] at h0
    have hs : (τ⁻¹).symm = τ := by rw [Equiv.Perm.inv_def, Equiv.symm_symm]
    rw [hs] at h0
    -- h0 : R F = physPerm τ⁻¹ (R (physPerm τ F))
    rw [hF τ, map_smul, map_smul] at h0
    have h2 := congrArg (fun v => ((Equiv.Perm.sign τ : ℤˣ) : ℂ) • v) h0
    simp only [smul_smul, sign_sq m, one_smul] at h2
    exact h2.symm
  intro σ
  have h := hall σ⁻¹
  rw [inv_inv, Equiv.Perm.sign_inv] at h
  exact h

end Anti

/-! ### The resolvent poles -/

section Poles

/-- `ω = 2π/L`. -/
def omegaL (L : ℝ) : ℝ := 2 * Real.pi / L

/-- `δ_r = 0` for odd `r`, `1/2` for even `r`. -/
def deltaR (r : ℕ) : ℝ := if Even r then 1 / 2 else 0

/-- **The poles of the resolvent are exactly `q = 1`**: for `r = n+1` and `ρ_r = (−1)^n`,
`1 − ρ_r e^{izL} = 0` iff `z = ω(k + δ_r)` for some integer `k` (the spectrum of `−i D_{ρ_r}`). -/
theorem q_eq_one_iff {L : ℝ} (hL : 0 < L) (n : ℕ) (z : ℂ) :
    (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) = 1 ↔
      ∃ k : ℤ, z = ((omegaL L * ((k : ℝ) + deltaR (n + 1)) : ℝ) : ℂ) := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  rcases Nat.even_or_odd n with hn | hn
  · have hδ : deltaR (n + 1) = 0 := by
      unfold deltaR
      rw [if_neg]
      intro h
      exact (Nat.not_even_iff_odd.2 hn.add_one) h
    rw [hn.neg_one_pow, one_mul, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h1 : z * L = 2 * Real.pi * k := by
        apply mul_left_cancel₀ hI
        linear_combination hk
      rw [hδ]; unfold omegaL
      push_cast
      field_simp
      linear_combination h1
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hδ] at hk; unfold omegaL at hk
      push_cast at hk
      rw [hk]
      field_simp
      simp
  · have hδ : deltaR (n + 1) = 1 / 2 := by
      unfold deltaR
      rw [if_pos]
      exact hn.add_one
    have hneg : (-1 : ℂ) ^ n = -1 := hn.neg_one_pow
    have hexp : -Complex.exp (Complex.I * z * L) = 1 ↔
        Complex.exp (Complex.I * z * L - Real.pi * Complex.I) = 1 := by
      rw [Complex.exp_sub, Complex.exp_pi_mul_I]
      constructor
      · intro h; rw [div_neg, div_one, h]
      · intro h
        have : Complex.exp (Complex.I * z * L) = -1 := by
          have h' : Complex.exp (Complex.I * z * L) / -1 = 1 := h
          rw [div_neg, div_one] at h'
          exact neg_eq_iff_eq_neg.1 h'
        rw [this]; simp
    rw [hneg, neg_one_mul, hexp, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have h1 : z * L = Real.pi * (2 * k + 1) := by
        apply mul_left_cancel₀ hI
        linear_combination hk
      rw [hδ]; unfold omegaL
      push_cast
      field_simp
      linear_combination h1
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [hδ] at hk; unfold omegaL at hk
      push_cast at hk
      rw [hk]
      field_simp
      ring

end Poles

/-! ### The symmetric sector -/

section SymSector

open QuantumNLS.KernelDefinition QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.BethePhysicalTransfer

variable (L : ℝ) [Fact (0 < L)]

/-- **Exact factorization for the actual DEF-048 kernel `K_{r,z} = physicalKernel L r z` on `Sym^r L²(𝕋_L)`**
(`QG:eq:haar-kernel-factorization`), for `z` outside the resolvent poles (`q = ρ_r e^{izL} ≠ 1`, see `q_eq_one_iff`):
`K_{r,z} w = (1−q)/r! · A_r^*(∧^r R_z^ρ) A_r w` with `A_r = S|_{sym}`, `A_r^* = S|_{anti}`, `∧^r R = R^{⊗r}|_{anti}`
(`Sop_mem_anti`, `Rtens_mem_anti`, `Sop_mem_sym`), in the physical position representation `physUnitary`. -/
theorem physicalKernel_factorization (n : ℕ) (z : ℂ)
    (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1)
    (w : SymSector ℂ (L2T L) (n + 1)) :
    physUnitary ((physicalKernel L (n + 1) z w : SymSector ℂ (L2T L) (n + 1)) :
        HilbertTensorPower ℂ (L2T L) (n + 1)) =
      ((1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) / ((n + 1).factorial : ℂ)) •
        Sop L (n + 1) ((Rtens L (n + 1) ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z).operator
          (Sop L (n + 1) (physUnitary (w : HilbertTensorPower ℂ (L2T L) (n + 1))))) := by
  have h := physicalKernel_action L (n + 1) z (w : HilbertTensorPower ℂ (L2T L) (n + 1))
  have hw : symProjToSector (n + 1) (w : HilbertTensorPower ℂ (L2T L) (n + 1)) = w := by
    apply Subtype.ext
    show symProj ℂ (L2T L) (n + 1) (w : HilbertTensorPower ℂ (L2T L) (n + 1)) = w
    rw [symProj_eq_starProjection]
    exact Submodule.starProjection_eq_self_iff.2 w.2
  have h' : extendSymKernel (physicalKernel L (n + 1) z)
      (w : HilbertTensorPower ℂ (L2T L) (n + 1)) =
      ((physicalKernel L (n + 1) z w : SymSector ℂ (L2T L) (n + 1)) :
        HilbertTensorPower ℂ (L2T L) (n + 1)) := by
    simp only [extendSymKernel, ContinuousLinearMap.comp_apply, hw, Submodule.subtypeL_apply]
  rw [h'] at h
  rw [h, compressed_operator_eq L n z hq]
  have hpa : positionAverage L (n + 1) (physUnitary (w : HilbertTensorPower ℂ (L2T L) (n + 1))) =
      physUnitary (w : HilbertTensorPower ℂ (L2T L) (n + 1)) := by
    rw [← physUnitary_symProj, symProj_eq_starProjection]
    congr 1
    exact Submodule.starProjection_eq_self_iff.2 w.2
  rw [hpa]

end SymSector

#print axioms Sop_Sop
#print axioms Sop_mem_anti
#print axioms Sop_mem_sym
#print axioms Rtens_mem_anti
#print axioms q_eq_one_iff
#print axioms physicalKernel_factorization

end QuantumNLS.HaarKernelFactorizationSym
