import Mathlib
import QuantumNLS.HaarSlaterDensity

/-!
# R-F611926F (R3, Slater determinants): products, Slater vectors, eigenvalues, orthonormality
(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:293`; imports HKF1 and the R1/R3 modules read-only)

* `Rtens_prodLp`: `R_z^{⊗r}(∏ f_i(x_i)) = ∏ (R_z f_i)(x_i)` (Fubini on the product measure).
* `slater e k = Σ_σ sgn σ ∏_i e_{k(σ⁻¹ i)}(x_i)`: the (unnormalized) Slater determinant of the modes `e_{k_1},…,e_{k_r}`;
  `slater_anti`: it is antisymmetric; `Rtens_slater`: if `R e_m = λ_m e_m` then `R^{⊗r} slater k = (∏ λ_{k_i}) slater k`.
* `inner_slater`: for strictly increasing `k, k'` of an orthonormal basis, `⟨slater k, slater k'⟩ = r! δ_{k k'}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory
open scoped InnerProductSpace BigOperators ComplexConjugate

namespace QuantumNLS.HaarSlater

open QuantumNLS.BetheIntegralOperator QuantumNLS.PhysicalTensor QuantumNLS.HaarKernelFactorization
  QuantumNLS.HaarKernelFactorizationOp QuantumNLS.HaarResolvent QuantumNLS.HaarTwisted
  QuantumNLS.HaarKernelFactorizationSym QuantumNLS.HaarSlaterDensity

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-! ### `R^{⊗r}` on product vectors -/

theorem Rtens_prodLp (q z : ℂ) (f : Fin N → L2T L) :
    (Rtens L N q z).operator (prodLp f) = prodLp (fun i => R1 L q z (f i)) := by
  refine Lp.ext ?_
  have h1 := (Rtens L N q z).operator_apply_ae (prodLp f)
  have h2 : ∀ᵐ x ∂(torusPiMeasure L N), ∀ i, R1 L q z (f i) (x i) =
      ∫ w, Rk q z (rep1 L (x i)) (rep1 L w) * f i w ∂(volume : Measure (AddCircle L)) := by
    rw [ae_all_iff]; intro i
    exact (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure (AddCircle L))) i).ae
      ((R1ker L q z).operator_apply_ae (f i))
  have h3 := (memLp_prodFun (fun i => R1 L q z (f i))).coeFn_toLp
  filter_upwards [h1, h2, h3] with x hx hy hz
  rw [hx]
  have hcongr : ∫ y, (Rtens L N q z).fn (x, y) * (prodLp f) y ∂torusPiMeasure L N =
      ∫ y, (Rtens L N q z).fn (x, y) * prodFun f y ∂torusPiMeasure L N := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_prodFun f).coeFn_toLp] with y hy
    rw [show (prodLp f) y = prodFun f y from hy]
  rw [hcongr]
  have e : ∫ y, (Rtens L N q z).fn (x, y) * prodFun f y ∂torusPiMeasure L N =
      ∏ i, ∫ w, Rk q z (rep1 L (x i)) (rep1 L w) * f i w ∂(volume : Measure (AddCircle L)) := by
    have : (fun y => (Rtens L N q z).fn (x, y) * prodFun f y) =
        fun y => ∏ i, (Rk q z (rep1 L (x i)) (rep1 L (y i)) * f i (y i)) := by
      funext y
      simp only [Rtens, prodFun, Finset.prod_mul_distrib]
      rfl
    rw [this]
    exact integral_fintype_prod_eq_prod
      (f := fun i w => Rk q z (rep1 L (x i)) (rep1 L w) * f i w)
  rw [e]
  show _ = (prodLp (fun i => R1 L q z (f i))) x
  rw [show (prodLp (fun i => R1 L q z (f i))) x = prodFun (fun i => R1 L q z (f i)) x from hz]
  unfold prodFun
  exact Finset.prod_congr rfl (fun i _ => (hy i).symm)

/-! ### Slater vectors -/

section Slater

variable (e : ℤ → L2T L)

/-- `slater e k = Σ_σ sgn σ ∏_i e_{k(σ⁻¹ i)}(x_i)`. -/
def slater (k : Fin N → ℤ) : L2TN L N :=
  ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤˣ) : ℂ) • prodLp (fun i => e (k (σ.symm i)))

theorem slater_anti (k : Fin N → ℤ) (τ : Equiv.Perm (Fin N)) :
    physPerm τ (slater e k) = ((Equiv.Perm.sign τ : ℤˣ) : ℂ) • slater e k := by
  unfold slater
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
  rw [map_smul, ← prodLp_perm]
  have hperm : (fun i => (fun i => e (k (σ.symm i))) (τ.symm i)) =
      fun i => e (k ((Equiv.mulLeft τ σ).symm i)) := by
    funext i
    rfl
  rw [hperm, smul_smul]
  congr 1
  simp only [Equiv.coe_mulLeft, map_mul, Units.val_mul, Int.cast_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

theorem Rtens_slater (q z : ℂ) (lam : ℤ → ℂ) (hlam : ∀ m, R1 L q z (e m) = lam m • e m)
    (k : Fin N → ℤ) :
    (Rtens L N q z).operator (slater e k) = (∏ i, lam (k i)) • slater e k := by
  unfold slater
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [map_smul, Rtens_prodLp]
  have hm : prodLp (fun i => R1 L q z (e (k (σ.symm i)))) =
      (∏ i, lam (k (σ.symm i))) • prodLp (fun i => e (k (σ.symm i))) := by
    have := (prodMultilinear (L := L) (N := N)).map_smul_univ (fun i => lam (k (σ.symm i)))
      (fun i => e (k (σ.symm i)))
    simp only [hlam]
    exact this
  have hprod : ∏ i, lam (k (σ.symm i)) = ∏ i, lam (k i) :=
    Equiv.prod_comp σ.symm (fun i => lam (k i))
  rw [hm, hprod]
  exact smul_comm _ _ _

end Slater

/-! ### Orthonormality of Slater vectors of a Hilbert basis -/

section Inner

variable (b : HilbertBasis ℤ ℂ (L2T L))

theorem conj_sign (σ : Equiv.Perm (Fin N)) :
    conj ((Equiv.Perm.sign σ : ℤˣ) : ℂ) = ((Equiv.Perm.sign σ : ℤˣ) : ℂ) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem inner_slater (k k' : Fin N → ℤ) :
    ⟪slater (fun m => b m) k, slater (fun m => b m) k'⟫_ℂ =
      ∑ σ : Equiv.Perm (Fin N), ∑ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ((Equiv.Perm.sign τ : ℤˣ) : ℂ) *
          ∏ i, (if k (σ.symm i) = k' (τ.symm i) then (1 : ℂ) else 0) := by
  unfold slater
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [inner_smul_left, conj_sign, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [inner_smul_right, inner_prodLp]
  have : ∀ i, ⟪b (k (σ.symm i)), b (k' (τ.symm i))⟫_ℂ =
      if k (σ.symm i) = k' (τ.symm i) then (1 : ℂ) else 0 := fun i =>
    orthonormal_iff_ite.mp b.orthonormal _ _
  simp only [this]
  ring

theorem eq_of_perm_eq {k k' : Fin N → ℤ} (hk : StrictMono k) (hk' : StrictMono k')
    (σ τ : Equiv.Perm (Fin N)) (h : ∀ i, k (σ.symm i) = k' (τ.symm i)) : k = k' ∧ σ = τ := by
  have hρ : ∀ j, k j = k' (τ.symm (σ j)) := fun j => by
    have := h (σ j); simpa using this
  have hmono : StrictMono (fun j => τ.symm (σ j)) := by
    intro i j hij
    have := hk hij
    rw [hρ i, hρ j] at this
    exact hk'.lt_iff_lt.1 this
  have hid : (fun j => τ.symm (σ j)) = id := hmono.eq_id
  have h1 : ∀ j, σ j = τ j := fun j => by
    have := congrFun hid j
    simp only [id] at this
    exact (Equiv.symm_apply_eq τ).1 this
  refine ⟨?_, Equiv.ext h1⟩
  funext j
  rw [hρ j, congrFun hid j]; rfl

theorem inner_slater_strictMono {k k' : Fin N → ℤ} (hk : StrictMono k) (hk' : StrictMono k') :
    ⟪slater (fun m => b m) k, slater (fun m => b m) k'⟫_ℂ =
      if k = k' then ((N.factorial : ℕ) : ℂ) else 0 := by
  rw [inner_slater]
  by_cases hkk : k = k'
  · subst hkk
    rw [if_pos rfl]
    have hterm : ∀ σ τ : Equiv.Perm (Fin N),
        ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ((Equiv.Perm.sign τ : ℤˣ) : ℂ) *
          ∏ i, (if k (σ.symm i) = k (τ.symm i) then (1 : ℂ) else 0) =
        if σ = τ then 1 else 0 := by
      intro σ τ
      by_cases hστ : σ = τ
      · subst hστ
        simp only [if_true]
        have : ∀ i, (if k (σ.symm i) = k (σ.symm i) then (1 : ℂ) else 0) = 1 := fun i => by simp
        simp only [this, Finset.prod_const_one, mul_one]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      · rw [if_neg hστ]
        have : ∃ i, k (σ.symm i) ≠ k (τ.symm i) := by
          by_contra hcon
          push_neg at hcon
          exact hστ (eq_of_perm_eq hk hk σ τ hcon).2
        obtain ⟨i, hi⟩ := this
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
    simp only [hterm]
    simp [Fintype.card_perm]
  · rw [if_neg hkk]
    refine Finset.sum_eq_zero (fun σ _ => Finset.sum_eq_zero (fun τ _ => ?_))
    have : ∃ i, k (σ.symm i) ≠ k' (τ.symm i) := by
      by_contra hcon
      push_neg at hcon
      exact hkk (eq_of_perm_eq hk hk' σ τ hcon).1
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]

end Inner

#print axioms Rtens_prodLp
#print axioms slater_anti
#print axioms Rtens_slater
#print axioms inner_slater_strictMono

end QuantumNLS.HaarSlater
