import Mathlib
import QuantumNLS.PlacementSquareSum

/-!
# R-F9AB39A7 `QG:lem:haar-offgrid-bessel`: the vector square-sum commutator estimate for averaged placements

(`QUANTUM_GAUGE_COMPONENTS.tex:669-686`.)  For a finite family `A_m` (`m ∈ F`) of kernels of rank `p` with
`∑_m ‖A_m x‖² ≤ B²‖x‖²` on `Sym^p`, and a bounded kernel `J` of rank `q`, on the full tensor power of `N` slots

  `(∑_m ‖[avg_p(A_m), avg_q(J)] ψ‖²)^{1/2} ≤ 2 B ‖J‖ (pq/N) ‖ψ‖`.

Printed proof, literally: expand both averages over independent subsets; disjoint placements commute; for an
overlapping pair the commutator vector (in `ℓ²(F; 𝓗_N)`) is bounded by `2B‖J‖‖ψ‖` (`∑‖K_nJψ‖² ≤ B²‖Jψ‖²` and
`‖J‖²∑‖K_nψ‖²`); the number of overlapping pairs is `≤ C(N,p)C(N,q)pq/N`; Minkowski in `ℓ²(F; 𝓗_N)`.
`l2 F v = (∑_{m∈F} ‖v_m‖²)^{1/2}` is the `ℓ²(F; 𝓗)` norm; Minkowski is proved from Cauchy–Schwarz.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open scoped InnerProductSpace ComplexConjugate BigOperators TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementFusion QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping QuantumNLS.PlacementUnionReindex
  QuantumNLS.PlacementFiberOperator QuantumNLS.RootOverlapCommutator QuantumNLS.PlacementSquareSum

namespace QuantumNLS.PlacementCommutatorL2

section L2

variable {ι' V : Type*} [NormedAddCommGroup V]

/-- The `ℓ²(F; V)` norm of a family. -/
def l2 (F : Finset ι') (v : ι' → V) : ℝ := Real.sqrt (∑ m ∈ F, ‖v m‖ ^ 2)

theorem l2_nonneg (F : Finset ι') (v : ι' → V) : 0 ≤ l2 F v := Real.sqrt_nonneg _

theorem l2_sq (F : Finset ι') (v : ι' → V) : l2 F v ^ 2 = ∑ m ∈ F, ‖v m‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun m _ => by positivity))

theorem l2_zero (F : Finset ι') : l2 F (fun _ => (0 : V)) = 0 := by simp [l2]

theorem l2_le_of_sq_le {F : Finset ι'} {v : ι' → V} {c : ℝ} (hc : 0 ≤ c)
    (h : ∑ m ∈ F, ‖v m‖ ^ 2 ≤ c ^ 2) : l2 F v ≤ c :=
  Real.sqrt_le_iff.mpr ⟨hc, h⟩

theorem l2_add_le (F : Finset ι') (a b : ι' → V) : l2 F (fun m => a m + b m) ≤ l2 F a + l2 F b := by
  refine l2_le_of_sq_le (add_nonneg (l2_nonneg _ _) (l2_nonneg _ _)) ?_
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt F (fun m => ‖a m‖) (fun m => ‖b m‖)
  calc ∑ m ∈ F, ‖a m + b m‖ ^ 2 ≤ ∑ m ∈ F, (‖a m‖ + ‖b m‖) ^ 2 :=
        Finset.sum_le_sum (fun m _ => pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2)
    _ = ∑ m ∈ F, ‖a m‖ ^ 2 + 2 * ∑ m ∈ F, ‖a m‖ * ‖b m‖ + ∑ m ∈ F, ‖b m‖ ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        ring
    _ ≤ (l2 F a + l2 F b) ^ 2 := by
        have h1 := l2_sq F a
        have h2 := l2_sq F b
        simp only [l2] at h1 h2 hcs ⊢
        nlinarith [hcs, Real.sqrt_nonneg (∑ m ∈ F, ‖a m‖ ^ 2), Real.sqrt_nonneg (∑ m ∈ F, ‖b m‖ ^ 2)]

theorem l2_neg (F : Finset ι') (a : ι' → V) : l2 F (fun m => -a m) = l2 F a := by
  simp [l2]

theorem l2_sub_le (F : Finset ι') (a b : ι' → V) : l2 F (fun m => a m - b m) ≤ l2 F a + l2 F b := by
  have := l2_add_le F a (fun m => -b m)
  rw [l2_neg] at this
  simpa [sub_eq_add_neg] using this

theorem l2_sum_le {κ : Type*} (F : Finset ι') (T : Finset κ) (v : κ → ι' → V) :
    l2 F (fun m => ∑ s ∈ T, v s m) ≤ ∑ s ∈ T, l2 F (v s) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [l2_zero]
  | insert a T ha ih =>
    simp only [Finset.sum_insert ha]
    refine (l2_add_le F (v a) (fun m => ∑ s ∈ T, v s m)).trans ?_
    linarith

variable [NormedSpace ℂ V]

theorem l2_smul (F : Finset ι') (c : ℂ) (a : ι' → V) : l2 F (fun m => c • a m) = ‖c‖ * l2 F a := by
  unfold l2
  simp only [norm_smul, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg c)]

theorem l2_le_mul {W : Type*} [NormedAddCommGroup W] (F : Finset ι') (a : ι' → V) (b : ι' → W) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ m ∈ F, ‖a m‖ ≤ C * ‖b m‖) : l2 F a ≤ C * l2 F b := by
  refine l2_le_of_sq_le (mul_nonneg hC (l2_nonneg _ _)) ?_
  calc ∑ m ∈ F, ‖a m‖ ^ 2 ≤ ∑ m ∈ F, (C * ‖b m‖) ^ 2 :=
        Finset.sum_le_sum (fun m hm => pow_le_pow_left₀ (norm_nonneg _) (h m hm) 2)
    _ = (C * l2 F b) ^ 2 := by
        rw [mul_pow, l2_sq, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [mul_pow]

theorem l2_sum_ite_le {κ : Type*} [Fintype κ] (F : Finset ι') (v : κ → ι' → V) (bad : κ → Prop)
    [DecidablePred bad] {c : ℝ} (h : ∀ z, l2 F (v z) ≤ if bad z then c else 0) :
    l2 F (fun m => ∑ z, v z m) ≤ (Finset.univ.filter bad).card * c := by
  refine (l2_sum_le F Finset.univ v).trans ?_
  refine (Finset.sum_le_sum (fun z _ => h z)).trans (le_of_eq ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

end L2

section Commutator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι' : Type*}

/-- The commutator vector `([P_S(A_m), P_T(J)] ψ)_m` of a pair of single placements. -/
def pairVec (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : ι' → BoundedSymmetricKernel H p)
    (J : BoundedSymmetricKernel H q) (ψ : HilbertTensorPower ℂ H N)
    (z : ActualPairPlacement N p q) (m : ι') : HilbertTensorPower ℂ H N :=
  ((rawSubsetPlacement N p hp z.1 (A m)).comp (rawSubsetPlacement N q hq z.2 J) -
    (rawSubsetPlacement N q hq z.2 J).comp (rawSubsetPlacement N p hp z.1 (A m))) ψ

/-- Pair bound for two single placements: `ℓ²`-norm of the commutator vector `≤ 2 B ‖J‖ ‖ψ‖`. -/
theorem pair_l2_le (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (F : Finset ι')
    (A : ι' → BoundedSymmetricKernel H p) (J : BoundedSymmetricKernel H q) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x : SymSector ℂ H p, ∑ m ∈ F, ‖A m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2)
    (z : ActualPairPlacement N p q) (ψ : HilbertTensorPower ℂ H N) :
    l2 F (pairVec N p q hp hq A J ψ z) ≤ 2 * (B * ‖J‖) * ‖ψ‖ := by
  have hJ := norm_rawSubsetPlacement_le N q hq z.2 J
  set PJ := rawSubsetPlacement N q hq z.2 J with hPJ
  have h1 : l2 F (fun m => rawSubsetPlacement N p hp z.1 (A m) (PJ ψ)) ≤ B * (‖J‖ * ‖ψ‖) := by
    refine l2_le_of_sq_le (by positivity) ?_
    refine (rawSubsetPlacement_sqsum N p hp z.1 F A hB (PJ ψ)).trans ?_
    have : ‖PJ ψ‖ ≤ ‖J‖ * ‖ψ‖ := (PJ.le_opNorm ψ).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) this 2) (by positivity)
  have h2 : l2 F (fun m => PJ (rawSubsetPlacement N p hp z.1 (A m) ψ)) ≤ ‖J‖ * (B * ‖ψ‖) := by
    refine le_trans (l2_le_mul F _ (fun m => rawSubsetPlacement N p hp z.1 (A m) ψ) (norm_nonneg J)
      (fun m _ => (PJ.le_opNorm _).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)))) ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine l2_le_of_sq_le (by positivity) ?_
    rw [mul_pow]
    exact rawSubsetPlacement_sqsum N p hp z.1 F A hB ψ
  have h3 := l2_sub_le F (fun m => rawSubsetPlacement N p hp z.1 (A m) (PJ ψ))
    (fun m => PJ (rawSubsetPlacement N p hp z.1 (A m) ψ))
  have e : pairVec N p q hp hq A J ψ z = fun m => rawSubsetPlacement N p hp z.1 (A m) (PJ ψ) -
      PJ (rawSubsetPlacement N p hp z.1 (A m) ψ) := by
    funext m
    rfl
  rw [e]
  nlinarith [h3, h1, h2]

theorem pairVec_disjoint (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : ι' → BoundedSymmetricKernel H p)
    (J : BoundedSymmetricKernel H q) (ψ : HilbertTensorPower ℂ H N) (z : ActualPairPlacement N p q)
    (hd : Disjoint (leftSlots hp z) (rightSlots hq z)) (m : ι') :
    pairVec N p q hp hq A J ψ z m = 0 := by
  unfold pairVec
  rw [rawPlacement_commute_of_disjoint N p q hp hq (A m) J z hd, sub_self]
  rfl

theorem avgCommVec_eq (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : ι' → BoundedSymmetricKernel H p)
    (J : BoundedSymmetricKernel H q) (ψ : HilbertTensorPower ℂ H N) (m : ι') :
    ((rawSubsetAverage N p hp (A m)).comp (rawSubsetAverage N q hq J) -
        (rawSubsetAverage N q hq J).comp (rawSubsetAverage N p hp (A m))) ψ =
      (((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹)) •
        ∑ z : ActualPairPlacement N p q, pairVec N p q hp hq A J ψ z m := by
  rw [average_commutator_eq, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  simp only [ContinuousLinearMap.sum_apply]
  exact (Fintype.sum_prod_type (f := fun z : PlacementSubset p (N - p) × PlacementSubset q (N - q) =>
    pairVec N p q hp hq A J ψ z m)).symm

theorem average_commutator_l2_le (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (hN : 1 ≤ N) (F : Finset ι')
    (A : ι' → BoundedSymmetricKernel H p) (J : BoundedSymmetricKernel H q) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x : SymSector ℂ H p, ∑ m ∈ F, ‖A m x‖ ^ 2 ≤ B ^ 2 * ‖x‖ ^ 2)
    (ψ : HilbertTensorPower ℂ H N) :
    l2 F (fun m => ((rawSubsetAverage N p hp (A m)).comp (rawSubsetAverage N q hq J) -
        (rawSubsetAverage N q hq J).comp (rawSubsetAverage N p hp (A m))) ψ) ≤
      2 * (B * ‖J‖) * ((p * q : ℝ) / N) * ‖ψ‖ := by
  classical
  have hcp : (N.choose p : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hp
  have hcq : (N.choose q : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hq
  have hcpos : 0 < (N.choose p : ℝ) * (N.choose q : ℝ) := by positivity
  have hnorm : ‖((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹)‖ =
      ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ := by
    rw [norm_mul, norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast, mul_inv]
  have hfun : (fun m => ((rawSubsetAverage N p hp (A m)).comp (rawSubsetAverage N q hq J) -
        (rawSubsetAverage N q hq J).comp (rawSubsetAverage N p hp (A m))) ψ) =
      fun m => (((N.choose p : ℂ)⁻¹) * ((N.choose q : ℂ)⁻¹)) •
        ∑ z : ActualPairPlacement N p q, pairVec N p q hp hq A J ψ z m :=
    funext (avgCommVec_eq N p q hp hq A J ψ)
  rw [hfun, l2_smul, hnorm]
  have hbad := card_badPairs_le hp hq hN
  have hsum : l2 F (fun m => ∑ z : ActualPairPlacement N p q, pairVec N p q hp hq A J ψ z m) ≤
      (Finset.univ.filter (fun z : ActualPairPlacement N p q =>
        ¬ Disjoint (leftSlots hp z) (rightSlots hq z))).card * (2 * (B * ‖J‖) * ‖ψ‖) := by
    refine l2_sum_ite_le F (pairVec N p q hp hq A J ψ) _ (fun z => ?_)
    by_cases hz : ¬ Disjoint (leftSlots hp z) (rightSlots hq z)
    · rw [if_pos hz]; exact pair_l2_le N p q hp hq F A J hB0 hB z ψ
    · rw [if_neg hz]
      have hd : Disjoint (leftSlots hp z) (rightSlots hq z) := not_not.mp hz
      have h0 : pairVec N p q hp hq A J ψ z = fun _ => 0 := funext (pairVec_disjoint N p q hp hq A J ψ z hd)
      rw [h0]
      exact (l2_zero F).le
  have hc0 : 0 ≤ 2 * (B * ‖J‖) * ‖ψ‖ := by positivity
  have hmul := mul_le_mul_of_nonneg_right hbad hc0
  calc ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ * l2 F (fun m => ∑ z : ActualPairPlacement N p q,
        pairVec N p q hp hq A J ψ z m)
      ≤ ((N.choose p : ℝ) * (N.choose q : ℝ))⁻¹ * ((N.choose p : ℝ) * (N.choose q : ℝ) *
          ((p * q : ℝ) / N) * (2 * (B * ‖J‖) * ‖ψ‖)) :=
        mul_le_mul_of_nonneg_left (hsum.trans hmul) (by positivity)
    _ = 2 * (B * ‖J‖) * ((p * q : ℝ) / N) * ‖ψ‖ := by field_simp

end Commutator

#print axioms average_commutator_l2_le

end QuantumNLS.PlacementCommutatorL2
