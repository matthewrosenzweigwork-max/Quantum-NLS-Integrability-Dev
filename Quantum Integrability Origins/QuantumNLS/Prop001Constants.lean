import QuantumNLS.Prop001Packets
import QuantumNLS.Prop001Flow

/-! The printed PROP-001 constants, their restart closure, and the exact
C_a=0 propagation branch on the actual symmetric tensor carriers. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace QuantumNLS.Prop001
open TensorCarrier TensorPlacements KernelDefinition PhysicalTensor TraceClass LinearTailPhysicalEvolution
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H

def collisionSum (A : Interactions H) (a : ℝ) : ℝ :=
  2 * ∑' n, (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n)

def errorSum (A : Interactions H) : ℝ :=
  6 * ∑' n, ((n + 1 : ℕ) : ℝ) ^ 3 * ‖A n‖

def stepTime (a Ca : ℝ) : ℝ := a / (4 * Ca)

def forcingConstant (a C0 τ : ℝ) : ℝ := 4 * C0 * τ / a ^ 2

def rateConstant (a C0 τ : ℝ) : ℝ :=
  max 1 (max (4 / a + 8 * C0 * τ / a ^ 2)
    ((Real.sqrt 2 + Real.sqrt (2 + forcingConstant a C0 τ)) ^ 2))

def rateExponent (τ T : ℝ) : ℝ :=
  (2 : ℝ) ^ (1 - (max 1 (⌈T / τ⌉₊) : ℝ))

theorem collisionSum_nonneg (A : Interactions H) (a : ℝ) : 0 ≤ collisionSum A a := by
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun n => by positivity))

theorem errorSum_nonneg (A : Interactions H) : 0 ≤ errorSum A := by
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun n => by positivity))

theorem stepTime_pos {a Ca : ℝ} (ha : 0 < a) (hCa : 0 < Ca) :
    0 < stepTime a Ca := div_pos ha (by positivity)

theorem source_stepTime_pos (D : ClassicalData H) (hCa : collisionSum D.A D.a ≠ 0) :
    0 < stepTime D.a (collisionSum D.A D.a) :=
  stepTime_pos D.a_pos (lt_of_le_of_ne (collisionSum_nonneg D.A D.a) hCa.symm)

theorem rateConstant_ge_one (a C0 τ : ℝ) : 1 ≤ rateConstant a C0 τ := le_max_left _ _

/-- The square-root term in the printed maximum closes the restart
recurrence exactly, for every D above that term. -/
theorem restart_closed {E D : ℝ} (hE : 0 ≤ E)
    (hD : (Real.sqrt 2 + Real.sqrt (2 + E)) ^ 2 ≤ D) :
    2 * Real.sqrt (2 * D) + E ≤ D := by
  have hp := Real.sqrt_nonneg (2 : ℝ)
  have hq := Real.sqrt_nonneg (2 + E)
  have hp2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hq2 := Real.sq_sqrt (show 0 ≤ 2 + E by linarith)
  have hpq : 0 ≤ Real.sqrt 2 * Real.sqrt (2 + E) := mul_nonneg hp hq
  have hpq2 : (Real.sqrt 2 * Real.sqrt (2 + E)) ^ 2 = 2 * (2 + E) := by
    rw [mul_pow, hp2, hq2]
  have hz : 2 * (Real.sqrt 2 * Real.sqrt (2 + E)) ≤ D - E - 4 := by
    nlinarith
  have hz2 : (2 * (Real.sqrt 2 * Real.sqrt (2 + E))) ^ 2 ≤ (D - E - 4) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hz 2
  have hD0 : 0 ≤ D := (sq_nonneg _).trans hD
  have hdE : 0 ≤ (D - E) / 2 := by nlinarith
  have hsq : 2 * D ≤ ((D - E) / 2) ^ 2 := by nlinarith [hpq2]
  have hs := (Real.sqrt_le_iff).mpr ⟨hdE, hsq⟩
  linarith

theorem rateConstant_restart {a C0 τ : ℝ} (hC0 : 0 ≤ C0) (hτ : 0 ≤ τ) :
    2 * Real.sqrt (2 * rateConstant a C0 τ) + forcingConstant a C0 τ ≤
      rateConstant a C0 τ := by
  apply restart_closed (by unfold forcingConstant; positivity)
  exact (le_max_right _ _).trans (le_max_right _ _)

/-- Vanishing of C_a forces every actual interaction kernel to vanish.
Summability is explicit, so a divergent series cannot masquerade as zero. -/
theorem kernels_zero_of_collisionSum_zero (A : Interactions H) {a : ℝ}
    (hs : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n)))
    (hCa : collisionSum A a = 0) : ∀ n, A n = 0 := by
  have hz : (∑' n, (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n)) = 0 := by
    unfold collisionSum at hCa
    linarith
  intro n
  have hn := hs.le_tsum n (fun _ _ => by positivity)
  rw [hz] at hn
  have hnorm : ‖A n‖ = 0 := by
    have hw : 0 < ((n + 1 : ℕ) : ℝ) * Real.exp (a * n) := by positivity
    have hb : (((n + 1 : ℕ) : ℝ) * Real.exp (a * n)) * ‖A n‖ ≤ 0 := by
      nlinarith [hn]
    have hp : (((n + 1 : ℕ) : ℝ) * Real.exp (a * n)) * ‖A n‖ = 0 :=
      le_antisymm hb (mul_nonneg hw.le (norm_nonneg (A n)))
    exact (mul_eq_zero.mp hp).resolve_left (ne_of_gt hw)
  exact (norm_eq_zero (a := A n)).mp hnorm

theorem generator_zero (A : Interactions H) (hA : ∀ n, A n = 0) (N : ℕ) :
    generator A N = 0 := by
  have hu (n : Fin N) : genericU_N_r N (n.val + 1)
      (Nat.succ_le_of_lt n.isLt) (A n.val) = 0 := by
    apply (norm_eq_zero (a := genericU_N_r N (n.val + 1)
      (Nat.succ_le_of_lt n.isLt) (A n.val))).mp
    apply le_antisymm _ (norm_nonneg (genericU_N_r N (n.val + 1)
      (Nat.succ_le_of_lt n.isLt) (A n.val)))
    simpa only [hA, ContinuousLinearMap.opNorm_zero] using
      norm_genericU_N_r_le N (n.val + 1) (Nat.succ_le_of_lt n.isLt) (A n.val)
  apply ContinuousLinearMap.ext
  intro x
  simp only [generator, smul_apply, sum_apply,
    hu, zero_apply, smul_zero, Finset.sum_const_zero]

theorem hartreeField_zero (A : Interactions H) (hA : ∀ n, A n = 0) (u : H) :
    Ext025A8.sourceHartreeField A u = 0 := by
  have hext (n : ℕ) : extendSymKernel (A n) = 0 := by
    apply (norm_eq_zero (a := extendSymKernel (A n))).mp
    apply le_antisymm _ (norm_nonneg (extendSymKernel (A n)))
    simpa only [hA, ContinuousLinearMap.opNorm_zero] using norm_extendSymKernel_le (A n)
  have ht (n : ℕ) : Ext025A8.hartreeTerm (fun m => extendSymKernel (A m)) n u = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg
      (Ext025A8.hartreeTerm (fun m => extendSymKernel (A m)) n u))
    simpa only [hext, ContinuousLinearMap.opNorm_zero, mul_zero, zero_mul] using
      Ext025A8.hartreeTerm_norm (fun m => extendSymKernel (A m)) n u
  simp only [Ext025A8.sourceHartreeField, Ext025A8.hartreeField, ht, tsum_zero, smul_zero]

theorem zero_collision_classical (A : Interactions H) {a : ℝ}
    (hs : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n)))
    (hCa : collisionSum A a = 0) (u : H) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => u) (Ext025A8.sourceHartreeField A u) t := by
  rw [hartreeField_zero A (kernels_zero_of_collisionSum_zero A hs hCa)]
  exact hasDerivAt_const t u

/-- The printed C_a=0 branch: the actual marginal is exactly the
coherent rank-one projector at every N, k≤N, and every real time. -/
theorem zero_collision_propagation (A : Interactions H) {a : ℝ}
    (hs : Summable (fun n => (n + 1 : ℕ) * ‖A n‖ * Real.exp (a * n)))
    (hCa : collisionSum A a = 0) (N k : ℕ) (hk : k ≤ N)
    (u : H) (hu : ‖u‖ = 1) (t : ℝ) :
    marginal A N k hk t (productVector N u) =
      InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ H k) (htpow k u) := by
  have hz := generator_zero A (kernels_zero_of_collisionSum_zero A hs hCa) N
  have hevo : quantumEvolution A N t = 1 := by
    unfold quantumEvolution evolution
    have hzarg : (t : ℂ) • ((-Complex.I) • generator A N) = 0 := by
      rw [hz]
      ext x
      simp
    rw [hzarg, NormedSpace.exp_zero]
  change reducedDensityN N k hk
    (quantumEvolution A N t (productVector N u) : HilbertTensorPower ℂ H N) = _
  rw [hevo, one_apply_eq_self]
  change reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ H N) = _
  rw [reducedDensityN_htpow, hu]
  simp

theorem zero_collision_trajectory (D : ClassicalData H)
    (hCa : collisionSum D.A D.a = 0) (u : Sphere H) :
    trajectory D u = fun _ => u.val := by
  symm
  apply (trajectory_spec D u).2.2.2 _ rfl
  intro t
  exact ⟨u.property, zero_collision_classical D.A D.exponential hCa u.val t⟩

/-- The entire autonomous zero-collision branch, comparing with the
constructed classical trajectory rather than a supplied comparison path. -/
theorem zero_collision_full (D : ClassicalData H)
    (hCa : collisionSum D.A D.a = 0) (u : Sphere H)
    (N k : ℕ) (hk : k ≤ N) (t : ℝ) :
    traceNorm (marginal D.A N k hk t (productVector N u.val) -
      InnerProductSpace.rankOne ℂ
        (htpow k (trajectory D u t) : HilbertTensorPower ℂ H k)
        (htpow k (trajectory D u t))) = 0 := by
  rw [zero_collision_trajectory D hCa,
    zero_collision_propagation D.A D.exponential hCa N k hk u.val u.property t,
    sub_self, traceNorm_eq_zero_iff]

end QuantumNLS.Prop001

#print axioms QuantumNLS.Prop001.collisionSum
#print axioms QuantumNLS.Prop001.errorSum
#print axioms QuantumNLS.Prop001.stepTime
#print axioms QuantumNLS.Prop001.forcingConstant
#print axioms QuantumNLS.Prop001.rateConstant
#print axioms QuantumNLS.Prop001.rateExponent
#print axioms QuantumNLS.Prop001.collisionSum_nonneg
#print axioms QuantumNLS.Prop001.errorSum_nonneg
#print axioms QuantumNLS.Prop001.stepTime_pos
#print axioms QuantumNLS.Prop001.source_stepTime_pos
#print axioms QuantumNLS.Prop001.rateConstant_ge_one
#print axioms QuantumNLS.Prop001.restart_closed
#print axioms QuantumNLS.Prop001.rateConstant_restart
#print axioms QuantumNLS.Prop001.kernels_zero_of_collisionSum_zero
#print axioms QuantumNLS.Prop001.generator_zero
#print axioms QuantumNLS.Prop001.hartreeField_zero
#print axioms QuantumNLS.Prop001.zero_collision_classical
#print axioms QuantumNLS.Prop001.zero_collision_propagation
#print axioms QuantumNLS.Prop001.zero_collision_trajectory
#print axioms QuantumNLS.Prop001.zero_collision_full
