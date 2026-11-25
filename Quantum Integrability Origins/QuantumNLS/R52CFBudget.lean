import QuantumNLS.R52CFKernels

/-!
# R-52CF5DA1 stage 5: one common factorial majorant for all frozen-contour kernels

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101): "Its interaction kernels have one common factorial
majorant because the contours are fixed and `|D_v|` has a common positive lower bound. A2's bounded-interaction
propagation theorem therefore applies uniformly there."

For the actual transfer kernels `K_r(z) = orderedKernel L r z` on any parameter family with `|Im z(θ)| ≤ h` and any
continuous weight with `‖w‖ ≤ W`, the frozen-contour kernels `kerA` (stage 4) are
* dominated by `b_j = ν(Θ) W · 2e^{Lh}(|κ|L)^{j+1}/√((2(j+1))!)` (accepted `KernelFactorialBound.kernel_bound`);
* `b` has convergent cubic and exponential (rate `a = 1`) weighted sums (`majorant_summable`);
hence they form a `Prop001.ClassicalData` (`classicalData`) and ONE `Prop001RtwentyAssembly.NormBudget`
(`budget`, depending only on `ν(Θ), W, κ, L, h`) dominates every such schedule (`dominates`).
No hypothesis is added; all inherited modules are read-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators Nat

namespace QuantumNLS.R52CFBudget

open TensorCarrier KernelDefinition QuantumNLS.R52CFKernels

/-- `n³ ≤ 8ⁿ`. -/
theorem cube_le (n : ℕ) : ((n : ℕ) : ℝ) ^ 3 ≤ 8 ^ n := by
  have h : n < 2 ^ n := by
    first | exact Nat.lt_two_pow_self | exact Nat.lt_two_pow n | exact Nat.lt_pow_self (by norm_num)
  have h' : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast h.le
  calc (n : ℝ) ^ 3 ≤ (2 ^ n) ^ 3 := by gcongr
    _ = 8 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- `r! ≤ √((2r)!)`. -/
theorem factorial_le_sqrt (r : ℕ) : ((r ! : ℕ) : ℝ) ≤ Real.sqrt (((2 * r) ! : ℕ) : ℝ) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  have hd : r ! * r ! ∣ (r + r) ! := Nat.factorial_mul_factorial_dvd_factorial_add r r
  have hle : r ! * r ! ≤ (2 * r) ! := by
    rw [two_mul]
    exact Nat.le_of_dvd (Nat.factorial_pos _) hd
  have : ((r ! * r ! : ℕ) : ℝ) ≤ (((2 * r) ! : ℕ) : ℝ) := by exact_mod_cast hle
  rw [sq]
  exact_mod_cast this

/-- The weighted factorial majorant is summable. -/
theorem majorant_summable (x : ℝ) (hx : 0 ≤ x) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 3 * Real.exp j *
      (x ^ (j + 1) / Real.sqrt (((2 * (j + 1)) ! : ℕ) : ℝ))) := by
  have hs : Summable (fun j : ℕ => (8 * Real.exp 1 * x) ^ (j + 1) / ((j + 1 : ℕ) ! : ℝ)) := by
    have := (Real.summable_pow_div_factorial (8 * Real.exp 1 * x))
    exact (summable_nat_add_iff 1).mpr this
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hs
  have hfac := factorial_le_sqrt (j + 1)
  have hfpos : (0 : ℝ) < ((j + 1 : ℕ) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hc := cube_le (j + 1)
  have he : Real.exp (j : ℝ) ≤ Real.exp 1 ^ (j + 1) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hnum : ((j + 1 : ℕ) : ℝ) ^ 3 * Real.exp j * x ^ (j + 1) ≤ (8 * Real.exp 1 * x) ^ (j + 1) := by
    rw [mul_pow, mul_pow]
    have h1 : 0 ≤ x ^ (j + 1) := by positivity
    have h2 : 0 ≤ Real.exp (j : ℝ) := (Real.exp_pos _).le
    have h3 : ((j + 1 : ℕ) : ℝ) ^ 3 * Real.exp j ≤ 8 ^ (j + 1) * Real.exp 1 ^ (j + 1) :=
      mul_le_mul hc he h2 (by positivity)
    exact mul_le_mul_of_nonneg_right h3 h1
  have key : ((j + 1 : ℕ) : ℝ) ^ 3 * Real.exp j * (x ^ (j + 1) / Real.sqrt (((2 * (j + 1)) ! : ℕ) : ℝ)) =
      (((j + 1 : ℕ) : ℝ) ^ 3 * Real.exp j * x ^ (j + 1)) / Real.sqrt (((2 * (j + 1)) ! : ℕ) : ℝ) := by
    ring
  rw [key]
  exact div_le_div₀ (by positivity) hnum hfpos hfac

variable {L : ℝ} [Fact (0 < L)]

/-- The factorial majorant on the strip `|Im z| ≤ h`. -/
def beta (L κ h : ℝ) (j : ℕ) : ℝ :=
  2 * Real.exp (L * h) * (|κ| * L) ^ (j + 1) / Real.sqrt (((2 * (j + 1)) ! : ℕ) : ℝ)

theorem physK_bound {Θ : Type*} (κ : ℝ) (z : Θ → ℂ) {h : ℝ} (hzh : ∀ θ, |(z θ).im| ≤ h) (j : ℕ) (θ : Θ) :
    |κ| ^ (j + 1) * ‖physK (L := L) z j θ‖ ≤ beta L κ h j := by
  have hk := KernelFactorialBound.kernel_bound (L := L) κ (j + 1) (z θ)
  refine hk.trans ?_
  unfold beta
  have hL : 0 < L := Fact.out
  gcongr
  exact hzh θ

theorem beta_nonneg (L κ h : ℝ) (hL : 0 < L) (j : ℕ) : 0 ≤ beta L κ h j := by
  unfold beta; positivity

/-- The common budget sequence. -/
def bseq (L κ h V W : ℝ) (j : ℕ) : ℝ := V * W * beta L κ h j

theorem bseq_summable (L κ h V W : ℝ) (hL : 0 < L) (hV : 0 ≤ V) (hW : 0 ≤ W) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 3 * bseq L κ h V W j) ∧
      Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) * bseq L κ h V W j * Real.exp (1 * j)) := by
  have hm := (majorant_summable (|κ| * L) (by positivity)).mul_left (V * W * (2 * Real.exp (L * h)))
  have hb : ∀ j : ℕ, ((j + 1 : ℕ) : ℝ) ^ 3 * bseq L κ h V W j * Real.exp j =
      V * W * (2 * Real.exp (L * h)) * (((j + 1 : ℕ) : ℝ) ^ 3 * Real.exp j *
        ((|κ| * L) ^ (j + 1) / Real.sqrt (((2 * (j + 1)) ! : ℕ) : ℝ))) := by
    intro j; unfold bseq beta; ring
  have hbn : ∀ j : ℕ, 0 ≤ bseq L κ h V W j := fun j => by
    unfold bseq; exact mul_nonneg (mul_nonneg hV hW) (beta_nonneg L κ h hL j)
  have hall : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ 3 * bseq L κ h V W j * Real.exp j) := by
    simp_rw [hb]; exact hm
  constructor
  · refine Summable.of_nonneg_of_le (fun j => by have := hbn j; positivity) (fun j => ?_) hall
    have h1 : (1 : ℝ) ≤ Real.exp j := Real.one_le_exp (by positivity)
    have h2 : 0 ≤ ((j + 1 : ℕ) : ℝ) ^ 3 * bseq L κ h V W j := by have := hbn j; positivity
    calc ((j + 1 : ℕ) : ℝ) ^ 3 * bseq L κ h V W j = ((j + 1 : ℕ) : ℝ) ^ 3 * bseq L κ h V W j * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 h2
  · refine Summable.of_nonneg_of_le (fun j => by have := hbn j; positivity) (fun j => ?_) hall
    have h1 : ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 3 := by
      have h1' : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
      simpa using pow_le_pow_right₀ h1' (by norm_num : 1 ≤ 3)
    rw [one_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (hbn j)) (Real.exp_pos _).le

/-- The common PROP-001 norm budget. -/
def budget (L κ h V W : ℝ) (hL : 0 < L) (hV : 0 ≤ V) (hW : 0 ≤ W) : Prop001RtwentyAssembly.NormBudget where
  a := 1
  a_pos := one_pos
  b := bseq L κ h V W
  nonneg := fun j => by unfold bseq; exact mul_nonneg (mul_nonneg hV hW) (beta_nonneg L κ h hL j)
  cubic := (bseq_summable L κ h V W hL hV hW).1
  exponential := (bseq_summable L κ h V W hL hV hW).2

variable {Θ : Type*} [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
  (ν : Measure Θ) [IsFiniteMeasure ν]

theorem kerA_le_bseq (κ : ℝ) (w : Θ → ℂ) (z : Θ → ℂ) {h W : ℝ} (hzh : ∀ θ, |(z θ).im| ≤ h)
    (hw : ∀ θ, ‖w θ‖ ≤ W) (hW : 0 ≤ W) (j : ℕ) :
    ‖kerA ν κ w (physK (L := L) z) j‖ ≤ bseq L κ h (ν.real univ) W j := by
  have := kerA_norm_le ν κ w (physK (L := L) z) j hw (physK_bound κ z hzh j) hW
  unfold bseq
  exact this

/-- The frozen-contour kernels as PROP-001 classical data. -/
def classicalData (κ : ℝ) (w : Θ → ℂ) (z : Θ → ℂ) {h W : ℝ} (hzh : ∀ θ, |(z θ).im| ≤ h)
    (hw : ∀ θ, ‖w θ‖ ≤ W) (hW : 0 ≤ W) : Prop001.ClassicalData (PhysicalTensor.L2T L) where
  A := kerA ν κ w (physK (L := L) z)
  selfAdjoint := kerA_selfAdjoint ν κ w (physK (L := L) z)
  a := 1
  a_pos := one_pos
  cubic := by
    have hL : 0 < L := Fact.out
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (bseq_summable L κ h (ν.real univ) W hL measureReal_nonneg hW).1
    exact mul_le_mul_of_nonneg_left (kerA_le_bseq ν κ w z hzh hw hW j) (by positivity)
  exponential := by
    have hL : 0 < L := Fact.out
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (bseq_summable L κ h (ν.real univ) W hL measureReal_nonneg hW).2
    gcongr
    exact kerA_le_bseq ν κ w z hzh hw hW j

/-- One budget dominates the one-segment schedule of every such frozen-contour generator. -/
theorem dominates (κ : ℝ) (w : Θ → ℂ) (z : Θ → ℂ) {h W : ℝ} (hzh : ∀ θ, |(z θ).im| ≤ h)
    (hw : ∀ θ, ‖w θ‖ ≤ W) (hW : 0 ≤ W) (s : ℝ) :
    Prop001RtwentyAssembly.Dominates
      (budget L κ h (ν.real univ) W (Fact.out : 0 < L) measureReal_nonneg hW)
      [(classicalData (L := L) ν κ w z hzh hw hW, s)] := by
  intro p hp j
  simp only [List.mem_singleton] at hp
  subst hp
  exact kerA_le_bseq ν κ w z hzh hw hW j

end QuantumNLS.R52CFBudget

#print axioms QuantumNLS.R52CFBudget.dominates
#print axioms QuantumNLS.R52CFBudget.classicalData
