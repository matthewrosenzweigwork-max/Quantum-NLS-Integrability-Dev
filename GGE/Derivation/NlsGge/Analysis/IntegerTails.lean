import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Concrete inverse-power numerical leaves for NEW-F02.05.
Zero denominators are explicitly assigned zero by the reciprocal kernels;
these zeros exclude resonant indices in the convolution, not physical modes. -/
set_option autoImplicit false
noncomputable section

namespace NlsGge.Analysis

open Filter
open scoped Topology

def inverseSquare (n : ℤ) : ℝ := 1 / (n : ℝ) ^ 2

def inverseFourth (n : ℤ) : ℝ := 1 / (n : ℝ) ^ 4

@[simp] theorem inverseSquare_zero : inverseSquare 0 = 0 := by
  simp [inverseSquare]

@[simp] theorem inverseFourth_zero : inverseFourth 0 = 0 := by
  simp [inverseFourth]

theorem inverseSquare_nonneg (n : ℤ) : 0 ≤ inverseSquare n := by
  unfold inverseSquare
  positivity

theorem inverseFourth_nonneg (n : ℤ) : 0 ≤ inverseFourth n := by
  unfold inverseFourth
  positivity

@[simp] theorem inverseSquare_neg (n : ℤ) : inverseSquare (-n) = inverseSquare n := by
  simp [inverseSquare]

@[simp] theorem inverseFourth_neg (n : ℤ) : inverseFourth (-n) = inverseFourth n := by
  simp only [inverseFourth, Int.cast_neg]
  congr 1
  ring

theorem summable_inverseSquare : Summable inverseSquare :=
  (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)

theorem summable_inverseFourth : Summable inverseFourth :=
  (Real.summable_one_div_int_pow (p := 4)).2 (by norm_num)

/-- The total is finite because summability was established first. -/
def inverseSquareTotal : ℝ := ∑' n : ℤ, inverseSquare n

def inverseFourthTotal : ℝ := ∑' n : ℤ, inverseFourth n

theorem inverseSquareTotal_nonneg : 0 ≤ inverseSquareTotal :=
  tsum_nonneg inverseSquare_nonneg

theorem inverseFourthTotal_nonneg : 0 ≤ inverseFourthTotal :=
  tsum_nonneg inverseFourth_nonneg

theorem inverseSquare_le_total (n : ℤ) : inverseSquare n ≤ inverseSquareTotal := by
  exact summable_inverseSquare.le_tsum n (fun m _ => inverseSquare_nonneg m)

/-- Real tail convergence is used only together with the summability theorem above. -/
theorem inverseSquare_compl_tail :
    Tendsto (fun s : Finset ℤ => ∑' n : {n // n ∉ s}, inverseSquare n)
      atTop (𝓝 0) :=
  tendsto_tsum_compl_atTop_zero inverseSquare

theorem inverseFourth_compl_tail :
    Tendsto (fun s : Finset ℤ => ∑' n : {n // n ∉ s}, inverseFourth n)
      atTop (𝓝 0) :=
  tendsto_tsum_compl_atTop_zero inverseFourth


/-- The source's symmetric integer Fourier cutoff. -/
def symmetricCutoff (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem symmetricCutoff_cofinal : Tendsto symmetricCutoff atTop atTop := by
  apply tendsto_atTop.2
  intro s
  refine eventually_atTop.2 ⟨s.sup Int.natAbs, ?_⟩
  intro N hN n hn
  have hbound : n.natAbs ≤ N := (Finset.le_sup hn).trans hN
  simp only [symmetricCutoff, Finset.mem_Icc]
  omega

theorem inverseSquare_symmetric_tail :
    Tendsto (fun N : ℕ => ∑' n : {n // n ∉ symmetricCutoff N}, inverseSquare n)
      atTop (𝓝 0) :=
  inverseSquare_compl_tail.comp symmetricCutoff_cofinal

theorem inverseFourth_symmetric_tail :
    Tendsto (fun N : ℕ => ∑' n : {n // n ∉ symmetricCutoff N}, inverseFourth n)
      atTop (𝓝 0) :=
  inverseFourth_compl_tail.comp symmetricCutoff_cofinal


end NlsGge.Analysis
