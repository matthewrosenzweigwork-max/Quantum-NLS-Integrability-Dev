import LiebLiniger.FixedPeriod.Quantum.HusimiFockBridge
import Mathlib.Analysis.Fourier.AddCircle

/-! Complete finite-mode occupation bases in actual spatial symmetric sectors. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

/-- Equal occupation counts give an actual particle permutation, hence the same symmetric tensor. -/
theorem occupationWordVector_eq_of_count_eq {n d : ℕ} (e : Fin d → Lp ℂ 2 μ)
    (f g : Fin n → Fin d) (hfg : occupationWordCount f = occupationWordCount g) :
    occupationWordVector μ e f = occupationWordVector μ e g := by
  classical
  let efib : ∀ j : Fin d, {i : Fin n // f i = j} ≃ {i : Fin n // g i = j} :=
    fun j => Fintype.equivOfCardEq (congrFun hfg j)
  let σ : Equiv.Perm (Fin n) := Equiv.ofFiberEquiv efib
  have hcomp : (fun i => g (σ i)) = f := by
    funext i
    exact Equiv.ofFiberEquiv_map efib i
  calc
    occupationWordVector μ e f = occupationWordVector μ e (fun i => g (σ i)) := by
      rw [hcomp]
    _ = occupationWordVector μ e g := by
      unfold occupationWordVector
      exact symmetricTensorContinuousMultilinear_permutation μ n σ (fun i => e (g i))

/-- The source normalization is independent of the representing particle word. -/
theorem normalizedOccupationWordVector_eq_of_count_eq {n d : ℕ}
    (e : Fin d → Lp ℂ 2 μ) (f g : Fin n → Fin d)
    (hfg : occupationWordCount f = occupationWordCount g) :
    normalizedOccupationWordVector μ e f = normalizedOccupationWordVector μ e g := by
  unfold normalizedOccupationWordVector
  rw [hfg, occupationWordVector_eq_of_count_eq μ e f g hfg]

end LiebLiniger.FixedPeriod.Quantum
