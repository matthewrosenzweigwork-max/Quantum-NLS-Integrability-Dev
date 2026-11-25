import NlsGge.Sobolev.CMBasisSeries
import NlsGge.Sobolev.RectangularBasisChange

/-!
Concrete consequence of the reviewed generic real basis-independence theorem
and the already checked fixed CM real-basis series. This states deterministic
image-norm summability only; it makes no Gaussian Cameron–Martin claim.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace NlsGge.Pilot

variable {lower upper : ℝ}

theorem cmToFullWeightedHilbert_any_sourceBasis_square_sum
    (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    {ι : Type*}
    (b : HilbertBasis ι ℝ (WeightedRealHilbert (cmModeWeight c))) :
    HasSum
      (fun i : ι =>
        ‖cmToFullWeightedHilbert c s
          (le_of_lt (by linarith : 0 < s)) (b i)‖ ^ 2)
      (∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s)) := by
  let T : WeightedRealHilbert (cmModeWeight c) →L[ℝ] FullWeightedHilbert c s :=
    cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
  let b₀ : HilbertBasis (ℤ × Fin 2) ℝ (WeightedRealHilbert (cmModeWeight c)) :=
    weightedRealHilbertBasis (cmModeWeight c)
  have hfixed :
      HasSum (fun p : ℤ × Fin 2 => ‖T (b₀ p)‖ ^ 2)
        (∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s)) := by
    simpa only [T, b₀] using cmToFullWeightedHilbert_basis_square_sum c s hs
  have hfixed_summable : Summable (fun p : ℤ × Fin 2 => ‖T (b₀ p)‖ ^ 2) :=
    hfixed.summable
  have hany :
      HasSum (fun i : ι => ‖T (b i)‖ ^ 2)
        (∑' p : ℤ × Fin 2, ‖T (b₀ p)‖ ^ 2) :=
    hasSum_norm_sq_apply_of_real_hilbertBasis (T := T) b₀ b hfixed_summable
  rw [hfixed.tsum_eq] at hany
  simpa only [T] using hany

theorem cmToFullWeightedHilbert_any_sourceBasis_square_summable
    (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    {ι : Type*}
    (b : HilbertBasis ι ℝ (WeightedRealHilbert (cmModeWeight c))) :
    Summable (fun i : ι =>
      ‖cmToFullWeightedHilbert c s
        (le_of_lt (by linarith : 0 < s)) (b i)‖ ^ 2) :=
  (cmToFullWeightedHilbert_any_sourceBasis_square_sum c s hs b).summable

end NlsGge.Pilot
