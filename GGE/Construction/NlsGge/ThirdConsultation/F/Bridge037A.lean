import Mathlib
import NlsGge.Hierarchy.RiccatiRealTrigApproxC2_38
import NlsGge.Hierarchy.GaussianTailContractionsF06C2_38

                                                                         
                                                                          
                                                                                       
                                                                                    
                                                                                     
                                                                                           
                                                                                         
                                                                                    
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.F
namespace Bridge037A

/-- Complex coefficient of the mode `n` of the real trigonometric polynomial with cosine
coefficients `a` and sine coefficients `b`: `a 0` at `n = 0`, `(a n - i b n)/2` at `n > 0`,
`(a |n| + i b |n|)/2` at `n < 0`. -/
def modeCoef037 (a b : ℕ → ℝ) (n : ℤ) : ℂ :=
  if n = 0 then (a 0 : ℂ)
  else if 0 < n then ((a n.natAbs : ℂ) - Complex.I * (b n.natAbs : ℂ)) / 2
  else ((a n.natAbs : ℂ) + Complex.I * (b n.natAbs : ℂ)) / 2

/-- Symmetric split of a sum over `Icc (-N) N`. -/
theorem sum_Icc_symm037 (G : ℤ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, G n =
      G 0 + ∑ k ∈ Finset.range N, (G ((k + 1 : ℕ) : ℤ) + G (-((k + 1 : ℕ) : ℤ))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) N)) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    rw [hset, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ]
    · push_cast
      ring
    · simp
    · simp only [Finset.mem_insert, Finset.mem_Icc]
      omega

/-- One positive frequency pair `±(j+1)`: the two modes reproduce the real pair
`a cos θ + b sin θ`, `θ = 2π (j+1) x`. -/
theorem pair037 (a b : ℕ → ℝ) (j : ℕ) (x : ℝ) :
    modeCoef037 a b ((j + 1 : ℕ) : ℤ) *
        Complex.exp (2 * Real.pi * Complex.I * (((j + 1 : ℕ) : ℤ) : ℂ) * (x : ℂ)) +
      modeCoef037 a b (-((j + 1 : ℕ) : ℤ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((-((j + 1 : ℕ) : ℤ) : ℤ) : ℂ) * (x : ℂ)) =
      ((a (j + 1) * Real.cos (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x) +
        b (j + 1) * Real.sin (2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x) : ℝ) : ℂ) := by
  have hpos : (0 : ℤ) < ((j + 1 : ℕ) : ℤ) := by omega
  have hne : ((j + 1 : ℕ) : ℤ) ≠ 0 := ne_of_gt hpos
  have hneg : -((j + 1 : ℕ) : ℤ) ≠ 0 := neg_ne_zero.2 hne
  have hnegpos : ¬ (0 < -((j + 1 : ℕ) : ℤ)) := by omega
  have hnat : ((j + 1 : ℕ) : ℤ).natAbs = j + 1 := rfl
  have hcoef1 : modeCoef037 a b ((j + 1 : ℕ) : ℤ) =
      ((a (j + 1) : ℂ) - Complex.I * (b (j + 1) : ℂ)) / 2 := by
    unfold modeCoef037
    rw [if_neg hne, if_pos hpos, hnat]
  have hcoef2 : modeCoef037 a b (-((j + 1 : ℕ) : ℤ)) =
      ((a (j + 1) : ℂ) + Complex.I * (b (j + 1) : ℂ)) / 2 := by
    unfold modeCoef037
    rw [if_neg hneg, if_neg hnegpos, Int.natAbs_neg, hnat]
  rw [hcoef1, hcoef2]
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = 2 * Real.pi * ((j + 1 : ℕ) : ℝ) * x := ⟨_, rfl⟩
  rw [← hθ]
  have e1 : 2 * Real.pi * Complex.I * (((j + 1 : ℕ) : ℤ) : ℂ) * (x : ℂ) =
      (θ : ℂ) * Complex.I := by
    rw [hθ]; push_cast; ring
  have e2 : 2 * Real.pi * Complex.I * ((-((j + 1 : ℕ) : ℤ) : ℤ) : ℂ) * (x : ℂ) =
      -(θ : ℂ) * Complex.I := by
    rw [hθ]; push_cast; ring
  rw [e1, e2, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_cos, Complex.ofReal_sin]
  unfold Complex.cos Complex.sin
  push_cast
  ring

/-- Real trigonometric polynomials are Fourier-plane realizations: the complex
coefficients `modeCoef037` on the modes `-N..N` reproduce `P` exactly. -/
theorem sum_modes037 (a b : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        modeCoef037 a b n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) =
      ((∑ k ∈ Finset.range (N + 1),
          (a k * Real.cos (2 * Real.pi * (k : ℝ) * x) +
            b k * Real.sin (2 * Real.pi * (k : ℝ) * x)) : ℝ) : ℂ) := by
  rw [sum_Icc_symm037, Finset.sum_range_succ', Complex.ofReal_add, Complex.ofReal_sum]
  have h0 : modeCoef037 a b 0 *
      Complex.exp (2 * Real.pi * Complex.I * (((0 : ℤ)) : ℂ) * (x : ℂ)) =
      ((a 0 * Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) * x) +
        b 0 * Real.sin (2 * Real.pi * ((0 : ℕ) : ℝ) * x) : ℝ) : ℂ) := by
    simp [modeCoef037]
  rw [h0, Finset.sum_congr rfl (fun k _ => pair037 a b k x)]
  ring

/-- Every real trigonometric polynomial is the real-line representative of a Fourier-plane
element of degree `N` (its own degree). -/
theorem trig_realize037 (P : ℝ → ℝ) (hP : IsRealTrigPoly38 P) :
    ∃ (N : ℕ) (z : FourierPlane N), ∀ x : ℝ, planeReal N z x = (P x : ℂ) := by
  obtain ⟨N, a, b, hPx⟩ := hP
  refine ⟨N, fun i => modeCoef037 a b (modeIndex N i), fun x => ?_⟩
  have hT := congrFun (planeReal_eq_tailField38 N (fun i => modeCoef037 a b (modeIndex N i))) x
  rw [hT]
  show ∑ k : Fin (2 * N + 1), modeCoef037 a b (modeIndex N k) *
      Complex.exp (2 * Real.pi * Complex.I * ((modeIndex N k : ℤ) : ℂ) * (x : ℂ)) = (P x : ℂ)
  have hsum : (∑ i : Fin (2 * N + 1),
      modeCoef037 a b (modeIndex N i) *
        Complex.exp (2 * Real.pi * Complex.I * ((modeIndex N i : ℤ) : ℂ) * (x : ℂ))) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        modeCoef037 a b n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) := by
    apply Finset.sum_nbij (modeIndex N)
    · intro i _
      exact Finset.mem_Icc.2 (modeIndex_bounds N i)
    · intro i _ j _ hij
      exact modeIndex_injective N hij
    · intro n hn
      have hn' := Finset.mem_Icc.1 (Finset.mem_coe.1 hn)
      obtain ⟨i, hi⟩ := modeIndex_covers N n hn'.1 hn'.2
      exact ⟨i, Finset.mem_coe.2 (Finset.mem_univ i), hi⟩
    · intro i _
      rfl
  rw [hsum, sum_modes037, hPx x]

end Bridge037A
end NlsGge.ThirdConsultation.F
end

