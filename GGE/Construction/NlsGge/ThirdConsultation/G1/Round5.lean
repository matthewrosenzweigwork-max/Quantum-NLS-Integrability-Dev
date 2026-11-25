import Mathlib
import NlsGge.Atomic.G1.G1062
import NlsGge.Sobolev.PeriodicBridge
import NlsGge.GK38.GradEigenDefs

                                                                                                                             
                                                                                                    
                                                                                                             
                                                                                                                            
                                                     
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

def weakDerivative (u : PhysicalL2) : PhysicalL2 :=
  let d : ℤ → ℂ := fun n =>
    (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
      reflectedFourierL2 u n
  if h : Memℓp d 2 then reflectedFourierL2.symm ⟨d, h⟩ else 0

def productInL2 (u v : PhysicalL2) : Prop :=
  MemLp (fun x : PhysicalCircle => u x * v x) 2 spatialMeasure

def physicalProduct (u v : PhysicalL2) : PhysicalL2 :=
  if h : productInL2 u v then
    h.toLp (fun x : PhysicalCircle => u x * v x)
  else 0

def wkbList (φ : PotPair) : ℕ → List PhysicalL2
  | 0 => []
  | N + 1 =>
    let a := wkbList φ N
    a ++ [if N = 0 then -φ.2 else
      weakDerivative (a.getD (N - 1) 0) +
        physicalProduct φ.1
          (∑ k ∈ Finset.range (N - 1),
            physicalProduct (a.getD k 0) (a.getD (N - 2 - k) 0))]

def wkbR (φ : PotPair) (n : ℕ) : PhysicalL2 :=
  (wkbList φ n).getD (n - 1) 0

theorem weakDerivative_coeff
    (u : PhysicalL2)
    (hu : Memℓp (fun n : ℤ =>
      (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 u n) 2)
    (n : ℤ) :
    reflectedFourierL2 (weakDerivative u) n =
      (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 u n := by
  unfold weakDerivative
  rw [dif_pos hu]
  simp

theorem physicalProduct_ae
    (u v : PhysicalL2) (huv : productInL2 u v) :
    (physicalProduct u v : PhysicalCircle → ℂ) =ᵐ[spatialMeasure]
      (fun x : PhysicalCircle => u x * v x) := by
  unfold physicalProduct
  rw [dif_pos huv]
  exact MemLp.coeFn_toLp huv

theorem weakDerivative_domain_of_H1
    (u : PhysicalL2) (hu : physicalSobolev 1 u) :
    Memℓp (fun n : ℤ =>
      (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) *
        reflectedFourierL2 u n) 2 := by
  rw [memℓp_gen_iff (by simp)]
  have h2 : Summable (fun n : ℤ => (4 * Real.pi ^ 2) *
      (Real.rpow (japaneseBracket n) (2 * 1) * ‖reflectedFourierL2 u n‖ ^ 2)) :=
    hu.mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h2
  have hb : Real.rpow (japaneseBracket n) (2 * 1) = 1 + (n : ℝ) ^ 2 := by
    have : Real.rpow (japaneseBracket n) (2 * 1) = (japaneseBracket n) ^ (2 : ℕ) := by
      rw [mul_one]; exact Real.rpow_two _ |>.trans rfl
    rw [this, japaneseBracket, Real.sq_sqrt (by positivity)]
  rw [hb]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [norm_mul]
  have e : ‖(-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))‖ = 2 * Real.pi * |(n : ℝ)| := by
    simp [abs_of_pos Real.pi_pos]
  rw [e, mul_pow, mul_pow, sq_abs]
  have hx := sq_nonneg ‖reflectedFourierL2 u n‖
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg Real.pi) hx) (by norm_num : (0:ℝ) ≤ 4)]

end NlsGge.GKDefinitionDesign
end
