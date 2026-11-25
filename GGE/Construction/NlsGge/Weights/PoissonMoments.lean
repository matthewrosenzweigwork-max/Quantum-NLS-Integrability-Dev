import NlsGge.Weights.Entire
/-! Concrete W02 prerequisites. Targets independently source-reviewed; actual
convergence/moment identities and factorial bounds are proved from pinned inputs. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Weights

def poissonTerm (t : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-t) * t^j / (Nat.factorial j : ℝ)

lemma poissonTerm_nonneg (t : ℝ) (ht : 0 ≤ t) (j : ℕ) :
    0 ≤ poissonTerm t j := by
  unfold poissonTerm
  positivity

lemma poissonTerm_hasSum (t : ℝ) (ht : 0 ≤ t) :
    HasSum (poissonTerm t) 1 := by
  have he : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have hs : HasSum (fun j : ℕ => Real.exp (-t) * (t^j / (Nat.factorial j : ℝ))) 1 := by
    simpa only [he] using (expSeries_hasSum t).mul_left (Real.exp (-t))
  apply hs.congr_fun
  intro j
  exact mul_div_assoc _ _ _

lemma poissonTerm_first_shift (t : ℝ) (j : ℕ) :
    ((j+1 : ℕ) : ℝ) * poissonTerm t (j+1) = t * poissonTerm t j := by
  have hj : ((j+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  simp only [poissonTerm, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp
  <;> ring

lemma poissonTerm_firstMoment_hasSum (t : ℝ) (ht : 0 ≤ t) :
    HasSum (fun j : ℕ => (j : ℝ) * poissonTerm t j) t := by
  have hs : HasSum (fun j : ℕ => ((j+1 : ℕ) : ℝ) * poissonTerm t (j+1)) t := by
    simpa only [mul_one] using ((poissonTerm_hasSum t ht).mul_left t).congr_fun
      (fun j => poissonTerm_first_shift t j)
  simpa using HasSum.zero_add (f := fun j : ℕ => (j : ℝ) * poissonTerm t j) hs

lemma poissonTerm_second_shift (t : ℝ) (j : ℕ) :
    ((j+2 : ℕ) : ℝ) * (((j+2 : ℕ) : ℝ)-1) * poissonTerm t (j+2) =
      t^2 * poissonTerm t j := by
  have hj1 : ((j+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hj2 : ((j+2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  rw [show j+2 = (j+1)+1 by omega]
  simp only [poissonTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp
  <;> ring

lemma poissonTerm_factorialSecondMoment_hasSum (t : ℝ) (ht : 0 ≤ t) :
    HasSum (fun j : ℕ => (j : ℝ) * ((j : ℝ)-1) * poissonTerm t j) (t^2) := by
  have hs : HasSum (fun j : ℕ =>
      ((j+2 : ℕ) : ℝ) * (((j+2 : ℕ) : ℝ)-1) * poissonTerm t (j+2)) (t^2) := by
    simpa only [mul_one] using ((poissonTerm_hasSum t ht).mul_left (t^2)).congr_fun
      (fun j => poissonTerm_second_shift t j)
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, zero_mul, sub_self, mul_zero, zero_add, add_zero] using
      HasSum.sum_range_add (f := fun j : ℕ => (j : ℝ) * ((j : ℝ)-1) * poissonTerm t j)
        (k := 2) hs

lemma poissonTerm_secondMoment_hasSum (t : ℝ) (ht : 0 ≤ t) :
    HasSum (fun j : ℕ => (j : ℝ)^2 * poissonTerm t j) (t^2+t) := by
  apply ((poissonTerm_factorialSecondMoment_hasSum t ht).add
    (poissonTerm_firstMoment_hasSum t ht)).congr_fun
  intro j
  ring

lemma poissonTerm_centeredSecondMoment_hasSum (t : ℝ) (ht : 0 ≤ t) :
    HasSum (fun j : ℕ => ((j : ℝ)-t)^2 * poissonTerm t j) t := by
  have hs := ((poissonTerm_secondMoment_hasSum t ht).sub
    ((poissonTerm_firstMoment_hasSum t ht).mul_left (2*t))).add
    ((poissonTerm_hasSum t ht).mul_left (t^2))
  have hval : (t^2+t) - (2*t)*t + t^2*1 = t := by ring
  rw [hval] at hs
  apply hs.congr_fun
  intro j
  ring

end NlsGge.Weights
