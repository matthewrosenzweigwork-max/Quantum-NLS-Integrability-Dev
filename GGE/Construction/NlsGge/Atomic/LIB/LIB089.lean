                                                                                               
                                                                                                            
                                                                     

                                                                                                             
                                       
                                                                             
                                      
                                                               
                                                                                                            
                                             
                                                            
                                                                      

import Mathlib

set_option autoImplicit false

namespace NlsGge.Atomic.LIB089

/-- The principal square root at a positive real is the real square root. -/
lemma cpow_half_ofReal (a : ℝ) (ha : 0 < a) :
    (a : ℂ) ^ ((2 : ℂ)⁻¹) = (Real.sqrt a : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha.le]
  congr 1
  push_cast
  ring

/-- The LIB-089 statement (verbatim from LIB089_COMMAND01.lean.txt). -/
theorem lib089_statement :
    ∀ a : ℝ, 0 < a →
    ∃ (U : Set ℂ) (s : ℂ → ℂ),
      IsOpen U ∧
      (a : ℂ) ∈ U ∧
      AnalyticOnNhd ℂ s U ∧
      s (a : ℂ) = (Real.sqrt a : ℂ) ∧
      (∀ z ∈ U, s z ^ 2 = z) ∧
      AnalyticOnNhd ℝ (fun x : ℝ => s (x : ℂ)) {x : ℝ | (x : ℂ) ∈ U ∧ 0 < x} ∧
      (∀ x : ℝ, (x : ℂ) ∈ U → 0 < x → ∃ r : ℝ, 0 < r ∧ s (x : ℂ) = (r : ℂ)) := by
  intro a ha
  refine ⟨Complex.slitPlane, fun z => z ^ ((2 : ℂ)⁻¹), Complex.isOpen_slitPlane, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofReal_mem_slitPlane.mpr ha
  · intro z hz
    exact (analyticAt_id.cpow analyticAt_const hz)
  · exact cpow_half_ofReal a ha
  · intro z _
    have h := Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)
    simpa using h
  · intro x hx
    have h1 : AnalyticAt ℝ (fun x : ℝ => (x : ℂ)) x := Complex.ofRealCLM.analyticAt x
    have h2 : AnalyticAt ℂ (fun z : ℂ => z ^ ((2 : ℂ)⁻¹)) (x : ℂ) :=
      analyticAt_id.cpow analyticAt_const hx.1
    exact h2.restrictScalars.comp h1
  · intro x hx hpos
    refine ⟨Real.sqrt x, Real.sqrt_pos.mpr hpos, ?_⟩
    exact cpow_half_ofReal x hpos

end NlsGge.Atomic.LIB089

