                                                                                                                                                                                 
import Mathlib
import NlsGge.GK38.DirichletCharDefs
import NlsGge.GK38.NeumannChar
import NlsGge.GK38.GradFundamentalDefs
import NlsGge.GK38.PairRealBridge
import NlsGge.GK38.PairAnalyticDet

                                                                               
                                                                                                                                 
                                                       

set_option autoImplicit false

namespace NlsGge.Atomic.G1051S3

open NlsGge.GK38

theorem entries (φ : PotPair) (z : ℂ) :
    discrim φ z = monodromyPair φ z 0 0 + monodromyPair φ z 1 1 ∧
    antiDiscrim φ z = monodromyPair φ z 0 1 + monodromyPair φ z 1 0 ∧
    monodromyPair φ z 0 0 * monodromyPair φ z 1 1 - monodromyPair φ z 0 1 * monodromyPair φ z 1 0 = 1 := by
  refine ⟨?_, rfl, ?_⟩
  · show Matrix.trace (monodromyPair φ z) = _
    rw [Matrix.trace_fin_two]
  · have h := det_monodromyPair φ z
    rwa [Matrix.det_fin_two] at h

theorem dirichlet_case (φ : PotPair) (z : ℂ) (h : dirichletChar φ z = 0) :
    discrim φ z ^ 2 - 4 = antiDiscrim φ z ^ 2 := by
  obtain ⟨e1, e2, hdet⟩ := entries φ z
  rw [dirichletChar_eq, div_eq_zero_iff] at h
  rcases h with h | h
  · rw [e1, e2]
    linear_combination (-(monodromyPair φ z 0 0 - monodromyPair φ z 1 1 + monodromyPair φ z 1 0 -
      monodromyPair φ z 0 1)) * h + 4 * hdet
  · exact absurd h (mul_ne_zero (by norm_num) Complex.I_ne_zero)

theorem neumann_case (φ : PotPair) (z : ℂ) (h : neumannChar38 φ z = 0) :
    discrim φ z ^ 2 - 4 = antiDiscrim φ z ^ 2 := by
  obtain ⟨e1, e2, hdet⟩ := entries φ z
  rw [neumannChar38_eq, div_eq_zero_iff] at h
  rcases h with h | h
  · rw [e1, e2]
    linear_combination (-(monodromyPair φ z 0 0 - monodromyPair φ z 1 1 + monodromyPair φ z 0 1 -
      monodromyPair φ z 1 0)) * h + 4 * hdet
  · exact absurd h (mul_ne_zero (by norm_num) Complex.I_ne_zero)

theorem G1051_main :
((
  (∀ (φ : PotPair) (z : ℂ), dirichletChar φ z = 0 →
    discrim φ z ^ 2 - 4 = antiDiscrim φ z ^ 2) ∧
  (∀ (φ : PotPair) (z : ℂ), neumannChar38 φ z = 0 →
    discrim φ z ^ 2 - 4 = antiDiscrim φ z ^ 2)
  : Prop)) := by
  exact ⟨dirichlet_case, neumann_case⟩

end NlsGge.Atomic.G1051S3
