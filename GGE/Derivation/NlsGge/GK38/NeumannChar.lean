import NlsGge.GK38.NeumannGauge
import NlsGge.GK38.DirichletChar

/-! GK I.5: physical Neumann characteristic with positive free sine. -/
set_option autoImplicit false
open Filter Topology Set
namespace NlsGge.GK38
noncomputable section

def neumannChar38 (φ : PotPair) (z : ℂ) : ℂ :=
  -((Matrix.mulVec (monodromyPair φ z) ![1, -1]) 0 +
    (Matrix.mulVec (monodromyPair φ z) ![1, -1]) 1) / (2 * Complex.I)

theorem neumannChar38_eq (φ : PotPair) (z : ℂ) :
    neumannChar38 φ z = (monodromyPair φ z 1 1 - monodromyPair φ z 1 0 +
      monodromyPair φ z 0 1 - monodromyPair φ z 0 0) / (2 * Complex.I) := by
  simp only [neumannChar38, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_neg_one]
  congr 1
  ring

theorem neumannChar38_eq_dirichlet_neg (φ : PotPair) (z : ℂ) :
    neumannChar38 φ z = dirichletChar (-φ) z := by
  rw [neumannChar38_eq, dirichletChar_eq, monodromyPair_neg_gauge38]
  simp only [gaugeJ38_conj_apply, gaugeSign38]
  norm_num
  ring

theorem neumannChar38_fun_eq_dirichlet_neg (φ : PotPair) :
    neumannChar38 φ = dirichletChar (-φ) := funext (neumannChar38_eq_dirichlet_neg φ)

theorem neumannChar38_zero_iff_boundary (φ : PotPair) (z : ℂ) :
    neumannChar38 φ z = 0 ↔
      (Matrix.mulVec (monodromyPair φ z) ![1, -1]) 0 +
        (Matrix.mulVec (monodromyPair φ z) ![1, -1]) 1 = 0 := by
  rw [neumannChar38, div_eq_zero_iff]
  simp only [dirichlet_denominator_ne_zero38, or_false, neg_eq_zero]

theorem neumannInitial38 : (![1, -1] : Fin 2 → ℂ) ≠ 0 ∧
    (![1, -1] : Fin 2 → ℂ) 0 + (![1, -1] : Fin 2 → ℂ) 1 = 0 := by
  constructor
  · intro h
    have := congrArg (fun v => v 0) h
    simp at this
  · simp

theorem analyticOnNhd_neumannChar38 :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => neumannChar38 p.1 p.2) univ := by
  have h := (((analyticOnNhd_monodromyPair 1 1).sub (analyticOnNhd_monodromyPair 1 0)).add
    (analyticOnNhd_monodromyPair 0 1)).sub (analyticOnNhd_monodromyPair 0 0)
  simpa only [neumannChar38_eq, Pi.add_apply, Pi.sub_apply] using h.div_const (c := 2 * Complex.I)

theorem analyticOnNhd_neumannChar38_z (φ : PotPair) :
    AnalyticOnNhd ℂ (neumannChar38 φ) univ := by
  rw [neumannChar38_fun_eq_dirichlet_neg]
  exact analyticOnNhd_dirichletChar_z (-φ)

theorem neumannChar38_zero (z : ℂ) : neumannChar38 0 z = Complex.sin z := by
  rw [neumannChar38_eq_dirichlet_neg, neg_zero, dirichletChar_zero]

theorem discrim_neg38 (φ : PotPair) : discrim (-φ) = discrim φ := by
  funext z
  simp [discrim, monodromyPair_neg_gauge38, Matrix.trace, Fin.sum_univ_two,
    gaugeJ38_conj_apply, gaugeSign38]

theorem perChar_neg38 (φ : PotPair) : perChar (-φ) = perChar φ := by
  funext z
  rw [perChar_eq, perChar_eq, congrFun (discrim_neg38 φ) z]

end
end NlsGge.GK38
