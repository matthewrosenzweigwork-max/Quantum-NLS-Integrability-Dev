import NlsGge.GK38.IsolatingCounting

/-! Compact-boundary stability for the four actual entire functions.
Strict sphere comparisons preserve both zero counts and boundary nonvanishing. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

def isolatingChar38 (φ : PotPair) (k : Fin 4) : ℂ → ℂ :=
  ![perChar φ, dirichletChar φ, neumannChar38 φ, deriv (discrim φ)] k

theorem analyticOnNhd_isolatingChar_joint38 (k : Fin 4) :
    AnalyticOnNhd ℂ (fun p : PotPair × ℂ => isolatingChar38 p.1 k p.2) univ := by
  fin_cases k
  · change AnalyticOnNhd ℂ (fun p : PotPair × ℂ => perChar p.1 p.2) univ
    change AnalyticOnNhd ℂ (fun p : PotPair × ℂ => discrim p.1 p.2 ^ 2 - 4) univ
    exact (analyticOnNhd_discrim.pow 2).sub analyticOnNhd_const
  · exact analyticOnNhd_dirichletChar
  · exact analyticOnNhd_neumannChar38
  · exact analyticOnNhd_discrimDeriv_joint38

theorem analyticOnNhd_isolatingChar_z38 (φ : PotPair) (k : Fin 4) :
    AnalyticOnNhd ℂ (isolatingChar38 φ k) univ := by
  fin_cases k
  · exact analyticOnNhd_perChar_z φ
  · exact analyticOnNhd_dirichletChar_z φ
  · exact analyticOnNhd_neumannChar38_z φ
  · exact analyticOnNhd_discrimDeriv38 φ

theorem isolating_one_boundary_stability38 (φ₀ : PotPair) (k : Fin 4) (C : ℂ) (R : ℝ)
    (hR : 0 < R) (hne : ∀ z ∈ sphere C R, isolatingChar38 φ₀ k z ≠ 0) :
    ∀ᶠ φ in 𝓝 φ₀,
      (Lib.zeroMultiset (isolatingChar38 φ k) (ball C R)).card =
        (Lib.zeroMultiset (isolatingChar38 φ₀ k) (ball C R)).card ∧
      ∀ z ∈ sphere C R, isolatingChar38 φ k z ≠ 0 := by
  have hcont : Continuous (fun p : PotPair × ℂ => isolatingChar38 p.1 k p.2) :=
    continuousOn_univ.mp (analyticOnNhd_isolatingChar_joint38 k).continuousOn
  obtain ⟨m, hm, hmin⟩ := Lib.exists_pos_le_norm_sphere hR
    ((analyticOnNhd_isolatingChar_z38 φ₀ k).continuousOn.mono (subset_univ _)) hne
  have hev := Lib.eventually_forall_sphere_norm_sub_lt
    (F := fun φ z => isolatingChar38 φ k z) (c := C) (R := R) hcont.continuousOn φ₀ hm
  filter_upwards [hev] with φ hφ
  refine ⟨Lib.rouche_circle hR ((analyticOnNhd_isolatingChar_z38 φ₀ k).mono (subset_univ _))
    ((analyticOnNhd_isolatingChar_z38 φ k).mono (subset_univ _))
    (fun z hz => (hφ z hz).trans_le (hmin z hz)), ?_⟩
  intro z hz hzero
  have hh := hφ z hz
  rw [hzero, zero_sub, norm_neg] at hh
  exact (not_lt.mpr (hmin z hz)) hh

theorem finite_boundary_stability38 (φ₀ : PotPair) (S : Finset ℤ)
    (C : ℤ → ℂ) (R : ℤ → ℝ)
    (h : ∀ n : ℤ, n ∈ S → 0 < R n ∧ ∀ z : ℂ, z ∈ sphere (C n) (R n) →
      perChar φ₀ z ≠ 0 ∧ dirichletChar φ₀ z ≠ 0 ∧ neumannChar38 φ₀ z ≠ 0 ∧ deriv (discrim φ₀) z ≠ 0) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∀ φ ∈ U, ∀ n : ℤ, n ∈ S →
      (Lib.zeroMultiset (perChar φ) (ball (C n) (R n))).card =
        (Lib.zeroMultiset (perChar φ₀) (ball (C n) (R n))).card ∧
      (Lib.zeroMultiset (dirichletChar φ) (ball (C n) (R n))).card =
        (Lib.zeroMultiset (dirichletChar φ₀) (ball (C n) (R n))).card ∧
      (Lib.zeroMultiset (neumannChar38 φ) (ball (C n) (R n))).card =
        (Lib.zeroMultiset (neumannChar38 φ₀) (ball (C n) (R n))).card ∧
      (Lib.zeroMultiset (deriv (discrim φ)) (ball (C n) (R n))).card =
        (Lib.zeroMultiset (deriv (discrim φ₀)) (ball (C n) (R n))).card ∧
      ∀ z : ℂ, z ∈ sphere (C n) (R n) → perChar φ z ≠ 0 ∧ dirichletChar φ z ≠ 0 ∧
        neumannChar38 φ z ≠ 0 ∧ deriv (discrim φ) z ≠ 0 := by
  have hevent : ∀ᶠ φ in 𝓝 φ₀, ∀ n ∈ S, ∀ k : Fin 4,
      (Lib.zeroMultiset (isolatingChar38 φ k) (ball (C n) (R n))).card =
        (Lib.zeroMultiset (isolatingChar38 φ₀ k) (ball (C n) (R n))).card ∧
      ∀ z ∈ sphere (C n) (R n), isolatingChar38 φ k z ≠ 0 := by
    apply (Filter.eventually_all_finset S).mpr
    intro n hn
    apply Filter.eventually_all.mpr
    intro k
    apply isolating_one_boundary_stability38 φ₀ k (C n) (R n) (h n hn).1
    intro z hz
    fin_cases k
    · exact (h n hn).2 z hz |>.1
    · exact ((h n hn).2 z hz).2.1
    · exact ((h n hn).2 z hz).2.2.1
    · exact ((h n hn).2 z hz).2.2.2
  refine ⟨_, hevent, ?_⟩
  intro φ hφ n hn
  exact ⟨(hφ n hn 0).1, (hφ n hn 1).1, (hφ n hn 2).1, (hφ n hn 3).1,
    fun z hz => ⟨(hφ n hn 0).2 z hz, (hφ n hn 1).2 z hz,
      (hφ n hn 2).2 z hz, (hφ n hn 3).2 z hz⟩⟩

end
end NlsGge.GK38
