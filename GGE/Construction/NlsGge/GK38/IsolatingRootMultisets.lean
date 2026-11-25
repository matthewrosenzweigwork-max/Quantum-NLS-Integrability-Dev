import NlsGge.GK38.IsolatingGeometry

/-! Exact multiplicity multisets from exhaustive labelled roots in separated
circles. Boundary exclusion is proved independently of the count identity. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem isolating_closed_index38 (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) (m n : ℤ) {z : ℂ}
    (hm : z ∈ ball (C m) (R m)) (hn : z ∈ closedBall (C n) (R n)) : m = n := by
  by_contra hmn
  have hsep := isolating_geometry_closure_separated38 C R c N hgeom m n hmn
  have htri := dist_triangle (C m) z (C n)
  have hm' : dist (C m) z < R m := by simpa only [dist_comm] using mem_ball.mp hm
  have hn' : dist z (C n) ≤ R n := mem_closedBall.mp hn
  linarith

theorem isolating_boundary_ne38 (f : ℂ → ℂ) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N)
    (hcover : ∀ z : ℂ, f z = 0 → ∃ m : ℤ, z ∈ ball (C m) (R m))
    (n : ℤ) (z : ℂ) (hz : z ∈ sphere (C n) (R n)) : f z ≠ 0 := by
  intro hzero
  obtain ⟨m, hm⟩ := hcover z hzero
  have he := isolating_closed_index38 C R c N hgeom m n hm (sphere_subset_closedBall hz)
  subst m
  have hlt := mem_ball.mp hm
  have heq := mem_sphere.mp hz
  linarith

theorem isolating_orderNat_eq38 (f : ℂ → ℂ) (z : ℂ) (k : ℕ)
    (h : analyticOrderAt f z = (k : ℕ∞)) : analyticOrderNatAt f z = k := by
  have hfin : analyticOrderAt f z ≠ ⊤ := by rw [h]; simp
  have hh := Nat.cast_analyticOrderNatAt hfin
  rw [h] at hh
  exact_mod_cast hh

theorem isolating_singleton_multiset38 (f : ℂ → ℂ) (L : ℤ → ℂ)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hf : AnalyticOnNhd ℂ f univ) (hgeom : IsolatingGeometry38 C R c N)
    (hL : ∀ n : ℤ, L n ∈ ball (C n) (R n))
    (hcover : ∀ z : ℂ, f z = 0 → ∃ m : ℤ, L m = z)
    (hsimple : ∀ n : ℤ, analyticOrderAt f (L n) = 1) (n : ℤ) :
    ({L n} : Multiset ℂ) = Lib.zeroMultiset f (ball (C n) (R n)) := by
  classical
  have hlocal : ∀ z ∈ closedBall (C n) (R n), f z = 0 → z = L n := by
    intro z hz hfz
    obtain ⟨m, hm⟩ := hcover z hfz
    have hi := isolating_closed_index38 C R c N hgeom m n (hm ▸ hL m) hz
    subst m
    exact hm.symm
  have hNat := isolating_orderNat_eq38 f (L n) 1 (hsimple n)
  symm
  apply Multiset.ext'
  intro z
  rw [Lib.count_zeroMultiset_ball (hf.mono (subset_univ _))]
  by_cases hz : z = L n
  · subst z
    simp [hL n, hNat]
  · have hzero : z ∈ ball (C n) (R n) → analyticOrderNatAt f z = 0 := by
      intro hzball
      have hne : f z ≠ 0 := fun h => hz (hlocal z (ball_subset_closedBall hzball) h)
      by_contra hNatNe
      exact hne (apply_eq_zero_of_analyticOrderNatAt_ne_zero hNatNe)
    by_cases hzball : z ∈ ball (C n) (R n)
    · simp [hz, hzball, hzero hzball]
    · simp [hz, hzball]

theorem isolating_pair_multiset38 (f : ℂ → ℂ) (A B : ℤ → ℂ)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hf : AnalyticOnNhd ℂ f univ) (hgeom : IsolatingGeometry38 C R c N)
    (hA : ∀ n : ℤ, A n ∈ ball (C n) (R n)) (hB : ∀ n : ℤ, B n ∈ ball (C n) (R n))
    (hcover : ∀ z : ℂ, f z = 0 → ∃ m : ℤ, z = A m ∨ z = B m)
    (hordA : ∀ n : ℤ, analyticOrderAt f (A n) = if A n = B n then 2 else 1)
    (hordB : ∀ n : ℤ, analyticOrderAt f (B n) = if A n = B n then 2 else 1) (n : ℤ) :
    (A n ::ₘ B n ::ₘ 0) = Lib.zeroMultiset f (ball (C n) (R n)) := by
  classical
  have hlocal : ∀ z ∈ closedBall (C n) (R n), f z = 0 → z = A n ∨ z = B n := by
    intro z hz hfz
    obtain ⟨m, hm | hm⟩ := hcover z hfz
    · have hi := isolating_closed_index38 C R c N hgeom m n (hm.symm ▸ hA m) hz
      subst m
      exact Or.inl hm
    · have hi := isolating_closed_index38 C R c N hgeom m n (hm.symm ▸ hB m) hz
      subst m
      exact Or.inr hm
  have hNatA : analyticOrderNatAt f (A n) = if A n = B n then 2 else 1 := by
    by_cases hh : A n = B n
    · simp only [ite_eq_left hh]
      exact isolating_orderNat_eq38 f (A n) 2 (by simpa [hh] using hordA n)
    · simp only [ite_eq_right hh]
      exact isolating_orderNat_eq38 f (A n) 1 (by simpa [hh] using hordA n)
  have hNatB : analyticOrderNatAt f (B n) = if A n = B n then 2 else 1 := by
    by_cases hh : A n = B n
    · simp only [ite_eq_left hh]
      exact isolating_orderNat_eq38 f (B n) 2 (by simpa [hh] using hordB n)
    · simp only [ite_eq_right hh]
      exact isolating_orderNat_eq38 f (B n) 1 (by simpa [hh] using hordB n)
  symm
  apply Multiset.ext'
  intro z
  rw [Lib.count_zeroMultiset_ball (hf.mono (subset_univ _))]
  by_cases hzA : z = A n
  · subst z
    by_cases hh : A n = B n <;> simp [hA n, hB n, hNatA, hNatB, hh, eq_comm]
  · by_cases hzB : z = B n
    · subst z
      simp [hB n, hNatB, hzA, Ne.symm hzA]
    · have hzero : z ∈ ball (C n) (R n) → analyticOrderNatAt f z = 0 := by
        intro hzball
        have hne : f z ≠ 0 := by
          intro h
          exact (hlocal z (ball_subset_closedBall hzball) h).elim hzA hzB
        by_contra hNatNe
        exact hne (apply_eq_zero_of_analyticOrderNatAt_ne_zero hNatNe)
      by_cases hzball : z ∈ ball (C n) (R n)
      · simp [hzA, hzB, hzball, hzero hzball]
      · simp [hzA, hzB, hzball]

end
end NlsGge.GK38
