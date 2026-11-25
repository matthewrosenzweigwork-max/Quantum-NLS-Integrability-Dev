import NlsGge.Atomic.KST.KST056
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

open Filter
open scoped Topology

namespace NlsGge.Atomic.KST

noncomputable section

/-- If the source sequence `c` is positive and increasing on its one-based
domain and tends to infinity, then the recursively defined minorant also
tends to infinity. This is the unboundedness step in Lemma 9.1 of
Kappeler--Serier--Topalov. -/
theorem dyadicMinorant_tendsto_atTop (c : ℕ → ℝ)
    (hpos : ∀ n, 1 ≤ n → 0 < c n)
    (hmono : MonotoneOn c (Set.Ici 1))
    (hc : Tendsto c atTop atTop) :
    Tendsto (dyadicMinorant c) atTop atTop := by
  have hprops := dyadicMinorant_properties c hpos hmono
  have hdpos := hprops.1
  have hdmonoOn := hprops.2.1
  have hdmono : Monotone (dyadicMinorant c) := by
    intro a b hab
    by_cases ha : a = 0
    · subst a
      cases b with
      | zero => rfl
      | succ b =>
          rw [dyadicMinorant_zero]
          exact le_of_lt (hdpos (b + 1) (by omega))
    · have ha' : 1 ≤ a := by omega
      have hb' : 1 ≤ b := by omega
      exact hdmonoOn (by simp; exact ha') (by simp; exact hb') hab
  rw [hdmono.tendsto_atTop_atTop_iff]
  intro B
  by_contra hno
  have hupper : ∀ n, dyadicMinorant c n ≤ B := by
    intro n
    by_contra hn
    exact hno ⟨n, le_of_not_ge hn⟩
  have hBdd : BddAbove (Set.range (dyadicMinorant c)) := by
    refine ⟨B, ?_⟩
    intro y hy
    rcases hy with ⟨n, rfl⟩
    exact hupper n
  let D : ℝ := sSup (Set.range (dyadicMinorant c))
  have hDpos : 0 < D := by
    have h1D : dyadicMinorant c 1 ≤ D :=
      le_csSup hBdd (Set.mem_range_self 1)
    exact lt_of_lt_of_le (hdpos 1 (by omega)) h1D
  have hDupper (n : ℕ) : dyadicMinorant c n ≤ D :=
    le_csSup hBdd (Set.mem_range_self n)
  have hnear : 3 * D / 4 < D := by nlinarith
  obtain ⟨y, hy, hnear⟩ :=
    exists_lt_of_lt_csSup (Set.range_nonempty _) hnear
  rcases hy with ⟨N, rfl⟩
  have hNpos : 1 ≤ N := by
    by_contra hN
    have hNzero : N = 0 := by omega
    subst N
    simp only [dyadicMinorant_zero] at hnear
    nlinarith [hDpos]
  obtain ⟨K, hK⟩ := (tendsto_atTop_atTop.mp hc) (2 * D + 1)
  let n := max N K
  have hnN : N ≤ n := Nat.le_max_left _ _
  have hnK : K ≤ n := Nat.le_max_right _ _
  have hnpos : 1 ≤ n := le_trans hNpos hnN
  have hdNn : dyadicMinorant c N ≤ dyadicMinorant c n :=
    hdmonoOn (by simp; exact hNpos) (by simp; exact hnpos) hnN
  have hdn : 3 * D / 4 < dyadicMinorant c n := lt_of_lt_of_le hnear hdNn
  have hc2n : 2 * D < c (2 * n) := by
    have hindex : K ≤ 2 * n := by omega
    have hlarge := hK (2 * n) hindex
    linarith
  have hrec := dyadicMinorant_even c n hnpos
  have hmin : min (2 * dyadicMinorant c n) (c (2 * n)) ≤ D := by
    rw [← hrec]
    exact hDupper (2 * n)
  have hcD : D < c (2 * n) := lt_trans (by nlinarith [hDpos]) hc2n
  have hdouble : 2 * dyadicMinorant c n ≤ D := by
    rcases min_le_iff.mp hmin with hleft | hright
    · exact hleft
    · exact (not_le_of_gt hcD hright).elim
  nlinarith [hDpos]

end
end NlsGge.Atomic.KST
