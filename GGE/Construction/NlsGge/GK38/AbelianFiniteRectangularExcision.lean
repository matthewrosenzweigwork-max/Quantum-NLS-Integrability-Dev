import NlsGge.GK38.AbelianRectangularFrame

/-! SOURCE ONLY: finite rectangular holes, using genuine closed-cell Cauchy.
Horizontal integrabilities are earned before telescoping any interval integral.
Exact targets+English preceded proof authoring. UNCOMPILED. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6RectBoundary_horizontal_partition38 (F : ℂ → ℂ) (a : ℕ → ℝ)
    (N : ℕ) (c d : ℝ)
    (hc : ∀ k < N, IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(c : ℂ)*Complex.I))
      volume (a k) (a (k+1)))
    (hd : ∀ k < N, IntervalIntegrable (fun x : ℝ => F ((x : ℂ)+(d : ℂ)*Complex.I))
      volume (a k) (a (k+1))) :
    (∑ k ∈ Finset.range N, p6RectBoundary38 F (a k) (a (k+1)) c d) =
      p6RectBoundary38 F (a 0) (a N) c d := by
  revert hc hd
  induction N with
  | zero =>
      intro hc hd
      simp [p6RectBoundary38]
  | succ N ih =>
      intro hc hd
      have hcN : ∀ k < N, IntervalIntegrable
          (fun x : ℝ => F ((x : ℂ)+(c : ℂ)*Complex.I)) volume (a k) (a (k+1)) :=
        fun k hk => hc k (Nat.lt_succ_of_lt hk)
      have hdN : ∀ k < N, IntervalIntegrable
          (fun x : ℝ => F ((x : ℂ)+(d : ℂ)*Complex.I)) volume (a k) (a (k+1)) :=
        fun k hk => hd k (Nat.lt_succ_of_lt hk)
      rw [Finset.sum_range_succ, ih hcN hdN]
      exact (p6RectBoundary_horizontal_split38 F (a 0) (a N) (a (N+1)) c d
        (IntervalIntegrable.trans_iterate hcN) (hc N (Nat.lt_succ_self N))
        (IntervalIntegrable.trans_iterate hdN) (hd N (Nat.lt_succ_self N))).symm

theorem p6Rect_finite_frame_excision38 (F : ℂ → ℂ) (N : ℕ)
    (a l r lo hi : ℕ → ℝ) (c d : ℝ)
    (hclo : ∀ k < N, c ≤ lo k)
    (hlohi : ∀ k < N, lo k ≤ hi k)
    (hhid : ∀ k < N, hi k ≤ d)
    (hleft : ∀ k < N, DifferentiableOn ℂ F
      ((Set.uIcc (a k) (l k)) ×ℂ (Set.uIcc c d)))
    (hright : ∀ k < N, DifferentiableOn ℂ F
      ((Set.uIcc (r k) (a (k+1))) ×ℂ (Set.uIcc c d)))
    (hbottom : ∀ k < N, DifferentiableOn ℂ F
      ((Set.uIcc (l k) (r k)) ×ℂ (Set.uIcc c (lo k))))
    (htop : ∀ k < N, DifferentiableOn ℂ F
      ((Set.uIcc (l k) (r k)) ×ℂ (Set.uIcc (hi k) d))) :
    p6RectBoundary38 F (a 0) (a N) c d =
      ∑ k ∈ Finset.range N, p6RectBoundary38 F (l k) (r k) (lo k) (hi k) := by
  have hc : ∀ k < N, IntervalIntegrable
      (fun x : ℝ => F ((x : ℂ)+(c : ℂ)*Complex.I)) volume (a k) (a (k+1)) := by
    intro k hk
    have hL := p6Rect_edges_integrable38 F (a k) (l k) c d (hleft k hk).continuousOn
    have hR := p6Rect_edges_integrable38 F (r k) (a (k+1)) c d (hright k hk).continuousOn
    have hB := p6Rect_edges_integrable38 F (l k) (r k) c (lo k) (hbottom k hk).continuousOn
    exact (hL.1.trans hB.1).trans hR.1
  have hd : ∀ k < N, IntervalIntegrable
      (fun x : ℝ => F ((x : ℂ)+(d : ℂ)*Complex.I)) volume (a k) (a (k+1)) := by
    intro k hk
    have hL := p6Rect_edges_integrable38 F (a k) (l k) c d (hleft k hk).continuousOn
    have hR := p6Rect_edges_integrable38 F (r k) (a (k+1)) c d (hright k hk).continuousOn
    have hT := p6Rect_edges_integrable38 F (l k) (r k) (hi k) d (htop k hk).continuousOn
    exact (hL.2.1.trans hT.2.1).trans hR.2.1
  rw [← p6RectBoundary_horizontal_partition38 F a N c d hc hd]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN := Finset.mem_range.mp hk
  exact p6Rect_frame_excision38 F (a k) (l k) (r k) (a (k+1)) c (lo k) (hi k) d
    (hclo k hkN) (hlohi k hkN) (hhid k hkN)
    (hleft k hkN) (hright k hkN) (hbottom k hkN) (htop k hkN)

end
end NlsGge.GK38
