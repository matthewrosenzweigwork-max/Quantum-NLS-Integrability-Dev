import NlsGge.GK38.AbelianOriginalMidpointSeparators
import NlsGge.GK38.AbelianOriginalColumnIntegrability
import NlsGge.GK38.AbelianFiniteRectangularExcision
import NlsGge.GK38.AbelianFiniteHoleOuterGeometry

/-! SOURCE ONLY: actual finite square-hole excision for the SUPPLIED family.
The original finite head is retained. Genuine horizontal CIs precede the finite
telescope; closed-cell Cauchy supplies each column. No excision identity oracle.
Exact target and English preceded proof. UNCOMPILED, outside next4 scope. -/
set_option autoImplicit false
open Set Metric MeasureTheory
open scoped Interval
namespace NlsGge.GK38
noncomputable section

theorem p6Original_finite_square_excision38 (φ : PotPair) (hφ : φ ∈ gkW)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ C R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) :
    ∃ L : ℕ, ∀ ν : ℕ, L ≤ ν →
      p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z)
        (-(ν*Real.pi+Real.pi/2)) (ν*Real.pi+Real.pi/2)
        (-(ν*Real.pi+Real.pi/2)) (ν*Real.pi+Real.pi/2) =
      ∑ k ∈ Finset.range (2*ν+1),
        p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z)
          ((C ((k : ℤ)-ν)).re-R ((k : ℤ)-ν))
          ((C ((k : ℤ)-ν)).re+R ((k : ℤ)-ν))
          (-R ((k : ℤ)-ν)) (R ((k : ℤ)-ν)) := by
  obtain ⟨c,N,hgeom,hspec⟩ := hfam
  have hfam : IsolatingFamily38 φ C R := ⟨c,N,hgeom,hspec⟩
  obtain ⟨L,hNL,hinside⟩ := p6Isolating_closed_prefix_inside_midpoint38 C R c N hgeom
  refine ⟨max L (N+1),fun ν hν => ?_⟩
  have hLν : L ≤ ν := le_trans (le_max_left _ _) hν
  have hNν : N < ν := lt_of_lt_of_le (Nat.lt_succ_self N) (le_trans (le_max_right _ _) hν)
  let H : ℝ := ν*Real.pi+Real.pi/2
  let a : ℕ → ℝ := fun k => p6OriginalSeparator38 C R ((k : ℤ)-ν-1)
  let m : ℕ → ℤ := fun k => (k : ℤ)-ν
  have ha0 : a 0 = -H := by
    simpa [a,H] using p6OriginalSeparator_tail_left38 C R c N hgeom ν hNν
  have haN : a (2*ν+1) = H := by
    have hi : ((2*ν+1 : ℕ) : ℤ)-(ν : ℤ)-1 = (ν : ℤ) := by omega
    change p6OriginalSeparator38 C R (((2*ν+1 : ℕ) : ℤ)-(ν : ℤ)-1) = H
    rw [hi]
    simpa [H] using p6OriginalSeparator_tail_right38 C R c N hgeom ν hNν
  have hcolumn (k : ℕ) (hk : k < 2*ν+1) :
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(-H : ℂ)*Complex.I) /
        canonRoot38 φ ((x : ℂ)+(-H : ℂ)*Complex.I)) volume (a k) (a (k+1)) ∧
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ)+(H : ℂ)*Complex.I) /
        canonRoot38 φ ((x : ℂ)+(H : ℂ)*Complex.I)) volume (a k) (a (k+1)) ∧
      p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z) (a k) (a (k+1)) (-H) H =
        p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z)
          ((C (m k)).re-R (m k)) ((C (m k)).re+R (m k)) (-R (m k)) (R (m k)) := by
    have hlabel : |m k| ≤ (ν : ℤ) := by dsimp [m]; rw [abs_le]; constructor <;> omega
    have hR : R (m k) ≤ H := le_of_lt
      (p6RealCenter_radius_lt_of_closedBall_inside38 (C (m k)) (R (m k)) H
        ((hgeom.1 (m k)).2) (le_of_lt (isolating_radius_pos38 hfam (m k)))
        (hinside ν hLν (m k) hlabel))
    have ha : a k = p6OriginalSeparator38 C R (m k-1) := rfl
    have hb : a (k+1) = p6OriginalSeparator38 C R (m k) := by
      dsimp [a,m]
      congr 1
      omega
    have hp := p6OriginalSeparator_bounds38 φ C R hfam (m k-1)
    have hn := p6OriginalSeparator_bounds38 φ C R hfam (m k)
    have hpred : m k-1+1=m k := by omega
    rw [hpred] at hp
    have haprev : (C (m k-1)).re+R (m k-1)<a k := by simpa [ha] using hp.1
    have hbnext : a (k+1)<(C (m k+1)).re-R (m k+1) := by simpa [hb] using hn.2
    have haown : a k≤(C (m k)).re-R (m k) := by simpa [ha] using le_of_lt hp.2
    have hbown : (C (m k)).re+R (m k)≤a (k+1) := by simpa [hb] using le_of_lt hn.1
    have hCI := p6Original_column_horizontal_integrable38 φ hφ C R hfam (m k)
      (a k) (a (k+1)) H haprev hbnext haown hbown hR f hf
    exact ⟨hCI.1,hCI.2,p6Original_column_quotient_excision38 φ hφ C R hfam (m k)
      (a k) (a (k+1)) H haprev hbnext haown hbown hR f hf⟩
  have hpartition := p6RectBoundary_horizontal_partition38
    (fun z : ℂ => f z/canonRoot38 φ z) a (2*ν+1) (-H) H
    (fun k hk => by simpa only [Complex.ofReal_neg] using (hcolumn k hk).1)
    (fun k hk => (hcolumn k hk).2.1)
  rw [ha0,haN] at hpartition
  change p6RectBoundary38 (fun z : ℂ => f z/canonRoot38 φ z) (-H) H (-H) H = _
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro k hk
  exact (hcolumn k (Finset.mem_range.mp hk)).2.2

end
end NlsGge.GK38
