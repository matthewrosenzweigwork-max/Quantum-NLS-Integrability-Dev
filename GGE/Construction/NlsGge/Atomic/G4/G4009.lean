import NlsGge.Atomic.LIB.LIB012

set_option autoImplicit false
noncomputable section

open Filter Metric Set
open scoped Topology

namespace NlsGge.Atomic.G4009

/-- Local finiteness of the exceptional set relative to the open domain: every
point of the domain has a neighborhood meeting `S ∩ D` in only finitely many points. -/
def LocallyFiniteWithin (D S : Set ℂ) : Prop :=
  ∀ z ∈ D, ∃ U ∈ 𝓝 z, (U ∩ (D ∩ S)).Finite

/-- A continuous scalar function on an open domain that is analytic off a
locally finite exceptional set is analytic throughout the domain. The local
finite-set condition is explicitly relative to the domain and imposes no global
finiteness assumption. -/
theorem analyticOnNhd_of_continuousOn_of_locallyFiniteWithin
    {f : ℂ → ℂ} {D S : Set ℂ} (hD : IsOpen D)
    (hcont : ContinuousOn f D) (hfinite : LocallyFiniteWithin D S)
    (han : AnalyticOnNhd ℂ f (D \ S)) : AnalyticOnNhd ℂ f D := by
  intro z hzD
  by_cases hzS : z ∈ S
  · obtain ⟨U, hU, hUfinite⟩ := hfinite z hzD
    let A : Set ℂ := U ∩ (D ∩ S)
    have hAfinite : A.Finite := hUfinite
    have hzA : z ∈ A := ⟨mem_of_mem_nhds hU, hzD, hzS⟩
    have hAminusFinite : (A \ {z}).Finite := hAfinite.subset sdiff_subset
    have hAminusClosed : IsClosed (A \ {z}) := hAminusFinite.isClosed
    have hO : U ∩ D ∩ (A \ {z})ᶜ ∈ 𝓝 z := by
      exact inter_mem (inter_mem hU (hD.mem_nhds hzD))
        (hAminusClosed.isOpen_compl.mem_nhds (by simp [hzA]))
    obtain ⟨r, hr, hclosedBall⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hO
    have hclosedD : closedBall z r ⊆ D := by
      intro w hw
      rcases hclosedBall hw with ⟨⟨_, hwD⟩, _⟩
      exact hwD
    have hpunct : ball z r \ {z} ⊆ D \ S := by
      intro w hw
      rcases hclosedBall (ball_subset_closedBall hw.1) with ⟨⟨hwU, hwD⟩, hwO⟩
      refine ⟨hwD, ?_⟩
      intro hwS
      have hwA : w ∈ A := ⟨hwU, hwD, hwS⟩
      exact hwO ⟨hwA, by simpa using hw.2⟩
    have hanPunct : AnalyticOnNhd ℂ f (ball z r \ {z}) := fun w hw =>
      han w (hpunct hw)
    have hcontBall : ContinuousOn f (closedBall z r) := hcont.mono hclosedD
    have hcompactF : IsCompact (f '' closedBall z r) :=
      (isCompact_closedBall z r).image_of_continuousOn hcontBall
    have hcompactNorm : IsCompact (norm '' (f '' closedBall z r)) :=
      hcompactF.image continuous_norm
    have hnormSubset : norm '' (f '' (ball z r \ {z})) ⊆
        norm '' (f '' closedBall z r) := by
      rintro y ⟨v, ⟨w, hw, rfl⟩, rfl⟩
      rcases hw with ⟨hwball, _hwz⟩
      exact ⟨f w, ⟨w, ball_subset_closedBall hwball, rfl⟩, rfl⟩
    have hbound : BddAbove (norm '' (f '' (ball z r \ {z}))) :=
      hcompactNorm.bddAbove.mono hnormSubset
    obtain ⟨g, hgan, hgeq, _hunique⟩ :=
      NlsGge.Atomic.removable_bounded_puncture hr hanPunct hbound
    have hcontAt : ContinuousAt f z := hcont.continuousAt (hD.mem_nhds hzD)
    have hcontG : ContinuousAt g z :=
      (hgan z (mem_ball_self hr)).continuousAt
    have hballPunct : ball z r ∈ 𝓝[≠] z := by
      rw [mem_nhdsWithin_iff]
      exact ⟨r, hr, fun w hw => hw.1⟩
    have hpunctEq : f =ᶠ[𝓝[≠] z] g := by
      filter_upwards [hballPunct, self_mem_nhdsWithin] with w hw hwz
      exact (hgeq ⟨hw, by simpa using hwz⟩).symm
    have hcenter : f z = g z := by
      exact tendsto_nhds_unique
        (hcontAt.mono_left nhdsWithin_le_nhds)
        (hcontG.mono_left nhdsWithin_le_nhds |>.congr' hpunctEq.symm)
    have hfgeq : f =ᶠ[𝓝 z] g := by
      filter_upwards [Metric.ball_mem_nhds z hr] with w hw
      by_cases hwz : w = z
      · simpa [hwz] using hcenter
      · exact (hgeq ⟨hw, by simpa using hwz⟩).symm
    exact (analyticAt_congr hfgeq).2 (hgan z (mem_ball_self hr))
  · exact han z ⟨hzD, hzS⟩

end NlsGge.Atomic.G4009
