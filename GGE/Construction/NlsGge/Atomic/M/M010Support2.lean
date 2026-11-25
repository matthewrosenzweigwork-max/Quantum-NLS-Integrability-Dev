import Mathlib
import NlsGge.Atomic.M.M010Support1

                                                                                                                  
                                                                                                           
                                                                                                                           
                                                                                                            
                                                                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section
attribute [local instance] Classical.propDecidable

theorem nonreal_primitive_membership
    (u : PhysicalL2) (z : ℂ) (hz : z.im ≠ 0) :
    realSlice u ∈ gkW ∧ z ∈ cutFreeFiber (realSlice u) :=
  ⟨realSlice_mem_gkW u, nonreal_mem_cutFreeFiber u hz⟩

theorem positiveHeightFilter_neBot : positiveHeightFilter.NeBot := by
  unfold positiveHeightFilter
  refine Filter.comap_neBot_iff.mpr (fun s hs => ?_)
  obtain ⟨t, ht1, ht2⟩ := Filter.nonempty_of_mem (Filter.inter_mem hs
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)))
  exact ⟨⟨t, ht2⟩, ht1⟩

theorem boundaryPoint_true (x : ℝ) (t : PositiveHeight) :
    boundaryPoint x true t = (x : ℂ) + Complex.I * (t.1 : ℂ) := by
  simp [boundaryPoint]

theorem boundaryPoint_false (x : ℝ) (t : PositiveHeight) :
    boundaryPoint x false t = (x : ℂ) - Complex.I * (t.1 : ℂ) := by
  simp [boundaryPoint, sub_eq_add_neg]

theorem boundaryPoint_true_im (x : ℝ) (t : PositiveHeight) : (boundaryPoint x true t).im = t.1 := by
  rw [boundaryPoint_true]; simp

theorem boundaryPoint_false_im (x : ℝ) (t : PositiveHeight) : (boundaryPoint x false t).im = -t.1 := by
  rw [boundaryPoint_false]; simp

theorem hasBoundaryValue_true (u : PhysicalL2) (x : ℝ) :
    HasBoundaryValue u x true (-Complex.I * actualQuasimomentumBoundaryE02_38 u x) := by
  have hmem : ∀ t : PositiveHeight, realSlice u ∈ gkW ∧
      boundaryPoint x true t ∈ endpointClosureFiber (realSlice u) := fun t =>
    ⟨realSlice_mem_gkW u, Or.inl (nonreal_mem_cutFreeFiber u (by
      rw [boundaryPoint_true_im]; exact t.2.ne'))⟩
  refine ⟨fun t => M.primitive ⟨(realSlice u, boundaryPoint x true t), hmem t⟩,
    fun t => ⟨hmem t, rfl⟩, ?_⟩
  have hg : Tendsto (fun ε : ℝ => -Complex.I * actualQuasimomentumE02_38 u ((x : ℂ) + Complex.I * (ε : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 (-Complex.I * actualQuasimomentumBoundaryE02_38 u x)) :=
    ((tendsto_actualQuasimomentumBoundaryE02_38 u x).comp
      (vertical_tendsto_upper_E02_38 x)).const_mul (-Complex.I)
  have hg2 := hg.comp (Filter.tendsto_comap (f := fun t : PositiveHeight => t.1) (x := 𝓝[>] (0 : ℝ)))
  refine hg2.congr (fun t => ?_)
  show -Complex.I * actualQuasimomentumE02_38 u ((x : ℂ) + Complex.I * (t.1 : ℂ)) = _
  rw [← boundaryPoint_true]
  exact ((primitive_formulas u).1 _ (by rw [boundaryPoint_true_im]; exact t.2)).symm

theorem hasBoundaryValue_false (u : PhysicalL2) (x : ℝ) :
    HasBoundaryValue u x false (-Complex.I * conj (actualQuasimomentumBoundaryE02_38 u x)) := by
  have hmem : ∀ t : PositiveHeight, realSlice u ∈ gkW ∧
      boundaryPoint x false t ∈ endpointClosureFiber (realSlice u) := fun t =>
    ⟨realSlice_mem_gkW u, Or.inl (nonreal_mem_cutFreeFiber u (by
      rw [boundaryPoint_false_im]; exact (neg_neg_of_pos t.2).ne))⟩
  refine ⟨fun t => M.primitive ⟨(realSlice u, boundaryPoint x false t), hmem t⟩,
    fun t => ⟨hmem t, rfl⟩, ?_⟩
  have hg : Tendsto (fun ε : ℝ => -Complex.I *
        conj (actualQuasimomentumE02_38 u ((x : ℂ) + Complex.I * (ε : ℂ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (-Complex.I * conj (actualQuasimomentumBoundaryE02_38 u x))) :=
    (((Complex.continuous_conj.tendsto _).comp ((tendsto_actualQuasimomentumBoundaryE02_38 u x).comp
      (vertical_tendsto_upper_E02_38 x))).const_mul (-Complex.I))
  have hg2 := hg.comp (Filter.tendsto_comap (f := fun t : PositiveHeight => t.1) (x := 𝓝[>] (0 : ℝ)))
  refine hg2.congr (fun t => ?_)
  show -Complex.I * conj (actualQuasimomentumE02_38 u ((x : ℂ) + Complex.I * (t.1 : ℂ))) = _
  have hc : conj (boundaryPoint x false t) = (x : ℂ) + Complex.I * (t.1 : ℂ) := by
    rw [boundaryPoint_false]; simp [Complex.conj_ofReal]
  have := (primitive_formulas u).2.1 (boundaryPoint x false t)
    (by rw [boundaryPoint_false_im]; exact neg_neg_of_pos t.2)
  rw [hc] at this
  exact this.symm

theorem hasBoundaryValue_unique (u : PhysicalL2) (x : ℝ) (upper : Bool) {A A' : ℂ}
    (h : HasBoundaryValue u x upper A) (h' : HasBoundaryValue u x upper A') : A = A' := by
  obtain ⟨F, hF, tF⟩ := h
  obtain ⟨F', hF', tF'⟩ := h'
  have hFF : F = F' := by
    funext t
    obtain ⟨ht, e⟩ := hF t
    obtain ⟨ht', e'⟩ := hF' t
    rw [e, e']
  subst hFF
  haveI := positiveHeightFilter_neBot
  exact tendsto_nhds_unique tF tF'

theorem boundary_value_exists_unique
    (u : PhysicalL2) (x : ℝ) (upper : Bool) :
    ∃! A : ℂ, HasBoundaryValue u x upper A := by
  cases upper
  · exact ⟨_, hasBoundaryValue_false u x, fun A hA => hasBoundaryValue_unique u x false hA
      (hasBoundaryValue_false u x)⟩
  · exact ⟨_, hasBoundaryValue_true u x, fun A hA => hasBoundaryValue_unique u x true hA
      (hasBoundaryValue_true u x)⟩

noncomputable def boundaryValue (u : PhysicalL2) (x : ℝ) (upper : Bool) : ℂ :=
  Classical.choose (boundary_value_exists_unique u x upper).exists

theorem boundary_value_characterization
    (u : PhysicalL2) (x : ℝ) (upper : Bool) :
    HasBoundaryValue u x upper (boundaryValue u x upper) ∧
    ∀ A : ℂ, HasBoundaryValue u x upper A → A = boundaryValue u x upper := by
  have hspec : HasBoundaryValue u x upper (boundaryValue u x upper) :=
    Classical.choose_spec (boundary_value_exists_unique u x upper).exists
  exact ⟨hspec, fun A hA => (boundary_value_exists_unique u x upper).unique hA hspec⟩

theorem boundaryValue_true (u : PhysicalL2) (x : ℝ) :
    boundaryValue u x true = -Complex.I * actualQuasimomentumBoundaryE02_38 u x :=
  ((boundary_value_characterization u x true).2 _ (hasBoundaryValue_true u x)).symm

theorem boundaryValue_false (u : PhysicalL2) (x : ℝ) :
    boundaryValue u x false = -Complex.I * conj (actualQuasimomentumBoundaryE02_38 u x) :=
  ((boundary_value_characterization u x false).2 _ (hasBoundaryValue_false u x)).symm

end
end NlsGge.ThirdConsultation.MPrimitive

namespace NlsGge.ThirdConsultation.M

noncomputable def boundaryPrimitive (u : PhysicalL2) (x : ℝ) (upper : Bool) : ℂ :=
  MPrimitive.boundaryValue u x upper

end NlsGge.ThirdConsultation.M
