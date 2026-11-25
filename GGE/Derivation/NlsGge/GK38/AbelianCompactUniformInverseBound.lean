import NlsGge.GK38.AbelianAllIndexInverseBound
import NlsGge.GK38.AbelianActualInverseTube

/-! Genuine compactness globalizes earned local all-index inverse bounds.
There is ONE B before the complex neighborhoods and every signed index. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38.P6InverseNeighborhood
noncomputable section
variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem compact_all_index_inverse_bound (K : Set X) (hK : IsCompact K)
    (T : ℤ → X → E →L[ℂ] E)
    (hlocal : ∀ x ∈ K, ∃ B : ℝ, 0 < B ∧ ∀ᶠ y in 𝓝 x, ∀ n : ℤ,
      (T n y).IsInvertible ∧ ‖(T n y).inverse‖ ≤ B) :
    ∃ B : ℝ, ∃ O : Set X, 0 < B ∧ IsOpen O ∧ K ⊆ O ∧
      ∀ y ∈ O, ∀ n : ℤ, (T n y).IsInvertible ∧ ‖(T n y).inverse‖ ≤ B := by
  classical
  choose B hB hnear using (fun x : K => hlocal x x.property)
  let U : K → Set X := fun x => interior
    {y | ∀ n : ℤ, (T n y).IsInvertible ∧ ‖(T n y).inverse‖ ≤ B x}
  have hxU (x : K) : x.val ∈ U x := mem_interior_iff_mem_nhds.mpr (hnear x)
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩
  obtain ⟨F,hF⟩ := hK.elim_finite_subcover U (fun _ => isOpen_interior) hcover
  let M : ℝ := 1+∑ x ∈ F, B x
  have hsum : 0 ≤ ∑ x ∈ F, B x := Finset.sum_nonneg (fun x _ => (hB x).le)
  refine ⟨M,⋃ x ∈ F, U x,?_,isOpen_biUnion (fun x _ => isOpen_interior),hF,?_⟩
  · dsimp [M]
    linarith
  · intro y hy n
    obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp hy
    have hprops := (interior_subset hyx) n
    have hBx : B x ≤ ∑ z ∈ F, B z := Finset.single_le_sum (fun z _ => (hB z).le) hx
    refine ⟨hprops.1,hprops.2.trans (hBx.trans ?_)⟩
    dsimp [M]
    linarith

theorem all_index_inverse_bound_product_tube (x : X) (W : Set X)
    (hW : IsOpen W) (hx : x ∈ W) (K : Set Y) (hK : IsCompact K)
    (T : ℤ → (X × Y) → E →L[ℂ] E)
    (hlocal : ∀ y ∈ K, ∃ B : ℝ, 0 < B ∧ ∀ᶠ p in 𝓝 (x,y), ∀ n : ℤ,
      (T n p).IsInvertible ∧ ‖(T n p).inverse‖ ≤ B) :
    ∃ B : ℝ, ∃ U : Set X, ∃ V : Set Y,
      0 < B ∧ IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ U ⊆ W ∧ K ⊆ V ∧
      ∀ a ∈ U, ∀ b ∈ V, ∀ n : ℤ,
        (T n (a,b)).IsInvertible ∧ ‖(T n (a,b)).inverse‖ ≤ B := by
  have hP : IsCompact (({x} : Set X) ×ˢ K) := isCompact_singleton.prod hK
  have hloc : ∀ p ∈ ({x} : Set X) ×ˢ K,
      ∃ B : ℝ, 0 < B ∧ ∀ᶠ q in 𝓝 p, ∀ n : ℤ,
        (T n q).IsInvertible ∧ ‖(T n q).inverse‖ ≤ B := by
    rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain rfl := mem_singleton_iff.mp ha
    exact hlocal b hb
  obtain ⟨B,O,hB,hO,hPO,hbound⟩ := compact_all_index_inverse_bound _ hP T hloc
  have hKO : ∀ y ∈ K, (x,y) ∈ O := fun y hy => hPO ⟨mem_singleton x,hy⟩
  obtain ⟨U,V,hU,hV,hxU,hUW,hKV,hUV⟩ :=
    NlsGge.GK38.p6Abstract_compact_open_tube38 x W hW hx K hK O hO hKO
  exact ⟨B,U,V,hB,hU,hV,hxU,hUW,hKV,fun a ha b hb n => hbound (a,b) (hUV ⟨ha,hb⟩) n⟩

end
end NlsGge.GK38.P6InverseNeighborhood
