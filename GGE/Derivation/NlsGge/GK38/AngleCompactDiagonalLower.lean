import NlsGge.GK38.AngleAllSignedDiagonalLower
import NlsGge.GK38.AbelianActualInverseTube

/-! A genuine finite subcover globalizes positive local ALL-index diagonal
bounds. Reciprocals are used only after positivity. The tube conclusion has
ONE positive constant before BOTH common neighborhoods and every n,m. -/
set_option autoImplicit false
open Set Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleCompact_all_diagonal_lower38 {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K)
    (T : ℤ → X → Lib.L2Seq →L[ℂ] Lib.L2Seq)
    (hlocal : ∀ x ∈ K, ∃ d : ℝ, 0 < d ∧ ∀ᶠ y in nhds x, ∀ n m : ℤ,
      d ≤ ‖T n y (lp.single 2 m (1 : ℂ)) m‖) :
    ∃ d : ℝ, ∃ O : Set X, 0 < d ∧ IsOpen O ∧ K ⊆ O ∧
      ∀ y ∈ O, ∀ n m : ℤ, d ≤ ‖T n y (lp.single 2 m (1 : ℂ)) m‖ := by
  classical
  choose c hc hnear using (fun x : K => hlocal x x.property)
  let U : K → Set X := fun x => interior
    {y | ∀ n m : ℤ, c x ≤ ‖T n y (lp.single 2 m (1 : ℂ)) m‖}
  have hxU (x : K) : x.val ∈ U x := mem_interior_iff_mem_nhds.mpr (hnear x)
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxU ⟨x,hx⟩⟩
  obtain ⟨F,hF⟩ := hK.elim_finite_subcover U (fun _ => isOpen_interior) hcover
  let M : ℝ := 1+∑ x ∈ F, (c x)⁻¹
  have hsum : 0 ≤ ∑ x ∈ F, (c x)⁻¹ :=
    Finset.sum_nonneg (fun x _ => (inv_pos.mpr (hc x)).le)
  have hM : 0 < M := by dsimp [M]; linarith
  refine ⟨M⁻¹,⋃ x ∈ F, U x,inv_pos.mpr hM,
    isOpen_biUnion (fun x _ => isOpen_interior),hF,?_⟩
  intro y hy n m
  obtain ⟨x,hx,hyx⟩ := mem_iUnion₂.mp hy
  have hcxsum : (c x)⁻¹ ≤ ∑ z ∈ F, (c z)⁻¹ :=
    Finset.single_le_sum (fun z _ => (inv_pos.mpr (hc z)).le) hx
  have hcxM : (c x)⁻¹ ≤ M := hcxsum.trans (le_add_of_nonneg_left zero_le_one)
  have hdc : M⁻¹ ≤ c x := by
    simpa only [inv_inv] using (inv_le_inv₀ hM (inv_pos.mpr (hc x))).mpr hcxM
  exact hdc.trans ((interior_subset hyx) n m)

theorem angleAll_diagonal_lower_product_tube38 {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (W : Set X) (hW : IsOpen W) (hx : x ∈ W)
    (K : Set Y) (hK : IsCompact K)
    (T : ℤ → (X × Y) → Lib.L2Seq →L[ℂ] Lib.L2Seq)
    (hlocal : ∀ y ∈ K, ∃ d : ℝ, 0 < d ∧ ∀ᶠ p in nhds (x,y), ∀ n m : ℤ,
      d ≤ ‖T n p (lp.single 2 m (1 : ℂ)) m‖) :
    ∃ d : ℝ, ∃ U : Set X, ∃ V : Set Y,
      0 < d ∧ IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ U ⊆ W ∧ K ⊆ V ∧
      ∀ a ∈ U, ∀ b ∈ V, ∀ n m : ℤ,
        d ≤ ‖T n (a,b) (lp.single 2 m (1 : ℂ)) m‖ := by
  have hP : IsCompact (({x} : Set X) ×ˢ K) := isCompact_singleton.prod hK
  have hloc : ∀ p ∈ ({x} : Set X) ×ˢ K,
      ∃ d : ℝ, 0 < d ∧ ∀ᶠ q in nhds p, ∀ n m : ℤ,
        d ≤ ‖T n q (lp.single 2 m (1 : ℂ)) m‖ := by
    rintro ⟨a,b⟩ ⟨ha,hb⟩
    obtain rfl := mem_singleton_iff.mp ha
    exact hlocal b hb
  obtain ⟨d,O,hd,hO,hPO,hbound⟩ := angleCompact_all_diagonal_lower38 _ hP T hloc
  have hKO : ∀ y ∈ K, (x,y) ∈ O := fun y hy => hPO ⟨mem_singleton x,hy⟩
  obtain ⟨U,V,hU,hV,hxU,hUW,hKV,hUV⟩ :=
    p6Abstract_compact_open_tube38 x W hW hx K hK O hO hKO
  exact ⟨d,U,V,hd,hU,hV,hxU,hUW,hKV,
    fun a ha b hb n m => hbound (a,b) (hUV ⟨ha,hb⟩) n m⟩

end
end NlsGge.GK38
