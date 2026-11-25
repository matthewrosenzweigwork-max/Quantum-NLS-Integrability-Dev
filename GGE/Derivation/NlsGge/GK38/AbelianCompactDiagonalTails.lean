import NlsGge.GK38.Lib.HilbertValuedAnalytic
import Mathlib.Order.Filter.Cofinite

/-! UNCOMPILED compact-operator-family diagonal tail lemma. Actual pointwise
square summability and actual operator-norm continuity are separate premises
to be realized for Qstar. No open-ball uniform tail conclusion is asserted. -/
set_option autoImplicit false
open Set Filter Topology
open scoped Classical
namespace NlsGge.GK38
noncomputable section

theorem p6UnitDiagonal_norm_le_operator38 {ι : Type*}
    (A : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2) (m : ι) :
    ‖A (lp.single 2 m (1 : ℂ)) m‖ ≤ ‖A‖ := by
  have he : ‖lp.single (E := fun _ : ι => ℂ) 2 m (1 : ℂ)‖ ≤ (1 : ℝ) := by
    rw [lp.norm_single (by norm_num : 0 < (2 : ENNReal)),norm_one]
  exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) _ m).trans
    (A.unit_le_opNorm _ he)

theorem p6Compact_diagonal_tails38 {X ι : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K)
    (A : X → (lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2))
    (hA : Continuous A)
    (hs : ∀ x ∈ K, Summable (fun m : ι => ‖A x (lp.single 2 m (1 : ℂ)) m‖^2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset ι, ∀ x ∈ K, ∀ m : ι, m ∉ S →
      ‖A x (lp.single 2 m (1 : ℂ)) m‖ < ε := by
  classical
  have hlocal (x : K) : ∃ V : Set X, V ∈ 𝓝 x.val ∧ ∃ S : Finset ι,
      ∀ y ∈ V, ∀ m : ι, m ∉ S → ‖A y (lp.single 2 m (1 : ℂ)) m‖ < ε := by
    have ht := (hs x.val x.property).tendsto_cofinite_zero.eventually
      (gt_mem_nhds (sq_pos_of_pos (half_pos hε)))
    have hpoint : ∀ᶠ m : ι in cofinite,
        ‖A x.val (lp.single 2 m (1 : ℂ)) m‖ < ε/2 := by
      filter_upwards [ht] with m hm
      nlinarith [norm_nonneg (A x.val (lp.single 2 m (1 : ℂ)) m)]
    have hbad : {m : ι | ¬ ‖A x.val (lp.single 2 m (1 : ℂ)) m‖ < ε/2}.Finite :=
      eventually_cofinite.mp hpoint
    let S : Finset ι := hbad.toFinset
    let V : Set X := {y | ‖A y-A x.val‖ < ε/2}
    have hV : V ∈ 𝓝 x.val := by
      have hc : Continuous (fun y : X => ‖A y-A x.val‖) := (hA.sub continuous_const).norm
      exact hc.continuousAt (gt_mem_nhds (by simpa using half_pos hε))
    refine ⟨V,hV,S,?_⟩
    intro y hy m hm
    have hmSmall : ‖A x.val (lp.single 2 m (1 : ℂ)) m‖ < ε/2 := by
      by_contra hh
      exact hm (by simpa only [S,Set.Finite.mem_toFinset,mem_ofPred_eq] using hh)
    have hd : ‖A y (lp.single 2 m (1 : ℂ)) m-
        A x.val (lp.single 2 m (1 : ℂ)) m‖ ≤ ‖A y-A x.val‖ :=
      p6UnitDiagonal_norm_le_operator38 (A y-A x.val) m
    have hn := norm_le_norm_sub_add (A y (lp.single 2 m (1 : ℂ)) m)
      (A x.val (lp.single 2 m (1 : ℂ)) m)
    change ‖A y-A x.val‖ < ε/2 at hy
    linarith
  choose V hV S hb using hlocal
  obtain ⟨T,hcover⟩ := hK.elim_nhds_subcover' (fun x hx => V ⟨x,hx⟩)
    (fun x hx => hV ⟨x,hx⟩)
  refine ⟨T.biUnion S,?_⟩
  intro x hx m hm
  obtain ⟨y,hy⟩ := mem_iUnion.mp (hcover hx)
  obtain ⟨hyT,hxV⟩ := mem_iUnion.mp hy
  apply hb y x hxV m
  intro hmS
  exact hm (Finset.mem_biUnion.mpr ⟨y,hyT,hmS⟩)

end
end NlsGge.GK38
