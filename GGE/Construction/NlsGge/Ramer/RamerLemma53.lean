import Mathlib

/-!
# Ramer 1974, Lemma 5.3 (stated without proof there)

If `C` is closed and bounded, `W` is continuous on `C` with values in a finite-dimensional
subspace `V`, and `x ↦ x + W x` is injective on `C`, then the inverse of `x ↦ x + W x` on
its image is continuous.
-/

namespace NlsGge.Ramer

open Filter Topology

theorem continuousOn_invFunOn_add_finiteDim {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC : IsClosed C) (hCb : Bornology.IsBounded C) {W : E → E} (hW : ContinuousOn W C)
    (V : Submodule ℝ E) [FiniteDimensional ℝ V] (hWV : ∀ x ∈ C, W x ∈ V)
    (hinj : Set.InjOn (fun x => x + W x) C) :
    ContinuousOn (Function.invFunOn (fun x => x + W x) C) ((fun x => x + W x) '' C) := by
  classical
  set f : E → E := fun x => x + W x with hf
  set g : E → E := Function.invFunOn f C with hg
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_iff_seqContinuous.2 ?_
  intro u y hu
  obtain ⟨y, x0, hx0, rfl⟩ := y
  have hgx0 : g (f x0) = x0 := hinj.leftInvOn_invFunOn hx0
  have hu' : Tendsto (fun k => (u k : E)) atTop (𝓝 (f x0)) := tendsto_subtype_rng.1 hu
  have hmem : ∀ k, g (u k) ∈ C ∧ f (g (u k)) = (u k : E) := fun k =>
    ⟨Function.invFunOn_mem (u k).2, Function.invFunOn_eq (u k).2⟩
  show Tendsto (fun k => g (u k : E)) atTop (𝓝 (g (f x0)))
  rw [hgx0]
  set xs : ℕ → E := fun k => g (u k : E) with hxs
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hu').exists_norm_le
  obtain ⟨R, hR⟩ := hCb.exists_norm_le
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hWk : ∀ k, W (xs k) = (u k : E) - xs k := fun k => by
    have := (hmem k).2
    simp only [hf] at this
    exact eq_sub_of_add_eq' this
  let w : ℕ → V := fun k => ⟨W (xs (ns k)), hWV _ (hmem _).1⟩
  have hw : ∀ k, w k ∈ Metric.closedBall (0 : V) (B + R) := fun k => by
    rw [mem_closedBall_zero_iff]
    show ‖W (xs (ns k))‖ ≤ B + R
    rw [hWk]
    exact (norm_sub_le _ _).trans (add_le_add (hB _ ⟨_, rfl⟩) (hR _ (hmem _).1))
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : V) (B + R)).tendsto_subseq hw
  refine ⟨φ, ?_⟩
  have hWa : Tendsto (fun k => W (xs (ns (φ k)))) atTop (𝓝 (a : E)) :=
    (continuous_subtype_val.tendsto a).comp hlim
  have huφ : Tendsto (fun k => (u (ns (φ k)) : E)) atTop (𝓝 (f x0)) :=
    hu'.comp ((hns.comp hφ.tendsto_atTop))
  have hxlim : Tendsto (fun k => xs (ns (φ k))) atTop (𝓝 (f x0 - a)) := by
    have := huφ.sub hWa
    refine this.congr fun k => ?_
    simp only [hWk]; abel
  have hx'C : f x0 - (a : E) ∈ C :=
    hC.mem_of_tendsto hxlim (Eventually.of_forall fun k => (hmem _).1)
  have hWx' : W (f x0 - a) = a := by
    have h1 : Tendsto (fun k => W (xs (ns (φ k)))) atTop (𝓝 (W (f x0 - a))) :=
      (hW _ hx'C).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hxlim, Eventually.of_forall fun k => (hmem _).1⟩)
    exact tendsto_nhds_unique h1 hWa
  have heq : f (f x0 - a) = f x0 := by
    simp only [hf]
    rw [hWx']; abel
  have : f x0 - (a : E) = x0 := hinj hx'C hx0 heq
  rw [this] at hxlim
  exact hxlim

end NlsGge.Ramer
