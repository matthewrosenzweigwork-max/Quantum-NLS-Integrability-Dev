import NlsGge.GK38.AbelianOmittedMovingGapCube
import NlsGge.GK38.AbelianSolutionTopology

/-! Uncompiled concrete closedness of the actual real gap-zero projection.
No local inverse, properness, finite-fiber or solution-existence oracle. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

abbrev p5RealSolutionSpace38 (n : ℤ) : Type :=
  {p : PhysicalL2 × P3RealSpace38 n //
    p.2 ∈ p5RealGapCube38 n p.1 ∧ p3RealFn38 n p.1 p.2=0}

def p5RealSolutionProjection38 (n : ℤ) : p5RealSolutionSpace38 n → PhysicalL2 :=
  fun p => p.val.1

theorem p5RealSolutionProjection_isClosedMap38 (n : ℤ) :
    IsClosedMap (p5RealSolutionProjection38 n) := by
  classical
  intro A hA
  apply IsSeqClosed.isClosed
  intro u u₀ huA hu
  choose p hpA hpu using huA
  let t : ℕ → P3RealSpace38 n := fun k => (p k).val.2
  have ht (k : ℕ) : t k ∈ p5RealGapCube38 n (u k) := by
    rw [← hpu k]
    exact (p k).property.1
  obtain ⟨t₀,ht₀,s,hs,htlim⟩ := p5Actual_omitted_gap_cube_subseq38 n u u₀ hu t ht
  have hpair : Tendsto (fun k => (u (s k),t (s k))) atTop (𝓝 (u₀,t₀)) :=
    (hu.comp hs.tendsto_atTop).prodMk_nhds htlim
  have hf := (p5RealJointFn_continuous38 n).continuousAt.tendsto.comp hpair
  have hfzero (k : ℕ) : p3RealFn38 n (u (s k)) (t (s k))=0 := by
    rw [← hpu (s k)]
    exact (p (s k)).property.2
  have hz : p3RealFn38 n u₀ t₀=0 := by
    have hc : Tendsto (fun _ : ℕ => (0 : P3RealSpace38 n)) atTop (𝓝 0) :=
      tendsto_const_nhds
    exact tendsto_nhds_unique hf (hc.congr' (Eventually.of_forall (fun k => (hfzero k).symm)))
  let p₀ : p5RealSolutionSpace38 n := ⟨(u₀,t₀),ht₀,hz⟩
  have hpambient : Tendsto (fun k => (p (s k)).val) atTop (𝓝 (u₀,t₀)) := by
    apply hpair.congr'
    apply Eventually.of_forall
    intro k
    apply Prod.ext
    · exact (hpu (s k)).symm
    · rfl
  have hps : Tendsto (fun k => p (s k)) atTop (𝓝 p₀) :=
    tendsto_subtype_rng.mpr hpambient
  exact ⟨p₀,hA.mem_of_tendsto hps (Eventually.of_forall (fun k => hpA (s k))),rfl⟩

end
end NlsGge.GK38
