import NlsGge.GK38.AbelianUniformBound
import NlsGge.GK38.AbelianRestriction

/-! Prospective actual omitted Hilbert realization, AFTER actual common square bounds.
The explicit zero branch outside W carries no analyticity or uniqueness claim there. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem p2OmittedPeriod_uniform_l2_bound38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∀ s ∈ V, ∀ n : ℤ,
        Summable (fun m : P2Index38 n => ‖(((n-m.1:ℤ):ℂ))*
          abelianPeriod38 m.1 φ (p2FullNumerator38 n s)‖^2) ∧
        (∑' m : P2Index38 n, ‖(((n-m.1:ℤ):ℂ))*
          abelianPeriod38 m.1 φ (p2FullNumerator38 n s)‖^2) ≤ B := by
  obtain ⟨U,hU,hUW,V,hV,B,hB,hb⟩ := p2FullPeriod_uniform_l2_bound38 φ₀ hφ₀ s₀
  refine ⟨U,hU,hUW,V,hV,B,hB,?_⟩
  intro φ hφ s hs n
  have h := hb φ hφ s hs n
  refine ⟨h.1.comp_injective (i := fun m : P2Index38 n => m.1) Subtype.val_injective,?_⟩
  exact (Summable.tsum_subtype_le (fun m : ℤ => ‖(((n-m:ℤ):ℂ))*
    abelianPeriod38 m φ (p2FullNumerator38 n s)‖^2) {m : ℤ | m ≠ n}
    (fun m => sq_nonneg _) h.1).trans h.2

theorem p2FnCoord_summable38 (n : ℤ) (p : PotPair × P2Space38 n) (hp : p.1 ∈ gkW) :
    Summable (fun m : P2Index38 n => ‖p2FnCoord38 n p m‖^2) := by
  obtain ⟨U,hU,_hUW,V,hV,B,_hB,hb⟩ :=
    p2OmittedPeriod_uniform_l2_bound38 p.1 hp (p2Extend38 n p.2)
  exact (hb p.1 (mem_of_mem_nhds hU) (p2Extend38 n p.2) (mem_of_mem_nhds hV) n).1

def p2FnElement38 (n : ℤ) (p : PotPair × P2Space38 n) (hp : p.1 ∈ gkW) : P2Space38 n :=
  ⟨p2FnCoord38 n p,(memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)).mpr
    (by simpa using p2FnCoord_summable38 n p hp)⟩

def p2Fn38 (n : ℤ) (p : PotPair × P2Space38 n) : P2Space38 n :=
  by
    classical
    exact if hp : p.1 ∈ gkW then p2FnElement38 n p hp else 0

 theorem p2Fn_apply38 (n : ℤ) (p : PotPair × P2Space38 n) (hp : p.1 ∈ gkW)
    (m : P2Index38 n) : p2Fn38 n p m=p2FnCoord38 n p m := by
  simp only [p2Fn38,dite_eq_left hp]
  rfl

 theorem p2FnCoord_analytic38 (n : ℤ) (m : P2Index38 n) :
    AnalyticOnNhd ℂ (fun p : PotPair × P2Space38 n => p2FnCoord38 n p m)
      (gkW ×ˢ (univ : Set (P2Space38 n))) := by
  intro p hp
  have he : AnalyticAt ℂ (fun q : PotPair × P2Space38 n => (q.1,p2Extend38 n q.2)) p :=
    analyticAt_fst.prod (((p2Extend38 n).analyticAt p.2).comp analyticAt_snd)
  exact AnalyticAt.comp
    (g := fun q : PotPair × Lib.L2Seq => (((n-m.1:ℤ):ℂ))*
      abelianPeriod38 m.1 q.1 (p2FullNumerator38 n q.2))
    (f := fun q : PotPair × P2Space38 n => (q.1,p2Extend38 n q.2))
    (p2FullCoordinate_analytic38 n m.1 (p.1,p2Extend38 n p.2) ⟨hp.1,mem_univ _⟩) he

 theorem p2Fn_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (p2Fn38 n) (gkW ×ˢ (univ : Set (P2Space38 n))) := by
  apply p2AnalyticOnNhd_of_coords_of_locBdd38 n _ (isOpen_gkW.prod isOpen_univ)
  · intro m p hp
    apply (p2FnCoord_analytic38 n m p hp).congr
    filter_upwards [(isOpen_gkW.prod isOpen_univ).mem_nhds hp] with q hq
    exact (p2Fn_apply38 n q hq.1 m).symm
  · intro p hp
    obtain ⟨U,hU,_hUW,V,hV,B,hB,hb⟩ :=
      p2OmittedPeriod_uniform_l2_bound38 p.1 hp.1 (p2Extend38 n p.2)
    have he : ContinuousAt (fun q : PotPair × P2Space38 n => (q.1,p2Extend38 n q.2)) p :=
      continuousAt_fst.prodMk (((p2Extend38 n).continuous.continuousAt).comp continuousAt_snd)
    have hnhds : {q : PotPair × P2Space38 n |
        q.1 ∈ U ∧ p2Extend38 n q.2 ∈ V ∧ q.1 ∈ gkW} ∈ 𝓝 p := by
      have ht := he (prod_mem_nhds hU hV)
      have hw : {q : PotPair × P2Space38 n | q.1 ∈ gkW} ∈ 𝓝 p :=
        continuousAt_fst (isOpen_gkW.mem_nhds hp.1)
      filter_upwards [ht,hw] with q hq hqw
      exact ⟨hq.1,hq.2,hqw⟩
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnhds
    refine ⟨r,hr,Real.sqrt B,?_⟩
    intro q hq
    obtain ⟨hqU,hqV,hqW⟩ := hball hq
    have hmass := (hb q.1 hqU (p2Extend38 n q.2) hqV n).2
    have hnorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ENNReal).toReal) (p2Fn38 n q)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hnorm
    have hsq : ‖p2Fn38 n q‖^2 ≤ B := by
      rw [hnorm]
      have hcoord (m : P2Index38 n) : p2Fn38 n q m =
          (((n-m.1:ℤ):ℂ))*abelianPeriod38 m.1 q.1
            (p2FullNumerator38 n (p2Extend38 n q.2)) := p2Fn_apply38 n q hqW m
      simp_rw [hcoord]
      exact hmass
    nlinarith [Real.sq_sqrt hB,Real.sqrt_nonneg B,norm_nonneg (p2Fn38 n q)]

#print axioms p2OmittedPeriod_uniform_l2_bound38
#print axioms p2FnCoord_summable38
#print axioms p2Fn_apply38
#print axioms p2FnCoord_analytic38
#print axioms p2Fn_analytic38
end
end NlsGge.GK38
