import NlsGge.GK38.AbelianFullPeriodScalarLimit
import NlsGge.GK38.AbelianFullPeriodVariation
import NlsGge.GK38.AbelianCoordinateLimitL2
import NlsGge.GK38.Lib.HilbertValuedAnalytic

/-! UNCOMPILED genuine full Hilbert period map and its ACTUAL Qstar.
Scalar limit plus bounded finite square masses earns lp2 membership before
bundling. Every derivative/matrix coefficient is realized by the actual map. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem p6FullPeriod_uniform_l2_bound38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (s₀ : Lib.L2Seq) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ φ ∈ U, ∀ s ∈ V,
        Summable (fun m : ℤ => ‖p6FullPeriodCoordinate38 (φ,s) m‖^2) ∧
        (∑' m : ℤ, ‖p6FullPeriodCoordinate38 (φ,s) m‖^2) ≤ B := by
  obtain ⟨U,hU,hUW,V,hV,B,hB,hb⟩ := p2FullPeriod_uniform_l2_bound38 φ₀ hφ₀ s₀
  refine ⟨U,hU,hUW,V,hV,B,hB,?_⟩
  intro φ hφ s hs
  apply p6CoordinateLimit_l2_mass38
    (fun k : ℕ => fun m : ℤ => ((((k : ℤ)-m : ℤ) : ℂ)) *
      abelianPeriod38 m φ (p2FullNumerator38 (k : ℤ) s))
    (p6FullPeriodCoordinate38 (φ,s)) B
  · intro k S
    obtain ⟨hSum,hMass⟩ := hb φ hφ s hs (k : ℤ)
    exact (hSum.sum_le_tsum S (fun _ _ => sq_nonneg _)).trans hMass
  · intro m
    exact p6FullPeriodCoordinate_limit38 φ (hUW hφ) s m

theorem p6FullPeriod_summable38 (p : PotPair × Lib.L2Seq) (hp : p.1 ∈ gkW) :
    Summable (fun m : ℤ => ‖p6FullPeriodCoordinate38 p m‖^2) := by
  obtain ⟨U,hU,_hUW,V,hV,B,_hB,hb⟩ := p6FullPeriod_uniform_l2_bound38 p.1 hp p.2
  exact (hb p.1 (mem_of_mem_nhds hU) p.2 (mem_of_mem_nhds hV)).1

def p6FullFnElement38 (p : PotPair × Lib.L2Seq) (hp : p.1 ∈ gkW) : Lib.L2Seq :=
  ⟨p6FullPeriodCoordinate38 p,
    (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mpr
      (by simpa using p6FullPeriod_summable38 p hp)⟩

def p6FullFn38 (p : PotPair × Lib.L2Seq) : Lib.L2Seq := by
  classical
  exact if hp : p.1 ∈ gkW then p6FullFnElement38 p hp else 0

theorem p6FullFn_apply38 (p : PotPair × Lib.L2Seq) (hp : p.1 ∈ gkW) (m : ℤ) :
    p6FullFn38 p m = p6FullPeriodCoordinate38 p m := by
  simp only [p6FullFn38,dite_eq_left hp]
  rfl

theorem p6FullFn_analytic38 :
    AnalyticOnNhd ℂ p6FullFn38 (gkW ×ˢ (univ : Set Lib.L2Seq)) := by
  apply Lib.analyticOnNhd_of_coords_of_locBdd p6FullFn38 (isOpen_gkW.prod isOpen_univ)
  · intro m p hp
    apply (p6FullPeriodCoordinate_analytic38 m p hp).congr
    filter_upwards [(isOpen_gkW.prod isOpen_univ).mem_nhds hp] with q hq
    exact (p6FullFn_apply38 q hq.1 m).symm
  · intro p hp
    obtain ⟨U,hU,hUW,V,hV,B,hB,hb⟩ := p6FullPeriod_uniform_l2_bound38 p.1 hp.1 p.2
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (prod_mem_nhds hU hV)
    refine ⟨r,hr,Real.sqrt B,?_⟩
    intro q hq
    have hqUV := hball hq
    have hqW : q.1 ∈ gkW := hUW hqUV.1
    have hmass := (hb q.1 hqUV.1 q.2 hqUV.2).2
    have hnorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
      (p6FullFn38 q)
    simp only [ENNReal.toReal_ofNat,Real.rpow_two] at hnorm
    have hsq : ‖p6FullFn38 q‖^2 ≤ B := by
      rw [hnorm]
      simp_rw [p6FullFn_apply38 q hqW]
      exact hmass
    nlinarith [Real.sq_sqrt hB,Real.sqrt_nonneg B,norm_nonneg (p6FullFn38 q)]

def p6Qstar38 (φ : PotPair) (s : Lib.L2Seq) : Lib.L2Seq →L[ℂ] Lib.L2Seq :=
  fderiv ℂ (fun t : Lib.L2Seq => p6FullFn38 (φ,t)) s

theorem p6Qstar_apply38 (φ : PotPair) (hφ : φ ∈ gkW) (s h : Lib.L2Seq) (m : ℤ) :
    p6Qstar38 φ s h m =
      abelianPeriod38 m φ (P6FullNumeratorVariation.fullVariation s h) := by
  let f : Lib.L2Seq → Lib.L2Seq := fun t => p6FullFn38 (φ,t)
  have ha : AnalyticAt ℂ f s := AnalyticAt.comp
    (g := p6FullFn38) (f := fun t : Lib.L2Seq => (φ,t))
    (p6FullFn_analytic38 (φ,s) ⟨hφ,mem_univ _⟩) (analyticAt_const.prod analyticAt_id)
  change (fderiv ℂ f s) h m = _
  rw [Lib.fderiv_coord_apply ha.differentiableAt h m]
  have he : (fun t : Lib.L2Seq => f t m) =
      (fun t : Lib.L2Seq => p6FullPeriodCoordinate38 (φ,t) m) :=
    funext (fun t => p6FullFn_apply38 (φ,t) hφ m)
  rw [he]
  exact P6FullPeriodDerivative.scalar_fderiv_apply m φ hφ s h

theorem p6Qstar_unit_column38 (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) (m r : ℤ) :
    p6Qstar38 φ s (lp.single 2 r (1 : ℂ)) m =
      abelianPeriod38 m φ (fun z : ℂ => (-2/(Real.pi : ℂ))*Lib.omitProd r s z) := by
  rw [p6Qstar_apply38 φ hφ s (lp.single 2 r (1 : ℂ)) m]
  congr 1
  funext z
  exact P6FullNumeratorVariation.fullVariation_unit_column r s z

theorem p6Qstar_joint_inr_fderiv38 (φ : PotPair) (hφ : φ ∈ gkW) (s : Lib.L2Seq) :
    (fderiv ℂ p6FullFn38 (φ,s)).comp
      (ContinuousLinearMap.inr ℂ PotPair Lib.L2Seq) = p6Qstar38 φ s := by
  have hi : HasFDerivAt (fun t : Lib.L2Seq => (φ,t))
      (ContinuousLinearMap.inr ℂ PotPair Lib.L2Seq) s := by
    convert (hasFDerivAt_const φ s).prodMk (hasFDerivAt_id s) using 1 <;> ext x <;> rfl
  have he := (p6FullFn_analytic38 (φ,s) ⟨hφ,mem_univ _⟩).differentiableAt.hasFDerivAt.comp s hi
  exact he.fderiv.symm

theorem p6Qstar_joint_analytic38 :
    AnalyticOnNhd ℂ (fun p : PotPair × Lib.L2Seq => p6Qstar38 p.1 p.2)
      (gkW ×ˢ (univ : Set Lib.L2Seq)) := by
  let T : ((PotPair × Lib.L2Seq) →L[ℂ] Lib.L2Seq) →L[ℂ]
      (Lib.L2Seq →L[ℂ] Lib.L2Seq) :=
    (ContinuousLinearMap.compL ℂ Lib.L2Seq (PotPair × Lib.L2Seq) Lib.L2Seq).flip
      (ContinuousLinearMap.inr ℂ PotPair Lib.L2Seq)
  intro p hp
  have ha := (T.analyticAt _).comp ((p6FullFn_analytic38 p hp).fderiv)
  apply ha.congr
  filter_upwards [(isOpen_gkW.prod isOpen_univ).mem_nhds hp] with q hq
  exact p6Qstar_joint_inr_fderiv38 q.1 hq.1 q.2

end
end NlsGge.GK38
