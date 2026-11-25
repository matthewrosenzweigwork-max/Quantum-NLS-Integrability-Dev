import Mathlib
import NlsGge.Atomic.M.M009Support8
import NlsGge.Atomic.G4.G4022

                                                                                                                 
                                                                                                                    
                                                                                               
                                                                                                                         
                                                                                                                    
                                                                                                   
                                                                                                                  
                    
                                                                                                             
                                                                   
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M011Aux
noncomputable section

open NlsGge.ThirdConsultation.MPrimitive

theorem omega_joint_analytic :
    AnalyticOnNhd ℂ (fun q : PotPair × ℂ => MContour.omega q.1 q.2) rootDomain38 := by
  intro q hq
  have h1 : AnalyticAt ℂ (fun p : PotPair × ℂ => deriv (discrim p.1) p.2) q :=
    analyticOnNhd_discrimDeriv_joint38 q (mem_univ q)
  have h2 : AnalyticAt ℂ (fun p : PotPair × ℂ => canonRoot38 p.1 p.2) q := canonRoot_analytic38 q hq
  exact h1.div h2 (canonRoot_ne_zero38 q.1 hq.1 q.2 hq.2)

theorem primitive_sub_eq_integral {ψ : PotPair} (hψ : ψ ∈ gkW) {a b : ℂ}
    (hseg : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → a + (s : ℂ) * (b - a) ∈ cutFreeFiber ψ)
    (ha : a ∈ endpointClosureFiber ψ) (hb : b ∈ endpointClosureFiber ψ) :
    M.primitive ⟨(ψ, b), ⟨hψ, hb⟩⟩ = M.primitive ⟨(ψ, a), ⟨hψ, ha⟩⟩ +
      (b - a) * ∫ s in (0 : ℝ)..1, MContour.omega ψ (a + (s : ℂ) * (b - a)) := by
  obtain ⟨P, L, hP, hLP, -, hL⟩ := symmetric_value_data ψ hψ
  have hval : ∀ z (hz : z ∈ endpointClosureFiber ψ),
      symmetricPrimitive ⟨(ψ, z), ⟨hψ, hz⟩⟩ = L z - L (lamMinus ψ 0) :=
    fun z hz => symmetric_primitive_value_eq hψ (fun z hz => (hL z hz).1) z hz
  have ha' : a ∈ cutFreeFiber ψ := by simpa using hseg 0 ⟨le_rfl, zero_le_one⟩
  have hb' : b ∈ cutFreeFiber ψ := by simpa using hseg 1 ⟨zero_le_one, le_rfl⟩
  show symmetricPrimitive _ = symmetricPrimitive _ + _
  rw [hval b hb, hval a ha, hLP b hb', hLP a ha']
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => P (a + (s : ℂ) * (b - a)))
      (MContour.omega ψ (a + (s : ℂ) * (b - a)) * (b - a)) s := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    have h1 : HasDerivAt (fun w : ℂ => a + w * (b - a)) (b - a) (s : ℂ) := by
      simpa using ((hasDerivAt_id (s : ℂ)).mul_const (b - a)).const_add a
    have h2 := (hP _ (hseg s hs)).comp (s : ℂ) h1
    exact h2.comp_ofReal
  have hcont : ContinuousOn (fun s : ℝ => MContour.omega ψ (a + (s : ℂ) * (b - a)) * (b - a))
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (omega_differentiableOn_fiber ψ hψ).continuousOn.comp (by fun_prop) (fun s hs => hseg s hs)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [intervalIntegral.integral_mul_const] at hftc
  have hab : a + ((1 : ℝ) : ℂ) * (b - a) = b := by push_cast; ring
  have ha0 : a + ((0 : ℝ) : ℂ) * (b - a) = a := by push_cast; ring
  simp only [hab, ha0] at hftc
  linear_combination (-1 : ℂ) * hftc

theorem transport {V : Set PotPair} (hV : IsOpen V) {a b F : PotPair → ℂ}
    (ha : AnalyticOnNhd ℂ a V) (hb : AnalyticOnNhd ℂ b V) (hF : AnalyticOnNhd ℂ F V)
    (hdom : ∀ ψ ∈ V, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      (ψ, a ψ + (s : ℂ) * (b ψ - a ψ)) ∈ rootDomain38)
    (hFa : ∀ ψ ∈ V, ∀ hp : ψ ∈ gkW ∧ a ψ ∈ endpointClosureFiber ψ,
      F ψ = M.primitive ⟨(ψ, a ψ), hp⟩) :
    AnalyticOnNhd ℂ (fun ψ => F ψ + (b ψ - a ψ) *
      ∫ s in (0 : ℝ)..1, MContour.omega ψ (a ψ + (s : ℂ) * (b ψ - a ψ))) V ∧
    ∀ ψ ∈ V, ∀ hp : ψ ∈ gkW ∧ b ψ ∈ endpointClosureFiber ψ,
      F ψ + (b ψ - a ψ) * (∫ s in (0 : ℝ)..1, MContour.omega ψ (a ψ + (s : ℂ) * (b ψ - a ψ))) =
        M.primitive ⟨(ψ, b ψ), hp⟩ := by
  constructor
  · have hI : AnalyticOnNhd ℂ (fun ψ => ∫ s in (0 : ℝ)..1,
        (fun q : PotPair × ℂ => MContour.omega q.1 q.2) (ψ, a ψ + (s : ℂ) * (b ψ - a ψ))) V :=
      NlsGge.G4022Support.segment_integral_analytic hV omega_joint_analytic ha hb hdom
    exact hF.add ((hb.sub ha).mul hI)
  · intro ψ hψ hp
    have hseg : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → a ψ + (s : ℂ) * (b ψ - a ψ) ∈ cutFreeFiber ψ :=
      fun s hs => (hdom ψ hψ s hs).2
    have ha' : a ψ ∈ endpointClosureFiber ψ :=
      Or.inl (by simpa using hseg 0 ⟨le_rfl, zero_le_one⟩)
    rw [primitive_sub_eq_integral hp.1 hseg ha' hp.2, hFa ψ hψ ⟨hp.1, ha'⟩]

/-- A local analytic representative of `psi ↦ primitive (psi, z)` near `φ`. -/
def Good (φ : PotPair) (z : ℂ) : Prop :=
  ∃ V : Set PotPair, IsOpen V ∧ φ ∈ V ∧ ∃ F : PotPair → ℂ,
    (∀ ψ ∈ V, (ψ, z) ∈ rootDomain38 ∧
      ∀ hp : ψ ∈ gkW ∧ z ∈ endpointClosureFiber ψ, F ψ = M.primitive ⟨(ψ, z), hp⟩) ∧
    AnalyticOnNhd ℂ F V

theorem good_step {φ : PotPair} {z z' z0 : ℂ} {V1 : Set PotPair} (hV1 : IsOpen V1) {r : ℝ}
    (hsub : V1 ×ˢ ball z0 r ⊆ rootDomain38) (hz : z ∈ ball z0 r) (hz' : z' ∈ ball z0 r)
    (hφ1 : φ ∈ V1) (hg : Good φ z) : Good φ z' := by
  obtain ⟨V, hV, hφV, F, hFv, hFan⟩ := hg
  have hdom : ∀ ψ ∈ V ∩ V1, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      (ψ, (fun _ : PotPair => z) ψ + (s : ℂ) * ((fun _ : PotPair => z') ψ - (fun _ : PotPair => z) ψ))
        ∈ rootDomain38 := by
    intro ψ hψ s hs
    apply hsub
    refine ⟨hψ.2, ?_⟩
    have := (convex_ball z0 r).add_smul_sub_mem hz hz' hs
    simpa [Complex.real_smul] using this
  obtain ⟨hAn, hVal⟩ := transport (hV.inter hV1) (a := fun _ => z) (b := fun _ => z')
    analyticOnNhd_const analyticOnNhd_const (hFan.mono inter_subset_left) hdom
    (fun ψ hψ hp => (hFv ψ hψ.1).2 hp)
  exact ⟨V ∩ V1, hV.inter hV1, ⟨hφV, hφ1⟩, _, fun ψ hψ => ⟨hsub ⟨hψ.2, hz'⟩, hVal ψ hψ⟩, hAn⟩

theorem good_of_good {φ : PotPair} (hφ : φ ∈ gkW) {z1 z : ℂ} (h1 : z1 ∈ cutFreeFiber φ)
    (hz : z ∈ cutFreeFiber φ) (hg : Good φ z1) : Good φ z := by
  have hpc : IsPreconnected (cutFreeFiber φ) :=
    polygonal_isPreconnected (cutFreeFiber_polygonal φ hφ)
  refine hpc.induction₂' (fun x y => Good φ x → Good φ y) ?_ ?_ h1 hz hg
  · intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_rootDomain38 (φ, x) ⟨hφ, hx⟩
    rw [← ball_prod_same] at hball
    have hev : ∀ᶠ y in 𝓝[cutFreeFiber φ] x, y ∈ ball x ε :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hε)
    filter_upwards [hev] with y hy
    exact ⟨good_step isOpen_ball hball (mem_ball_self hε) hy (mem_ball_self hε),
      good_step isOpen_ball hball hy (mem_ball_self hε) (mem_ball_self hε)⟩
  · intro x y w _ _ _ hxy hyw hx
    exact hyw (hxy hx)

theorem hasEndpointIntegral_of_eq (ψ : PotPair) (p : ℝ → ℂ) (k : ℝ → ℂ)
    (hk : ContinuousOn k (Icc (0 : ℝ) 1))
    (heq : ∀ t ∈ Ioo (0 : ℝ) 1, MContour.omega ψ (p t) * deriv p t = k t) :
    MContour.HasEndpointIntegral ψ p (∫ t in (0 : ℝ)..1, k t) := by
  set kk : ℝ → ℂ := fun t => k (max 0 (min 1 t)) with hkkdef
  have hkk : Continuous kk :=
    hk.comp_continuous (by fun_prop)
      (fun t => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩)
  have hkkeq : ∀ t ∈ Icc (0 : ℝ) 1, kk t = k t := fun t ht => by
    simp only [hkkdef, min_eq_right ht.2, max_eq_right ht.1]
  have hint : ∀ a b : ℝ, IntervalIntegrable kk volume a b := fun a b => hkk.intervalIntegrable a b
  have hsub : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 → uIcc ε (1 - η) ⊆ Ioo (0 : ℝ) 1 := by
    intro ε η hε hη h x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hEq : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
      EqOn (fun t : ℝ => MContour.omega ψ (p t) * deriv p t) kk (uIcc ε (1 - η)) := by
    intro ε η hε hη h t ht
    have ht' := hsub ε η hε hη h ht
    simp only
    rw [heq t ht', hkkeq t (Ioo_subset_Icc_self ht')]
  refine ⟨fun ε η hε hη hεη => ?_, ?_⟩
  · exact (hkk.continuousOn.congr (hEq ε η hε hη hεη)).intervalIntegrable
  · have hK : Continuous (fun x : ℝ => ∫ t in (0 : ℝ)..x, kk t) :=
      intervalIntegral.continuous_primitive hint 0
    have hc : Continuous (fun q : ℝ × ℝ =>
        (∫ t in (0 : ℝ)..(1 - q.2), kk t) - ∫ t in (0 : ℝ)..q.1, kk t) :=
      (hK.comp (by fun_prop)).sub (hK.comp continuous_fst)
    have hval : (∫ t in (0 : ℝ)..(1 - ((0 : ℝ), (0 : ℝ)).2), kk t) -
        (∫ t in (0 : ℝ)..((0 : ℝ), (0 : ℝ)).1, kk t) = ∫ t in (0 : ℝ)..1, k t := by
      simp only [sub_zero, intervalIntegral.integral_same]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le zero_le_one] at ht
      exact hkkeq t ht
    have hlim := (hc.tendsto ((0 : ℝ), (0 : ℝ))).mono_left
      (nhdsWithin_le_nhds (s := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}))
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq
    obtain ⟨h1, h2, h3⟩ := hq
    rw [intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
    exact (intervalIntegral.integral_congr (hEq q.1 q.2 h1 h2 h3)).symm

end
end NlsGge.ThirdConsultation.M011Aux
