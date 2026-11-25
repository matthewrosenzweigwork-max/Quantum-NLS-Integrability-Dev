import Mathlib
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M008Loops
import NlsGge.Atomic.M.M008Endpoint
import NlsGge.Atomic.M.M008EndpointConst
import NlsGge.Atomic.M.M008EndpointChains
import NlsGge.Atomic.M.M008EndpointPolygonal
import NlsGge.Atomic.M.M009Host
import NlsGge.Atomic.M.M009Support2
import NlsGge.Atomic.M.M009Support3
import NlsGge.Atomic.M.M009Support4

                                                                                                                         
                                                                                                                           
                                                                                                                            
                                                                                                                  
                                                                                                       
                                                                            
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section

theorem polygonal_isPreconnected {s : Set ℂ}
    (h : ∀ z ∈ s, ∀ w ∈ s,
      Relation.ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ s) z w) : IsPreconnected s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact isPreconnected_empty
  · refine isPreconnected_of_forall x (fun y hy => ?_)
    have key : ∀ y, Relation.ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ s) x y →
        ∃ t, t ⊆ s ∧ x ∈ t ∧ y ∈ t ∧ IsPreconnected t := by
      intro y hxy
      induction hxy with
      | refl => exact ⟨{x}, by simpa using hx, rfl, rfl, isPreconnected_singleton⟩
      | @tail b c _ hbc ih =>
        obtain ⟨t, hts, hxt, hbt, htc⟩ := ih
        exact ⟨t ∪ segment ℝ b c, union_subset hts hbc, Or.inl hxt,
          Or.inr (right_mem_segment ℝ b c),
          htc.union b hbt (left_mem_segment ℝ b c) (convex_segment b c).isPreconnected⟩
    exact key y (h x hx y hy)

theorem gapDomain_eq (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    (MContour.gapDiscSeg φ hφ n).domain = discU φ n ∩ cutFreeFiber φ := by
  ext z
  constructor
  · intro hz
    refine ⟨?_, MContour.gapDiscSeg_domain_subset φ hφ n hz⟩
    rw [MContour.gapDiscSeg_domain] at hz
    exact hz.1
  · rintro ⟨h1, h2⟩
    rw [MContour.gapDiscSeg_domain]
    exact ⟨h1, fun h => h2 (Set.mem_iUnion.2 ⟨n, h⟩)⟩

theorem primitive_eq_add_const (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) {P F : ℂ → ℂ}
    (hP : ∀ z ∈ (MContour.gapDiscSeg φ hφ n).domain, HasDerivAt P (MContour.omega φ z) z)
    (hF : ∀ z ∈ (MContour.gapDiscSeg φ hφ n).domain, HasDerivAt F (MContour.omega φ z) z) :
    ∃ c : ℂ, ∀ z ∈ (MContour.gapDiscSeg φ hφ n).domain, P z = F z + c := by
  set W := (MContour.gapDiscSeg φ hφ n).domain with hW
  have hWo : IsOpen W := isOpen_domain _
  have hWc : IsPreconnected W := polygonal_isPreconnected (MContour.domain_polygonal _)
  rcases W.eq_empty_or_nonempty with h | ⟨y0, hy0⟩
  · exact ⟨0, fun z hz => by rw [h] at hz; exact absurd hz (notMem_empty z)⟩
  · refine ⟨P y0 - F y0, fun z hz => ?_⟩
    have hd : ∀ z ∈ W, HasDerivAt (fun y => P y - F y) 0 z := by
      intro z hz
      have := (hP z hz).sub (hF z hz)
      rwa [sub_self] at this
    have := hWo.is_const_of_deriv_eq_zero hWc (f := fun y => P y - F y)
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (hd y hy).deriv) hz hy0
    have h' : P z - F z = P y0 - F y0 := this
    linear_combination h'

theorem fiber_primitive_gap_limits (φ : PotPair) (hφ : φ ∈ gkW) {P : ℂ → ℂ}
    (hP : ∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z) (n : ℤ) :
    ∃ ℓ : ℂ, Tendsto P (𝓝[cutFreeFiber φ] (lamMinus φ n)) (𝓝 ℓ) ∧
      Tendsto P (𝓝[cutFreeFiber φ] (lamPlus φ n)) (𝓝 ℓ) := by
  have hPD : ∀ z ∈ (MContour.gapDiscSeg φ hφ n).domain, HasDerivAt P (MContour.omega φ z) z :=
    fun z hz => hP z (MContour.gapDiscSeg_domain_subset φ hφ n hz)
  have hdomeq := gapDomain_eq φ hφ n
  have hnh : ∀ e : ℂ, e ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) →
      𝓝[(MContour.gapDiscSeg φ hφ n).domain] e = 𝓝[cutFreeFiber φ] e := by
    intro e he
    rw [hdomeq]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds
      (isOpen_ball.mem_nhds (MContour.own_segment_subset_disc φ hφ n he)))
  have hm := left_mem_segment ℝ (lamMinus φ n) (lamPlus φ n)
  have hp := right_mem_segment ℝ (lamMinus φ n) (lamPlus φ n)
  -- a local primitive F on the slit disc with a common limit at both endpoints
  have hF : ∃ (F : ℂ → ℂ) (ℓ : ℂ),
      (∀ z ∈ (MContour.gapDiscSeg φ hφ n).domain, HasDerivAt F (MContour.omega φ z) z) ∧
      Tendsto F (𝓝[(MContour.gapDiscSeg φ hφ n).domain] (lamMinus φ n)) (𝓝 ℓ) ∧
      Tendsto F (𝓝[(MContour.gapDiscSeg φ hφ n).domain] (lamPlus φ n)) (𝓝 ℓ) := by
    by_cases hgap : lamMinus φ n = lamPlus φ n
    · obtain ⟨Fc, hFc, hcont⟩ := MContour.omega_collapsed_primitive φ hφ n hgap
      have hme : lamMinus φ n ∈ discU φ n :=
        MContour.own_segment_subset_disc φ hφ n hm
      have ht : Tendsto Fc (𝓝[(MContour.gapDiscSeg φ hφ n).domain] (lamMinus φ n))
          (𝓝 (Fc (lamMinus φ n))) :=
        (hcont _ hme).tendsto.mono_left nhdsWithin_le_nhds
      refine ⟨Fc, Fc (lamMinus φ n), hFc, ht, ?_⟩
      rw [← hgap]; exact ht
    · obtain ⟨F, hF, ℓ, h1, h2⟩ := MContour.omega_primitive_common_limit φ hφ n hgap
      exact ⟨F, ℓ, hF, h1, h2⟩
  obtain ⟨F, ℓ, hFD, h1, h2⟩ := hF
  obtain ⟨c, hc⟩ := primitive_eq_add_const φ hφ n hPD hFD
  refine ⟨ℓ + c, ?_, ?_⟩
  · rw [← hnh _ hm]
    refine Tendsto.congr' ?_ (h1.add_const c)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hc z hz).symm
  · rw [← hnh _ hp]
    refine Tendsto.congr' ?_ (h2.add_const c)
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hc z hz).symm

theorem fiber_primitive_endpoint_limit (φ : PotPair) (hφ : φ ∈ gkW) {P : ℂ → ℂ}
    (hP : ∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z)
    {z : ℂ} (hz : z ∈ endpointClosureFiber φ) :
    ∃ ℓ : ℂ, Tendsto P (𝓝[cutFreeFiber φ] z) (𝓝 ℓ) := by
  rcases hz with hz | ⟨n, hn | hn⟩
  · exact ⟨P z, (hP z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩
  · obtain ⟨ℓ, h1, -⟩ := fiber_primitive_gap_limits φ hφ hP n
    exact ⟨ℓ, hn ▸ h1⟩
  · obtain ⟨ℓ, -, h2⟩ := fiber_primitive_gap_limits φ hφ hP n
    exact ⟨ℓ, hn ▸ h2⟩

theorem endpointIntegral_const_zero (φ : PotPair) (q : ℝ → ℂ) (c : ℂ)
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, q t = c) : MContour.HasEndpointIntegral φ q 0 := by
  have hzero : ∀ t ∈ Ioo (0 : ℝ) 1, MContour.omega φ (q t) * deriv q t = 0 := by
    intro t ht
    have hev : q =ᶠ[𝓝 t] fun _ => c := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hq s (Ioo_subset_Icc_self hs)
    rw [hev.deriv_eq]
    simp
  have hIcc : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 → Icc ε (1 - η) ⊆ Ioo (0 : ℝ) 1 := by
    intro ε η hε hη h x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  refine ⟨fun ε η hε hη h => ?_, ?_⟩
  · have hle : ε ≤ 1 - η := by linarith
    have hc : ContinuousOn (fun t : ℝ => MContour.omega φ (q t) * deriv q t) (uIcc ε (1 - η)) := by
      rw [uIcc_of_le hle]
      exact continuousOn_const.congr (fun t ht => hzero t (hIcc ε η hε hη h ht))
    exact hc.intervalIntegrable
  · have : (fun s : ℝ × ℝ => ∫ t in s.1..(1 - s.2), MContour.omega φ (q t) * deriv q t) =ᶠ[
        𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}] ((0 : ℝ), (0 : ℝ))]
        fun _ => (0 : ℂ) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hle : s.1 ≤ 1 - s.2 := by linarith [hs.2.2]
      have : ∫ t in s.1..(1 - s.2), MContour.omega φ (q t) * deriv q t = ∫ t in s.1..(1 - s.2), (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hle] at ht
        exact hzero t (hIcc s.1 s.2 hs.1 hs.2.1 hs.2.2 ht)
      rw [this]; simp
    exact tendsto_const_nhds.congr' this.symm

theorem chain_values_of_limits (φ : PotPair) (hφ : φ ∈ gkW) {P : ℂ → ℂ}
    (hP : ∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z) (L : ℂ → ℂ)
    (hL : ∀ z ∈ endpointClosureFiber φ, Tendsto P (𝓝[cutFreeFiber φ] z) (𝓝 (L z)))
    (a b : ℂ) (ha : a ∈ endpointClosureFiber φ) (hb : b ∈ endpointClosureFiber φ)
    (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ) (hp : AdmissiblePrimitiveChain φ a b m p) :
    MContour.HasFiniteChainIntegral φ m p (L b - L a) := by
  obtain ⟨hcompat, hreg, h0, hlast, hgeo⟩ := hp
  have hω := (omega_differentiableOn_fiber φ hφ).continuousOn
  rcases hgeo with ⟨hopen, hjunc⟩ | ⟨hab, hconst⟩
  · have hstart : ∀ i : Fin (m + 1), p i 0 ∈ endpointClosureFiber φ := by
      intro i
      cases i using Fin.cases with
      | zero => rw [h0]; exact ha
      | succ j => rw [← hcompat j]; exact Or.inl (hjunc j)
    have hend : ∀ i : Fin (m + 1), p i 1 ∈ endpointClosureFiber φ := by
      intro i
      cases i using Fin.lastCases with
      | last => rw [hlast]; exact hb
      | cast j => exact Or.inl (hjunc j)
    refine ⟨fun i => L (p i 1) - L (p i 0), fun i => ?_, ?_⟩
    · exact MContour.endpointIntegral_of_primitive φ (cutFreeFiber φ) hω P hP (p i) (hreg i).1
        (hreg i).2 (hopen i) _ _ (hL _ (hstart i)) (hL _ (hend i))
    · rw [tele_sum_fin m (fun i => L (p i 0)) (fun i => L (p i 1))
        (fun i => by show L (p i.castSucc 1) = L (p i.succ 0); rw [hcompat i]), hlast, h0]
  · subst hab
    refine ⟨fun _ => 0, fun i => ?_, ?_⟩
    · exact endpointIntegral_const_zero φ (p i) a (fun t ht => hconst i t ht)
    · simp

theorem fiber_primitive_chain_values (φ : PotPair) (hφ : φ ∈ gkW) {P : ℂ → ℂ}
    (hP : ∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z) :
    ∃ L : ℂ → ℂ, (∀ z ∈ endpointClosureFiber φ, Tendsto P (𝓝[cutFreeFiber φ] z) (𝓝 (L z))) ∧
      ∀ (a b : ℂ), a ∈ endpointClosureFiber φ → b ∈ endpointClosureFiber φ →
      ∀ (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ), AdmissiblePrimitiveChain φ a b m p →
        MContour.HasFiniteChainIntegral φ m p (L b - L a) := by
  classical
  have hex : ∀ z : ℂ, ∃ ℓ : ℂ, z ∈ endpointClosureFiber φ →
      Tendsto P (𝓝[cutFreeFiber φ] z) (𝓝 ℓ) := by
    intro z
    by_cases hz : z ∈ endpointClosureFiber φ
    · obtain ⟨ℓ, hℓ⟩ := fiber_primitive_endpoint_limit φ hφ hP hz
      exact ⟨ℓ, fun _ => hℓ⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose L hL using hex
  exact ⟨L, hL, chain_values_of_limits φ hφ hP L hL⟩

/-- Pro round 13 section 11, Stage 1 leaf (head verbatim). -/
theorem primitive_chain_integral_exists
    (φ : PotPair) (hφ : φ ∈ gkW)
    (a b : ℂ)
    (ha : a ∈ endpointClosureFiber φ)
    (hb : b ∈ endpointClosureFiber φ)
    (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ)
    (hp : AdmissiblePrimitiveChain φ a b m p) :
  ∃ A : ℂ, MContour.HasFiniteChainIntegral φ m p A := by
  obtain ⟨P, hP⟩ := fiber_omega_primitive φ hφ
  obtain ⟨L, hL⟩ := fiber_primitive_chain_values φ hφ hP
  exact ⟨_, hL.2 a b ha hb m p hp⟩

/-- Pro round 13 section 11, Stage 1 leaf (head verbatim). -/
theorem primitive_path_independent
    (φ : PotPair) (hφ : φ ∈ gkW)
    (a b : ℂ)
    (ha : a ∈ endpointClosureFiber φ)
    (hb : b ∈ endpointClosureFiber φ)
    (m k : ℕ)
    (p : Fin (m + 1) → ℝ → ℂ)
    (q : Fin (k + 1) → ℝ → ℂ)
    (hp : AdmissiblePrimitiveChain φ a b m p)
    (hq : AdmissiblePrimitiveChain φ a b k q) :
  ∃ A : ℂ,
    MContour.HasFiniteChainIntegral φ m p A ∧
    MContour.HasFiniteChainIntegral φ k q A := by
  obtain ⟨P, hP⟩ := fiber_omega_primitive φ hφ
  obtain ⟨L, hL⟩ := fiber_primitive_chain_values φ hφ hP
  exact ⟨_, hL.2 a b ha hb m p hp, hL.2 a b ha hb k q hq⟩

end
end NlsGge.ThirdConsultation.MPrimitive
