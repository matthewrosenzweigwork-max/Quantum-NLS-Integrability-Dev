import Mathlib
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M008Loops
import NlsGge.Atomic.M.M009Host
import NlsGge.Atomic.M.M009Support3
import NlsGge.Atomic.M.M009Support4
import NlsGge.Atomic.M.M009Support5

                                                                                                             
                                                                                                                     
                                                                                                             
                                                           
                                                                                               
                                                                                                 
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology BigOperators
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section

theorem endpoint_ray (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) {e : ℂ}
    (he : e ∈ segment ℝ (lamMinus φ n) (lamPlus φ n)) :
    ∃ v : ℂ, v ≠ 0 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) δ → e + (ε : ℂ) * v ∈ cutFreeFiber φ := by
  have hweb : e ∈ discU φ n := MContour.own_segment_subset_disc φ hφ n he
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.1 (isOpen_ball (x := discC φ n) (ε := discR φ n)) e hweb
  by_cases hd : lamPlus φ n - lamMinus φ n = 0
  · have hpm : lamPlus φ n = lamMinus φ n := sub_eq_zero.1 hd
    have hee : e = lamMinus φ n := by
      rw [hpm, segment_same] at he; exact he
    refine ⟨1, one_ne_zero, r, hr, fun ε hε => ?_⟩
    apply MContour.gapDiscSeg_domain_subset φ hφ n
    rw [MContour.gapDiscSeg_domain]
    refine ⟨hrb ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, mul_one, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos hε.1]; exact hε.2
    · rw [hpm, segment_same]
      intro h
      have : e + (ε : ℂ) * 1 = lamMinus φ n := h
      rw [hee] at this
      have h2 : (ε : ℂ) = 0 := by linear_combination this
      exact hε.1.ne' (by exact_mod_cast h2)
  · have hv : Complex.I * (lamPlus φ n - lamMinus φ n) ≠ 0 := mul_ne_zero Complex.I_ne_zero hd
    have hvn : 0 < ‖Complex.I * (lamPlus φ n - lamMinus φ n)‖ := norm_pos_iff.2 hv
    refine ⟨Complex.I * (lamPlus φ n - lamMinus φ n), hv, r / ‖Complex.I * (lamPlus φ n - lamMinus φ n)‖,
      div_pos hr hvn, fun ε hε => ?_⟩
    apply MContour.gapDiscSeg_domain_subset φ hφ n
    rw [MContour.gapDiscSeg_domain]
    refine ⟨hrb ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε.1]
      have := hε.2
      rw [lt_div_iff₀ hvn] at this
      exact this
    · intro h
      rw [segment_eq_image'] at h he
      obtain ⟨s, -, hs⟩ := he
      obtain ⟨u, -, hu⟩ := h
      have hs' : e = lamMinus φ n + (s : ℂ) * (lamPlus φ n - lamMinus φ n) := by
        rw [← hs]; simp [Complex.real_smul]
      have hu' : e + (ε : ℂ) * (Complex.I * (lamPlus φ n - lamMinus φ n)) =
          lamMinus φ n + (u : ℂ) * (lamPlus φ n - lamMinus φ n) := by
        rw [← hu]; simp [Complex.real_smul]
      have h3 : ((u : ℂ) - s - ε * Complex.I) * (lamPlus φ n - lamMinus φ n) = 0 := by
        linear_combination (-1 : ℂ) * hu' + hs'
      have h4 : (u : ℂ) - s - ε * Complex.I = 0 := (mul_eq_zero.1 h3).resolve_right hd
      have h5 := congrArg Complex.im h4
      simp at h5
      exact hε.1.ne' (by linarith)

theorem endpoint_nhdsWithin_neBot (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) {e : ℂ}
    (he : e ∈ segment ℝ (lamMinus φ n) (lamPlus φ n)) : (𝓝[cutFreeFiber φ] e).NeBot := by
  obtain ⟨v, -, δ, hδ, hray⟩ := endpoint_ray φ hφ n he
  have ht : Tendsto (fun ε : ℝ => e + (ε : ℂ) * v) (𝓝[>] (0 : ℝ)) (𝓝[cutFreeFiber φ] e) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun ε : ℝ => e + (ε : ℂ) * v) := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
      exact hray ε hε
  exact ht.neBot

theorem fiber_neBot (φ : PotPair) (hφ : φ ∈ gkW) {z : ℂ} (hz : z ∈ endpointClosureFiber φ) :
    (𝓝[cutFreeFiber φ] z).NeBot := by
  rcases hz with hz | ⟨n, hn | hn⟩
  · rw [(cutFreeFiber_isOpen φ hφ).nhdsWithin_eq hz]; infer_instance
  · exact endpoint_nhdsWithin_neBot φ hφ n (hn ▸ left_mem_segment ℝ _ _)
  · exact endpoint_nhdsWithin_neBot φ hφ n (hn ▸ right_mem_segment ℝ _ _)

/-- Base-disc identification: any limit values of the fiber primitive at the two endpoints of a gap agree. -/
theorem fiber_primitive_gap_values_eq (φ : PotPair) (hφ : φ ∈ gkW) {P : ℂ → ℂ}
    (hP : ∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z) (n : ℤ) {l1 l2 : ℂ}
    (h1 : Tendsto P (𝓝[cutFreeFiber φ] (lamMinus φ n)) (𝓝 l1))
    (h2 : Tendsto P (𝓝[cutFreeFiber φ] (lamPlus φ n)) (𝓝 l2)) : l1 = l2 := by
  obtain ⟨ℓ, g1, g2⟩ := fiber_primitive_gap_limits φ hφ hP n
  haveI := endpoint_nhdsWithin_neBot φ hφ n (left_mem_segment ℝ (lamMinus φ n) (lamPlus φ n))
  haveI := endpoint_nhdsWithin_neBot φ hφ n (right_mem_segment ℝ (lamMinus φ n) (lamPlus φ n))
  exact (tendsto_nhds_unique h1 g1).trans (tendsto_nhds_unique g2 h2)

theorem exists_inner_point (φ : PotPair) (hφ : φ ∈ gkW) {a : ℂ} (ha : a ∈ endpointClosureFiber φ) :
    ∃ a' : ℂ, a' ∈ cutFreeFiber φ ∧ ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      a + (t : ℂ) * (a' - a) ∈ cutFreeFiber φ := by
  rcases ha with ha | ⟨n, hn | hn⟩
  · exact ⟨a, ha, fun t _ => by simpa using ha⟩
  · obtain ⟨v, -, δ, hδ, hray⟩ := endpoint_ray φ hφ n (e := a) (by rw [hn]; exact left_mem_segment ℝ _ _)
    refine ⟨a + ((δ / 2 : ℝ) : ℂ) * v, hray _ ⟨by positivity, by linarith⟩, fun t ht => ?_⟩
    have := hray (t * (δ / 2)) ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩
    convert this using 1
    rw [hn] ; push_cast; ring
  · obtain ⟨v, -, δ, hδ, hray⟩ := endpoint_ray φ hφ n (e := a) (by rw [hn]; exact right_mem_segment ℝ _ _)
    refine ⟨a + ((δ / 2 : ℝ) : ℂ) * v, hray _ ⟨by positivity, by linarith⟩, fun t ht => ?_⟩
    have := hray (t * (δ / 2)) ⟨by nlinarith [ht.1], by nlinarith [ht.1, ht.2]⟩
    convert this using 1
    rw [hn] ; push_cast; ring

/-- A chain of the first kind: open pieces and junctions in the cut-free fiber (route helper, Prop only). -/
def FiberChain (φ : PotPair) (a b : ℂ) (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ) : Prop :=
  MContour.ChainCompatible m p ∧
  (∀ i : Fin (m + 1),
    ContinuousOn (p i) (Icc (0 : ℝ) 1) ∧ ContDiffOn ℝ 1 (p i) (Ioo (0 : ℝ) 1)) ∧
  p 0 0 = a ∧ p (Fin.last m) 1 = b ∧
  (∀ (i : Fin (m + 1)) (t : ℝ), t ∈ Ioo (0 : ℝ) 1 → p i t ∈ cutFreeFiber φ) ∧
  (∀ i : Fin m, p i.castSucc 1 ∈ cutFreeFiber φ)

theorem FiberChain.admissible {φ : PotPair} {a b : ℂ} {m : ℕ} {p : Fin (m + 1) → ℝ → ℂ}
    (h : FiberChain φ a b m p) : AdmissiblePrimitiveChain φ a b m p :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, Or.inl ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩⟩

theorem fiberChain_snoc {φ : PotPair} {a b c : ℂ} {m : ℕ} {p : Fin (m + 1) → ℝ → ℂ}
    (hp : FiberChain φ a b m p) (hb : b ∈ cutFreeFiber φ) (q : ℝ → ℂ)
    (hq0 : q 0 = b) (hq1 : q 1 = c) (hqc : ContinuousOn q (Icc (0 : ℝ) 1))
    (hqd : ContDiffOn ℝ 1 q (Ioo (0 : ℝ) 1)) (hqU : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∈ cutFreeFiber φ) :
    FiberChain φ a c (m + 1) (Fin.snoc (α := fun _ => ℝ → ℂ) p q) := by
  obtain ⟨hcompat, hreg, h0, hlast, hopen, hjunc⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i using Fin.lastCases with
    | last => simp [hlast, hq0]
    | cast j =>
      rw [Fin.succ_castSucc]
      simp only [Fin.snoc_castSucc]
      exact hcompat j
  · intro i
    cases i using Fin.lastCases with
    | last => simpa using ⟨hqc, hqd⟩
    | cast j => simpa using hreg j
  · simpa using h0
  · simpa using hq1
  · intro i t ht
    cases i using Fin.lastCases with
    | last => simpa using hqU t ht
    | cast j => simpa using hopen j t ht
  · intro i
    cases i using Fin.lastCases with
    | last => simpa [hlast] using hb
    | cast j => simpa using hjunc j

theorem affine_piece_data (x y : ℂ) :
    ContinuousOn (fun t : ℝ => x + (t : ℂ) * (y - x)) (Icc (0 : ℝ) 1) ∧
    ContDiffOn ℝ 1 (fun t : ℝ => x + (t : ℂ) * (y - x)) (Ioo (0 : ℝ) 1) := by
  have hc : ContDiff ℝ 1 (fun t : ℝ => x + (t : ℂ) * (y - x)) := by
    have : ContDiff ℝ 1 (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
    exact contDiff_const.add (this.mul contDiff_const)
  exact ⟨hc.continuous.continuousOn, hc.contDiffOn⟩

theorem exists_admissible_chain (φ : PotPair) (hφ : φ ∈ gkW) {a b : ℂ}
    (ha : a ∈ endpointClosureFiber φ) (hb : b ∈ endpointClosureFiber φ) :
    ∃ (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ), AdmissiblePrimitiveChain φ a b m p := by
  by_cases hab : a = b
  · subst hab
    refine ⟨0, fun _ _ => a, ?_⟩
    refine ⟨fun i => Fin.elim0 i, fun i => ⟨continuousOn_const, contDiffOn_const⟩, rfl, rfl,
      Or.inr ⟨rfl, fun _ _ _ => rfl⟩⟩
  · obtain ⟨a', ha', haU⟩ := exists_inner_point φ hφ ha
    obtain ⟨b', hb', hbU⟩ := exists_inner_point φ hφ hb
    -- start piece a -> a'
    have h0 : FiberChain φ a a' 0 (fun _ => fun t : ℝ => a + (t : ℂ) * (a' - a)) :=
      ⟨fun i => Fin.elim0 i, fun _ => affine_piece_data a a', by simp, by simp,
        fun _ t ht => haU t ht, fun i => Fin.elim0 i⟩
    -- polygonal fiber path a' -> y
    have key : ∀ y, Relation.ReflTransGen (fun u v : ℂ => segment ℝ u v ⊆ cutFreeFiber φ) a' y →
        ∃ (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ), FiberChain φ a y m p := by
      intro y hy
      induction hy with
      | refl => exact ⟨0, _, h0⟩
      | @tail u w _ hsw ih =>
        obtain ⟨m, p, hp⟩ := ih
        have hu : u ∈ cutFreeFiber φ := hsw (left_mem_segment ℝ u w)
        refine ⟨m + 1, _, fiberChain_snoc hp hu (fun t : ℝ => u + (t : ℂ) * (w - u)) (by simp) (by simp)
          (affine_piece_data u w).1 (affine_piece_data u w).2 (fun t ht => hsw ?_)⟩
        rw [segment_eq_image']
        exact ⟨t, ⟨ht.1.le, ht.2.le⟩, by simp [Complex.real_smul]⟩
    obtain ⟨m, p, hp⟩ := key b' (cutFreeFiber_polygonal φ hφ a' ha' b' hb')
    refine ⟨m + 1, _, (fiberChain_snoc hp hb' (fun t : ℝ => b' + (t : ℂ) * (b - b')) (by simp) (by simp)
      (affine_piece_data b' b).1 (affine_piece_data b' b).2 (fun t ht => ?_)).admissible⟩
    have := hbU (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    convert this using 1
    push_cast; ring

end
end NlsGge.ThirdConsultation.MPrimitive
