import Mathlib
import NlsGge.Atomic.G1.G1102
import NlsGge.Atomic.G5.G5029Sup3
import NlsGge.Atomic.G5.G5001Host

/- G5-029 SUPPORT 5 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5029Sup5.lean, namespace NlsGge.GKDefinitionDesign.G5029Sup5Aux.
   GK Lemma 18.4, first approximation step (proof development G5029_STOP.md N3): at a point w whose k-th and l-th Dirichlet
   points are at the left endpoints of open gaps, approximate w INSIDE Iso(w) by potentials whose k-th and l-th Dirichlet
   points are interior.  Route: G1-102 homeomorphism Iso(w) ~ gapCircleProduct w (signed Dirichlet data); each open gap
   circle is connected (G1102 isConnected_gapCircle) and contains both endpoint data (lower: landed G5029Sup3
   left_datum_mem_gapCircle; upper: right_datum_mem_gapCircle below), so its first projection covers [lower, upper];
   choose data with first coordinate lower + (upper-lower)/(i+2) in gaps k,l, unchanged elsewhere; their limit is the datum of w.
   No hypothesis beyond the stated ones. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G5029Sup5Aux
noncomputable section

theorem endpoint_re_sq_sub_four (b : PhysicalL2) (n : ℤ) :
    (discrim (realSlice b) (actualGapLowerAllE02_38 b n : ℂ)).re ^ 2 - 4 = 0 ∧
    (discrim (realSlice b) (actualGapUpperAllE02_38 b n : ℂ)).re ^ 2 - 4 = 0 := by
  have hv := NlsGge.GK38.gap_discrim_endpoint_values38 b n
  have hs : Real.sin ((n : ℝ) * Real.pi) = 0 := Real.sin_int_mul_pi n
  have h1 := Real.sin_sq_add_cos_sq ((n : ℝ) * Real.pi)
  rw [hs] at h1
  have hre : (2 * (Real.cos ((n : ℝ) * Real.pi) : ℂ)) =
      (((2 * Real.cos ((n : ℝ) * Real.pi)) : ℝ) : ℂ) := by push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hv.1, hre, Complex.ofReal_re]; nlinarith [h1]
  · rw [hv.2, hre, Complex.ofReal_re]; nlinarith [h1]

theorem right_datum_mem_gapCircle (b : PhysicalL2) (n : ℤ)
    (h : actualGapLowerAllE02_38 b n < actualGapUpperAllE02_38 b n) :
    ((actualGapUpperAllE02_38 b n, (0 : ℝ)) : ℝ × ℝ) ∈ gapCircle b n := by
  refine ⟨h.le, le_rfl, ?_⟩
  have := (endpoint_re_sq_sub_four b n).2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  linarith

theorem exists_gapCircle_fst (b : PhysicalL2) (n : ℤ)
    (h : actualGapLowerAllE02_38 b n < actualGapUpperAllE02_38 b n) (x : ℝ)
    (hx : x ∈ Icc (actualGapLowerAllE02_38 b n) (actualGapUpperAllE02_38 b n)) :
    ∃ y : ℝ, ((x, y) : ℝ × ℝ) ∈ gapCircle b n := by
  have hc : IsPreconnected (Prod.fst '' gapCircle b n) :=
    (isConnected_gapCircle n b).isPreconnected.image _ continuous_fst.continuousOn
  have h1 : actualGapLowerAllE02_38 b n ∈ Prod.fst '' gapCircle b n :=
    ⟨_, left_datum_mem_gapCircle b n h, rfl⟩
  have h2 : actualGapUpperAllE02_38 b n ∈ Prod.fst '' gapCircle b n :=
    ⟨_, right_datum_mem_gapCircle b n h, rfl⟩
  obtain ⟨p, hp, hpx⟩ := hc.Icc_subset h1 h2 hx
  refine ⟨p.2, ?_⟩
  rw [← hpx]
  exact hp

theorem gap_seq (b : PhysicalL2) (n : ℤ)
    (h : actualGapLowerAllE02_38 b n < actualGapUpperAllE02_38 b n) :
    ∃ q : ℕ → ℝ × ℝ, (∀ i : ℕ, q i ∈ gapCircle b n) ∧
      (∀ i : ℕ, actualGapLowerAllE02_38 b n < (q i).1 ∧ (q i).1 < actualGapUpperAllE02_38 b n) ∧
      Tendsto q atTop (𝓝 ((actualGapLowerAllE02_38 b n, (0 : ℝ)) : ℝ × ℝ)) := by
  set L := actualGapLowerAllE02_38 b n with hL
  set U := actualGapUpperAllE02_38 b n with hU
  let x : ℕ → ℝ := fun i => L + (U - L) / ((i : ℝ) + 2)
  have hUL : 0 < U - L := sub_pos.2 h
  have hxin : ∀ i : ℕ, L < x i ∧ x i < U := by
    intro i
    have hi : (2 : ℝ) ≤ (i : ℝ) + 2 := by have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
    have hpos : 0 < (i : ℝ) + 2 := by linarith
    have hd : 0 < (U - L) / ((i : ℝ) + 2) := div_pos hUL hpos
    refine ⟨by simp only [x]; linarith, ?_⟩
    have : (U - L) / ((i : ℝ) + 2) < U - L := by
      rw [div_lt_iff₀ hpos]; nlinarith
    simp only [x]; linarith
  have hy : ∀ i : ℕ, ∃ y : ℝ, ((x i, y) : ℝ × ℝ) ∈ gapCircle b n := fun i =>
    exists_gapCircle_fst b n h (x i) ⟨(hxin i).1.le, (hxin i).2.le⟩
  choose y hyc using hy
  refine ⟨fun i => (x i, y i), hyc, hxin, ?_⟩
  have hxt : Tendsto x atTop (𝓝 L) := by
    have hg : Tendsto (fun i : ℕ => (i : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h0 : Tendsto (fun i : ℕ => (U - L) / ((i : ℝ) + 2)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := U - L)).div_atTop hg
    have := (tendsto_const_nhds (x := L)).add h0
    simpa only [add_zero] using this
  have hcont : Continuous (fun t : ℝ => (discrim (realSlice b) (t : ℂ)).re ^ 2 - 4) := by
    have hd : Continuous (discrim (realSlice b)) :=
      continuousOn_univ.1 (analyticOnNhd_discrim_z (realSlice b)).continuousOn
    exact ((Complex.continuous_re.comp (hd.comp Complex.continuous_ofReal)).pow 2).sub continuous_const
  have hg0 : Tendsto (fun i : ℕ => (discrim (realSlice b) (x i : ℂ)).re ^ 2 - 4) atTop (𝓝 0) := by
    have := (hcont.tendsto L).comp hxt
    rw [show (discrim (realSlice b) (L : ℂ)).re ^ 2 - 4 = 0 from (endpoint_re_sq_sub_four b n).1] at this
    exact this
  have hyt : Tendsto y atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp hg0
    rw [Real.sqrt_zero] at hs
    have habs : Tendsto (fun i : ℕ => |y i|) atTop (𝓝 0) := by
      refine hs.congr (fun i => ?_)
      have h2 : (y i) ^ 2 = (discrim (realSlice b) (x i : ℂ)).re ^ 2 - 4 := (hyc i).2.2
      simp only [Function.comp_apply]
      rw [← h2, Real.sqrt_sq_eq_abs]
    exact (tendsto_zero_iff_abs_tendsto_zero y).2 habs
  exact hxt.prodMk_nhds hyt

theorem datum_of_left (b : PhysicalL2) (n : ℤ) (hleft : gkMu b n = actualGapLowerAllE02_38 b n) :
    signedDirichletData b n = ((actualGapLowerAllE02_38 b n, (0 : ℝ)) : ℝ × ℝ) := by
  have hw : b ∈ isospectralSet b := fun z => rfl
  have hm := (signedDirichletData_mem_gapCircle hw n).2.2
  have h1 : (signedDirichletData b n).1 = actualGapLowerAllE02_38 b n := hleft
  rw [h1, (endpoint_re_sq_sub_four b n).1] at hm
  refine Prod.ext h1 ?_
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hm

theorem allLeft_interior_approx (w : PhysicalL2) (k l : ℤ)
    (hk : gkMu w k = actualGapLowerAllE02_38 w k) (hl : gkMu w l = actualGapLowerAllE02_38 w l)
    (hgk : actualGapLowerAllE02_38 w k < actualGapUpperAllE02_38 w k)
    (hgl : actualGapLowerAllE02_38 w l < actualGapUpperAllE02_38 w l) :
    ∃ φ : ℕ → PhysicalL2, (∀ i : ℕ, φ i ∈ isospectralSet w) ∧
      (∀ i : ℕ, InteriorRealDirichletGap k (φ i) ∧ InteriorRealDirichletGap l (φ i)) ∧
      Tendsto φ atTop (𝓝 w) := by
  obtain ⟨qk, hqk, hik, tk⟩ := gap_seq w k hgk
  obtain ⟨ql, hql, hil, tl⟩ := gap_seq w l hgl
  have hw : w ∈ isospectralSet w := fun z => rfl
  let p : ℕ → ℤ → ℝ × ℝ := fun i n =>
    if n = k then qk i else if n = l then ql i else signedDirichletData w n
  have hp : ∀ i : ℕ, p i ∈ gapCircleProduct w := by
    intro i n
    by_cases hnk : n = k
    · subst hnk; simp only [p, if_pos rfl]; exact hqk i
    · by_cases hnl : n = l
      · subst hnl; simp only [p, if_neg hnk, if_pos rfl]; exact hql i
      · simp only [p, if_neg hnk, if_neg hnl]; exact signedDirichletData_mem_gapCircle hw n
  have hin : ∀ (i : ℕ) (n : ℤ), (n = k ∨ n = l) →
      actualGapLowerAllE02_38 w n < (p i n).1 ∧ (p i n).1 < actualGapUpperAllE02_38 w n := by
    intro i n hn
    by_cases hnk : n = k
    · subst hnk; simp only [p, if_pos rfl]; exact hik i
    · have hnl : n = l := hn.resolve_left hnk
      subst hnl; simp only [p, if_neg hnk, if_pos rfl]; exact hil i
  have hlim : Tendsto p atTop (𝓝 (signedDirichletData w)) := by
    refine tendsto_pi_nhds.2 fun n => ?_
    by_cases hnk : n = k
    · subst hnk; simp only [p, if_pos rfl]; rw [datum_of_left w n hk]; exact tk
    · by_cases hnl : n = l
      · subst hnl; simp only [p, if_neg hnk, if_pos rfl]; rw [datum_of_left w n hl]; exact tl
      · simp only [p, if_neg hnk, if_neg hnl]; exact tendsto_const_nhds
  obtain ⟨⟨e, he⟩, -⟩ := G1_102 w
  have hsd : signedDirichletData w ∈ gapCircleProduct w := fun n => signedDirichletData_mem_gapCircle hw n
  let c : ℕ → {q : ℤ → ℝ × ℝ // q ∈ gapCircleProduct w} := fun i => ⟨p i, hp i⟩
  have hc : Tendsto c atTop (𝓝 (⟨signedDirichletData w, hsd⟩ : {q : ℤ → ℝ × ℝ // q ∈ gapCircleProduct w})) :=
    tendsto_subtype_rng.2 hlim
  have hew : e.symm ⟨signedDirichletData w, hsd⟩ = ⟨w, hw⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext (he ⟨w, hw⟩).symm
  have hdat : ∀ i : ℕ, signedDirichletData (e.symm (c i)).1 = p i := by
    intro i
    rw [← he, e.apply_symm_apply]
  refine ⟨fun i => (e.symm (c i)).1, fun i => (e.symm (c i)).2, fun i => ?_, ?_⟩
  · have hiso : isospectral w (e.symm (c i)).1 := (e.symm (c i)).2
    have hmu : ∀ n : ℤ, gkMu (e.symm (c i)).1 n = (p i n).1 := fun n =>
      congrArg Prod.fst (congrFun (hdat i) n)
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [hmu, isospectral_gapLower_eq hiso]; exact (hin i k (Or.inl rfl)).1
    · rw [hmu, isospectral_gapUpper_eq hiso]; exact (hin i k (Or.inl rfl)).2
    · rw [hmu, isospectral_gapLower_eq hiso]; exact (hin i l (Or.inr rfl)).1
    · rw [hmu, isospectral_gapUpper_eq hiso]; exact (hin i l (Or.inr rfl)).2
  · have h1 := (e.symm.continuous.tendsto _).comp hc
    rw [hew] at h1
    exact (continuous_subtype_val.tendsto _).comp h1
end
end G5029Sup5Aux
end NlsGge.GKDefinitionDesign
