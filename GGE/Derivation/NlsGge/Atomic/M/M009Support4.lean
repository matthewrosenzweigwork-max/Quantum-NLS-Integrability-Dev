import Mathlib
import NlsGge.GK38.XiSqPeriod
import NlsGge.GK38.ContourAction
import NlsGge.GK38.IsolatingRootMultisets
import NlsGge.GK38.IsolatingTopology
import NlsGge.Atomic.Support.ContourChain
import NlsGge.Atomic.Support.ContourCycleIndex
import NlsGge.Atomic.Support.ContourCycleCauchy
import NlsGge.Atomic.LIB.LIB015
import NlsGge.Atomic.G1.G1103Circ
import NlsGge.ThirdConsultation.G2.G2037P4M4
import NlsGge.Atomic.M.M008Host
import NlsGge.Atomic.M.M009Host
import NlsGge.Atomic.M.M009Support3

/- M-009 SUPPORT04 (proof development, AUTHOR; not reviewed).  Pieces 2 and 3a of Pro round 13 section 11 ("Proof route and actual
   remaining bridge"): zero integral of omega over every closed C1 chain in the cut-free fiber (finite cycle/index argument),
   the resulting global primitive P on the fiber, and the improper chain integrals of admissible chains with endpoints in the
   fiber.  Route (as in Pro): Dixon's cycle Cauchy theorem (landed ContourCycleCauchy) for the cycle  Gamma - sum_n k_n * circle_n
   with k_n = index of Gamma on the n-th cut (finitely many nonzero), circle_n the isolating circle whose omega-period vanishes
   (landed a5FixedPeriod_zero38, the same fact as M-008 conjunct (1)/(2)); then G2037P4M4 `exists_primitive_of_zero_periods`
   with M009Support3 polygonal connectivity; then FTC on the trimmed pieces.  No period/integrability hypothesis is assumed. -/
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology BigOperators unitInterval
open NlsGge.Pilot NlsGge.GK38
open NlsGge.GK38.Lib.SlitContours
open NlsGge.Atomic.ContourChain
open NlsGge.Atomic.G1103Circ

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section

theorem omega_differentiableOn_fiber (φ : PotPair) (hφ : φ ∈ gkW) :
    DifferentiableOn ℂ (MContour.omega φ) (cutFreeFiber φ) :=
  (a5LogQuotient_analytic38 φ hφ).differentiableOn

theorem sphere_subset_fiber (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    sphere (discC φ n) (discR φ n) ⊆ cutFreeFiber φ :=
  fixed_sphere_subset φ (discC φ) (discR φ) (isolating_family38 φ hφ) n

theorem not_mem_fiber_of_mem_cut {φ : PotPair} {m : ℤ} {w : ℂ}
    (hw : w ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) : w ∉ cutFreeFiber φ :=
  fun h => h (Set.mem_iUnion.2 ⟨m, hw⟩)

theorem exists_cut_of_not_mem_fiber {φ : PotPair} {w : ℂ} (hw : w ∉ cutFreeFiber φ) :
    ∃ m : ℤ, w ∈ segment ℝ (lamMinus φ m) (lamPlus φ m) :=
  Set.mem_iUnion.1 (not_not.1 hw)

theorem circle_index_cut (φ : PotPair) (hφ : φ ∈ gkW) (n m : ℤ) {w : ℂ}
    (hw : w ∈ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    (circleCycle (discC φ n) (discR φ n)).index w = if n = m then 1 else 0 := by
  obtain ⟨c, N, hgeom, hspec⟩ := isolating_family38 φ hφ
  have hwb : w ∈ ball (discC φ m) (discR φ m) := (hspec.1 m).1 hw
  have hρ : 0 < discR φ n := (hgeom.1 n).1
  by_cases hnm : n = m
  · subst hnm
    rw [if_pos rfl]
    apply circleCycle_index_inside _ hρ
    rw [← dist_eq_norm]
    exact mem_ball.1 hwb
  · rw [if_neg hnm]
    apply circleCycle_index_outside _ hρ
    by_contra hle
    push Not at hle
    have hcl : w ∈ closedBall (discC φ n) (discR φ n) := by
      rw [mem_closedBall, dist_eq_norm]; exact hle
    exact hnm (isolating_closed_index38 (discC φ) (discR φ) c N hgeom m n hwb hcl).symm

theorem circleCycle_integral_zero (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ) :
    (circleCycle (discC φ n) (discR φ n)).Integrable
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (MContour.omega φ w)) ∧
    (circleCycle (discC φ n) (discR φ n)).integral
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (MContour.omega φ w)) = 0 := by
  have hf := isolating_family38 φ hφ
  have hρ : 0 < discR φ n := (isolating_radius_pos38 hf n)
  have hsph := sphere_subset_fiber φ hφ n
  have hωc : ContinuousOn (MContour.omega φ) (cutFreeFiber φ) :=
    (omega_differentiableOn_fiber φ hφ).continuousOn
  have hcont : ContinuousOn
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (MContour.omega φ w)) (cutFreeFiber φ) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).continuous.comp_continuousOn hωc
  refine ⟨Cycle.integrable_of_continuousOn hcont
    ((circleCycle_range_subset (discC φ n) hρ.le).trans hsph), ?_⟩
  rw [circleCycle_integral]
  have hfun : (fun w => ContinuousLinearMap.toSpanSingleton ℂ (MContour.omega φ w)) =
      complexForm (MContour.omega φ) := by
    funext w; exact toSpanSingleton_eq_complexForm _ w
  rw [hfun, curveIntegral_circleLoop _ _ _ hρ (hωc.mono hsph)]
  exact (a5FixedPeriod_zero38 φ hφ (discC φ) (discR φ) hf n).2

/-- **Piece 2 (chain form).**  Every closed finite C1 chain in the cut-free fiber has zero omega-integral. -/
theorem closedChain_omega_zero (φ : PotPair) (hφ : φ ∈ gkW) {a : ℂ}
    (L : Chain a a) (hL : L.trace ⊆ cutFreeFiber φ) :
    L.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (MContour.omega φ w)) = 0 := by
  classical
  have hUo : IsOpen (cutFreeFiber φ) := cutFreeFiber_isOpen φ hφ
  have hdiff := omega_differentiableOn_fiber φ hφ
  let Γ : Cycle := Cycle.single ⟨a, L⟩
  have hΓU : Γ.range ⊆ cutFreeFiber φ := by
    rw [Cycle.range_single]; exact hL
  have hint_idx : ∀ m : ℤ, ∃ k : ℤ, ∀ w ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      Γ.index w = (k : ℂ) := by
    intro m
    have hseg_sub : segment ℝ (lamMinus φ m) (lamPlus φ m) ⊆ Γ.rangeᶜ :=
      fun w hw hwr => not_mem_fiber_of_mem_cut hw (hΓU hwr)
    obtain ⟨k, hk⟩ := Γ.exists_int_index (hseg_sub (left_mem_segment ℝ _ _))
    refine ⟨k, fun w hw => ?_⟩
    rw [Γ.index_eq_of_isPreconnected (convex_segment _ _).isPreconnected hseg_sub hw
      (left_mem_segment ℝ _ _), hk]
  choose k hk using hint_idx
  obtain ⟨Rb, hRb, hball, hfar⟩ := Γ.exists_pos_index_eq_zero_outside_ball 0
  have hfin : {m : ℤ | k m ≠ 0}.Finite := by
    have hlf := Support3Aux.locallyFinite_cuts (isolating_family38 φ hφ)
    refine (hlf.finite_nonempty_inter_compact (isCompact_closedBall (0 : ℂ) Rb)).subset ?_
    intro m hm
    by_contra hne
    apply hm
    have h0 := hk m (lamMinus φ m) (left_mem_segment ℝ _ _)
    have h1 : Γ.index (lamMinus φ m) = 0 := hfar _ (fun hb =>
      hne ⟨lamMinus φ m, left_mem_segment ℝ _ _, ball_subset_closedBall hb⟩)
    exact_mod_cast h0.symm.trans h1
  let S : Finset ℤ := hfin.toFinset
  obtain ⟨Θ, hΘr, hΘi, hΘint⟩ := exists_weighted_cycle (F := ℂ) S
    (fun j => circleCycle (discC φ j) (discR φ j)) k
  have hcircU : ∀ j : ℤ, (circleCycle (discC φ j) (discR φ j)).range ⊆ cutFreeFiber φ :=
    fun j => (circleCycle_range_subset (discC φ j)
      (isolating_radius_pos38 (isolating_family38 φ hφ) j).le).trans (sphere_subset_fiber φ hφ j)
  have hΘU : Θ.range ⊆ cutFreeFiber φ := by
    intro z hz
    obtain ⟨j, _, hzj⟩ := hΘr z hz
    exact hcircU j hzj
  obtain ⟨hΘI, hΘI2⟩ := hΘint (fun w => ContinuousLinearMap.toSpanSingleton ℂ (MContour.omega φ w))
    (fun j _ => (circleCycle_integral_zero φ hφ j).1)
  have hΘzero : Θ.integral
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (MContour.omega φ w)) = 0 := by
    rw [hΘI2]
    apply Finset.sum_eq_zero
    intro j _
    rw [(circleCycle_integral_zero φ hφ j).2, smul_zero]
  have hΘidx : ∀ m : ℤ, ∀ w ∈ segment ℝ (lamMinus φ m) (lamPlus φ m),
      Θ.index w = (k m : ℂ) := by
    intro m w hw
    rw [hΘi w (fun j _ hj => not_mem_fiber_of_mem_cut hw (hcircU j hj))]
    have : ∀ j ∈ S, (k j : ℂ) * (circleCycle (discC φ j) (discR φ j)).index w =
        if j = m then (k m : ℂ) else 0 := by
      intro j _
      rw [circle_index_cut φ hφ j m hw]
      by_cases hjm : j = m
      · subst hjm; simp
      · simp [hjm]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' S m (fun _ => (k m : ℂ))]
    by_cases hmS : m ∈ S
    · rw [if_pos hmS]
    · rw [if_neg hmS]
      have : ¬ (k m ≠ 0) := fun h => hmS (hfin.mem_toFinset.2 h)
      push Not at this
      simp [this]
  have hΓ'U : (Γ.append Θ.reverse).range ⊆ cutFreeFiber φ := by
    rw [Cycle.range_append, Cycle.range_reverse]
    exact union_subset hΓU hΘU
  have hind : ∀ w : ℂ, w ∉ cutFreeFiber φ → (Γ.append Θ.reverse).index w = 0 := by
    intro w hw
    obtain ⟨m, hm⟩ := exists_cut_of_not_mem_fiber hw
    have hwΘ : w ∉ Θ.range := fun h => hw (hΘU h)
    rw [Cycle.index_append, Cycle.index_reverse Θ hwΘ, hk m w hm, hΘidx m w hm]
    ring
  have h0 := Cycle.integral_eq_zero (Γ.append Θ.reverse) hUo hΓ'U hind hdiff
  rw [Cycle.integral_append, Cycle.integral_reverse hΘI, hΘzero, neg_zero, add_zero] at h0
  simpa [Γ] using h0

/-- **Piece 3a.**  A global primitive of omega on the cut-free fiber. -/
theorem fiber_omega_primitive (φ : PotPair) (hφ : φ ∈ gkW) :
    ∃ P : ℂ → ℂ, ∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z :=
  NlsGge.G2037P4M4.exists_primitive_of_zero_periods (cutFreeFiber_isOpen φ hφ)
    (omega_differentiableOn_fiber φ hφ) (cutFreeFiber_polygonal φ hφ)
    (fun L hL => closedChain_omega_zero φ hφ L hL)

theorem piece_endpoint_integral (φ : PotPair) (hφ : φ ∈ gkW) {P : ℂ → ℂ}
    (hP : ∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z)
    (q : ℝ → ℂ) (hqc : ContinuousOn q (Icc (0 : ℝ) 1))
    (hqd : ContDiffOn ℝ 1 q (Ioo (0 : ℝ) 1))
    (hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ cutFreeFiber φ) :
    MContour.HasEndpointIntegral φ q (P (q 1) - P (q 0)) := by
  have hω := (omega_differentiableOn_fiber φ hφ).continuousOn
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt q (deriv q x) x := fun x hx =>
    (((hqd.differentiableOn one_ne_zero) x hx).differentiableAt
      (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  have hdcont : ContinuousOn (deriv q) (Ioo (0 : ℝ) 1) :=
    hqd.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hIcc : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 → Icc ε (1 - η) ⊆ Ioo (0 : ℝ) 1 := by
    intro ε η hε hη h x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hFTC : ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
      IntervalIntegrable (fun t : ℝ => MContour.omega φ (q t) * deriv q t) volume ε (1 - η) ∧
      ∫ t in ε..(1 - η), MContour.omega φ (q t) * deriv q t = P (q (1 - η)) - P (q ε) := by
    intro ε η hε hη hεη
    have hle : ε ≤ 1 - η := by linarith
    have hsub := hIcc ε η hε hη hεη
    have hcont : ContinuousOn (fun t : ℝ => MContour.omega φ (q t) * deriv q t)
        (uIcc ε (1 - η)) := by
      rw [uIcc_of_le hle]
      refine ContinuousOn.mul ?_ (hdcont.mono hsub)
      exact hω.comp (hqc.mono (hsub.trans Ioo_subset_Icc_self))
        (fun t ht => hqU t (Ioo_subset_Icc_self (hsub ht)))
    have hi : IntervalIntegrable (fun t : ℝ => MContour.omega φ (q t) * deriv q t) volume ε (1 - η) :=
      hcont.intervalIntegrable
    refine ⟨hi, intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => P (q t)) (fun x hx => ?_) hi⟩
    have hx' : x ∈ Ioo (0 : ℝ) 1 := hsub (by rwa [uIcc_of_le hle] at hx)
    have h1 := (hP (q x) (hqU x (Ioo_subset_Icc_self hx'))).scomp x (hderiv x hx')
    exact h1.congr_deriv (by rw [smul_eq_mul, mul_comm])
  refine ⟨fun ε η hε hη h => (hFTC ε η hε hη h).1, ?_⟩
  have h0 : Tendsto (fun s : ℝ × ℝ => q s.1)
      (𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}] ((0 : ℝ), (0 : ℝ))) (𝓝 (q 0)) := by
    have h1 : Tendsto (fun s : ℝ × ℝ => s.1)
        (𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}] ((0 : ℝ), (0 : ℝ)))
        (𝓝[Icc (0 : ℝ) 1] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · exact (continuous_fst.tendsto ((0 : ℝ), (0 : ℝ))).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact ⟨hs.1.le, by linarith [hs.2.1, hs.2.2]⟩
    exact (hqc 0 ⟨le_rfl, zero_le_one⟩).tendsto.comp h1
  have h1 : Tendsto (fun s : ℝ × ℝ => q (1 - s.2))
      (𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}] ((0 : ℝ), (0 : ℝ))) (𝓝 (q 1)) := by
    have h2 : Tendsto (fun s : ℝ × ℝ => 1 - s.2)
        (𝓝[{q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}] ((0 : ℝ), (0 : ℝ)))
        (𝓝[Icc (0 : ℝ) 1] 1) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h3 : Tendsto (fun s : ℝ × ℝ => s.2) (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 0) :=
          continuous_snd.tendsto ((0 : ℝ), (0 : ℝ))
        have h4 := (h3.const_sub (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}))
        simpa using h4
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact ⟨by linarith [hs.2.1, hs.2.2, hs.1], by linarith [hs.2.1]⟩
    exact (hqc 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp h2
  have hPq0 := ((hP (q 0) (hqU 0 ⟨le_rfl, zero_le_one⟩)).continuousAt.tendsto).comp h0
  have hPq1 := ((hP (q 1) (hqU 1 ⟨zero_le_one, le_rfl⟩)).continuousAt.tendsto).comp h1
  refine Tendsto.congr' ?_ (hPq1.sub hPq0)
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ((hFTC s.1 s.2 hs.1 hs.2.1 hs.2.2).2).symm

theorem tele_sum_fin (m : ℕ) (u v : Fin (m + 1) → ℂ)
    (h : ∀ i : Fin m, v i.castSucc = u i.succ) :
    ∑ i, (v i - u i) = v (Fin.last m) - u 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have h' : ∀ i : Fin m, (fun j : Fin (m + 1) => v j.castSucc) i.castSucc =
        (fun j : Fin (m + 1) => u j.castSucc) i.succ := by
      intro i
      simp only
      rw [h i.castSucc, Fin.succ_castSucc]
    have := ih (fun j => u j.castSucc) (fun j => v j.castSucc) h'
    simp only [Fin.castSucc_zero] at this
    rw [this]
    have h2 := h (Fin.last m)
    rw [Fin.succ_last] at h2
    rw [h2]
    ring

theorem admissible_chain_integral (φ : PotPair) (hφ : φ ∈ gkW) {P : ℂ → ℂ}
    (hP : ∀ z ∈ cutFreeFiber φ, HasDerivAt P (MContour.omega φ z) z)
    {a b : ℂ} (ha : a ∈ cutFreeFiber φ) (hb : b ∈ cutFreeFiber φ)
    (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ) (hp : AdmissiblePrimitiveChain φ a b m p) :
    MContour.HasFiniteChainIntegral φ m p (P b - P a) := by
  obtain ⟨hcompat, hreg, h0, hlast, hgeo⟩ := hp
  have hends : ∀ (i : Fin (m + 1)) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → p i t ∈ cutFreeFiber φ := by
    intro i t ht
    rcases hgeo with ⟨hopen, hjunc⟩ | ⟨hab, hconst⟩
    · rcases ht.1.eq_or_lt with h | h
      · subst h
        cases i using Fin.cases with
        | zero => rw [h0]; exact ha
        | succ j => rw [← hcompat j]; exact hjunc j
      · rcases ht.2.eq_or_lt with h' | h'
        · subst h'
          cases i using Fin.lastCases with
          | last => rw [hlast]; exact hb
          | cast j => exact hjunc j
        · exact hopen i t ⟨h, h'⟩
    · rw [hconst i t ht]; exact ha
  refine ⟨fun i => P (p i 1) - P (p i 0), fun i => ?_, ?_⟩
  · exact piece_endpoint_integral φ hφ hP (p i) (hreg i).1 (hreg i).2 (hends i)
  · rw [tele_sum_fin m (fun i => P (p i 0)) (fun i => P (p i 1))
      (fun i => by show P (p i.castSucc 1) = P (p i.succ 0); rw [hcompat i]), hlast, h0]

/-- **Piece 2 (Pro chain form).**  Every closed admissible primitive chain in the cut-free fiber has the finite chain
integral `0`; the integral exists (joint improper limit on each piece) and is zero.  Nothing about periods is assumed. -/
theorem closed_chain_integral_zero (φ : PotPair) (hφ : φ ∈ gkW) {a : ℂ}
    (ha : a ∈ cutFreeFiber φ) (m : ℕ) (p : Fin (m + 1) → ℝ → ℂ)
    (hp : AdmissiblePrimitiveChain φ a a m p) :
    MContour.HasFiniteChainIntegral φ m p 0 := by
  obtain ⟨P, hP⟩ := fiber_omega_primitive φ hφ
  have := admissible_chain_integral φ hφ hP ha ha m p hp
  rwa [sub_self] at this

end
end NlsGge.ThirdConsultation.MPrimitive
