import QuantumNLS.ProductTorusLocalDiff

/-! Time-dependent GP-04. The integral estimate is uniform in both time
directions. The derivative is the independently constructed variational solution. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Filter Topology Function ODE
open scoped NNReal

namespace QuantumNLS.Ext025GP04FlowR30m

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem duration {a b s t : ℝ} (_hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    |t - s| ≤ max (b - s) (s - a) := by
  rw [abs_le]
  constructor
  · linarith [le_max_right (b - s) (s - a), ht.1]
  · linarith [le_max_left (b - s) (s - a), ht.2]

private theorem stable {a b s K C M : ℝ} {e g : ℝ → F}
    (hs : s ∈ Icc a b) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hshort : 2 * K * max (b - s) (s - a) ≤ 1)
    (he : ContinuousOn e (Icc a b)) (hC : ‖e s‖ ≤ C)
    (heq : ∀ t ∈ Icc a b, e t = e s + ∫ z in s..t, g z)
    (hg : ∀ z ∈ Icc a b, ‖g z‖ ≤ K * ‖e z‖ + M) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ 2 * (C + max (b - s) (s - a) * M) := by
  let v : C(Icc a b, F) := ⟨fun t => e t, continuousOn_iff_continuous_domRestrict.mp he⟩
  have hsup (z : ℝ) (hz : z ∈ Icc a b) : ‖e z‖ ≤ ‖v‖ :=
    ContinuousMap.norm_coe_le_norm v ⟨z, hz⟩
  have hT : 0 ≤ max (b - s) (s - a) := (sub_nonneg.mpr hs.2).trans (le_max_left _ _)
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      ‖e t‖ ≤ C + (K * ‖v‖ + M) * max (b - s) (s - a) := by
    rw [heq t ht]
    refine (norm_add_le _ _).trans (add_le_add hC ?_)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans
      (mul_le_mul_of_nonneg_left (duration hs ht) (by positivity))
    intro z hz
    have hz' := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hz)
    exact (hg z hz').trans (add_le_add (mul_le_mul_of_nonneg_left (hsup z hz') hK) le_rfl)
  have hC₀ := (norm_nonneg _).trans hC
  have hv := (ContinuousMap.norm_le v (show 0 ≤ C + (K * ‖v‖ + M) *
      max (b - s) (s - a) by positivity)).mpr fun t => hpoint t t.2
  have hh := mul_le_mul_of_nonneg_right hshort (norm_nonneg v)
  intro t ht
  exact (hsup t ht).trans (by linarith only [hv, hh])

private theorem along {a b : ℝ} {U : Set E} {B : ℝ → E → F} {v : ℝ → E}
    (hB : ContinuousOn (uncurry B) (Icc a b ×ˢ U)) (hv : ContinuousOn v (Icc a b))
    (hm : MapsTo v (Icc a b) U) :
    ContinuousOn (fun t => B t (v t)) (Icc a b) :=
  hB.comp (continuousOn_id.prodMk hv) (fun _t ht => ⟨ht, hm ht⟩)

/-- Uniform control of the state derivative near the compact graph of one trajectory,
in the relative topology of the time interval and state set. -/
private theorem derivative_near {a b : ℝ} {U : Set E} {A : ℝ → E → F} {v : ℝ → E}
    (hA : ContinuousOn (uncurry A) (Icc a b ×ˢ U)) (hv : ContinuousOn v (Icc a b))
    (hm : MapsTo v (Icc a b) U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∀ z ∈ U, dist z (v t) < δ →
      dist (A t z) (A t (v t)) < ε := by
  let P := Icc a b ×ˢ U
  let graph : Icc a b → P := fun t => ⟨(t, v t), t.2, hm t.2⟩
  have hg : Continuous graph :=
    (continuous_subtype_val.prodMk (continuousOn_iff_continuous_domRestrict.mp hv)).subtype_mk _
  let S := range graph
  have hS : IsCompact S := isCompact_range hg
  let D : P → F := fun p => A p.1.1 p.1.2
  have hD : Continuous D := continuousOn_iff_continuous_domRestrict.mp hA
  have hnear := hS.uniformContinuousAt_of_continuousAt D
    (fun x _ => hD.continuousAt) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hnear⟩ := Metric.mem_uniformity_dist.mp hnear
  refine ⟨δ, hδ, fun t ht z hz hdist => ?_⟩
  let x := graph ⟨t, ht⟩
  let y : P := ⟨(t, z), ht, hz⟩
  have hxy : dist x y < δ := by
    change max (dist t t) (dist (v t) z) < δ
    rw [dist_self, max_eq_right dist_nonneg, dist_comm]
    exact hdist
  have hh := hnear (a := x) (b := y) hxy
  have hval : dist (D x) (D y) < ε := hh ⟨⟨t, ht⟩, rfl⟩
  simpa only [dist_comm (D x), D, x, y, graph] using hval

variable {f : ℝ → E → E} {a b : ℝ} {s : Icc a b} {p : E} {R r L K : ℝ≥0}

theorem separated (hf : IsPicardLindelof f s p R r L K)
    (hshort : 2 * (K : ℝ) * max (b - s) (s - a) ≤ 1)
    {v w : ℝ → E} {x y : E} (hv : Continuous v) (hw : Continuous w)
    (hvm : MapsTo v (Icc a b) (closedBall p R)) (hwm : MapsTo w (Icc a b) (closedBall p R))
    (hv0 : v s = x) (hw0 : w s = y)
    (hvq : ∀ t ∈ Icc a b, v t = picard f s x v t)
    (hwq : ∀ t ∈ Icc a b, w t = picard f s y w t) :
    ∀ t ∈ Icc a b, ‖v t - w t‖ ≤ 2 * ‖x - y‖ := by
  have hvf := along hf.continuousOn_uncurry hv.continuousOn hvm
  have hwf := along hf.continuousOn_uncurry hw.continuousOn hwm
  simpa using stable (e := fun t => v t - w t) (g := fun t => f t (v t) - f t (w t))
    s.2 K.2 (le_refl (0 : ℝ)) hshort (hv.sub hw).continuousOn
    (show ‖v s - w s‖ ≤ ‖x - y‖ by rw [hv0, hw0])
    (by
      intro t ht
      have hsub := uIcc_subset_Icc s.2 ht
      rw [intervalIntegral.integral_sub ((hvf.mono hsub).intervalIntegrable)
        ((hwf.mono hsub).intervalIntegrable), hvq t ht, hwq t ht, picard_apply,
        picard_apply, hv0, hw0]
      abel)
    (by
      intro t ht
      have h := (hf.lipschitzOnWith t ht).dist_le_mul _ (hvm ht) _ (hwm ht)
      rw [dist_eq_norm, dist_eq_norm] at h
      change ‖f t (v t) - f t (w t)‖ ≤ (K : ℝ) * ‖v t - w t‖ + 0
      rw [add_zero]
      exact h)

/-- Local existence, continuous state derivative and its variational equation on the same
two-sided interval. The constant extension away from the initial-state ball is immaterial. -/
theorem local_c1 (hf : IsPicardLindelof f s p R r L K)
    (A : ℝ → E → E →L[ℝ] E)
    (hd : ∀ t ∈ Icc a b, ∀ z ∈ closedBall p R, HasFDerivAt (f t) (A t z) z)
    (hA : ContinuousOn (uncurry A) (Icc a b ×ˢ closedBall p R))
    (hK : ∀ t ∈ Icc a b, ∀ z ∈ closedBall p R, ‖A t z‖ ≤ K)
    (hshort : 2 * (K : ℝ) * max (b - s) (s - a) ≤ 1) :
    ∃ φ : ℝ → E → E, ∃ J : E → ℝ → E →L[ℝ] E,
      (∀ x ∈ ball p r, Continuous (fun t => φ t x) ∧ φ s x = x ∧
        (∀ t ∈ Icc a b, φ t x ∈ closedBall p R ∧
          φ t x = picard f s x (fun z => φ z x) t ∧
          HasDerivWithinAt (fun z => φ z x) (f t (φ t x)) (Icc a b) t)) ∧
      (∀ x ∈ ball p r, Continuous (J x) ∧ J x s = ContinuousLinearMap.id ℝ E ∧
        (∀ t ∈ Icc a b, J x t = ContinuousLinearMap.id ℝ E +
          ∫ z in (s : ℝ)..t, (A z (φ z x)).comp (J x z)) ∧
        (∀ t ∈ Icc a b, HasDerivWithinAt (J x)
          ((A t (φ t x)).comp (J x t)) (Icc a b) t ∧ HasFDerivAt (φ t) (J x t) x)) ∧
      (∀ t ∈ Icc a b, ContDiffOn ℝ 1 (φ t) (ball p r)) := by
  classical
  choose v hvc hv0 hvm hvq hvd using fun x : closedBall p (r : ℝ) =>
    Ext025A2.gp04_differential_existence hf x.2
  let φ : ℝ → E → E := fun t x => if hx : x ∈ closedBall p (r : ℝ) then v ⟨x, hx⟩ t else x
  have hφ (x : E) (hx : x ∈ closedBall p r) : (fun t => φ t x) = v ⟨x, hx⟩ := by
    funext t
    simp only [φ, dite_eq_left hx]
  have hc (x : E) (hx : x ∈ ball p r) : Continuous (fun t => φ t x) := by
    rw [hφ x (ball_subset_closedBall hx)]
    exact hvc _
  have hm (x : E) (hx : x ∈ ball p r) : MapsTo (fun t => φ t x) (Icc a b) (closedBall p R) := by
    rw [hφ x (ball_subset_closedBall hx)]
    exact fun t _ => hvm _ t
  have hin (x : E) (hx : x ∈ ball p r) : φ s x = x := congrFun (hφ x (ball_subset_closedBall hx)) s |>.trans (hv0 _)
  have hq (x : E) (hx : x ∈ ball p r) (t : ℝ) (ht : t ∈ Icc a b) :
      φ t x = picard f s x (fun z => φ z x) t := by
    change (fun z => φ z x) t = _
    rw [hφ x (ball_subset_closedBall hx)]
    exact hvq _ t ht
  let B : E → ℝ → E →L[ℝ] E := fun x t => A t (φ t x)
  have hBc (x : E) (hx : x ∈ ball p r) : ContinuousOn (B x) (Icc a b) :=
    along hA (hc x hx).continuousOn (hm x hx)
  choose j hjc hj0 hjq hjd using fun x : ball p (r : ℝ) =>
    Ext025A3.gp04_variational_existence (t₀ := s) (B x) (hBc x x.2) K
      (fun t ht => hK t ht _ (hm x x.2 ht)) hshort
  let J : E → ℝ → E →L[ℝ] E := fun x t => if hx : x ∈ ball p (r : ℝ) then j ⟨x, hx⟩ t else 0
  have hJ (x : E) (hx : x ∈ ball p r) : J x = j ⟨x, hx⟩ := by
    funext t
    simp only [J, dite_eq_left hx]
  have hJc (x : E) (hx : x ∈ ball p r) : Continuous (J x) := by
    rw [hJ x hx]
    exact hjc _
  have hJ0 (x : E) (hx : x ∈ ball p r) : J x s = ContinuousLinearMap.id ℝ E := by
    rw [hJ x hx]
    exact hj0 _
  have hJq (x : E) (hx : x ∈ ball p r) (t : ℝ) (ht : t ∈ Icc a b) :
      J x t = ContinuousLinearMap.id ℝ E + ∫ z in (s : ℝ)..t, (B x z).comp (J x z) := by
    rw [hJ x hx]
    exact hjq _ t ht
  have hcomp (x : E) (hx : x ∈ ball p r) :
      ContinuousOn (fun z => (B x z).comp (J x z)) (Icc a b) :=
    (hBc x hx).clm_comp (hJc x hx).continuousOn
  have hsep (x y : E) (hx : x ∈ ball p r) (hy : y ∈ ball p r) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖φ t y - φ t x‖ ≤ 2 * ‖y - x‖ :=
    separated hf hshort (hc y hy) (hc x hx) (hm y hy) (hm x hx) (hin y hy) (hin x hx)
      (hq y hy) (hq x hx) t ht
  set T : ℝ := max (b - s) (s - a)
  have hT : 0 ≤ T := (sub_nonneg.mpr s.2.2).trans (le_max_left _ _)
  have small (x : E) (hx : x ∈ ball p r) {ε : ℝ} (hε : 0 < ε) :
      ∃ δ > 0, ∀ y ∈ ball x δ, y ∈ ball p r ∧
        (∀ t ∈ Icc a b, ‖B y t - B x t‖ ≤ ε ∧
          ‖f t (φ t y) - f t (φ t x) - B x t (φ t y - φ t x)‖ ≤ ε * ‖φ t y - φ t x‖) := by
    obtain ⟨ρ, hρ, hnear⟩ := derivative_near hA (hc x hx).continuousOn (hm x hx) hε
    obtain ⟨η, hη, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
    refine ⟨min η (ρ / 2), by positivity, fun y hy => ?_⟩
    have hy' := hsub (ball_subset_ball (min_le_left _ _) hy)
    refine ⟨hy', fun t ht => ?_⟩
    have hclose : dist (φ t y) (φ t x) < ρ := by
      rw [dist_eq_norm]
      have h := mem_ball.mp (ball_subset_ball (min_le_right η (ρ / 2)) hy)
      rw [dist_eq_norm] at h
      linarith [hsep x y hx hy' t ht]
    refine ⟨(by simpa only [B, dist_eq_norm] using
      (hnear t ht _ (hm y hy' ht) hclose).le), ?_⟩
    let U := closedBall p (R : ℝ) ∩ ball (φ t x) ρ
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (s := U) (fun z hz => (hd t ht z hz.1).hasFDerivWithinAt)
      (fun z hz => by simpa only [dist_eq_norm] using (hnear t ht z hz.1 (mem_ball.mp hz.2)).le)
      ((convex_closedBall _ _).inter (convex_ball _ _))
      ⟨hm x hx ht, mem_ball_self hρ⟩ ⟨hm y hy' ht, hclose⟩
  have ident (x : E) (hx : x ∈ ball p r) (t : ℝ) (ht : t ∈ Icc a b) :
      HasFDerivAt (φ t) (J x t) x := by
    rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc₀
    let ε := c / (4 * (T + 1))
    have hε : 0 < ε := by positivity
    obtain ⟨δ, hδ, hδb⟩ := small x hx hε
    filter_upwards [ball_mem_nhds x hδ] with y hy
    obtain ⟨hy', hb⟩ := hδb y hy
    let e := fun z => φ z y - φ z x - J x z (y - x)
    let g := fun z => f z (φ z y) - f z (φ z x) - B x z (J x z (y - x))
    have hec : Continuous e := ((hc y hy').sub (hc x hx)).sub
      ((hJc x hx).clm_apply continuous_const)
    have he0 : e s = 0 := by simp [e, hin y hy', hin x hx, hJ0 x hx]
    have heq (w : ℝ) (hw : w ∈ Icc a b) : e w = e s + ∫ z in (s : ℝ)..w, g z := by
      have hsub := uIcc_subset_Icc s.2 hw
      have ho (x : E) (hx : x ∈ ball p r) :=
        ((along hf.continuousOn_uncurry (hc x hx).continuousOn (hm x hx)).mono hsub).intervalIntegrable (μ := MeasureTheory.volume)
      have hB := ((hcomp x hx).mono hsub).intervalIntegrable (μ := MeasureTheory.volume)
      have hBa := (((hcomp x hx).clm_apply (continuousOn_const (c := y - x))).mono hsub).intervalIntegrable (μ := MeasureTheory.volume)
      rw [he0, zero_add]
      change φ w y - φ w x - J x w (y - x) =
        ∫ z in (s : ℝ)..w, (f z (φ z y) - f z (φ z x)) - ((B x z).comp (J x z)) (y - x)
      rw [intervalIntegral.integral_sub ((ho y hy').sub (ho x hx)) hBa,
        intervalIntegral.integral_sub (ho y hy') (ho x hx), ← ContinuousLinearMap.intervalIntegral_apply hB,
        hq y hy' w hw, hq x hx w hw, hJq x hx w hw]
      simp only [picard_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply]
      abel
    have hg (z : ℝ) (hz : z ∈ Icc a b) : ‖g z‖ ≤ K * ‖e z‖ + ε * (2 * ‖y - x‖) := by
      let rem := f z (φ z y) - f z (φ z x) - B x z (φ z y - φ z x)
      have hsplit : g z = B x z (e z) + rem := by
        dsimp [g, e, rem]
        simp only [map_sub]
        abel
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add
        (((B x z).le_opNorm _).trans (mul_le_mul_of_nonneg_right
          (hK z hz _ (hm x hx hz)) (norm_nonneg _)))
        ((hb z hz).2.trans (mul_le_mul_of_nonneg_left (hsep x y hx hy' z hz) hε.le)))
    refine (stable s.2 K.2 (by positivity) hshort hec.continuousOn
      (show ‖e s‖ ≤ 0 by simp [he0]) heq hg t ht).trans ?_
    have hεeq : 4 * (T + 1) * ε = c := by
      dsimp [ε]
      field_simp
    nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) hε.le) (norm_nonneg (y - x)),
      congrArg (fun k : ℝ => k * ‖y - x‖) hεeq]
  have jbound (x : E) (hx : x ∈ ball p r) (t : ℝ) (ht : t ∈ Icc a b) :
      ‖J x t‖ ≤ 2 := by
    simpa using stable (e := J x) (g := fun z => (B x z).comp (J x z))
      s.2 K.2 (le_refl (0 : ℝ)) hshort (hJc x hx).continuousOn
      (show ‖J x s‖ ≤ 1 by rw [hJ0 x hx]; exact ContinuousLinearMap.norm_id_le)
      (fun z hz => by rw [hJq x hx z hz, hJ0 x hx])
      (fun z hz => by
        rw [add_zero]
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hK z hz _ (hm x hx hz)) (norm_nonneg _))) t ht
  have jcontinuous (t : ℝ) (ht : t ∈ Icc a b) :
      ContinuousOn (fun x => J x t) (ball p r) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    rw [Metric.continuousAt_iff]
    intro c hc₀
    let ε := c / (8 * (T + 1))
    have hε : 0 < ε := by positivity
    obtain ⟨δ, hδ, hδb⟩ := small x hx hε
    refine ⟨δ, hδ, fun {y} hy => ?_⟩
    obtain ⟨hy', hb⟩ := hδb y hy
    let e := fun z => J y z - J x z
    let g := fun z => (B y z).comp (J y z) - (B x z).comp (J x z)
    have he0 : e s = 0 := by simp [e, hJ0 y hy', hJ0 x hx]
    have heq (w : ℝ) (hw : w ∈ Icc a b) : e w = e s + ∫ z in (s : ℝ)..w, g z := by
      have hsub := uIcc_subset_Icc s.2 hw
      rw [he0, zero_add]
      change J y w - J x w = _
      rw [show g = _ from rfl, intervalIntegral.integral_sub
        (((hcomp y hy').mono hsub).intervalIntegrable) (((hcomp x hx).mono hsub).intervalIntegrable),
        hJq y hy' w hw, hJq x hx w hw]
      abel
    have hg (z : ℝ) (hz : z ∈ Icc a b) : ‖g z‖ ≤ K * ‖e z‖ + ε * 2 := by
      have hsplit : g z = (B x z).comp (e z) + (B y z - B x z).comp (J y z) := by
        simp only [g, e, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
        abel
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hK z hz _ (hm x hx hz)) (norm_nonneg _)))
        ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hb z hz).1 (jbound y hy' z hz) (norm_nonneg _) hε.le)))
    rw [dist_eq_norm]
    refine (stable s.2 K.2 (by positivity) hshort ((hJc y hy').sub (hJc x hx)).continuousOn
      (show ‖e s‖ ≤ 0 by simp [he0]) heq hg t ht).trans_lt ?_
    have hεeq : 8 * (T + 1) * ε = c := by
      dsimp [ε]
      field_simp
    nlinarith
  refine ⟨φ, J, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨hc x hx, hin x hx, fun t ht => ⟨hm x hx ht, hq x hx t ht, ?_⟩⟩
    change HasDerivWithinAt (fun z => φ z x) (f t ((fun z => φ z x) t)) (Icc a b) t
    rw [hφ x (ball_subset_closedBall hx)]
    exact hvd _ t ht
  · intro x hx
    refine ⟨hJc x hx, hJ0 x hx, hJq x hx, fun t ht => ⟨?_, ident x hx t ht⟩⟩
    rw [hJ x hx]
    exact hjd _ t ht
  · intro t ht
    rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
    refine ⟨fun x hx => (ident x hx t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact contDiffOn_zero.mpr ((jcontinuous t ht).congr (fun x hx => (ident x hx t ht).fderiv))

end QuantumNLS.Ext025GP04FlowR30m

#print axioms QuantumNLS.Ext025GP04FlowR30m.local_c1
