import QuantumNLS.HolomorphicStageD4

/-! Round 91 batch: complex Banach Picard support. The exact real Banach
HeldGP04AnalyticInitialDependence application remains open; see the gaps. -/

/-! GP-04 support: uniform limits on complex Banach balls.
The derivative convergence is derived from Cauchy estimates; no derivative
convergence or analyticity of the limit is a premise. This module does not
assert the real compact-trajectory application Prop in ProductTorusAnalytic. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology Set Metric
namespace QuantumNLS.Ext025A4AnalyticLimit
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Uniform convergence on a ball forces uniform Cauchy convergence of
Fréchet derivatives on the concentric half ball, by Cauchy's estimate. -/
theorem fderiv_uniformCauchy {f : ℕ → E → F} {g : E → F} {a : E} {R : ℝ}
    (hR : 0 < R) (hf : ∀ n, DifferentiableOn ℂ (f n) (ball a R))
    (hg : TendstoUniformlyOn f g atTop (ball a R)) :
    UniformCauchySeqOn (fun n => fderiv ℂ (f n)) atTop (ball a (R / 2)) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hg.uniformCauchySeqOn
    (ε * R / 8) (by positivity)
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  have hsub : ball x (R / 2) ⊆ ball a R := by
    intro y hy
    rw [mem_ball] at hx hy ⊢
    linarith [dist_triangle y x a]
  have hxR : x ∈ ball a R := ball_subset_ball (by linarith) hx
  have hbound : ∀ y ∈ ball x (R / 2), ‖f m y - f n y‖ ≤ ε * R / 8 := by
    intro y hy
    have hh : ‖f m y - f n y‖ < ε * R / 8 := by
      simpa [dist_eq_norm] using hN m hm n hn y (hsub hy)
    exact hh.le
  have hd : DifferentiableOn ℂ (fun y => f m y - f n y) (ball a R) :=
    (hf m).sub (hf n)
  have hnorm : ‖fderiv ℂ (f m) x - fderiv ℂ (f n) x‖ ≤ ε / 2 := by
    have he := fderiv_sub ((hf m).differentiableAt (isOpen_ball.mem_nhds hxR))
      ((hf n).differentiableAt (isOpen_ball.mem_nhds hxR))
    rw [← he]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hv := QuantumNLS.HolomorphicCauchyC1.norm_fderiv_apply_le hd (half_pos hR) hsub hbound v
    convert hv using 1
    field_simp
    ring
  rw [dist_eq_norm]
  exact hnorm.trans_lt (by linarith)

/-- The Banach-domain holomorphic uniform-limit theorem on a smaller ball. -/
theorem differentiableOn_uniformLimit {f : ℕ → E → F} {g : E → F} {a : E} {R : ℝ}
    (hR : 0 < R) (hf : ∀ n, DifferentiableOn ℂ (f n) (ball a R))
    (hg : TendstoUniformlyOn f g atTop (ball a R)) :
    DifferentiableOn ℂ g (ball a (R / 2)) := by
  let D : E → E →L[ℂ] F := fun x => limUnder atTop (fun n => fderiv ℂ (f n) x)
  have hc := fderiv_uniformCauchy hR hf hg
  have hp : ∀ x ∈ ball a (R / 2),
      Tendsto (fun n => fderiv ℂ (f n) x) atTop (𝓝 (D x)) :=
    fun x hx => tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hc.cauchySeq hx))
  have hu := hc.tendstoUniformlyOn_of_tendsto hp
  intro x hx
  have hm : ball a (R / 2) ⊆ ball a R := ball_subset_ball (by linarith)
  exact (hasFDerivAt_of_tendsto_locally_uniformly_on' isOpen_ball
    hu.tendstoLocallyUniformlyOn (fun n => (hf n).mono hm)
    (fun y hy => hg.tendsto_at (hm hy)) hx).differentiableAt.differentiableWithinAt

/-- GP-05 is applied to the proved holomorphic limit, on the half ball. -/
theorem analyticOnNhd_uniformLimit {f : ℕ → E → F} {g : E → F} {a : E} {R : ℝ}
    (hR : 0 < R) (hf : ∀ n, DifferentiableOn ℂ (f n) (ball a R))
    (hg : TendstoUniformlyOn f g atTop (ball a R)) :
    AnalyticOnNhd ℂ g (ball a (R / 2)) :=
  QuantumNLS.HolomorphicStageD3.analyticOnNhd_of_differentiableOn isOpen_ball
    (differentiableOn_uniformLimit hR hf hg)

/-- Uniform limits on an arbitrary open Banach domain are holomorphic. -/
theorem differentiableOn_uniformLimit_open {f : ℕ → E → F} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hg : TendstoUniformlyOn f g atTop U) : DifferentiableOn ℂ g U := by
  intro a ha
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU a ha
  have hd := differentiableOn_uniformLimit hR (fun n => (hf n).mono hRU) (hg.mono hRU)
  exact (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hR)))).differentiableWithinAt

/-- An open-domain uniform holomorphic limit is Banach analytic by GP-05. -/
theorem analyticOnNhd_uniformLimit_open {f : ℕ → E → F} {g : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hg : TendstoUniformlyOn f g atTop U) : AnalyticOnNhd ℂ g U :=
  QuantumNLS.HolomorphicStageD3.analyticOnNhd_of_differentiableOn hU
    (differentiableOn_uniformLimit_open hU hf hg)

end QuantumNLS.Ext025A4AnalyticLimit


end


/-! GP-04 support: holomorphic Picard iteration for a contracting map on
an actual complete ball. Iterates, the limit, uniform convergence and
analyticity are constructed. The path-space ODE map and the real compact
trajectory application are not constructed by this abstract theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped NNReal
open Filter Topology Set Metric
namespace QuantumNLS.Ext025A4AnalyticPicard
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def iterate (P : E × F → F) (b : F) : ℕ → E → F
  | 0, _ => b
  | n+1, x => P (x, iterate P b n x)

omit [CompleteSpace F] in
/-- Holomorphy of every Picard iterate on the initial-point domain. -/
theorem iterate_differentiable {P : E × F → F} {b : F} {U : Set E} {r R : ℝ}
    (hU : IsOpen U) (hr : 0 ≤ r) (hrR : r < R)
    (hP : DifferentiableOn ℂ P (U ×ˢ ball b R))
    (hmap : ∀ x ∈ U, ∀ y ∈ closedBall b r, P (x,y) ∈ closedBall b r) :
    ∀ n, (∀ x ∈ U, iterate P b n x ∈ closedBall b r) ∧
      DifferentiableOn ℂ (iterate P b n) U := by
  intro n
  induction n with
  | zero => exact ⟨fun _ _ => mem_closedBall_self hr, differentiableOn_const _⟩
  | succ n ih =>
    refine ⟨fun x hx => hmap x hx _ (ih.1 x hx), fun x hx => ?_⟩
    have hy : iterate P b n x ∈ ball b R :=
      lt_of_le_of_lt (ih.1 x hx) hrR
    have hpair : DifferentiableAt ℂ (fun x => (x, iterate P b n x)) x :=
      differentiableAt_id.prodMk (ih.2.differentiableAt (hU.mem_nhds hx))
    exact ((hP.differentiableAt ((hU.prod isOpen_ball).mem_nhds ⟨hx,hy⟩)).comp x hpair).differentiableWithinAt

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- Construction of the fixed branch, with geometric error uniform in the
initial point. The contraction and ball invariance are hypotheses on `P`. -/
theorem exists_uniformLimit {P : E × F → F} {b : F} {U : Set E} {r : ℝ} {q : ℝ≥0}
    (hr : 0 ≤ r) (hq : q < 1)
    (hmap : ∀ x ∈ U, ∀ y ∈ closedBall b r, P (x,y) ∈ closedBall b r)
    (hlip : ∀ x ∈ U, LipschitzOnWith q (fun y => P (x,y)) (closedBall b r)) :
    ∃ g : E → F, (∀ x ∈ U, g x ∈ closedBall b r ∧ P (x,g x) = g x) ∧
      TendstoUniformlyOn (iterate P b) g atTop U := by
  classical
  have hex : ∀ x : E, ∃ y : F, x ∈ U → y ∈ closedBall b r ∧ P (x,y) = y ∧
      ∀ n, dist (iterate P b n x) y ≤ (2 * r / (1 - (q : ℝ))) * (q : ℝ)^n := by
    intro x
    by_cases hx : x ∈ U
    · let A := closedBall b r
      let z : A := ⟨b, mem_closedBall_self hr⟩
      let p : A → A := fun y => ⟨P (x,y), hmap x hx y y.2⟩
      let : Nonempty A := ⟨z⟩
      let : CompleteSpace A := Metric.isClosed_closedBall.isComplete.completeSpace_coe
      have hc : ContractingWith q p := ⟨hq, (hlip x hx).mapsToRestrict (hmap x hx)⟩
      let y := hc.fixedPoint p
      have hy : P (x,(y : F)) = y := congrArg Subtype.val hc.fixedPoint_isFixedPt
      have hi : ∀ n, ((p^[n] z : A) : F) = iterate P b n x := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => simp only [Function.iterate_succ_apply', p, iterate, ih]
      refine ⟨y, fun _ => ⟨y.2, hy, fun n => ?_⟩⟩
      have hh := hc.apriori_dist_iterate_fixedPoint_le z n
      have hdist : dist z (p z) ≤ 2 * r := by
        change dist b (P (x,b)) ≤ 2*r
        have hm := hmap x hx b (mem_closedBall_self hr)
        rw [mem_closedBall, dist_comm] at hm
        linarith
      have he : dist (iterate P b n x) (y : F) ≤ dist z (p z) * (q : ℝ)^n / (1-(q : ℝ)) := by
        change dist ((p^[n] z : A) : F) (y : F) ≤ dist z (p z) * (q : ℝ)^n / (1-(q : ℝ)) at hh
        rw [hi n] at hh
        exact hh
      refine he.trans ?_
      have hp : 0 < 1 - (q : ℝ) := by exact_mod_cast hc.one_sub_K_pos
      calc dist z (p z) * (q : ℝ)^n / (1-(q : ℝ))
          ≤ (2*r) * (q : ℝ)^n / (1-(q : ℝ)) := by gcongr
        _ = (2*r / (1-(q : ℝ))) * (q : ℝ)^n := by ring
    · exact ⟨b, fun h => (hx h).elim⟩
  choose g hg using hex
  refine ⟨g, fun x hx => ⟨(hg x hx).1, (hg x hx).2.1⟩, ?_⟩
  have hqreal : (q : ℝ) < 1 := by exact_mod_cast hq
  have ht : Tendsto (fun n : ℕ => (2*r / (1-(q : ℝ))) * (q : ℝ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one q.coe_nonneg hqreal).const_mul (2*r / (1-(q : ℝ)))
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x hx
  rw [dist_comm]
  exact ((hg x hx).2.2 n).trans_lt hn

/-- Analyticity of the constructed fixed branch, proved from holomorphic
iterates and their uniform geometric convergence. No analytic branch is supplied. -/
theorem analytic_fixedPoint {P : E × F → F} {b : F} {U : Set E} {r R : ℝ} {q : ℝ≥0}
    (hU : IsOpen U) (hr : 0 ≤ r) (hrR : r < R) (hq : q < 1)
    (hP : DifferentiableOn ℂ P (U ×ˢ ball b R))
    (hmap : ∀ x ∈ U, ∀ y ∈ closedBall b r, P (x,y) ∈ closedBall b r)
    (hlip : ∀ x ∈ U, LipschitzOnWith q (fun y => P (x,y)) (closedBall b r)) :
    ∃ g : E → F, AnalyticOnNhd ℂ g U ∧
      (∀ x ∈ U, g x ∈ closedBall b r ∧ P (x,g x) = g x) ∧
      TendstoUniformlyOn (iterate P b) g atTop U := by
  obtain ⟨g, hg, hu⟩ := exists_uniformLimit hr hq hmap hlip
  exact ⟨g, QuantumNLS.Ext025A4AnalyticLimit.analyticOnNhd_uniformLimit_open hU
    (fun n => (iterate_differentiable hU hr hrR hP hmap n).2) hu, hg, hu⟩
end QuantumNLS.Ext025A4AnalyticPicard


end


/-! GP-04 support: a prescribed complex ball and value bound give an
explicit common Taylor radius and coefficient majorant. The radius does
not depend on a choice of a local bound for the individual map.
The ODE-to-contraction application remains a separate obligation. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped NNReal
open Filter Topology Metric Complex Set
namespace QuantumNLS.Ext025A4AnalyticMajorant
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Quantitative version of the accepted GP-05 bridge, using the given
ball instead of choosing an individual local radius. -/
theorem powerSeries_with_bound {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) {x : E} (hx : x ∈ U) {R M : ℝ}
    (hR : 0 < R) (hM0 : 0 ≤ M) (hxU : ball x R ⊆ U)
    (hM : ∀ z ∈ ball x R, ‖f z‖ ≤ M) :
    let r := Real.toNNReal (R / (4 * Real.exp 1))
    0 < r ∧ HasFPowerSeriesOnBall f (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x) x r ∧
      ∀ n, ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x‖ * (r : ℝ)^n ≤ M * Real.exp 1 := by
  have hexp : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    linarith
  set r0 : ℝ := R / (4 * Real.exp 1) with hr0_def
  have hr0 : 0 < r0 := div_pos hR (by positivity)
  have hr0_lt : r0 < R / 2 := by
    rw [hr0_def, div_lt_iff₀ (by positivity)]
    nlinarith
  let r : NNReal := Real.toNNReal r0
  have hrr : (r : ℝ) = r0 := Real.coe_toNNReal r0 hr0.le
  have hr : (0 : NNReal) < r := by
    rw [← NNReal.coe_pos, hrr]
    exact hr0
  have hcoef : ∀ n, ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x‖ * (r : ℝ)^n ≤ M * Real.exp 1 := by
    intro n
    rw [hrr]
    exact QuantumNLS.HolomorphicStageD1.coeff_radius_bound hU hf hR hM0 hxU hM n
  refine ⟨hr, ⟨?_, ?_, ?_⟩, hcoef⟩
  · -- radius bound from stage D1
    exact FormalMultilinearSeries.le_radius_of_bound
      (p := fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f x) (M * Real.exp 1)
      (r := r)
      (fun n => by
        rw [hrr]
        exact QuantumNLS.HolomorphicStageD1.coeff_radius_bound hU hf hR hM0 hxU hM n)
  · exact ENNReal.coe_pos.2 hr
  · intro y hy
    -- the slice is complex-differentiable on ball 0 2 and stays in U
    have hyn : ‖y‖ < r0 := by
      have h1 : ‖y‖₊ < r := by
        rw [Metric.mem_eball, edist_zero_right] at hy
        exact ENNReal.coe_lt_coe.1 hy
      have h2 : (‖y‖₊ : ℝ) < (r : ℝ) := NNReal.coe_lt_coe.2 h1
      rw [coe_nnnorm, hrr] at h2
      exact h2
    have hsmul : ∀ t : ℂ, ‖t‖ < 2 → x + t • y ∈ U := by
      intro t ht
      apply hxU
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
      have hy2 : ‖y‖ < R / 2 := by linarith
      nlinarith [norm_nonneg t, norm_nonneg y]
    have hlin : DifferentiableOn ℂ (fun s : ℂ => x + s • y) (ball (0 : ℂ) 2) :=
      (by fun_prop : Differentiable ℂ (fun s : ℂ => x + s • y)).differentiableOn
    have hmaps : MapsTo (fun s : ℂ => x + s • y) (ball (0 : ℂ) 2) U := by
      intro s hs
      exact hsmul s (by simpa [mem_ball_zero_iff] using hs)
    have hgd : DifferentiableOn ℂ (fun s : ℂ => f (x + s • y)) (ball (0 : ℂ) 2) :=
      DifferentiableOn.comp hf hlin hmaps
    have h1mem : (1 : ℂ) ∈ ball (0 : ℂ) 2 := by
      simp
    have hT := Complex.hasSum_taylorSeries_on_ball hgd h1mem
    have hT2 : HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (1 - 0 : ℂ) ^ n •
        iteratedDeriv n (fun s : ℂ => f (x + s • y)) 0) (f (x + y)) := by
      have h := hT
      rwa [one_smul] at h
    have hdiag : ∀ n : ℕ, iteratedDeriv n (fun s : ℂ => f (x + s • y)) 0
        = iteratedFDeriv ℂ n f x (fun _ => y) := by
      intro n
      have h := QuantumNLS.HolomorphicStageD2.iteratedDeriv_slice hU hf x y n 0 (by simpa using hx)
      rw [zero_smul, add_zero] at h
      exact h
    convert hT2 using 1
    funext n
    simp only [smul_apply]
    rw [hdiag n]
    simp

/-- Uniform Taylor series for a family of constructed contracting branches.
This is the complex fixed-point stage, before constructing the real ODE
path map and the compact-trajectory subdivision required by the consumer. -/
theorem family_fixedPoint_uniformSeries {ι : Type*} {P : ι → E × F → F} {b : F}
    {U : Set E} {a : E} {r R D : ℝ} {q : ℝ≥0}
    (hU : IsOpen U) (ha : a ∈ U) (hr : 0 ≤ r) (hrR : r < R)
    (hD : 0 < D) (hDU : ball a D ⊆ U) (hq : q < 1)
    (hP : ∀ i, DifferentiableOn ℂ (P i) (U ×ˢ ball b R))
    (hmap : ∀ i x, x ∈ U → ∀ y ∈ closedBall b r, P i (x,y) ∈ closedBall b r)
    (hlip : ∀ i x, x ∈ U → LipschitzOnWith q (fun y => P i (x,y)) (closedBall b r)) :
    ∃ g : ι → E → F,
      (∀ i x, x ∈ U → g i x ∈ closedBall b r ∧ P i (x,g i x) = g i x) ∧
      ∃ ρ > (0 : ℝ), ∃ C : ℝ, ∀ i, ∃ p : FormalMultilinearSeries ℂ E F,
        HasFPowerSeriesOnBall (g i) p a (ENNReal.ofReal ρ) ∧ ∀ n, ‖p n‖ * ρ^n ≤ C := by
  classical
  choose g hg using fun i => QuantumNLS.Ext025A4AnalyticPicard.analytic_fixedPoint
    hU hr hrR hq (hP i) (hmap i) (hlip i)
  let ρ : NNReal := Real.toNNReal (D / (4 * Real.exp 1))
  have hρ : (0 : ℝ) < ρ := by
    change 0 < max (_ / (4 * Real.exp 1)) 0
    exact (div_pos hD (by positivity)).trans_le (le_max_left _ _) 
  refine ⟨g, fun i x hx => (hg i).2.1 x hx, ρ, hρ, (‖b‖ + r) * Real.exp 1, fun i => ?_⟩
  have hM : ∀ z ∈ ball a D, ‖g i z‖ ≤ ‖b‖ + r := by
    intro z hz
    exact norm_le_norm_add_const_of_dist_le ((hg i).2.1 z (hDU hz)).1
  have hb := powerSeries_with_bound hU (hg i).1.differentiableOn ha hD
    (add_nonneg (norm_nonneg _) hr) hDU hM
  refine ⟨fun n => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (g i) a, ?_, hb.2.2⟩
  simpa only [ENNReal.ofReal_coe_nnreal] using hb.2.1

end QuantumNLS.Ext025A4AnalyticMajorant


end


/-! GP-04 support: the actual composition map on continuous path space.
Its complex Fréchet derivative is constructed pointwise and bounded in the
sup norm, using the Cauchy quadratic remainder of the original field. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Filter Topology Set Metric
namespace QuantumNLS.Ext025A4AnalyticPath
universe u v
variable {K : Type v} {E : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Pointwise application of a continuous operator-valued path. -/
def applyPath (A : C(K, E →L[ℂ] E)) : C(K,E) →L[ℂ] C(K,E) :=
  LinearMap.mkContinuous
    { toFun := fun w => ⟨fun t => A t (w t), A.continuous.clm_apply w.continuous⟩
      map_add' := fun v w => by ext t; exact map_add (A t) (v t) (w t)
      map_smul' := fun c w => by ext t; exact map_smul (A t) c (w t) }
    ‖A‖ (fun w => (ContinuousMap.norm_le _ (by positivity)).mpr fun t =>
      (ContinuousLinearMap.le_opNorm (A t) (w t)).trans
        (mul_le_mul (A.norm_coe_le_norm t) (w.norm_coe_le_norm t) (norm_nonneg (w t)) (norm_nonneg A)))


/-- Composition by the continuous field on continuous paths. -/
def superposition (f : E → E) (hc : Continuous f) (v : C(K,E)) : C(K,E) :=
  ⟨fun t => f (v t), hc.comp v.continuous⟩


/-- Complex differentiation of the actual path-space composition map.
Only field differentiability and a Lipschitz bound for its derivative are
premises; no path-space differential or analytic branch is supplied. -/
theorem superposition_differentiable {f : E → E} (hc : Continuous f) {a : E} {R Λ : ℝ}
    (_hR : 0 < R) (hf : DifferentiableOn ℂ f (ball a R)) (hΛ : 0 ≤ Λ)
    (hLip : ∀ x ∈ ball a R, ∀ y ∈ ball a R,
      ‖fderiv ℂ f x - fderiv ℂ f y‖ ≤ Λ * ‖x-y‖) :
    DifferentiableOn ℂ (superposition f hc : C(K,E) → C(K,E))
      (ball (ContinuousMap.const K a) R) := by
  intro v hv
  have hvn : ‖v - ContinuousMap.const K a‖ < R := by
    simpa only [mem_ball, dist_eq_norm] using hv
  have hvm : ∀ t : K, v t ∈ ball a R := by
    intro t
    rw [mem_ball, dist_eq_norm]
    exact ((v - ContinuousMap.const K a).norm_coe_le_norm t).trans_lt hvn
  have hdf : ContinuousOn (fderiv ℂ f) (ball a R) :=
    (QuantumNLS.HolomorphicCauchyC1.contDiffOn_one_of_differentiableOn isOpen_ball hf).continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  let A : C(K,E →L[ℂ] E) := ⟨fun t => fderiv ℂ f (v t),
    hdf.comp_continuous v.continuous hvm⟩
  suffices hd : HasFDerivAt (superposition f hc) (applyPath A) v from
    hd.differentiableAt.differentiableWithinAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hδ : 0 < min (R - ‖v - ContinuousMap.const K a‖) (ε / (Λ+1)) := by
    exact lt_min (sub_pos.mpr hvn) (div_pos hε (by linarith))
  filter_upwards [Metric.ball_mem_nhds (0 : C(K,E)) hδ] with w hw
  have hwn : ‖w‖ < min (R - ‖v - ContinuousMap.const K a‖) (ε / (Λ+1)) := by
    simpa only [mem_ball, dist_zero_right] using hw
  have hwsmall := lt_of_lt_of_le hwn (min_le_left _ _)
  have hweps := lt_of_lt_of_le hwn (min_le_right _ _)
  have hvw : ∀ t : K, v t + w t ∈ ball a R := by
    intro t
    rw [mem_ball, dist_eq_norm]
    calc ‖v t + w t - a‖ = ‖(v t - a) + w t‖ := by congr 1; abel
      _ ≤ ‖v t - a‖ + ‖w t‖ := norm_add_le _ _
      _ ≤ ‖v - ContinuousMap.const K a‖ + ‖w‖ :=
        add_le_add ((v - ContinuousMap.const K a).norm_coe_le_norm t) (w.norm_coe_le_norm t)
      _ < R := by linarith
  have hb : ‖superposition f hc (v+w) - superposition f hc v - applyPath A w‖ ≤ Λ * ‖w‖^2 := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    change ‖f (v t + w t) - f (v t) - fderiv ℂ f (v t) (w t)‖ ≤ Λ * ‖w‖^2
    have hh := QuantumNLS.HolomorphicStageB1.norm_sub_sub_fderiv_le isOpen_ball hf
      (subset_refl _) (convex_ball a R) hΛ hLip (hvm t) (hvw t)
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (w.norm_coe_le_norm t) 2) hΛ)
  have hs : Λ * ‖w‖ ≤ ε := by
    have hh := (lt_div_iff₀ (by linarith : 0 < Λ+1)).mp hweps
    nlinarith [norm_nonneg w]
  calc ‖superposition f hc (v+w) - superposition f hc v - applyPath A w‖ ≤ Λ * ‖w‖^2 := hb
    _ = (Λ * ‖w‖) * ‖w‖ := by ring
    _ ≤ ε * ‖w‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg _)

end QuantumNLS.Ext025A4AnalyticPath


end


/-! The actual bounded complex-linear time-primitive and Picard map on
continuous paths. Its derivative is obtained from the proved superposition
differential, rather than supplied as an assumption. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped NNReal
open Filter Topology Set Metric MeasureTheory
namespace QuantumNLS.Ext025A4AnalyticIntegral
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
abbrev Time := Icc (0 : ℝ) 1
abbrev Path (E : Type u) [TopologicalSpace E] := C(Time,E)

/-- Extension of a continuous path by constant endpoint values. -/
def extend (v : Path E) : C(ℝ,E) := ContinuousMap.IccExtend zero_le_one v

/-- The literal primitive on the unit time interval. -/
def primitivePath (v : Path E) : Path E :=
  ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), extend v s,
    (intervalIntegral.differentiable_integral_of_continuous (extend v).continuous).continuous.comp continuous_subtype_val⟩

/-- Sup-norm bound for the time primitive. -/
theorem primitivePath_norm (v : Path E) : ‖primitivePath v‖ ≤ ‖v‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (f := fun s => extend v s)
    (fun s _ => v.norm_coe_le_norm (Set.projIcc 0 1 zero_le_one s))
  change ‖∫ s in (0 : ℝ)..(t : ℝ), extend v s‖ ≤ ‖v‖
  calc _ ≤ ‖v‖ * |(t : ℝ)-0| := hb
    _ ≤ ‖v‖ := by rw [sub_zero, abs_of_nonneg t.2.1]; nlinarith [norm_nonneg v, t.2.2]

/-- The time-primitive operator is complex-linear and bounded by one. -/
def primitive : Path E →L[ℂ] Path E :=
  LinearMap.mkContinuous
    { toFun := primitivePath
      map_add' := fun v w => by
        ext t
        change (∫ s in (0 : ℝ)..(t : ℝ), extend (v+w) s) = _
        have he : ∀ s, extend (v+w) s = extend v s + extend w s := fun _ => rfl
        simp_rw [he]
        exact intervalIntegral.integral_add ((extend v).continuous.intervalIntegrable _ _)
          ((extend w).continuous.intervalIntegrable _ _)
      map_smul' := fun c v => by
        ext t
        change (∫ s in (0 : ℝ)..(t : ℝ), extend (c • v) s) = _
        have he : ∀ s, extend (c • v) s = c • extend v s := fun _ => rfl
        simp_rw [he]
        exact intervalIntegral.integral_smul c _ }
    1 (fun v => by simpa using primitivePath_norm v)

@[simp] theorem primitive_apply (v : Path E) (t : Time) :
    primitive v t = ∫ s in (0 : ℝ)..(t : ℝ), extend v s := rfl

/-- Literal scaled Picard operator on continuous paths. -/
def picard (f : E → E) (hc : Continuous f) (T : ℝ) (p : E × Path E) : Path E :=
  ContinuousMap.const Time p.1 + (T : ℂ) • primitive (QuantumNLS.Ext025A4AnalyticPath.superposition f hc p.2)

/-- Complex differentiability of the actual path-space Picard operator. -/
theorem picard_differentiable {f : E → E} (hc : Continuous f) {a : E} {R Λ T : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball a R)) (hΛ : 0 ≤ Λ)
    (hLip : ∀ x ∈ ball a R, ∀ y ∈ ball a R,
      ‖fderiv ℂ f x - fderiv ℂ f y‖ ≤ Λ * ‖x-y‖) (U : Set E) :
    DifferentiableOn ℂ (picard f hc T) (U ×ˢ ball (ContinuousMap.const Time a) R) := by
  have hN := QuantumNLS.Ext025A4AnalyticPath.superposition_differentiable (K := Time) hc hR hf hΛ hLip
  intro p hp
  have hs : DifferentiableAt ℂ (fun p : E × Path E =>
      QuantumNLS.Ext025A4AnalyticPath.superposition f hc p.2) p :=
    (hN.differentiableAt (isOpen_ball.mem_nhds hp.2)).comp p differentiableAt_snd
  have hi : DifferentiableAt ℂ (fun p : E × Path E =>
      primitive (QuantumNLS.Ext025A4AnalyticPath.superposition f hc p.2)) p :=
    (primitive (E := E)).differentiableAt.comp p hs
  have hx : DifferentiableAt ℂ (fun p : E × Path E => ContinuousMap.const Time p.1) p :=
    (ContinuousLinearMap.const Time (R := ℂ) (M := E)).differentiableAt.comp p differentiableAt_fst
  exact (hx.add (hi.const_smul (T : ℂ))).differentiableWithinAt

omit [NormedSpace ℂ E] [CompleteSpace E] in
/-- Pointwise ball control from the path sup norm. -/
theorem path_mem {a : E} {r : ℝ} {v : Path E}
    (hv : v ∈ closedBall (ContinuousMap.const Time a) r) (t : Time) :
    v t ∈ closedBall a r := by
  rw [mem_closedBall, dist_eq_norm] at hv ⊢
  exact ((v - ContinuousMap.const Time a).norm_coe_le_norm t).trans hv

/-- The actual Picard map preserves the complete path ball, from field
value bounds and the usual time-radius inequality. -/
theorem picard_maps_ball {f : E → E} (hc : Continuous f) {a : E} {r δ M : ℝ} {T : ℝ≥0}
    (hM : ∀ y ∈ closedBall a r, ‖f y‖ ≤ M) (hsize : δ + (T : ℝ)*M ≤ r) :
    ∀ x ∈ ball a δ, ∀ v ∈ closedBall (ContinuousMap.const Time a) r,
      picard f hc T (x,v) ∈ closedBall (ContinuousMap.const Time a) r := by
  intro x hx v hv
  rw [mem_ball, dist_eq_norm] at hx
  rw [mem_closedBall, dist_eq_norm]
  have hn : ‖QuantumNLS.Ext025A4AnalyticPath.superposition f hc v‖ ≤ M := by
    apply (ContinuousMap.norm_le_of_nonempty _).mpr
    intro t
    exact hM _ (path_mem hv t)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hn
  have hr0 : 0 ≤ r := by nlinarith [norm_nonneg (x-a), mul_nonneg T.coe_nonneg hM0]
  apply (ContinuousMap.norm_le _ hr0).mpr
  intro t
  change ‖x + (T : ℂ) • primitive (QuantumNLS.Ext025A4AnalyticPath.superposition f hc v) t - a‖ ≤ r
  calc _ = ‖(x-a) + (T : ℂ) • primitive (QuantumNLS.Ext025A4AnalyticPath.superposition f hc v) t‖ := by congr 1; abel
    _ ≤ ‖x-a‖ + ‖(T : ℂ) • primitive (QuantumNLS.Ext025A4AnalyticPath.superposition f hc v) t‖ := norm_add_le _ _
    _ = ‖x-a‖ + (T : ℝ) * ‖primitive (QuantumNLS.Ext025A4AnalyticPath.superposition f hc v) t‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg T.coe_nonneg]
    _ ≤ δ + (T : ℝ)*M := by
      gcongr
      exact ((primitive (QuantumNLS.Ext025A4AnalyticPath.superposition f hc v)).norm_coe_le_norm t).trans
        ((primitivePath_norm _).trans hn)
    _ ≤ r := hsize

/-- The actual path-space contraction constant is time times the field
Lipschitz constant. -/
theorem picard_lipschitz {f : E → E} (hc : Continuous f) {a : E} {r : ℝ} (T K : ℝ≥0)
    (hK : LipschitzOnWith K f (closedBall a r)) (x : E) :
    LipschitzOnWith (T*K) (fun v => picard f hc T (x,v)) (closedBall (ContinuousMap.const Time a) r) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  have hn : ‖QuantumNLS.Ext025A4AnalyticPath.superposition f hc v -
      QuantumNLS.Ext025A4AnalyticPath.superposition f hc w‖ ≤ (K : ℝ)*‖v-w‖ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro t
    change ‖f (v t) - f (w t)‖ ≤ (K : ℝ)*‖v-w‖
    have hh := hK.dist_le_mul _ (path_mem hv t) _ (path_mem hw t)
    rw [dist_eq_norm, dist_eq_norm] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ((v-w).norm_coe_le_norm t) K.coe_nonneg)
  rw [dist_eq_norm, dist_eq_norm]
  have he : picard f hc T (x,v) - picard f hc T (x,w) =
      (T : ℂ) • primitive (QuantumNLS.Ext025A4AnalyticPath.superposition f hc v -
        QuantumNLS.Ext025A4AnalyticPath.superposition f hc w) := by
    simp only [picard, map_sub, smul_sub]
    abel
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg T.coe_nonneg, NNReal.coe_mul]
  calc (T : ℝ)*‖primitive (QuantumNLS.Ext025A4AnalyticPath.superposition f hc v -
        QuantumNLS.Ext025A4AnalyticPath.superposition f hc w)‖
      ≤ (T : ℝ)*((K : ℝ)*‖v-w‖) :=
        mul_le_mul_of_nonneg_left ((primitivePath_norm _).trans hn) T.coe_nonneg
    _ = (T : ℝ)*(K : ℝ)*‖v-w‖ := by ring

/-- A holomorphic path-valued solution of the literal Picard integral
equation is constructed from bounds on the field, with no supplied fixed
branch, derivative, or analyticity conclusion. -/
theorem local_holomorphic_solution {f : E → E} (hc : Continuous f) {a : E} {r R δ M Λ : ℝ}
    (T K : ℝ≥0) (hr : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball a R)) (hΛ : 0 ≤ Λ)
    (hLip : ∀ x ∈ ball a R, ∀ y ∈ ball a R,
      ‖fderiv ℂ f x - fderiv ℂ f y‖ ≤ Λ * ‖x-y‖)
    (hM : ∀ y ∈ closedBall a r, ‖f y‖ ≤ M)
    (hsize : δ + (T : ℝ)*M ≤ r) (hK : LipschitzOnWith K f (closedBall a r))
    (hsmall : T*K < 1) :
    ∃ g : E → Path E, AnalyticOnNhd ℂ g (ball a δ) ∧
      ∀ x ∈ ball a δ, g x ∈ closedBall (ContinuousMap.const Time a) r ∧
        ∀ t : Time, g x t = x + (T : ℂ) • ∫ s in (0 : ℝ)..(t : ℝ), extend
          (QuantumNLS.Ext025A4AnalyticPath.superposition f hc (g x)) s := by
  obtain ⟨g, hg, hfix, _⟩ := QuantumNLS.Ext025A4AnalyticPicard.analytic_fixedPoint
    (P := picard f hc T) isOpen_ball hr hrR hsmall
    (picard_differentiable hc (lt_of_le_of_lt hr hrR) hf hΛ hLip (ball a δ))
    (picard_maps_ball hc hM hsize) (fun x _ => picard_lipschitz hc T K hK x)
  refine ⟨g, hg, fun x hx => ⟨(hfix x hx).1, fun t => ?_⟩⟩
  have hh := congrArg (fun v : Path E => v t) (hfix x hx).2
  exact hh.symm

/-- Uniform complex Taylor majorants for every time evaluation of the
actual local Picard solutions, simultaneously over a family of fields.
No analytic dependence or solution map is a premise. -/
theorem family_local_uniformSeries {ι : Type*} (f : ι → E → E) (hc : ∀ i, Continuous (f i))
    {a : E} {r R δ M Λ : ℝ} (T K : ℝ≥0) (hr : 0 ≤ r) (hrR : r < R) (hδ : 0 < δ)
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball a R)) (hΛ : 0 ≤ Λ)
    (hLip : ∀ i x, x ∈ ball a R → ∀ y ∈ ball a R,
      ‖fderiv ℂ (f i) x - fderiv ℂ (f i) y‖ ≤ Λ * ‖x-y‖)
    (hM : ∀ i y, y ∈ closedBall a r → ‖f i y‖ ≤ M)
    (hsize : δ + (T : ℝ)*M ≤ r) (hK : ∀ i, LipschitzOnWith K (f i) (closedBall a r))
    (hsmall : T*K < 1) :
    ∃ g : ι → E → Path E,
      (∀ i, AnalyticOnNhd ℂ (g i) (ball a δ)) ∧
      (∀ i x, x ∈ ball a δ → g i x ∈ closedBall (ContinuousMap.const Time a) r ∧
        ∀ t : Time, g i x t = x + (T : ℂ) • ∫ s in (0 : ℝ)..(t : ℝ), extend
          (QuantumNLS.Ext025A4AnalyticPath.superposition (f i) (hc i) (g i x)) s) ∧
      ∃ ρ > (0 : ℝ), ∃ C : ℝ, ∀ i t, ∃ p : FormalMultilinearSeries ℂ E E,
        HasFPowerSeriesOnBall (fun x => g i x t) p a (ENNReal.ofReal ρ) ∧ ∀ n, ‖p n‖ * ρ^n ≤ C := by
  classical
  choose g hg using fun i => local_holomorphic_solution (hc i) T K hr hrR
    (hf i) hΛ (hLip i) (hM i) hsize (hK i) hsmall
  let ρ : NNReal := Real.toNNReal (δ / (4 * Real.exp 1))
  have hρ : (0 : ℝ) < ρ := by
    change 0 < max (δ / (4 * Real.exp 1)) 0
    exact (div_pos hδ (by positivity)).trans_le (le_max_left _ _)
  refine ⟨g, fun i => (hg i).1, fun i => (hg i).2,
    ρ, hρ, (‖a‖+r)*Real.exp 1, fun i t => ?_⟩
  have he : AnalyticOnNhd ℂ (fun x => g i x t) (ball a δ) := by
    intro x hx
    exact ((ContinuousMap.evalCLM (R := ℂ) (M := E) t).analyticAt (g i x)).comp ((hg i).1 x hx)
  have hb : ∀ x ∈ ball a δ, ‖g i x t‖ ≤ ‖a‖ + r := by
    intro x hx
    exact norm_le_norm_add_const_of_dist_le (path_mem ((hg i).2 x hx).1 t)
  have hp := QuantumNLS.Ext025A4AnalyticMajorant.powerSeries_with_bound isOpen_ball
    he.differentiableOn (mem_ball_self hδ) hδ (add_nonneg (norm_nonneg _) hr) (subset_refl _) hb
  refine ⟨fun n => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (fun x => g i x t) a, ?_, hp.2.2⟩
  simpa only [ENNReal.ofReal_coe_nnreal] using hp.2.1

end QuantumNLS.Ext025A4AnalyticIntegral


end

#print axioms QuantumNLS.Ext025A4AnalyticLimit.fderiv_uniformCauchy
#print axioms QuantumNLS.Ext025A4AnalyticLimit.differentiableOn_uniformLimit
#print axioms QuantumNLS.Ext025A4AnalyticLimit.analyticOnNhd_uniformLimit
#print axioms QuantumNLS.Ext025A4AnalyticLimit.differentiableOn_uniformLimit_open
#print axioms QuantumNLS.Ext025A4AnalyticLimit.analyticOnNhd_uniformLimit_open
#print axioms QuantumNLS.Ext025A4AnalyticPicard.iterate
#print axioms QuantumNLS.Ext025A4AnalyticPicard.iterate_differentiable
#print axioms QuantumNLS.Ext025A4AnalyticPicard.exists_uniformLimit
#print axioms QuantumNLS.Ext025A4AnalyticPicard.analytic_fixedPoint
#print axioms QuantumNLS.Ext025A4AnalyticMajorant.powerSeries_with_bound
#print axioms QuantumNLS.Ext025A4AnalyticMajorant.family_fixedPoint_uniformSeries
#print axioms QuantumNLS.Ext025A4AnalyticPath.applyPath
#print axioms QuantumNLS.Ext025A4AnalyticPath.superposition
#print axioms QuantumNLS.Ext025A4AnalyticPath.superposition_differentiable
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.family_local_uniformSeries
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.path_mem
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.picard_maps_ball
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.picard_lipschitz
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.local_holomorphic_solution
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.extend
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.primitivePath
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.primitivePath_norm
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.primitive
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.picard
#print axioms QuantumNLS.Ext025A4AnalyticIntegral.picard_differentiable

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4Analytic" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
