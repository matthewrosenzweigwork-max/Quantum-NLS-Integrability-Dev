import QuantumNLS.RetargetStageR48b
import QuantumNLS.RetargetRoughR48b
import QuantumNLS.DynSeedR47b

/-! Rough profile passage and quantitative conclusions for the one selected
gauge. The source-node binding waits for the accepted R-300B8640 module. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology
open scoped ComplexConjugate

namespace QuantumNLS.RetargetFinalProofR48b
open PhysicalTensor TensorCarrier Occupation OccupationHilbert FullOccupationAffinity FiniteCellGauge
open RetargetAnglesR48b RetargetStageR48b RetargetWeightsR48b RetargetCellR48b RetargetAssemblyR48b
open RetargetAffinityR48b RetargetRoughR48b
variable {L κ : ℝ} [Fact (0 < L)]

theorem continuous_coefficients (hκ : 0 < κ) (n : ℕ) :
    Continuous (coefficients (L := L) hκ n) := by
  have hc : Continuous (fun u : L2T L => htpow (𝕜 := ℂ) (n+1) u) := by
    have hm : Continuous (fun u : L2T L => IntrinsicContact.htpowML (n+1) (fun _ => u)) :=
      (IntrinsicContact.htpowML (E := L2T L) (n+1)).cont.comp
        (continuous_pi (fun _ : Fin (n+1) => continuous_id))
    have he : (fun u : L2T L => IntrinsicContact.htpowML (n+1) (fun _ => u)) =
        (fun u : L2T L => htpow (𝕜 := ℂ) (n+1) u) := by
      funext u
      exact IntrinsicContact.htpowML_apply (n+1) (fun _ => u)
    exact he ▸ hm
  exact (RetargetEdgeR48b.J _).continuous.comp (hc.subtype_mk _)

theorem continuous_coordinate (hκ : 0 < κ) (a : ℤ) :
    Continuous (fun u : L2T L => coordinate hκ u a) := by
  let C := Def021ChartR41b.chart L κ hκ
  exact (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 a).continuous.comp
    (continuous_iff_continuousAt.mpr fun u => (C.analytic u).continuousAt)

theorem continuousAt_pairPhase (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    ContinuousAt (fun p : ℂ × ℂ => (pairPhase p.1 p.2).1) (z,w) := by
  let f (p : ℂ × ℂ) : ℂ := FiniteCellFinal.symbol p.1 p.2
  have hf : ContinuousAt f (z,w) := by
    have he : ((‖z * w‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (mul_ne_zero hz hw))
    exact (continuous_fst.mul (Complex.continuous_conj.comp continuous_snd)).continuousAt.div
      ((Complex.continuous_ofReal.comp (continuous_fst.mul continuous_snd).norm).continuousAt) he
  have he : f =ᶠ[𝓝 (z,w)] fun p : ℂ × ℂ => (pairPhase p.1 p.2).1 := by
    filter_upwards [continuous_fst.continuousAt.eventually_ne hz,
      continuous_snd.continuousAt.eventually_ne hw] with p hp hq
    exact (pairPhase_eq_printed p.1 p.2 hp hq).symm
  exact hf.congr he

/-- At fixed particle number all scalar and operator tests are continuous.
Only the phase test uses a strictly positive margin. -/
theorem stage_closure (hκ : 0 < κ) {j n : ℕ} {q : Arr (n+1) → Phase}
    (hs : Stage (L := L) hκ j n q) (u : L2T L)
    (hu : u ∈ closure (R52CFCompact.profileClass L j)) (a b : ↥(labels j)) :
    let g := coefficients hκ n u
    let z := coordinate hκ u a.1
    let w := coordinate hκ u b.1
    ‖cartesian q a.1 b.1 g - (z * conj w) • g‖ ≤ stageBound j ∧
    (a.1 ≠ b.1 → stageBound j < ‖z‖^2 → stageBound j < ‖w‖^2 →
      ‖FiniteCellGauge.W q a.1 b.1 g - (pairPhase z w).1 • g‖ ≤ stageBound j) := by
  let g := coefficients (L := L) hκ n
  let z (v : L2T L) := coordinate hκ v a.1
  let w (v : L2T L) := coordinate hκ v b.1
  have hg : Continuous g := continuous_coefficients hκ n
  have hz : Continuous z := continuous_coordinate hκ a.1
  have hw : Continuous w := continuous_coordinate hκ b.1
  constructor
  · have hclosed : IsClosed {v | ‖cartesian q a.1 b.1 (g v) - (z v * conj (w v)) • g v‖ ≤
        stageBound j} :=
      isClosed_le (((cartesian q a.1 b.1).continuous.comp hg).sub
        ((hz.mul (Complex.continuous_conj.comp hw)).smul hg)).norm continuous_const
    exact closure_minimal (fun v hv => (hs v hv a b).1) hclosed hu
  · intro hab hza hzb
    let S := R52CFCompact.profileClass L j
    have hδ : 0 < stageBound j := by unfold stageBound; positivity
    have hzn : z u ≠ 0 := by
      intro he
      simp [show coordinate hκ u a.1 = 0 from he] at hza
      linarith
    have hwn : w u ≠ 0 := by
      intro he
      simp [show coordinate hκ u b.1 = 0 from he] at hzb
      linarith
    let f (v : L2T L) := ‖FiniteCellGauge.W q a.1 b.1 (g v) -
      (pairPhase (z v) (w v)).1 • g v‖
    have hp : ContinuousAt (fun v : L2T L => (z v, w v)) u := (hz.prodMk hw).continuousAt
    have hphase : ContinuousAt (fun v : L2T L => (pairPhase (z v) (w v)).1) u :=
      (continuousAt_pairPhase (z u) (w u) hzn hwn).comp_of_eq hp rfl
    have hfc : ContinuousAt f u :=
      (((FiniteCellGauge.W q a.1 b.1).continuous.comp hg).continuousAt.sub
        (hphase.smul hg.continuousAt)).norm
    have hne : (𝓝[S] u).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hu
    have hlim : Tendsto f (𝓝[S] u) (𝓝 (f u)) := hfc.continuousWithinAt
    apply le_of_tendsto hlim
    have hza' : ∀ᶠ v in 𝓝[S] u, stageBound j < ‖z v‖^2 :=
      ((hz.norm.pow 2).continuousAt.eventually (lt_mem_nhds hza)).filter_mono nhdsWithin_le_nhds
    have hzb' : ∀ᶠ v in 𝓝[S] u, stageBound j < ‖w v‖^2 :=
      ((hw.norm.pow 2).continuousAt.eventually (lt_mem_nhds hzb)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hza', hzb'] with v hv ha hb
    exact (hs v hv a b).2 hab ha.le hb.le

/-- Both limits on the actual unit DEF-002 balls and full corrected arrays. -/
def GaugeConclusion (hκ : 0 < κ) (s : ℕ → ℕ) (q : ∀ n, Arr (n+1) → Phase) : Prop :=
  Monotone s ∧ Tendsto s atTop atTop ∧
  (∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ u ∈ unitBall (L := L) R,
    ∀ a b : ↥(labels (s n)),
      let g := coefficients hκ n u
      let z := coordinate hκ u a.1
      let w := coordinate hκ u b.1
      ‖cartesian (q n) a.1 b.1 g - (z * conj w) • g‖ +
      ‖(cartesian (q n) a.1 b.1).adjoint g - conj (z * conj w) • g‖ ≤ ε) ∧
  (∀ R ρ ε : ℝ, 0 < ρ → 0 < ε → ∀ᶠ n in atTop, ∀ u ∈ unitBall (L := L) R,
    ∀ a b : ↥(labels (s n)), a.1 ≠ b.1 →
      let g := coefficients hκ n u
      let z := coordinate hκ u a.1
      let w := coordinate hκ u b.1
      let ζ := pairPhase z w
      ρ ≤ ‖z‖^2 → ρ ≤ ‖w‖^2 →
        ‖FiniteCellGauge.W (q n) a.1 b.1 g - ζ.1 • g‖ ≤ ε ∧
        ‖(FiniteCellGauge.W (q n) a.1 b.1).adjoint g - conj ζ.1 • g‖ ≤ ε ∧
        ExactShiftResidual.missing a.1 g ≤ ε ∧ ExactShiftResidual.missing b.1 g ≤ ε ∧
        |affinity a.1 b.1 g - 1| ≤ ε ∧ |defect a.1 b.1 (edgePhase (q n) a.1 b.1) ζ g| ≤ ε ∧
        ‖overlap a.1 b.1 (edgePhase (q n) a.1 b.1) g - ζ.1‖ ≤ ε)

/-- The mathematical gauge conclusion obtained by the compact-profile proof.
The declared printed-node acceptance binding is separate. -/
theorem gauge_conclusion_intermediate (hκ : 0 < κ) :
    ∃ (s : ℕ → ℕ) (q : ∀ n, Arr (n+1) → Phase), GaugeConclusion (L := L) hκ s q := by
  obtain ⟨s, q, hs, hs_atTop, hstage⟩ := smooth_intermediate (L := L) hκ
  have hR_atTop (R : ℝ) : ∀ᶠ n in atTop, R < (s n : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hs_atTop).eventually (eventually_gt_atTop R)
  have hpos : ∀ᶠ n in atTop, 0 < s n := hs_atTop.eventually (eventually_gt_atTop 0)
  have hb_zero := stageBound_tendsto.comp hs_atTop
  refine ⟨s,q,hs,hs_atTop,?_,?_⟩
  · intro R ε hε
    filter_upwards [hR_atTop R,hpos,hb_zero.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))]
      with n hnR hn hne
    intro u hu a b
    have hmem := mem_smooth_closure R (s n) hnR hu
    have hf := (stage_closure hκ (hstage n hn) u hmem a b).1
    have hr := (stage_closure hκ (hstage n hn) u hmem b a).1
    dsimp only
    rw [cartesian_adjoint]
    have hconj : conj (coordinate hκ u a.1 * conj (coordinate hκ u b.1)) =
        coordinate hκ u b.1 * conj (coordinate hκ u a.1) := by
      simp [mul_comm]
    rw [hconj]
    have hsmall : stageBound (s n) < ε / 2 := hne
    exact (add_le_add hf hr).trans (by linarith only [hsmall])
  · intro R ρ ε hρ hε
    let d := min (ε/2) (1/2)
    have hd : 0 < d := lt_min (by positivity) (by norm_num)
    have hdε : d ≤ ε := (min_le_left _ _).trans (by linarith)
    have hhalf : d ≤ 1/2 := min_le_right _ _
    have hdsq2 : 2*d^2 ≤ ε := (show 2*d^2 ≤ d by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hhalf)]).trans hdε
    filter_upwards [hR_atTop R,hpos,hb_zero.eventually (gt_mem_nhds hρ),hb_zero.eventually (gt_mem_nhds hd)]
      with n hnR hn hnρ hnd
    intro u hu a b hab g z w ζ ha hb
    have hmem := mem_smooth_closure R (s n) hnR hu
    have hf := ((stage_closure hκ (hstage n hn) u hmem a b).2 hab
      (hnρ.trans_le ha) (hnρ.trans_le hb)).trans hnd.le
    have hr := ((stage_closure hκ (hstage n hn) u hmem b a).2 hab.symm
      (hnρ.trans_le hb) (hnρ.trans_le ha)).trans hnd.le
    have hr' : ‖(FiniteCellGauge.W (q n) a.1 b.1).adjoint g - conj ζ.1 • g‖ ≤ d := by
      have hζ : (pairPhase w z).1 = conj ζ.1 := phase_reverse z w
      rw [W_adjoint (q n) a.1 b.1 hab, ← hζ]
      exact hr
    obtain ⟨h1,h2,hA,hD,hc⟩ := phase_errors (q n) a.1 b.1 hab ζ
      ⟨g, coefficients_unit hκ n u hu.1⟩ d hd.le hf hr'
    have hdsq : d^2 ≤ ε := by linarith [sq_nonneg d]
    exact ⟨hf.trans hdε,hr'.trans hdε,h1.trans hdsq2,h2.trans hdsq2,hA.trans hdsq,hD.trans hdsq,hc.trans hdε⟩

end QuantumNLS.RetargetFinalProofR48b

#print axioms QuantumNLS.RetargetFinalProofR48b.gauge_conclusion_intermediate

end

/-! Transfer the coefficient-side statements back to the physical N-particle
sectors using the actual corrected occupation transform. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
open Filter Topology
open scoped ComplexConjugate

namespace QuantumNLS.RetargetPhysicalR48b
open PhysicalTensor BetheCoefficientTransform BetheLabels Occupation OccupationHilbert
open FullOccupationAffinity FiniteCellGauge RetargetEdgeR48b RetargetWeightsR48b
variable {L κ : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The inverse transformation preserves the adjoint and residual norms on
every vector, including the actual products. -/
def physical (B : BetheBasis L N) (A : H N →L[ℂ] H N) : HN L N →L[ℂ] HN L N :=
  (J B).symm.toLinearIsometry.toContinuousLinearMap ∘L A ∘L
    (J B).toLinearIsometry.toContinuousLinearMap

theorem physical_apply (B : BetheBasis L N) (A : H N →L[ℂ] H N) (ψ : HN L N) :
    physical B A ψ = (J B).symm (A (J B ψ)) := rfl

theorem physical_adjoint (B : BetheBasis L N) (A : H N →L[ℂ] H N) :
    (physical B A).adjoint = physical B A.adjoint := by
  simp only [physical, ContinuousLinearMap.adjoint_comp,
    BethePhysicalTransfer.adjoint_isometryEquiv, LinearIsometryEquiv.symm_symm,
    ContinuousLinearMap.comp_assoc]

theorem physical_residual (B : BetheBasis L N) (A : H N →L[ℂ] H N) (ψ : HN L N) (z : ℂ) :
    ‖physical B A ψ - z • ψ‖ = ‖A (J B ψ) - z • J B ψ‖ := by
  rw [physical_apply, ← (J B).symm.norm_map (A (J B ψ) - z • J B ψ), map_sub, map_smul,
    LinearIsometryEquiv.symm_apply_apply]

theorem directed_formula (B : BetheBasis L N) (q : Arr N → Phase) (a b : ℤ) (m : MArr N) :
    physical B (FiniteCellGauge.W q a b) (B m) =
      if hd : DonorOK a m.val then
        ((q (marrArr N m)).1 * conj (q (shiftArr a b (marrArr N m) hd)).1) •
          B (DynSeedGradingR47b.transfer a b m hd)
      else 0 := by
  have hj := J_basis B m
  have hw := W_basis q a b (marrArr N m)
  simp only [single_classical] at hj hw
  rw [physical_apply, hj, hw]
  by_cases hd : DonorOK a m.val
  · have hd' : DonorOK a (marrArr N m).1 := hd
    have ht := J_basis B (DynSeedGradingR47b.transfer a b m hd)
    rw [DynSeedGradingR47b.transfer, Equiv.apply_symm_apply] at ht
    simp only [single_classical] at ht
    rw [dite_eq_left hd', dite_eq_left hd, map_smul, ← ht, LinearIsometryEquiv.symm_apply_apply]
    rfl
  · have hd' : ¬ DonorOK a (marrArr N m).1 := hd
    rw [dite_eq_right hd', dite_eq_right hd, map_zero]

theorem cartesian_formula (B : BetheBasis L N) (q : Arr N → Phase) (a b : ℤ) (m : MArr N) :
    physical B (cartesian q a b) (B m) =
      if hd : DonorOK a m.val then
        ((q (marrArr N m)).1 * conj (q (shiftArr a b (marrArr N m) hd)).1 *
          (coef N a b (marrArr N m).1 : ℂ)) • B (DynSeedGradingR47b.transfer a b m hd)
      else 0 := by
  have hj := J_basis B m
  have hc := cartesian_single q a b (marrArr N m)
  simp only [single_classical] at hj hc
  rw [physical_apply, hj, hc]
  by_cases hd : DonorOK a m.val
  · have hd' : DonorOK a (marrArr N m).1 := hd
    let d := shiftArr a b (marrArr N m) hd'
    let z := (q (marrArr N m)).1 * conj (q d).1 * (coef N a b (marrArr N m).1 : ℂ)
    have ht := J_basis B (DynSeedGradingR47b.transfer a b m hd)
    rw [DynSeedGradingR47b.transfer, Equiv.apply_symm_apply] at ht
    have hsingle : (lp.single 2 d z : H N) = z • (lp.single 2 d 1 : H N) := by
      rw [← lp.single_smul]
      simp only [smul_eq_mul, mul_one]
    simp only [single_classical] at ht hsingle
    rw [dite_eq_left hd', dite_eq_left hd]
    change (J B).symm _ = z • B (DynSeedGradingR47b.transfer a b m hd)
    rw [hsingle, map_smul, ← ht, LinearIsometryEquiv.symm_apply_apply]
    rfl
  · have hd' : ¬ DonorOK a (marrArr N m).1 := hd
    rw [dite_eq_right hd', dite_eq_right hd, map_zero]

/-- The physical diagonal is exactly the accepted intensive count. -/
theorem cartesian_count (hκ : 0 < κ) (n : ℕ) (q : Arr (n+1) → Phase) (a : ℤ) :
    physical (Def044D1SpectralR51a.basis (L := L) hκ n) (cartesian q a a) =
      Prop010ContourBindingR11.B L hκ (Nat.succ_pos n) a := by
  rw [cartesian_diag, ← RetargetStageR48b.count_coordinates (L := L) hκ n a]
  apply ContinuousLinearMap.ext
  intro ψ
  rw [physical_apply, inCoefficients_apply, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]

/-- The scalar weight is the positive square root of the product of the
two intensive diagonal eigenvalues, with the exact one-particle correction. -/
theorem cartesian_weight (hN : 0 < N) (a b : ℤ) (hab : a ≠ b) (m : MArr N) :
    coef N a b m.val =
      Real.sqrt (((m.val a : ℝ) / N) * ((m.val b : ℝ) / N + (N : ℝ)⁻¹)) := by
  let d := marrArr N m
  change coef N a b d.1 = Real.sqrt (frac N a d * (frac N b d + (N : ℝ)⁻¹))
  rw [← weighted_sq hN a b hab d, Real.sqrt_sq (coef_nonneg N a b d.1)]

theorem exact_exterior (a b i : ℤ) (m : MArr N) (hd : DonorOK a m.val)
    (hia : i ≠ a) (hib : i ≠ b) :
    (DynSeedGradingR47b.transfer a b m hd).val i = m.val i :=
  DynSeedGradingR47b.transfer_exterior a b m hd i hia hib

/-- The chosen array function in every physical sector, with the vacuum
assigned phase one. -/
def gauge (q : ∀ n, Arr (n+1) → Phase) : BetheOccupationGauge.Gauge
  | 0, _ => FiniteCellGauge.phaseOne
  | n+1, m => q n (marrArr (n+1) m)

/-- The physical shift uses the ratio of the same gauge on the two literal
complete Bethe arrays. -/
theorem physical_phase_ratio (hκ : 0 < κ) (n : ℕ) (q : ∀ n, Arr (n+1) → Phase)
    (a b : ℤ) (m : MArr (n+1)) :
    let B := Def044D1SpectralR51a.basis (L := L) hκ n
    physical B (FiniteCellGauge.W (q n) a b) (B m) =
      if hd : DonorOK a m.val then
        let d := DynSeedGradingR47b.transfer a b m hd
        ((gauge q (n+1) m).1 * conj (gauge q (n+1) d).1) • B d
      else 0 := by
  let B := Def044D1SpectralR51a.basis (L := L) hκ n
  change physical B (FiniteCellGauge.W (q n) a b) (B m) = _
  rw [directed_formula B (q n) a b m]
  split_ifs with hd
  · have he : marrArr (n+1) (DynSeedGradingR47b.transfer a b m hd) =
        shiftArr a b (marrArr (n+1) m) hd := by
      rw [DynSeedGradingR47b.transfer, Equiv.apply_symm_apply]
    change _ = ((q n (marrArr (n+1) m)).1 *
        conj (q n (marrArr (n+1) (DynSeedGradingR47b.transfer a b m hd))).1) • _
    rw [he]
  · rfl

/-- Convert the positive-sector index to the literal particle number. -/
def physicalSchedule (s : ℕ → ℕ) (N : ℕ) : ℕ := s (N-1)

theorem physicalSchedule_monotone {s : ℕ → ℕ} (hs : Monotone s) :
    Monotone (physicalSchedule s) :=
  hs.comp (fun _ _ hab => Nat.sub_le_sub_right hab 1)

theorem physicalSchedule_tendsto {s : ℕ → ℕ} (hs : Tendsto s atTop atTop) :
    Tendsto (physicalSchedule s) atTop atTop := by
  have hp : Tendsto (fun N : ℕ => N-1) atTop atTop := by
    refine tendsto_atTop.2 (fun j => ?_)
    filter_upwards [eventually_ge_atTop (j+1)] with N hN
    omega
  exact hs.comp hp

/-- The Cartesian residual of the printed physical operators has the same
uniform bound as the coefficient expression, for the very same gauge. -/
theorem physical_cartesian_limit (hκ : 0 < κ) (s : ℕ → ℕ) (q : ∀ n, Arr (n+1) → Phase)
    (h : RetargetFinalProofR48b.GaugeConclusion (L := L) hκ s q) :
    ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ∀ a b : ↥(RetargetAnglesR48b.labels (physicalSchedule s (n+1))),
        let ψ : HN L (n+1) := HighMomentsOps.wvec (n+1) u
        let B := Def044D1SpectralR51a.basis (L := L) hκ n
        let E := physical B (cartesian (q n) a.1 b.1)
        let z := DynSeedClassicalR47b.symbol hκ a.1 b.1 u
        ‖E ψ - z • ψ‖ + ‖E.adjoint ψ - conj z • ψ‖ ≤ ε := by
  intro R ε hε
  filter_upwards [h.2.2.1 R ε hε] with n hn
  intro u hu a b ψ B E z
  change ‖physical B (cartesian (q n) a.1 b.1) ψ - z • ψ‖ +
    ‖(physical B (cartesian (q n) a.1 b.1)).adjoint ψ - conj z • ψ‖ ≤ ε
  rw [physical_adjoint, physical_residual, physical_residual]
  exact hn u hu a b


/-- The physical directed residuals use the same selected gauge and the
same fixed positive action floor as the coefficient estimates. -/
theorem physical_phase_limit (hκ : 0 < κ) (s : ℕ → ℕ) (q : ∀ n, Arr (n+1) → Phase)
    (h : RetargetFinalProofR48b.GaugeConclusion (L := L) hκ s q) :
    ∀ R ρ ε : ℝ, 0 < ρ → 0 < ε → ∀ᶠ n in atTop,
      ∀ u ∈ RetargetRoughR48b.unitBall (L := L) R,
      ∀ a b : ↥(RetargetAnglesR48b.labels (physicalSchedule s (n+1))), a.1 ≠ b.1 →
        let ψ : HN L (n+1) := HighMomentsOps.wvec (n+1) u
        let B := Def044D1SpectralR51a.basis (L := L) hκ n
        let z := RetargetStageR48b.coordinate hκ u a.1
        let w := RetargetStageR48b.coordinate hκ u b.1
        let ζ := RetargetCellR48b.pairPhase z w
        let A := physical B (FiniteCellGauge.W (q n) a.1 b.1)
        ρ ≤ ‖z‖^2 → ρ ≤ ‖w‖^2 →
          ‖A ψ - ζ.1 • ψ‖ ≤ ε ∧ ‖A.adjoint ψ - conj ζ.1 • ψ‖ ≤ ε := by
  intro R ρ ε hρ hε
  filter_upwards [h.2.2.2 R ρ ε hρ hε] with n hn
  intro u hu a b hab ψ B z w ζ A ha hb
  have hlim := hn u hu a b hab ha hb
  constructor
  · change ‖physical B (FiniteCellGauge.W (q n) a.1 b.1) ψ - ζ.1 • ψ‖ ≤ ε
    rw [physical_residual]
    exact hlim.1
  · change ‖(physical B (FiniteCellGauge.W (q n) a.1 b.1)).adjoint ψ - conj ζ.1 • ψ‖ ≤ ε
    rw [physical_adjoint, physical_residual]
    exact hlim.2.1

/-- A uniformly norm-close preparation changes a scalar residual by at most
the norm error times the two bounded factors. -/
theorem preparation_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : H →L[ℂ] H) (z : ℂ) (x y : H) :
    ‖A y - z • y‖ ≤ ‖A x - z • x‖ + (‖A‖ + ‖z‖) * ‖y - x‖ := by
  have h : A y - z • y = A x - z • x + (A (y-x) - z • (y-x)) := by
    rw [map_sub, smul_sub]
    abel
  rw [h, add_mul]
  exact (norm_add_le _ _).trans
    (add_le_add le_rfl ((norm_sub_le _ _).trans (by
      rw [norm_smul]
      exact add_le_add (A.le_opNorm _) le_rfl)))


section Predecessor

open ActualModelTargetR53a Def033HierarchyR24m
open DynSeedInputR47b DynSeedClassicalR47b RetargetFinalProofR48b

/-- The exact inherited input has the same type as in the frozen conditional
seed. The static compact-profile extension reuses that seed's proof
components, while the joint-time specialization is bound verbatim here. -/
theorem retarget_with_seed_intermediate (hκ : 0 < κ) (F : HigherFlows L κ)
    (u : Smooth L) (hu : ‖Def033HierarchyR24m.physical u‖ = 1)
    (R : Finset ℕ) (lo hi : ℕ → ℝ) (a b : ℤ) (hab : a ≠ b)
    (flow_actions : ∀ t : TimeBox R lo hi,
      classicalOrbit hκ F u R t.val ∈ torus hκ (Def033HierarchyR24m.physical u))
    (mixed : MixedFinite hκ F u R)
    (PredecessorInput : DynftFullTorusInput hκ F u R) :
    DynSeedR47b.SeedStatement hκ F u R lo hi a b ∧
      (∃ (s : ℕ → ℕ) (q : ∀ n, Arr (n+1) → Phase), GaugeConclusion (L := L) hκ s q) := by
  exact ⟨DynSeedR47b.seed_intermediate hκ F u hu R lo hi a b hab flow_actions mixed PredecessorInput,
    gauge_conclusion_intermediate hκ⟩

end Predecessor

end QuantumNLS.RetargetPhysicalR48b

#print axioms QuantumNLS.RetargetPhysicalR48b.directed_formula
#print axioms QuantumNLS.RetargetPhysicalR48b.cartesian_formula
#print axioms QuantumNLS.RetargetPhysicalR48b.physical_phase_ratio
#print axioms QuantumNLS.RetargetPhysicalR48b.retarget_with_seed_intermediate
#print axioms QuantumNLS.RetargetPhysicalR48b.physical_cartesian_limit
#print axioms QuantumNLS.RetargetPhysicalR48b.physical_phase_limit

end

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (name, _) in env.constants.toList do
    if
        name.toString.startsWith "QuantumNLS.RetargetFinalProofR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetFinalProofR48b." ||
        name.toString.startsWith "QuantumNLS.RetargetPhysicalR48b." ||
        name.toString.startsWith "_private.QuantumNLS.RetargetPhysicalR48b." then
      pending := pending.push name
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      if (name.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {name}"
      if let some info := env.find? name then
        match info with
        | .axiomInfo _ =>
          unless name == ``propext || name == ``Classical.choice || name == ``Quot.sound do
            throwError "Nonstandard dependency: {name}"
        | _ => pure ()
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? (allowOpaque := true) then
          pending := pending ++ value.getUsedConstants
      else
        throwError "Missing dependency: {name}"
  Lean.logInfo m!"R48b aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only."
