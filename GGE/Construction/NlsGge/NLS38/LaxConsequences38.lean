import NlsGge.NLS38.PhysicalFlow38
import NlsGge.NLS38.ClassicalSolution38
import NlsGge.NLS38.LaxHalfTrace38
import NlsGge.Birkhoff.S04Moments38
import NlsGge.Hierarchy.ALCompactConsistency38
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.NLS38.MeasureDetermination38
import NlsGge.Birkhoff.F01Determinant38

/-! # GWP piece B4: Lax consequences for the actual flow (38)

Plan: `campaign/GWP_PLAN.md` §6.3 and §7 (B4).

* `halfTrace_eq_halfTraceOf38` : for `H¹` data the E02 half trace is `halfTraceOf` of the continuous
  representative `serU (physicalFourier u)`.
* `actualPhysicalUnitHalfTrace_nlsFlow` (`H³` data), then the consequences that depend on `u` only through the
  half trace: gap height, `energyW38`, quasimomentum, gap actions.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.SpectralFoundations Set Filter Topology
open scoped ComplexConjugate NNReal ENNReal

/-! ## Half trace of `H¹` data through the continuous representative -/

/-- For `H¹` data the E02 unit half trace is the half trace of the Dyson monodromy of the continuous
representative `serU (physicalFourier u)` of the potential. -/
theorem halfTrace_eq_halfTraceOf38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (z : ℂ) :
    actualPhysicalUnitHalfTrace32 u z = halfTraceOf (fun θ => serU (physicalFourier u) θ) z := by
  have hae := NlsGge.AblowitzLadik.h1_cover_ae38 u hu
  have hU : (fun θ : ℝ => serU (physicalFourier u) θ) =
      fun s : ℝ => NlsGge.Analysis.physicalH1Continuous u hu (s : PhysicalCircle) :=
    funext fun θ => serU_eq_physicalH1Continuous hu θ
  rw [NlsGge.AblowitzLadik.actualHalfTrace_eq_dyson38 u (U := fun θ => serU (physicalFourier u) θ)
    (by rw [hU]; exact hae) z]
  rfl

theorem sobolev_three_to_one38 {u : PhysicalL2} (hu : SobolevSquareSummable 3 (physicalFourier u)) :
    physicalFourier u ∈ seqSobolev38 ((3 : ℕ) : ℝ) ∧
      SobolevSquareSummable 1 (physicalFourier u) := by
  have h3 : physicalFourier u ∈ seqSobolev38 ((3 : ℕ) : ℝ) :=
    (mem_seqSobolev38_iff _ _).2 (by rw [Nat.cast_ofNat]; exact hu)
  refine ⟨h3, ?_⟩
  have := seqSobolev38_mono (by norm_num : (1 : ℝ) ≤ ((3 : ℕ) : ℝ)) h3
  exact (mem_seqSobolev38_iff _ _).1 this

/-- B4: the actual unit half trace is conserved by the NLS flow for `H³` data (Lax). -/
theorem actualPhysicalUnitHalfTrace_nlsFlow (u : PhysicalL2)
    (hu : SobolevSquareSummable 3 (physicalFourier u)) (t : ℝ) (z : ℂ) :
    actualPhysicalUnitHalfTrace32 (nlsFlowL2 t u) z = actualPhysicalUnitHalfTrace32 u z := by
  obtain ⟨h3, hu1⟩ := sobolev_three_to_one38 hu
  have hw1 : SobolevSquareSummable 1 (physicalFourier (nlsFlowL2 t u)) := by
    have := nlsFlowL2_mem 1 le_rfl (u := u) (by simpa using hu1) t
    simpa using this
  rw [halfTrace_eq_halfTraceOf38 _ hw1, halfTrace_eq_halfTraceOf38 _ hu1,
    physicalFourier_nlsFlowL2 hu1]
  obtain ⟨Ux, Uxx, Ut, hU, hUx, hUxx, hUt, h1, h2, h3', hpde, hper⟩ :=
    classical_solution (physicalFourier u) h3
  have key := halfTrace_const_of_classical (fun s θ => serU (nlsFlowSeq s (physicalFourier u)) θ)
    Ux Uxx Ut hU hUx hUxx hUt h1 h2 h3' hper hpde z t
  rw [key, nlsFlowSeq_zero]


/-! ## Quantities that depend on `u` only through the half trace -/

/-- The gap height depends on `u` only through the half trace. -/
theorem actualGapHeight_eq_of_halfTrace_eq (u v : PhysicalL2)
    (h : ∀ z, actualPhysicalUnitHalfTrace32 u z = actualPhysicalUnitHalfTrace32 v z) (l : ℝ) :
    actualGapHeightE02_38 u l = actualGapHeightE02_38 v l := by
  unfold actualGapHeightE02_38
  rw [h]

/-- B4: the quasimomentum on the upper half plane depends on `u` only through the half trace. -/
theorem actualQuasimomentum_eq_of_halfTrace_eq (u v : PhysicalL2)
    (h : ∀ z, actualPhysicalUnitHalfTrace32 u z = actualPhysicalUnitHalfTrace32 v z) :
    Set.EqOn (actualQuasimomentumE02_38 u) (actualQuasimomentumE02_38 v) {z | 0 < z.im} := by
  obtain ⟨ha, hc, hi, hn⟩ := isActualQuasimomentumBranch_actualQuasimomentumE02_38 v
  exact actualQuasimomentumE02_38_eqOn_of_isBranch u _
    ⟨ha, fun z hz => (hc z hz).trans (h z).symm, hi, hn⟩

theorem extendFrom_congr38 {A : Set ℂ} {f g : ℂ → ℂ} (h : Set.EqOn f g A) (x : ℂ) :
    extendFrom A f x = extendFrom A g x := by
  unfold extendFrom limUnder
  rw [Filter.map_congr (eventuallyEq_nhdsWithin_of_eqOn h)]

theorem actualGapActionAllE02_38_eq_of_halfTrace_eq (u v : PhysicalL2)
    (h : ∀ z, actualPhysicalUnitHalfTrace32 u z = actualPhysicalUnitHalfTrace32 v z) (n : ℤ) :
    actualGapActionAllE02_38 u n = actualGapActionAllE02_38 v n := by
  have hb : ∀ x : ℝ, actualQuasimomentumBoundaryE02_38 u x = actualQuasimomentumBoundaryE02_38 v x :=
    fun x => extendFrom_congr38 (actualQuasimomentum_eq_of_halfTrace_eq u v h) (x : ℂ)
  have hp : actualQuasimomentumRealPartE02_38 u = actualQuasimomentumRealPartE02_38 v :=
    funext fun x => by unfold actualQuasimomentumRealPartE02_38; rw [hb]
  have hg : actualGapHeightE02_38 u = actualGapHeightE02_38 v :=
    funext (actualGapHeight_eq_of_halfTrace_eq u v h)
  have hL : actualGapLevelSetE02_38 u n = actualGapLevelSetE02_38 v n := by
    unfold actualGapLevelSetE02_38; rw [hp]
  unfold actualGapActionAllE02_38 actualGapLowerAllE02_38 actualGapUpperAllE02_38
  rw [hL, hg]

theorem energyW38_eq_of_halfTrace_eq (c : ℕ → ℝ) (u v : PhysicalL2)
    (h : ∀ z, actualPhysicalUnitHalfTrace32 u z = actualPhysicalUnitHalfTrace32 v z) :
    energyW38 c u = energyW38 c v := by
  have hg : actualGapHeightE02_38 u = actualGapHeightE02_38 v :=
    funext (actualGapHeight_eq_of_halfTrace_eq u v h)
  unfold energyW38
  rw [hg]

/-- B4: the gap height is conserved by the flow for `H³` data. -/
theorem actualGapHeight_nlsFlow (u : PhysicalL2) (hu : SobolevSquareSummable 3 (physicalFourier u))
    (t : ℝ) (l : ℝ) : actualGapHeightE02_38 (nlsFlowL2 t u) l = actualGapHeightE02_38 u l :=
  actualGapHeight_eq_of_halfTrace_eq _ _ (actualPhysicalUnitHalfTrace_nlsFlow u hu t) l

/-- B4: `energyW38` is conserved by the flow for `H³` data. -/
theorem energyW38_nlsFlow (c : ℕ → ℝ) (u : PhysicalL2)
    (hu : SobolevSquareSummable 3 (physicalFourier u)) (t : ℝ) :
    energyW38 c (nlsFlowL2 t u) = energyW38 c u :=
  energyW38_eq_of_halfTrace_eq c _ _ (actualPhysicalUnitHalfTrace_nlsFlow u hu t)

/-- B4: the gap actions are conserved by the flow for `H³` data. -/
theorem actualGapActionAllE02_38_nlsFlow (u : PhysicalL2)
    (hu : SobolevSquareSummable 3 (physicalFourier u)) (t : ℝ) (n : ℤ) :
    actualGapActionAllE02_38 (nlsFlowL2 t u) n = actualGapActionAllE02_38 u n :=
  actualGapActionAllE02_38_eq_of_halfTrace_eq _ _ (actualPhysicalUnitHalfTrace_nlsFlow u hu t) n


/-! ## `H¹` data by density -/

/-- The half trace is continuous on `L²` (Lipschitz on balls, E02). -/
theorem continuous_halfTrace_L2_38 (z : ℂ) :
    Continuous fun u : PhysicalL2 => actualPhysicalUnitHalfTrace32 u z := by
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  obtain ⟨C, hC0, hL⟩ := actualPhysicalUnitHalfTrace_lipschitz_E02_38 (‖u₀‖ + 1) ‖z‖
    (by positivity) (norm_nonneg _)
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min 1 (ε / (C + 1)), by positivity, fun u hu => ?_⟩
  rw [dist_eq_norm] at hu ⊢
  have h1 : ‖u - u₀‖ < 1 := lt_of_lt_of_le hu (min_le_left _ _)
  have h2 : ‖u - u₀‖ < ε / (C + 1) := lt_of_lt_of_le hu (min_le_right _ _)
  have hn : ‖u‖ ≤ ‖u₀‖ + 1 := by
    have := norm_add_le u₀ (u - u₀)
    simp only [add_sub_cancel] at this
    linarith
  have h := hL u u₀ hn (by linarith) z le_rfl
  calc ‖actualPhysicalUnitHalfTrace32 u z - actualPhysicalUnitHalfTrace32 u₀ z‖
      ≤ C * ‖u - u₀‖ := h
    _ ≤ (C + 1) * ‖u - u₀‖ := by nlinarith [norm_nonneg (u - u₀)]
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left h2 (by linarith)
    _ = ε := by field_simp

theorem physH38_physIncl38 (x : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    physH38 1 (physIncl38 1 x) = x := by
  have hm : fourierSeq38 (physIncl38 1 x) ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
    rw [fourierSeq38_physIncl38]; exact carrierCoe38_mem _ x
  rw [physH38_of_mem 1 _ hm]
  exact carrierExt38 (by simp [fourierSeq38_physIncl38])

/-- `physIncl38` of a finitely supported carrier element is an `H³` field. -/
theorem physIncl38_proj_h3 (N : ℕ) (X : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    SobolevSquareSummable 3 (physicalFourier (physIncl38 1 (projC38 _ N X))) := by
  rw [← fourierSeq38_mem_iff, mem_seqSobolev38_iff, fourierSeq38_physIncl38]
  unfold SobolevSquareSummable
  refine summable_of_ne_finset_zero (s := symmetricModes N) fun n hn => ?_
  simp [carrierCoe38_projC38, hn]

/-- B4 (optional): the half trace is conserved for `H¹` data, by density from the `H³` case. -/
theorem actualPhysicalUnitHalfTrace_nlsFlow_h1 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (t : ℝ) (z : ℂ) :
    actualPhysicalUnitHalfTrace32 (nlsFlowL2 t u) z = actualPhysicalUnitHalfTrace32 u z := by
  have hu1 : fourierSeq38 u ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    (fourierSeq38_mem_iff _ u).2 (by simpa using hu)
  have hw1 : fourierSeq38 (nlsFlowL2 t u) ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    (fourierSeq38_mem_iff _ _).2 (nlsFlowL2_mem 1 le_rfl (u := u) (by simpa using hu) t)
  set X : SobolevCarrier38 ((1 : ℕ) : ℝ) := physH38 1 u with hX
  set F := nlsFlowC 1 le_rfl t with hF
  set g : SobolevCarrier38 ((1 : ℕ) : ℝ) → ℂ :=
    fun x => actualPhysicalUnitHalfTrace32 (physIncl38 1 x) z with hg
  have hgc : Continuous g := (continuous_halfTrace_L2_38 z).comp (continuous_physIncl38 1)
  have hFc : Continuous F := (continuous_nlsFlowC_uncurry 1 le_rfl).comp
    (Continuous.prodMk_right t)
  have hXN : Tendsto (fun N : ℕ => projC38 _ N X) atTop (𝓝 X) := tendsto_projC38 _ X
  have h1 : Tendsto (fun N : ℕ => g (projC38 _ N X)) atTop (𝓝 (g X)) :=
    (hgc.tendsto X).comp hXN
  have h2 : Tendsto (fun N : ℕ => g (F (projC38 _ N X))) atTop (𝓝 (g (F X))) :=
    (hgc.tendsto (F X)).comp ((hFc.tendsto X).comp hXN)
  have h3 : ∀ N : ℕ, g (F (projC38 _ N X)) = g (projC38 _ N X) := by
    intro N
    set uN := physIncl38 1 (projC38 _ N X) with huN
    have hN1 : fourierSeq38 uN ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
      rw [huN, fourierSeq38_physIncl38]; exact carrierCoe38_mem _ _
    have hflow : physIncl38 1 (F (projC38 _ N X)) = nlsFlowL2 t uN := by
      have := physH38_nlsFlowL2 1 le_rfl hN1 t
      rw [huN, physH38_physIncl38] at this
      have hw : fourierSeq38 (nlsFlowL2 t uN) ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
        (fourierSeq38_mem_iff _ _).2 (nlsFlowL2_mem 1 le_rfl (u := uN)
          (by simpa using (fourierSeq38_mem_iff _ _).1 hN1) t)
      rw [hF, ← this, physIncl38_physH38 1 _ hw]
    simp only [hg]
    rw [hflow]
    exact actualPhysicalUnitHalfTrace_nlsFlow uN (physIncl38_proj_h3 N X) t z
  have h4 : g (F X) = g X := tendsto_nhds_unique h2 (by simpa only [h3] using h1)
  have e1 : physIncl38 1 X = u := physIncl38_physH38 1 u hu1
  have e2 : physIncl38 1 (F X) = nlsFlowL2 t u := by
    have := physH38_nlsFlowL2 1 le_rfl hu1 t
    rw [← hX, ← hF] at this
    rw [← this, physIncl38_physH38 1 _ hw1]
  simp only [hg] at h4
  rwa [e1, e2] at h4


/-! ## Regression probe: the plane wave -/

theorem planeWaveL2_H3_38 (k : ℤ) (a : ℂ) :
    SobolevSquareSummable 3 (physicalFourier (planeWaveL2_38 k a)) := by
  rw [← mem_seqSobolev38_iff, physicalFourier_planeWaveL2_38]
  refine finiteSupport_mem_seqSobolev38 _ _ ((Set.finite_singleton k).subset fun n hn => ?_)
  by_contra h
  have h' : n ≠ k := fun e => h (by simp [e])
  exact hn (by simp [h'])

/-- The continuous representative of the flowed plane wave is the explicit plane wave of B3
(`planeWave a k t`, the solution of `i u_t = -u_xx + 2|u|² u` with `ω = (2πk)² + 2|a|²`). -/
theorem serU_flow_eq_planeWave38 (k : ℤ) (a : ℂ) (t θ : ℝ) :
    serU (nlsFlowSeq t (Pi.single k a)) θ = planeWave a k t θ := by
  rw [serU_flow_planeWave]
  unfold planeWave planeWavePhase eT pwFreq38
  rw [mul_comm _ a, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Probe: for the plane wave the E02 half trace of the flow is the Dyson half trace of the explicit
solution `planeWave a k t`, and it is independent of `t` (B4 conservation, `H³` and `H¹` routes). -/
theorem halfTrace_planeWave_probe38 (k : ℤ) (a : ℂ) (t : ℝ) (z : ℂ) :
    actualPhysicalUnitHalfTrace32 (nlsFlowL2 t (planeWaveL2_38 k a)) z =
        halfTraceOf (planeWave a k t) z ∧
    actualPhysicalUnitHalfTrace32 (nlsFlowL2 t (planeWaveL2_38 k a)) z =
        actualPhysicalUnitHalfTrace32 (planeWaveL2_38 k a) z ∧
    actualPhysicalUnitHalfTrace32 (nlsFlowL2 t (planeWaveL2_38 k a)) z =
        actualPhysicalUnitHalfTrace32 (planeWaveL2_38 k a) z := by
  refine ⟨?_, actualPhysicalUnitHalfTrace_nlsFlow _ (planeWaveL2_H3_38 k a) t z,
    actualPhysicalUnitHalfTrace_nlsFlow_h1 _ (planeWaveL2_H1_38 k a) t z⟩
  have hw1 : SobolevSquareSummable 1 (physicalFourier (nlsFlowL2 t (planeWaveL2_38 k a))) := by
    have := nlsFlowL2_mem 1 le_rfl (u := planeWaveL2_38 k a) (by simpa using planeWaveL2_H1_38 k a) t
    simpa using this
  rw [halfTrace_eq_halfTraceOf38 _ hw1, physicalFourier_nlsFlowL2 (planeWaveL2_H1_38 k a),
    physicalFourier_planeWaveL2_38]
  congr 1
  funext θ
  exact serU_flow_eq_planeWave38 k a t θ

/-- Probe: the gap height, the gap actions and `energyW38` of a plane wave are unchanged by the flow. -/
theorem planeWave_spectral_conserved38 (c : ℕ → ℝ) (k : ℤ) (a : ℂ) (t l : ℝ) (n : ℤ) :
    actualGapHeightE02_38 (nlsFlowL2 t (planeWaveL2_38 k a)) l =
        actualGapHeightE02_38 (planeWaveL2_38 k a) l ∧
    actualGapActionAllE02_38 (nlsFlowL2 t (planeWaveL2_38 k a)) n =
        actualGapActionAllE02_38 (planeWaveL2_38 k a) n ∧
    energyW38 c (nlsFlowL2 t (planeWaveL2_38 k a)) = energyW38 c (planeWaveL2_38 k a) :=
  ⟨actualGapHeight_nlsFlow _ (planeWaveL2_H3_38 k a) t l,
    actualGapActionAllE02_38_nlsFlow _ (planeWaveL2_H3_38 k a) t n,
    energyW38_nlsFlow c _ (planeWaveL2_H3_38 k a) t⟩

end NlsGge.NLS38
