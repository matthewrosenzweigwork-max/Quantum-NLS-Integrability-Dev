import QuantumNLS.RootOccupationDet
import QuantumNLS.RootMeasureExistence
import QuantumNLS.BetheOccupationGauge

/-! R-E6DFC650, ROOT_occupation_limit.tex:14, `thm:root-occupation-limit`: the probabilistic half
and the named theorem `root_occupation_limit`.

Statement correspondence.  `u : L2T L` with `‖u‖ = 1`, positive `κ`; the sampled law is the
Born law `|⟨ψ_{α,N}, u^{⊗N}⟩|²` on `𝓜_N` of the accepted physical basis, rephased by an
arbitrary diagonal gauge `g` (`BetheOccupationGauge.gaugedBasis`, which does not change the
law, `bornG_eq`).  The occupation proportions are `m_n/N` (`occVec`), the target is the indexed
mass vector `I_n^{(κ)}(u) = RootIndexedMasses.masses hκ u` (R-950BFB30 / R-2EAD2BB6); only
its definition clause, nonnegativity, summability and total mass are used, so the collapsed-interval clause
is not needed and nothing is carried as a hypothesis.  The measure `μ_u` is produced by the
read-only `RootMeasureExistence.exists_limiting_measure` (R-09E1EAE9) and identified with the
physical quantum measure by the read-only `Prop026Bound.physical_eq_limit`.  Printed proof: the
deterministic argument is `RootOccupationDet.occ_tendsto_seq` (PROP-002 `weak_joint_limit_DEF043`
plus the fibre/mass identification and Scheffe); the subsequence/Borel-Cantelli passage is replaced
by the equivalent uniform form `occ_uniform` (contradiction along an antitone neighbourhood basis).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.RootOccupationLimit
open QuantumNLS.RootOccupationDet QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis empiricalProb IsLimitingRapidityMeasure)
open PhysicalTensor (L2T)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The occupation proportions `m_n / N`. -/
def occVec (N : ℕ) (m : MArr N) (n : ℤ) : ℝ := (m.1 n : ℝ) / N

/-- The `ℓ¹(ℤ)` distance from the proportions to the indexed masses `I_n^{(κ)}(u)`. -/
def occDist (hκ : 0 < κ) (u : L2T L) (N : ℕ) (m : MArr N) : ℝ :=
  ∑' n, |occVec N m n - (RootIndexedMasses.masses hκ u).1 n|

/-! ### 1. Gauge independence of the sampled law -/

theorem bornG_eq (hκ : 0 < κ) (g : BetheOccupationGauge.Gauge) (u : L2T L) (hu : ‖u‖ = 1) (N : ℕ) :
    bornMeasure (BetheOccupationGauge.gaugedBasis (physBasis L hκ N) g) u hu =
      bornMeasure (physBasis L hκ N) u hu := by
  unfold bornMeasure
  congr 1
  apply PMF.ext
  intro m
  rw [BetheCoefficientTransform.bornPMF_apply, BetheCoefficientTransform.bornPMF_apply,
    BetheOccupationGauge.bornLaw_invariant]

/-! ### 2. Arrays as on-shell configurations -/

theorem exists_bridge (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : MArr N) :
    ∃ B : OnShellBethe L κ N, rootP B hN = empiricalProb L κ N m ∧
      ∀ n, occ B n = occVec N m n := by
  obtain ⟨B, hq, hc⟩ := onShell_arr (Fact.out : 0 < L) hκ hN m
  refine ⟨B, ?_, fun n => ?_⟩
  · have h := LabelWeakJointLimit.rootP_eq_empirical B hN m hq
    have h2 : empiricalProb L κ N m = LabelWeakJointLimit.empiricalP L κ hN m := by
      unfold BulkResponseActual.empiricalProb LabelWeakJointLimit.empiricalP
      exact dif_pos hN
    rw [h2]
    exact Subtype.ext h
  · unfold occ occVec
    rw [← hc n]
    ring

/-! ### 3. Weak neighbourhoods in the Levy-Prokhorov metric -/

theorem exists_lp_ball (μ : ProbabilityMeasure ℝ) (U : Set (ProbabilityMeasure ℝ))
    (hU : U ∈ 𝓝 μ) :
    ∃ ε > 0, ∀ ν : ProbabilityMeasure ℝ,
      levyProkhorovDist ν.toMeasure μ.toMeasure < ε → ν ∈ U := by
  have h := (LevyProkhorov.probabilityMeasureHomeomorph (Ω := ℝ)).symm.continuous.continuousAt
    (x := LevyProkhorov.ofMeasure μ)
  have h1 : (LevyProkhorov.probabilityMeasureHomeomorph (Ω := ℝ)).symm
      (LevyProkhorov.ofMeasure μ) = μ := rfl
  have h2 := h.preimage_mem_nhds (by rw [h1]; exact hU)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 h2
  refine ⟨ε, hε, fun ν hν => ?_⟩
  have : LevyProkhorov.ofMeasure ν ∈ Metric.ball (LevyProkhorov.ofMeasure μ) ε := by
    rw [Metric.mem_ball]
    exact hν
  exact hb this

/-! ### 4. Convergence in probability in `ℓ¹` -/

theorem occDist_prob (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => bornMeasure (physBasis L hκ N) u hu {m | ε < occDist hκ u N m})
      atTop (𝓝 0) := by
  obtain ⟨μ, hμ⟩ := RootMeasureExistence.exists_limiting_measure hκ u hu
  have hμe : (μ : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u :=
    (Prop026Bound.physical_eq_limit hκ u hu hμ).symm
  obtain ⟨U, hU, N₀, hN₀⟩ := occ_uniform hκ u hu hμe hε
  obtain ⟨r, hr, hrU⟩ := exists_lp_ball μ U hU
  have h := (BornConvergence.tendstoInProbabilityWeak_iff _ _ _).1 hμ (r / 2) (half_pos hr)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
  apply measure_mono
  intro m hm
  simp only [mem_setOf_eq] at hm ⊢
  by_contra hcon
  push Not at hcon
  have hN1 : 0 < N := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hN)
  obtain ⟨B, hB, hocc⟩ := exists_bridge (L := L) hκ hN1 m
  have hU' : rootP B hN1 ∈ U := by
    rw [hB]
    apply hrU
    exact lt_of_le_of_lt hcon (half_lt_self hr)
  have := hN₀ N hN1 ((le_max_left _ _).trans hN) B hU'
  have he : ∑' n, |occ B n - (RootIndexedMasses.masses hκ u).1 n| = occDist hκ u N m := by
    unfold occDist
    exact tsum_congr fun n => by rw [hocc n]
  rw [he] at this
  exact absurd hm (not_lt.2 this.le)

/-! ### 5. Boundedness and summability of the distance -/

theorem summable_occDist (hκ : 0 < κ) (u : L2T L) (N : ℕ) (m : MArr N) :
    Summable (fun n => |occVec N m n - (RootIndexedMasses.masses hκ u).1 n|) := by
  have h1 : Summable (occVec N m) := by
    apply summable_of_ne_finset_zero (s := m.1.support)
    intro n hn
    unfold occVec
    simp [Finsupp.notMem_support_iff.1 hn]
  exact (h1.sub (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.1).abs

theorem occDist_nonneg (hκ : 0 < κ) (u : L2T L) (N : ℕ) (m : MArr N) : 0 ≤ occDist hκ u N m :=
  tsum_nonneg fun _ => abs_nonneg _

theorem occDist_le_two (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {N : ℕ} (hN : 0 < N)
    (m : MArr N) : occDist hκ u N m ≤ 2 := by
  obtain ⟨B, -, hocc⟩ := exists_bridge (L := L) hκ hN m
  have ha : HasSum (occVec N m) 1 := by
    have := hasSum_occ hN B
    have he : occ B = occVec N m := funext hocc
    rwa [he] at this
  have hcl := RootIndexedMasses.root_indexed_masses_proved_clauses hκ u
  have hb : HasSum (fun k => (RootIndexedMasses.masses hκ u).1 k) 1 := by
    have := hcl.2.2.1.hasSum
    rwa [hcl.2.2.2.1, hu, one_pow] at this
  have hocc0 : ∀ n, 0 ≤ occVec N m n := fun n => by
    rw [← hocc n]; exact occ_nonneg _ _
  calc occDist hκ u N m
      ≤ ∑' n, (occVec N m n + (RootIndexedMasses.masses hκ u).1 n) := by
        apply Summable.tsum_le_tsum _ (summable_occDist hκ u N m) (ha.summable.add hb.summable)
        intro n
        have := hcl.2.1 n
        have := hocc0 n
        rw [abs_le]; constructor <;> linarith
    _ = 2 := by rw [ha.summable.tsum_add hb.summable, ha.tsum_eq, hb.tsum_eq]; norm_num

theorem integrable_of_bdd {N : ℕ} (P : Measure (MArr N)) [IsFiniteMeasure P] (f : MArr N → ℝ)
    (C : ℝ) (h : ∀ m, |f m| ≤ C) : Integrable f P :=
  Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable C
    (Eventually.of_forall fun m => by simpa [Real.norm_eq_abs] using h m)

/-! ### 6. Convergence in every finite `L^p` -/

theorem occDist_Lp (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun N : ℕ => ∫ m, occDist hκ u N m ^ p ∂(bornMeasure (physBasis L hκ N) u hu))
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set ε : ℝ := (η / 2) ^ p⁻¹ with hεdef
  have hε : 0 < ε := Real.rpow_pos_of_pos (by positivity) _
  have hεp : ε ^ p = η / 2 := Real.rpow_inv_rpow (by positivity) hp.ne'
  have hprob := occDist_prob hκ u hu hε
  have hreal : Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
      {m | ε < occDist hκ u N m}) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hprob
    exact this
  have h2p : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos two_pos p
  have hsmall : ∀ᶠ N : ℕ in atTop, (bornMeasure (physBasis L hκ N) u hu).real
      {m | ε < occDist hκ u N m} < η / 2 / 2 ^ p :=
    hreal.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN hN1
  have hN1' : 0 < N := hN1
  set P := bornMeasure (physBasis L hκ N) u hu with hP
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set S : Set (MArr N) := {m | ε < occDist hκ u N m} with hS
  have hSm : MeasurableSet S := MeasurableSet.of_discrete
  have hpt : ∀ m, occDist hκ u N m ^ p ≤ ε ^ p + 2 ^ p * S.indicator (1 : MArr N → ℝ) m := by
    intro m
    by_cases hm : m ∈ S
    · simp only [Set.indicator_of_mem hm, Pi.one_apply, mul_one]
      have := Real.rpow_le_rpow (occDist_nonneg hκ u N m) (occDist_le_two hκ u hu hN1' m) hp.le
      have h3 : 0 ≤ ε ^ p := by positivity
      linarith
    · simp only [Set.indicator_of_notMem hm, mul_zero, add_zero]
      exact Real.rpow_le_rpow (occDist_nonneg hκ u N m) (not_lt.1 hm) hp.le
  have hint1 : Integrable (fun m => occDist hκ u N m ^ p) P :=
    integrable_of_bdd P _ (2 ^ p) fun m => by
      rw [abs_of_nonneg (Real.rpow_nonneg (occDist_nonneg hκ u N m) _)]
      exact Real.rpow_le_rpow (occDist_nonneg hκ u N m) (occDist_le_two hκ u hu hN1' m) hp.le
  have hint2 : Integrable (fun m => ε ^ p + 2 ^ p * S.indicator (1 : MArr N → ℝ) m) P :=
    integrable_of_bdd P _ (ε ^ p + 2 ^ p) fun m => by
      have h0 : 0 ≤ S.indicator (1 : MArr N → ℝ) m := Set.indicator_nonneg (fun _ _ => zero_le_one) m
      have h1 : S.indicator (1 : MArr N → ℝ) m ≤ 1 := by
        by_cases hm : m ∈ S <;> simp [hm]
      have : 0 ≤ ε ^ p := by positivity
      rw [abs_of_nonneg (by positivity)]
      nlinarith
  have hle := integral_mono hint1 hint2 hpt
  have hval : ∫ m, (ε ^ p + 2 ^ p * S.indicator (1 : MArr N → ℝ) m) ∂P = ε ^ p + 2 ^ p * P.real S := by
    rw [integral_add (integrable_const _), integral_const, integral_const_mul,
      integral_indicator_one hSm]
    · simp
    · exact (integrable_indicator_iff hSm).2 (integrable_const _ |>.integrableOn) |>.const_mul _
  have hnn : 0 ≤ ∫ m, occDist hκ u N m ^ p ∂P :=
    integral_nonneg fun m => Real.rpow_nonneg (occDist_nonneg hκ u N m) _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  rw [hval] at hle
  have : 2 ^ p * P.real S < η / 2 := by
    have := mul_lt_mul_of_pos_left hN h2p
    rwa [mul_div_cancel₀ _ h2p.ne'] at this
  linarith

/-! ### 7. Expected occupation vectors in `ℓ¹` -/

theorem expected_l1 (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {N : ℕ} (hN : 0 < N) :
    Summable (fun n : ℤ => |∫ m, occVec N m n ∂(bornMeasure (physBasis L hκ N) u hu) -
        (RootIndexedMasses.masses hκ u).1 n|) ∧
    ∑' n : ℤ, |∫ m, occVec N m n ∂(bornMeasure (physBasis L hκ N) u hu) -
        (RootIndexedMasses.masses hκ u).1 n| ≤
      ∫ m, occDist hκ u N m ∂(bornMeasure (physBasis L hκ N) u hu) := by
  set P := bornMeasure (physBasis L hκ N) u hu with hP
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  set I : ℤ → ℝ := fun n => (RootIndexedMasses.masses hκ u).1 n with hI
  have hf : ∀ n m, |occVec N m n - I n| ≤ occDist hκ u N m := fun n m =>
    (summable_occDist hκ u N m).le_tsum n (fun _ _ => abs_nonneg _)
  have hfint : ∀ n, Integrable (fun m => |occVec N m n - I n|) P := fun n =>
    integrable_of_bdd P _ 2 fun m => by
      rw [abs_of_nonneg (abs_nonneg _)]
      exact (hf n m).trans (occDist_le_two hκ u hu hN m)
  have hdint : Integrable (fun m => occDist hκ u N m) P :=
    integrable_of_bdd P _ 2 fun m => by
      rw [abs_of_nonneg (occDist_nonneg hκ u N m)]
      exact occDist_le_two hκ u hu hN m
  have hgint : ∀ n, Integrable (fun m => occVec N m n - I n) P := fun n =>
    integrable_of_bdd P _ 2 fun m => (hf n m).trans (occDist_le_two hκ u hu hN m)
  have hEint : ∀ n, Integrable (fun m => occVec N m n) P := fun n => by
    exact ((hgint n).add (integrable_const (I n))).congr
      (Eventually.of_forall fun m => by simp)
  have hdiff : ∀ n, ∫ m, occVec N m n ∂P - I n = ∫ m, (occVec N m n - I n) ∂P := fun n => by
    rw [integral_sub (hEint n) (integrable_const _), integral_const]; simp
  have hbound : ∀ s : Finset ℤ, ∑ n ∈ s, |∫ m, occVec N m n ∂P - I n| ≤ ∫ m, occDist hκ u N m ∂P := by
    intro s
    calc ∑ n ∈ s, |∫ m, occVec N m n ∂P - I n|
        = ∑ n ∈ s, ‖∫ m, (occVec N m n - I n) ∂P‖ := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hdiff n, Real.norm_eq_abs]
      _ ≤ ∑ n ∈ s, ∫ m, ‖occVec N m n - I n‖ ∂P :=
          Finset.sum_le_sum fun n _ => norm_integral_le_integral_norm _
      _ = ∫ m, ∑ n ∈ s, |occVec N m n - I n| ∂P := by
          simp only [Real.norm_eq_abs]
          rw [← integral_finsetSum _ (fun n _ => hfint n)]
      _ ≤ ∫ m, occDist hκ u N m ∂P := by
          apply integral_mono (integrable_finsetSum _ fun n _ => hfint n) hdint
          intro m
          exact Summable.sum_le_tsum s (fun _ _ => abs_nonneg _) (summable_occDist hκ u N m)
  exact ⟨summable_of_sum_le (fun _ => abs_nonneg _) hbound,
    Real.tsum_le_of_sum_le (fun _ => abs_nonneg _) hbound⟩

/-! ### 8. The named theorem -/

/-- **R-E6DFC650, `thm:root-occupation-limit`.**  Let `u ∈ L²(𝕋_L)` have norm one and `κ > 0`.
Sample `m ∈ 𝓜_N` with the product-state law `|⟨ψ_{α,N}, u^{⊗N}⟩|²` of the normalized Bethe vectors
in any diagonal phase convention `g`.  Then `(m_n/N)_n → (I_n^{(κ)}(u))_n` in probability in `ℓ¹(ℤ)`,
the `ℓ¹` distance tends to zero in every finite `L^p`, and the expected occupation vectors
converge in `ℓ¹`.  No exterior cutoff, moment or energy hypothesis occurs. -/
theorem root_occupation_limit (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (g : BetheOccupationGauge.Gauge) :
    (∀ ε : ℝ, 0 < ε → Tendsto (fun N : ℕ =>
      bornMeasure (BetheOccupationGauge.gaugedBasis (physBasis L hκ N) g) u hu
        {m | ε < ∑' n, |(m.1 n : ℝ) / N - (RootIndexedMasses.masses hκ u).1 n|})
      atTop (𝓝 0)) ∧
    (∀ p : ℝ, 0 < p → Tendsto (fun N : ℕ =>
      ∫ m, (∑' n, |(m.1 n : ℝ) / N - (RootIndexedMasses.masses hκ u).1 n|) ^ p
        ∂(bornMeasure (BetheOccupationGauge.gaugedBasis (physBasis L hκ N) g) u hu))
      atTop (𝓝 0)) ∧
    (∀ N : ℕ, 0 < N → Summable (fun n : ℤ =>
      |∫ m, (m.1 n : ℝ) / N
          ∂(bornMeasure (BetheOccupationGauge.gaugedBasis (physBasis L hκ N) g) u hu) -
        (RootIndexedMasses.masses hκ u).1 n|)) ∧
    Tendsto (fun N : ℕ => ∑' n : ℤ,
      |∫ m, (m.1 n : ℝ) / N
          ∂(bornMeasure (BetheOccupationGauge.gaugedBasis (physBasis L hκ N) g) u hu) -
        (RootIndexedMasses.masses hκ u).1 n|) atTop (𝓝 0) := by
  simp only [bornG_eq hκ g u hu]
  refine ⟨fun ε hε => occDist_prob hκ u hu hε, fun p hp => occDist_Lp hκ u hu hp,
    fun N hN => (expected_l1 hκ u hu hN).1, ?_⟩
  have h1 := occDist_Lp hκ u hu one_pos
  simp only [Real.rpow_one] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
    (Eventually.of_forall fun N => tsum_nonneg fun _ => abs_nonneg _) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (expected_l1 hκ u hu hN).2

end QuantumNLS.RootOccupationLimit
#print axioms QuantumNLS.RootOccupationLimit.root_occupation_limit
#print axioms QuantumNLS.RootOccupationLimit.bornG_eq
#print axioms QuantumNLS.RootOccupationLimit.exists_bridge
#print axioms QuantumNLS.RootOccupationLimit.occDist_prob
#print axioms QuantumNLS.RootOccupationLimit.occDist_le_two
#print axioms QuantumNLS.RootOccupationLimit.occDist_Lp
#print axioms QuantumNLS.RootOccupationLimit.expected_l1
