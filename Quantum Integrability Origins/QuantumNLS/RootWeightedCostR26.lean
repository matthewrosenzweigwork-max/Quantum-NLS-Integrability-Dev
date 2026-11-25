import QuantumNLS.RootWeightedCellsR26
import QuantumNLS.RootDisplacementEstimate
import QuantumNLS.RootMeasureExistence
import QuantumNLS.LabelWeakJointLimit

/-! Passage of the finite displacement estimate to the physical unit law.
Only the analytic boundary branch of joint convergence is used; the
DEF-043 regular-cut structure is never instantiated. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal BigOperators
namespace QuantumNLS.RootWeightedCostR26
open PhysicalTensor (L2T)
open BetheLabels LabelJointLimit LabelJointWeak LabelWeakJointLimit
open RootWeightedCellsR26
variable {L κ : ℝ} [Fact (0 < L)]

def config {N : ℕ} (hκ : 0 < κ) (hN : 0 < N) (m : MArr N) : OnShellBethe L κ N where
  q := arrRoots L (κ/N) m
  n := correctedInt (labelsEquivArr.symm m)
  q_strict := roots_strictMono_labels Fact.out (div_pos hκ (by exact_mod_cast hN)) _
  n_mono := correctedInt_monotone _
  bethe := by
    obtain ⟨M,rfl⟩ : ∃ M, N = M+1 := ⟨N-1, by omega⟩
    intro j
    have h := RootDisplacementEstimate.bethe_printed
      (div_pos hκ (by exact_mod_cast hN)) (labelsEquivArr.symm m)
      (arrRoots L (κ/(M+1 : ℕ)) m) L
      (roots_strictMono_labels Fact.out (div_pos hκ (by exact_mod_cast hN)) _)
      ((rapidityEq_iff_roots Fact.out (div_pos hκ (by exact_mod_cast hN)) _ _).mpr rfl) j
    linarith

theorem config_rootP {N : ℕ} (hκ : 0 < κ) (hN : 0 < N) (m : MArr N) :
    rootP (config (L := L) hκ hN m) hN = BulkResponseActual.empiricalProb L κ N m := by
  have he := rootP_eq_empirical (config (L := L) hκ hN m) hN m rfl
  have he2 : BulkResponseActual.empiricalProb L κ N m = empiricalP L κ hN m := by
    unfold BulkResponseActual.empiricalProb empiricalP
    exact dite_eq_left hN
  rw [he2]
  exact Subtype.ext he

def cost (L : ℝ) (p : ℝ × ℤ) : ℝ := (p.1-momentum L p.2)^2

theorem continuous_cost (L : ℝ) : Continuous (cost L) := by
  exact (continuous_fst.sub ((continuous_of_discreteTopology (f := momentum L)).comp
    continuous_snd)).pow 2

theorem finite_cost {N : ℕ} (hκ : 0 < κ) (hN : 0 < N) (m : MArr N) :
    (∫ p, cost L p ∂(jointP (config (L := L) hκ hN m) hN)) ≤ κ/L := by
  have hf := RootDisplacementEstimate.root_displacement_estimate
    (labelsEquivArr.symm m) (arrRoots L (κ/N) m)
    ⟨hN,Fact.out,hκ,
      (rapidityEq_iff_roots Fact.out (div_pos hκ (by exact_mod_cast hN)) _ _).mpr rfl⟩
  change (∫ p, cost L p ∂emp (pts (config (L := L) hκ hN m))) ≤ _
  rw [integral_emp]
  change (N : ℝ)⁻¹ * ∑ j, (arrRoots L (κ/N) m j-
    RootDisplacementEstimate.pn L (correctedInt (labelsEquivArr.symm m) j))^2 ≤ _
  have hg : κ/L*(1-1/(N : ℝ)) ≤ κ/L := by
    have hp : 0 ≤ κ/L := div_nonneg hκ.le (Fact.out : 0 < L).le
    have hN' : 0 ≤ (1 : ℝ)/(N : ℝ) := by positivity
    nlinarith
  calc
    _ ≤ (κ/L)*(1-1/(N : ℝ)) := by simpa only [one_div] using hf
    _ ≤ _ := hg

/-- Deterministic actual configurations can be selected from the converging
Born laws. The particle numbers tend to infinity and are positive. -/
theorem exists_sequence (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    {μ : ProbabilityMeasure ℝ} (hμ : BulkResponseActual.IsLimitingRapidityMeasure L κ hκ u hu μ) :
    ∃ (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (m : ∀ k, MArr (N k)),
      Tendsto N atTop atTop ∧
      Tendsto (fun k => rootP (config (L := L) hκ (hN k) (m k)) (hN k)) atTop (𝓝 μ) := by
  have hp := (BornConvergence.tendstoInProbabilityWeak_iff _ _ _).mp hμ
  have pick : ∀ k : ℕ, ∃ N : ℕ, k+1 ≤ N ∧ ∃ m : MArr N,
      levyProkhorovDist (BulkResponseActual.empiricalProb L κ N m).toMeasure μ.toMeasure ≤
        1/((k : ℝ)+1) := by
    intro k
    have hε : 0 < 1/((k : ℝ)+1) := by positivity
    obtain ⟨N,hN,hbad⟩ := ((eventually_ge_atTop (k+1)).and
      ((hp _ hε).eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num)))).exists
    refine ⟨N,hN,?_⟩
    by_contra he
    push Not at he
    have hs : {m : MArr N | 1/((k : ℝ)+1) <
        levyProkhorovDist (BulkResponseActual.empiricalProb L κ N m).toMeasure μ.toMeasure} = univ :=
      Set.eq_univ_of_forall he
    rw [hs,measure_univ] at hbad
    exact lt_irrefl _ hbad
  choose N hN m hm using pick
  have hNpos : ∀ k, 0 < N k := fun k => lt_of_lt_of_le (Nat.succ_pos _) (hN k)
  refine ⟨N,hNpos,m,tendsto_atTop_mono (fun k => (Nat.le_succ k).trans (hN k)) tendsto_id,?_⟩
  simp only [config_rootP]
  have hdist : Tendsto (fun k => levyProkhorovDist
      (BulkResponseActual.empiricalProb L κ (N k) (m k)).toMeasure μ.toMeasure) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => by unfold levyProkhorovDist; exact ENNReal.toReal_nonneg) hm
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun k => LevyProkhorov.ofMeasure
      (BulkResponseActual.empiricalProb L κ (N k) (m k))) atTop (𝓝 (LevyProkhorov.ofMeasure μ)) :=
    tendsto_iff_dist_tendsto_zero.mpr hdist
  exact (LevyProkhorov.probabilityMeasureHomeomorph (Ω := ℝ)).symm.continuous.continuousAt.tendsto.comp ht

/-- Weak lower semicontinuity of the nonnegative continuous joint cost,
with no moment-finiteness premise on the limiting law. -/
theorem weak_cost_bound {γ : ProbabilityMeasure (ℝ × ℤ)}
    {γs : ℕ → ProbabilityMeasure (ℝ × ℤ)} (hc : Tendsto γs atTop (𝓝 γ))
    {C : ℝ} (hb : ∀ n, (∫⁻ p, ENNReal.ofReal (cost L p) ∂(γs n)) ≤ ENNReal.ofReal C) :
    (∫⁻ p, ENNReal.ofReal (cost L p) ∂γ) ≤ ENNReal.ofReal C := by
  have h := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (continuous_cost L) (fun _ => sq_nonneg _) (fun G hG =>
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hc hG)
  exact h.trans (liminf_le_of_frequently_le (Frequently.of_forall hb))

theorem unit_cost (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) :
    (∫⁻ x, ENNReal.ofReal ((x-cellMomentum hκ u x)^2)
      ∂PhysicalQuantumMeasure.measure hκ u) ≤ ENNReal.ofReal (κ/L) := by
  obtain ⟨μ,hμ⟩ := RootMeasureExistence.exists_limiting_measure hκ u hu
  have hμe : (μ : Measure ℝ) = PhysicalQuantumMeasure.measure hκ u :=
    (Prop026Bound.physical_eq_limit hκ u hu hμ).symm
  obtain ⟨N,hN,m,hNt,hc⟩ := exists_sequence hκ u hu hμ
  let B := fun k => config (L := L) hκ (hN k) (m k)
  have : NullSingletonClass (μ : Measure ℝ) := by
    rw [hμe]
    exact PhysicalUnconditionalTrace.atomless hκ u
  have hn : ∀ᵐ x ∂(μ : Measure ℝ), (cellIndex hκ u x : ℝ) =
      IndexedScalarMeasure.indexLabel L κ (Prop026Bound.reG hκ u) x := by
    rw [hμe]
    filter_upwards [ae_integer_phase hκ u] with x hx
    rw [Prop026Bound.label_eq]
    exact ((div_eq_iff Real.pi_ne_zero).mpr hx).symm
  have hbd : IndexedScalarMeasure.LocallyUniformBoundary (μ : Measure ℝ) (Prop026Bound.reG hκ u) ∨
      IndexedScalarMeasure.BoundedAEBoundary (μ : Measure ℝ) (Prop026Bound.reG hκ u) := by
    rw [hμe]
    exact Or.inr (Prop026Bound.boundary_bounded hκ u)
  have hj := weak_joint_limit (Fact.out : 0 < L) hκ hc hNt hbd hn
  have hb : ∀ k, (∫⁻ p, ENNReal.ofReal (cost L p) ∂jointP (B k) (hN k)) ≤
      ENNReal.ofReal (κ/L) := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal
      (show Integrable (cost L) (jointP (B k) (hN k) : Measure (ℝ × ℤ)) from
        by
          change Integrable _ (emp (pts (B k)))
          unfold emp
          apply Integrable.smul_measure
          · exact integrable_finsetSum_measure.mpr (fun j _ => integrable_dirac (by simp))
          · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast (hN k).ne'))
      (ae_of_all _ (fun _ => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (finite_cost (L := L) hκ (hN k) (m k))
  have h := weak_cost_bound hj hb
  rw [graphP_toMeasure] at h
  have he := lintegral_map (μ := (μ : Measure ℝ)) (f := fun p => ENNReal.ofReal (cost L p))
    (g := fun x : ℝ => (x,cellIndex hκ u x))
    ((ENNReal.continuous_ofReal.comp (continuous_cost L)).measurable)
    (measurable_id.prodMk (measurable_cellIndex hκ u))
  rw [he, hμe] at h
  exact h

end QuantumNLS.RootWeightedCostR26
