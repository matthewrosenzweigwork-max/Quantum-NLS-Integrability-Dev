import QuantumNLS.F03Actual
import QuantumNLS.DetGapFinal
import QuantumNLS.VarW2Weak
import QuantumNLS.F02Tightness
import QuantumNLS.ActualGapProbabilityR26

/-! Physical response data, phase inverse, and the two original-law errors.
The accepted occupation limit is consumed read-only. No regular-cut interpretation is made. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators
namespace QuantumNLS.ActualGapDataR26
open PhysicalTensor (L2T)
open BetheLabels (MArr arrRoots)
open F04SelBand (Mu II th sep)
open BulkResponseForm (BulkMeasure BulkResponseData L2Unit)
open StepIntegrals (stepL2)
open StrongLimitBulk (Q2)
open RootOccupationLimit (occDist)
open RootEnergyMomentLaws (law)
open BornConvergence (TendstoInProbability)
variable {L κ : ℝ} [Fact (0 < L)]

/-- All real phase levels have a preimage, by the accepted separator identities. -/
theorem phase_surjective (hκ : 0 < κ) (u : L2T L) : Function.Surjective (th hκ u) := by
  intro y
  let t : ℝ := y / Real.pi
  let k : ℤ := ⌊t⌋
  have h1 : (k : ℝ) ≤ t := Int.floor_le t
  have h2 : t < (k : ℝ) + 1 := Int.lt_floor_add_one t
  have ht : y = t * Real.pi := by dsimp [t]; field_simp
  apply intermediate_value_univ (sep hκ u (k - 1)) (sep hκ u (k + 1)) (F04SelBand.th_cont hκ u)
  rw [F04SelBand.th_sep, F04SelBand.th_sep, ht]
  push_cast
  constructor <;> nlinarith [Real.pi_pos]

/-- Response and physical measure data, with a globally chosen phase inverse. -/
structure Data (hκ : 0 < κ) (u : L2T L) where
  bulk : BulkMeasure (Mu hκ u)
  F : L2Unit
  response : (⟨L,κ,Fact.out,hκ,Mu hκ u,bulk⟩ : BulkResponseData).IsResponse F
  f : ℝ → ℝ
  fm : Measurable f
  pull : (F : ℝ → ℝ) =ᵐ[QuantileForm.uI] fun t => f (QuantileTransport.qm (Mu hκ u) t)
  xl : ℝ → ℝ
  phase : ∀ lam, th hκ u (xl lam) = lam * Real.pi

def Data.bd {hκ : 0 < κ} {u : L2T L} (D : Data hκ u) : BulkResponseData :=
  ⟨L,κ,Fact.out,hκ,Mu hκ u,D.bulk⟩

def Data.integrand {hκ : 0 < κ} {u : L2T L} (D : Data hκ u) (lam : ℝ) : ℝ :=
  DetGapRowLim.fext L κ (Mu hκ u) D.f (D.xl lam)

def Data.omega {hκ : 0 < κ} {u : L2T L} (D : Data hκ u) (a b : ℤ) : ℝ :=
  4 * Real.pi * ∫ lam in (b : ℝ)..(a : ℝ), D.integrand lam

/-- No bulk or response assumption is added: these data exist for every unit H¹ input. -/
theorem data_exists (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 u) : Nonempty (Data hκ u) := by
  classical
  obtain ⟨A⟩ := F03ActualData.actualBulkData_nonempty hκ hu hH
  have hm := Prop026Bound.physical_eq_limit hκ u hu A.limit
  have hb : BulkMeasure (Mu hκ u) := by rw [show Mu hκ u = (A.μ : Measure ℝ) from hm]; exact A.bulk
  obtain ⟨F,hF,f,hfm,hFf⟩ := DetGapFinal.exists_response_pullback hκ u hu hb
  have hx : ∀ lam : ℝ, ∃ x, th hκ u x = lam * Real.pi := fun lam => phase_surjective hκ u _
  choose xl hxl using hx
  exact ⟨⟨hb,F,hF,f,hfm,hFf,xl,hxl⟩⟩

/-- A single-label occupation, used only to fill a finite initial segment. -/
def singleArr (N : ℕ) (a : ℤ) : MArr N := ⟨Finsupp.single a N, by simp⟩

instance (N : ℕ) : Nonempty (MArr N) := ⟨singleArr N 0⟩

def err {hκ : 0 < κ} {u : L2T L} (D : Data hκ u) (N : ℕ) (m : MArr N) : ℝ :=
  occDist hκ u N m + ‖stepL2 (arrRoots L (κ / N) m) - Q2 D.bd‖ ^ 2

theorem err_nonneg {hκ : 0 < κ} {u : L2T L} (D : Data hκ u) (N : ℕ) (m : MArr N) :
    0 ≤ err D N m := add_nonneg (RootOccupationLimit.occDist_nonneg hκ u N m) (sq_nonneg _)

/-- The two errors converge jointly in probability under the original physical law. -/
theorem err_probability (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 u) (D : Data hκ u) :
    TendstoInProbability (fun n : ℕ => law hκ u hu (n + 1)) (fun n : ℕ => err D (n + 1)) 0 := by
  have hoc : TendstoInProbability (fun n : ℕ => law hκ u hu (n + 1))
      (fun n : ℕ => occDist hκ u (n + 1)) 0 := by
    intro ε hε
    have h := (RootOccupationLimit.occDist_prob hκ u hu hε).comp (tendsto_add_atTop_nat 1)
    dsimp only [Function.comp_def] at h
    simpa only [law,Real.dist_eq,sub_zero,abs_of_nonneg (RootOccupationLimit.occDist_nonneg hκ u _ _)] using h
  obtain ⟨A⟩ := F03ActualData.actualBulkData_nonempty hκ hu hH
  have hm := Prop026Bound.physical_eq_limit hκ u hu A.limit
  have heq : A.toBulkResponseData = D.bd := by
    dsimp only [BulkResponseActual.ActualBulkData.toBulkResponseData,Data.bd]
    congr 1
    exact hm.symm
  have hF : A.toBulkResponseData.IsResponse D.F := by rw [heq]; exact D.response
  have hs := (F03Actual.mean_square_of_data hκ u hu hH A hF).1
  rw [heq] at hs
  have hp : TendstoInProbability (fun n : ℕ => law hκ u hu (n + 1))
      (fun n m => ‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) m) - Q2 D.bd‖ ^ 2) 0 := by
    intro ε hε
    have hb : ∀ n : ℕ, (law hκ u hu (n + 1))
        {m | ε < dist (‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) m) - Q2 D.bd‖ ^ 2) 0} ≤
        (∫⁻ m, ENNReal.ofReal (‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) m) - Q2 D.bd‖ ^ 2)
          ∂law hκ u hu (n + 1)) / ENNReal.ofReal ε := by
      intro n
      refine (measure_mono ?_).trans (meas_ge_le_lintegral_div
        Measurable.of_discrete.aemeasurable (ENNReal.ofReal_pos.2 hε).ne' ENNReal.ofReal_ne_top)
      intro m hm
      simp only [mem_ofPred_eq, Real.dist_eq, sub_zero] at hm ⊢
      rw [abs_of_nonneg (sq_nonneg _)] at hm
      exact ENNReal.ofReal_le_ofReal hm.le
    have hh : Tendsto (fun n : ℕ => (∫⁻ m, ENNReal.ofReal
        (‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) m) - Q2 D.bd‖ ^ 2) ∂law hκ u hu (n + 1)) /
        ENNReal.ofReal ε) atTop (𝓝 0) := by
      have hh := ENNReal.Tendsto.mul_const hs
        (Or.inr (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hε).ne'))
      simpa [div_eq_mul_inv,F03Actual.rts] using hh
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh (fun _ => bot_le) hb
  change TendstoInProbability _ (fun n m => occDist hκ u (n + 1) m +
    ‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) m) - Q2 D.bd‖ ^ 2) 0
  simpa only [zero_add] using hoc.add hp

/-- Error convergence gives both deterministic inputs. -/
theorem err_limits {hκ : 0 < κ} {u : L2T L} (D : Data hκ u)
    (m : ∀ n : ℕ, MArr (n + 1))
    (he : Tendsto (fun n : ℕ => err D (n + 1) (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => occDist hκ u (n + 1) (m n)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) (m n)) - Q2 D.bd‖) atTop (𝓝 0) := by
  have h1 := squeeze_zero (fun n : ℕ => RootOccupationLimit.occDist_nonneg hκ u _ _)
    (fun n : ℕ => le_add_of_nonneg_right (sq_nonneg _)) he
  have h2 : Tendsto (fun n : ℕ => ‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) (m n)) - Q2 D.bd‖ ^ 2)
      atTop (𝓝 0) := squeeze_zero (fun n : ℕ => sq_nonneg _)
    (fun n : ℕ => le_add_of_nonneg_left (RootOccupationLimit.occDist_nonneg hκ u _ _)) he
  refine ⟨h1, ?_⟩
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp h2
  dsimp only [Function.comp_def] at hh
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

/-- Convert quantile norm convergence to the extended Wasserstein convention. -/
theorem wasserstein {hκ : 0 < κ} {u : L2T L} (D : Data hκ u)
    (m : ∀ n : ℕ, MArr (n + 1))
    (hq : Tendsto (fun n : ℕ => ‖stepL2 (arrRoots L (κ / ((n + 1 : ℕ) : ℝ)) (m n)) - Q2 D.bd‖) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => QuantileTransport.W2
      (QuantileTransport.empirical (n + 1) (arrRoots L (κ / ((n : ℝ) + 1)) (m n)))
        (Mu hκ u)) atTop (𝓝 0) := by
  have hh := ENNReal.tendsto_ofReal hq
  simp only [ENNReal.ofReal_zero] at hh
  refine hh.congr fun n => ?_
  have hc : 0 < κ / ((n : ℝ) + 1) := by positivity
  have hm : Monotone (arrRoots L (κ / ((n : ℝ) + 1)) (m n)) :=
    (RootContraction.isActual_roots (Fact.out : 0 < L) hc (AdjacentResponse.labs_mono (m n))).sorted.monotone
  have hn := DetGapW2.norm_step_sub_Q2 D.bd (Nat.succ_pos n) hm
  letI := D.bulk.isProbability
  letI := QuantileTransport.isProbabilityMeasure_empirical (Nat.succ_pos n)
    (arrRoots L (κ / ((n : ℝ) + 1)) (m n))
  have he : QuantileTransport.empirical (n + 1) (arrRoots L (κ / ((n : ℝ) + 1)) (m n)) =
      EmpiricalRapidity.empiricalMeasure L (κ / ((n : ℝ) + 1)) (m n) := by
    unfold QuantileTransport.empirical EmpiricalRapidity.empiricalMeasure
    rw [Finset.smul_sum]
  have hf := (RootEnergyMomentLaws.sample_second_moment (L := L) (κ := κ) (Nat.succ_pos n) (m n)).1
  have hf' : QuantileTransport.HasFiniteSecondMoment (QuantileTransport.empirical (n + 1)
      (arrRoots L (κ / ((n : ℝ) + 1)) (m n))) := by simpa only [QuantileTransport.HasFiniteSecondMoment,he,Nat.cast_add,Nat.cast_one,Nat.cast_succ] using hf
  have hb := BulkResponseRiesz.hasFiniteSecondMoment_of_moment D.bulk.finiteSecondMoment
  have ht := (QuantileTransport.W2_toReal_eq_sqrt _ _ hf' hb).1.ne
  simpa [Data.bd] using
    (congrArg ENNReal.ofReal hn).trans (ENNReal.ofReal_toReal ht)

end QuantumNLS.ActualGapDataR26
#print axioms QuantumNLS.ActualGapDataR26.data_exists
#print axioms QuantumNLS.ActualGapDataR26.err_probability
#print axioms QuantumNLS.ActualGapDataR26.wasserstein
