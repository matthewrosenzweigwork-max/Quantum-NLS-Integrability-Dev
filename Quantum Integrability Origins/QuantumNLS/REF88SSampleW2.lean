import QuantumNLS.REF88SQuantiles
import QuantumNLS.REF88SDiagonal

/-! R-EF8C2837 item (iv): actual-law samples provide the endpoint hW2.
The truncation-measure W₂ convergence is supplied by REF88SQuantiles.normalized_W2;
the approximation of each measure is DERIVED from accepted actual-law quantile convergence.
A slow diagonal keeps N=n+1, so no extension of VarFinal to subsequences is assumed.
Author sol_multi round23; independent reviewer terra_review. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace QuantumNLS.REF88SSampleW2
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ActualGapDataR26
open QuantumNLS.ActualGapTransferR26
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.StepIntegrals (stepL2)
open QuantumNLS.StrongLimitBulk (Q2)
open QuantumNLS.QuantileTransport
variable {L : ℝ} [Fact (0 < L)]

/-- Pointwise version of the accepted quantile norm identity, in the extended W₂ convention. -/
theorem sample_W2_eq_norm {K : ℝ} (hK : 0 < K) {u : L2T L} (D : Data hK u)
    (n : ℕ) (m : MArr (n + 1)) :
    W2 (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) m)) (Mu hK u) =
      ENNReal.ofReal ‖stepL2 (arrRoots L (K / ((n : ℝ) + 1)) m) - Q2 D.bd‖ := by
  have hc : 0 < K / ((n : ℝ) + 1) := by positivity
  have hm := (RootContraction.isActual_roots (Fact.out : 0 < L) hc
    (AdjacentResponse.labs_mono m)).sorted.monotone
  have hn := DetGapW2.norm_step_sub_Q2 D.bd (Nat.succ_pos n) hm
  letI := D.bulk.isProbability
  letI := isProbabilityMeasure_empirical (Nat.succ_pos n) (arrRoots L (K / ((n : ℝ) + 1)) m)
  have he : empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) m) =
      EmpiricalRapidity.empiricalMeasure L (K / ((n : ℝ) + 1)) m := by
    unfold empirical EmpiricalRapidity.empiricalMeasure
    rw [Finset.smul_sum]
  have hf := (RootEnergyMomentLaws.sample_second_moment (L := L) (κ := K) (Nat.succ_pos n) m).1
  have hf' : HasFiniteSecondMoment (empirical (n + 1) (arrRoots L (K / ((n : ℝ) + 1)) m)) := by
    simpa only [HasFiniteSecondMoment,he,Nat.cast_add,Nat.cast_one,Nat.cast_succ] using hf
  have hb := BulkResponseRiesz.hasFiniteSecondMoment_of_moment D.bulk.finiteSecondMoment
  have ht := (W2_toReal_eq_sqrt _ _ hf' hb).1.ne
  exact ((congrArg ENNReal.ofReal hn).trans (ENNReal.ofReal_toReal ht)).symm

/-- One fixed profile supplies samples approximating occupation, quantile AND actual gap. -/
theorem fixed_samples {K : ℝ} (hK : 0 < K) (u : L2T L) (hu : ‖u‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 u) (D : Data hK u) {a b : ℤ}
    (hab : a ≠ b) (ha : 0 < II hK u a) (hb : 0 < II hK u b) :
    ∃ m : ∀ n : ℕ, MArr (n + 1),
      Tendsto (fun n => err D (n + 1) (m n) +
        |F02Tightness.gap L K a b (m n) - D.omega a b|) atTop (𝓝 0) := by
  obtain ⟨m,hm⟩ := ActualGapProbabilityR26.select_sequence
    (fun n => RootEnergyMomentLaws.law hK u hu (n + 1))
    (fun n => err D (n + 1)) (fun n => err_nonneg D (n + 1))
    (err_probability hK u hu hH D)
  have hg := (deterministic_actual hK u hu D hab ha hb m hm).2
  exact ⟨m, by simpa only [sub_self,abs_zero,add_zero] using hm.add ((hg.sub_const (D.omega a b)).abs)⟩

/-- The printed diagonal selection supplies the exact endpoint W₂ convergence used by VarFinal.
The physical truncation theorem supplies the profile sequence and normalized_W2 supplies hμ.
No endpoint empirical W₂ hypothesis is assumed. -/
theorem actual_diagonal_endpoint (Ks : ℕ → ℝ) (hKs : ∀ j, 0 < Ks j)
    (v : ℕ → L2T L) (hv : ∀ j, ‖v j‖ = 1)
    (hH : ∀ j, ProductEnergyPreparation.OneH1 (v j)) (D : ∀ j, Data (hKs j) (v j))
    {a b : ℤ} (hab : a ≠ b) (ha : ∀ j, 0 < II (hKs j) (v j) a)
    (hb : ∀ j, 0 < II (hKs j) (v j) b)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Tendsto (fun j => W2 (Mu (hKs j) (v j)) μ) atTop (𝓝 0)) :
    ∃ (k : ℕ → ℕ) (η : ∀ n : ℕ, MArr (n + 1)),
      Monotone k ∧ Tendsto k atTop atTop ∧
      Tendsto (fun n => RootOccupationLimit.occDist (hKs (k n)) (v (k n)) (n + 1) (η n)) atTop (𝓝 0) ∧
      Tendsto (fun n => W2 (empirical (n + 1)
        (arrRoots L (Ks (k n) / ((n : ℝ) + 1)) (η n))) μ) atTop (𝓝 0) ∧
      Tendsto (fun n => F02Tightness.gap L (Ks (k n)) a b (η n) - (D (k n)).omega a b)
        atTop (𝓝 0) := by
  classical
  choose m hm using fun j => fixed_samples (hKs j) (v j) (hv j) (hH j) (D j) hab (ha j) (hb j)
  let e (j n : ℕ) := err (D j) (n + 1) (m j n) +
    |F02Tightness.gap L (Ks j) a b (m j n) - (D j).omega a b|
  obtain ⟨k,hmono,hk,he⟩ := REF88SDiagonal.slow_diagonal e hm
  let η : ∀ n : ℕ, MArr (n + 1) := fun n => m (k n) n
  have herr : Tendsto (fun n => err (D (k n)) (n + 1) (η n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => err_nonneg _ _ _) (fun n => le_add_of_nonneg_right (abs_nonneg _)) he
  have hgap : Tendsto (fun n => |F02Tightness.gap L (Ks (k n)) a b (η n) - (D (k n)).omega a b|)
      atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) (fun n => le_add_of_nonneg_left (err_nonneg _ _ _)) he
  have hocc : Tendsto (fun n => RootOccupationLimit.occDist (hKs (k n)) (v (k n)) (n + 1) (η n))
      atTop (𝓝 0) :=
    squeeze_zero (fun n => RootOccupationLimit.occDist_nonneg _ _ _ _)
      (fun n => le_add_of_nonneg_right (sq_nonneg _)) herr
  have hsq : Tendsto (fun n => ‖stepL2 (arrRoots L (Ks (k n) / ((n : ℝ) + 1)) (η n)) - Q2 (D (k n)).bd‖ ^ 2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _)
      (fun n => le_add_of_nonneg_left (RootOccupationLimit.occDist_nonneg (hKs (k n)) (v (k n)) (n + 1) (η n)))
    simpa only [err,Nat.cast_add,Nat.cast_one] using herr
  have hnorm : Tendsto (fun n => ‖stepL2 (arrRoots L (Ks (k n) / ((n : ℝ) + 1)) (η n)) - Q2 (D (k n)).bd‖)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hsample : Tendsto (fun n => W2 (empirical (n + 1)
      (arrRoots L (Ks (k n) / ((n : ℝ) + 1)) (η n))) (Mu (hKs (k n)) (v (k n)))) atTop (𝓝 0) := by
    have heq : ∀ n : ℕ, W2 (empirical (n + 1)
        (arrRoots L (Ks (k n) / ((n : ℝ) + 1)) (η n))) (Mu (hKs (k n)) (v (k n))) =
        ENNReal.ofReal ‖stepL2 (arrRoots L (Ks (k n) / ((n : ℝ) + 1)) (η n)) - Q2 (D (k n)).bd‖ :=
      fun n => sample_W2_eq_norm (hKs (k n)) (D (k n)) n (η n)
    simp_rw [heq]
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hnorm
  refine ⟨k,η,hmono,hk,hocc,?_,(tendsto_zero_iff_abs_tendsto_zero _).2 hgap⟩
  have hsum := hsample.add (hμ.comp hk)
  rw [zero_add] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le)
  intro n
  letI := (D (k n)).bulk.isProbability
  letI := isProbabilityMeasure_empirical (Nat.succ_pos n)
    (arrRoots L (Ks (k n) / ((n : ℝ) + 1)) (η n))
  exact W2_triangle _ _ _

#print axioms sample_W2_eq_norm
#print axioms fixed_samples
#print axioms actual_diagonal_endpoint
end QuantumNLS.REF88SSampleW2
