import Mathlib
import NlsGge.Atomic.AL.AL080
import NlsGge.Atomic.AL.AL085
import NlsGge.ThirdConsultation.AL.Basic
import NlsGge.Hierarchy.ALFreeFields38
import NlsGge.Birkhoff.S05FreeEnergy38b
import NlsGge.Birkhoff.W04WeightedSmoothing38b

/- AL-086 PRODUCTION01 (proof development, AUTHOR; target NlsGge/Atomic/AL/AL086.lean; not self-reviewed). Head verbatim from defs3 STATEMENTS/AL.md AL-086 (followup2 identical).
   Route: realization = finite-dimensional linear embedding (measurable); norm identity from norm_sq_eCarrier38; single-mode bound from AL-085; exact radial law from complexGaussian_sqNorm_le38; compact sets are bounded; non-tightness from law(K) -> 0 and probability. -/
set_option autoImplicit false
open scoped BigOperators ENNReal Topology
open Set Filter MeasureTheory
open NlsGge.Pilot NlsGge.AblowitzLadik NlsGge.Weights NlsGge.Birkhoff
namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem al086_mem_of_support {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)
    (S : Finset ℤ) (x : ℤ → ℂ) (hx : ∀ n, n ∉ S → x n = 0) : x ∈ seqE38 c s := by
  rw [mem_seqE38_iff]
  exact summable_of_ne_finset_zero (s := S) fun n hn => by rw [hx n hn]; simp

theorem al086_uh_support (c : ℕ → ℝ) (N : ℕ) (g : ℤ → ℂ) (n : ℤ)
    (hn : n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ)) : alUhCoef38 c N g n = 0 := by
  unfold alUhCoef38
  rw [if_neg]
  intro h
  exact hn (Finset.mem_Icc.2 (abs_le.1 h))

theorem al086_exists_phi {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ) (N : ℕ) :
    ∃ Φ : ((Finset.Icc (-(N : ℤ)) (N : ℤ)) → ℂ) →ₗ[ℝ] ECarrier38 c s,
      ∀ a m, eCoe38 c s (Φ a) m =
        if h : m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a ⟨m, h⟩ else 0 := by
  classical
  let ext : ((Finset.Icc (-(N : ℤ)) (N : ℤ)) → ℂ) → ℤ → ℂ := fun a m =>
    if h : m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a ⟨m, h⟩ else 0
  have hext : ∀ a, ext a ∈ seqE38 c s := fun a =>
    al086_mem_of_support c s (Finset.Icc (-(N : ℤ)) (N : ℤ)) _ fun n hn => by show (if h : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a ⟨n, h⟩ else 0) = 0; rw [dif_neg hn]
  refine ⟨{ toFun := fun a => eMk38 c s (ext a) (hext a)
            map_add' := fun a b => eExt38 c s (funext fun m => ?_)
            map_smul' := fun r a => eExt38 c s (funext fun m => ?_) }, fun a m => rfl⟩
  · rw [eAdd_apply38]
    simp only [eCoe38_mk, ext]
    split_ifs <;> simp
  · rw [eSmul_apply38]
    simp only [eCoe38_mk, ext, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul]

theorem al086 (lower upper : ℝ) (c : BoundedCoefficients lower upper) (s : ℝ)
    [MeasurableSpace (ECarrier38 c s)] [BorelSpace (ECarrier38 c s)] :
    let b : ℕ → ℝ := fun N =>
      alEdgeRatio38 c.val N * sobolevModeWeight (-s) (N : ℤ)
    (∀ N : ℕ, Measurable (alCriticalRealization c s N) ∧ ∀ g : ℤ → ℂ,
      eCoe38 c s (alCriticalRealization c s N g) = alUhCoef38 c.val N g ∧
      ‖alCriticalRealization c s N g‖ ^ 2 = alESqNorm38 c.val s N g) ∧
    (∀ M : ℝ,
      (∀ᶠ N : ℕ in atTop, 0 < b N ∧
        alCriticalLaw c s N {x | ‖x‖ ≤ M} ≤
          alFreeLaw38 {g | b N * ‖g (N : ℤ)‖ ^ 2 ≤ M ^ 2} ∧
        alFreeLaw38 {g | b N * ‖g (N : ℤ)‖ ^ 2 ≤ M ^ 2} =
          ENNReal.ofReal (1 - Real.exp (-(M ^ 2 / b N)))) ∧
      Tendsto (fun N : ℕ => alCriticalLaw c s N {x | ‖x‖ ≤ M}) atTop (𝓝 0)) ∧
    (∀ K : Set (ECarrier38 c s), IsCompact K →
      Tendsto (fun N : ℕ => alCriticalLaw c s N K) atTop (𝓝 0)) ∧
    ¬ (∀ ε : ℝ, 0 < ε → ∃ K : Set (ECarrier38 c s), IsCompact K ∧
      ∀ N : ℕ, alCriticalLaw c s N Kᶜ ≤ ENNReal.ofReal ε) := by
  intro b
  classical
  have hA := al080Aux.admissible c
  have hmem : ∀ N g, alUhCoef38 c.val N g ∈ seqE38 c s := fun N g =>
    al086_mem_of_support c s _ _ (al086_uh_support c.val N g)
  have hreal : ∀ N g, eCoe38 c s (alCriticalRealization c s N g) = alUhCoef38 c.val N g := by
    intro N g
    unfold alCriticalRealization
    rw [dif_pos (hmem N g)]
    exact eCoe38_mk c s _ _
  have hfw : ∀ k : ℤ, fullModeWeight c s k = alRateCont38 c.val k * sobolevModeWeight (-s) k := by
    intro k
    unfold fullModeWeight sourceRate alRateCont38 sobolevModeWeight
    rw [show (-2 * s) = 2 * -s by ring]
  have hnorm : ∀ N g, ‖alCriticalRealization c s N g‖ ^ 2 = alESqNorm38 c.val s N g := by
    intro N g
    rw [norm_sq_eCarrier38]
    simp only [hreal]
    rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n hn => by
      rw [al086_uh_support c.val N g n hn]; simp)]
    unfold alESqNorm38
    exact Finset.sum_congr rfl fun k _ => by rw [hfw k]
  have hmeas : ∀ N, Measurable (alCriticalRealization c s N) := by
    intro N
    obtain ⟨Φ, hΦ⟩ := al086_exists_phi c s N
    have hΦc : Continuous Φ := LinearMap.continuous_of_finiteDimensional Φ
    have hfun : alCriticalRealization c s N =
        fun g => Φ (fun k => alUhCoef38 c.val N g (k : ℤ)) := by
      funext g
      refine eExt38 c s (funext fun m => ?_)
      rw [hreal, hΦ]
      by_cases hm : m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
      · simp [hm]
      · simp [hm, al086_uh_support c.val N g m hm]
    rw [hfun]
    refine hΦc.measurable.comp (measurable_pi_iff.2 fun k => ?_)
    have hk : |(k : ℤ)| ≤ (N : ℤ) := abs_le.2 (Finset.mem_Icc.1 k.2)
    have : (fun g : ℤ → ℂ => alUhCoef38 c.val N g (k : ℤ)) =
        fun g => g (k : ℤ) / ((Real.sqrt (alRateFree38 c.val N k) : ℝ) : ℂ) := by
      funext g; simp [alUhCoef38, hk]
    rw [this]
    exact (measurable_pi_apply (k : ℤ)).div_const _
  have hbtop : Tendsto b atTop atTop := alEdgeCoeff_tendsto_top38 hA s
  have hlawset : ∀ (N : ℕ) (M : ℝ), alCriticalLaw c s N {x | ‖x‖ ≤ M} =
      alFreeLaw38 (alCriticalRealization c s N ⁻¹' {x | ‖x‖ ≤ M}) := fun N M => by
    unfold alCriticalLaw
    exact Measure.map_apply (hmeas N) (isClosed_le continuous_norm continuous_const).measurableSet
  have hmain : ∀ M : ℝ, ∀ᶠ N : ℕ in atTop, 0 < b N ∧
        alCriticalLaw c s N {x | ‖x‖ ≤ M} ≤
          alFreeLaw38 {g | b N * ‖g (N : ℤ)‖ ^ 2 ≤ M ^ 2} ∧
        alFreeLaw38 {g | b N * ‖g (N : ℤ)‖ ^ 2 ≤ M ^ 2} =
          ENNReal.ofReal (1 - Real.exp (-(M ^ 2 / b N))) := by
    intro M
    have h85 := (al085 lower upper c s).2
    filter_upwards [h85, hbtop.eventually_gt_atTop 0] with N hN hbN
    refine ⟨hbN, ?_, ?_⟩
    · rw [hlawset]
      refine measure_mono fun g hg => ?_
      have h1 : ‖alCriticalRealization c s N g‖ ≤ M := hg
      have h2 : ‖alCriticalRealization c s N g‖ ^ 2 ≤ M ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [hnorm] at h2
      exact (hN.2 g).trans h2
    · have hm : MeasurableSet {z : ℂ | ‖z‖ ^ 2 ≤ M ^ 2 / b N} :=
        measurableSet_le (by fun_prop) measurable_const
      have hset : {g : ℤ → ℂ | b N * ‖g (N : ℤ)‖ ^ 2 ≤ M ^ 2} =
          (fun g : ℤ → ℂ => g (N : ℤ)) ⁻¹' {z : ℂ | ‖z‖ ^ 2 ≤ M ^ 2 / b N} := by
        ext g
        simp only [mem_setOf_eq, mem_preimage]
        exact (le_div_iff₀' hbN).symm
      have h := NlsGge.Measure.countableComplexGaussian_map_eval (fun _ : ℤ => (1 : ℝ)) (N : ℤ)
      rw [hset]
      have h2 : alFreeLaw38 ((fun g : ℤ → ℂ => g (N : ℤ)) ⁻¹' {z : ℂ | ‖z‖ ^ 2 ≤ M ^ 2 / b N}) =
          NlsGge.Measure.complexGaussian 1 {z : ℂ | ‖z‖ ^ 2 ≤ M ^ 2 / b N} := by
        rw [← h, Measure.map_apply (measurable_pi_apply (N : ℤ)) hm]
        rfl
      rw [h2]
      exact NlsGge.Measure.complexGaussian_sqNorm_le38 _ (by positivity)
  have hT : ∀ M : ℝ, Tendsto (fun N : ℕ => alCriticalLaw c s N {x | ‖x‖ ≤ M}) atTop (𝓝 0) := by
    intro M
    have hup : Tendsto (fun N : ℕ => ENNReal.ofReal (M ^ 2 / b N)) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop hbtop (a := M ^ 2))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun N => zero_le) ?_
    filter_upwards [hmain M] with N ⟨hbN, h1, h2⟩
    refine h1.trans ?_
    rw [h2]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Real.add_one_le_exp (-(M ^ 2 / b N))
    linarith
  have hK : ∀ K : Set (ECarrier38 c s), IsCompact K →
      Tendsto (fun N : ℕ => alCriticalLaw c s N K) atTop (𝓝 0) := by
    intro K hKc
    obtain ⟨C, hC⟩ := hKc.isBounded.exists_norm_le
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hT C)
      (Eventually.of_forall fun N => zero_le) (Eventually.of_forall fun N => ?_)
    exact measure_mono fun x hx => hC x hx
  refine ⟨fun N => ⟨hmeas N, fun g => ⟨hreal N g, hnorm N g⟩⟩,
    fun M => ⟨hmain M, hT M⟩, hK, ?_⟩
  intro h
  obtain ⟨K, hKc, hKb⟩ := h (1 / 2) (by norm_num)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hprob : ∀ N, IsProbabilityMeasure (alCriticalLaw c s N) := fun N => by
    unfold alCriticalLaw
    refine ⟨?_⟩
    rw [Measure.map_apply (hmeas N) MeasurableSet.univ, preimage_univ]
    exact measure_univ
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 4) := ENNReal.ofReal_pos.2 (by norm_num)
  obtain ⟨N, hN⟩ := ((hK K hKc).eventually (gt_mem_nhds hpos)).exists
  haveI := hprob N
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 4) + ENNReal.ofReal (1 / 2) := by
    calc (1 : ℝ≥0∞) = alCriticalLaw c s N K + alCriticalLaw c s N Kᶜ := by
          rw [measure_add_measure_compl hKm]; simp
      _ ≤ _ := add_le_add hN.le (hKb N)
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), ENNReal.one_le_ofReal] at h1
  norm_num at h1

end
end NlsGge.ThirdConsultation.AL
