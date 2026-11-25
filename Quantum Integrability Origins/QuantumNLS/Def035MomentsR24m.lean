import QuantumNLS.Def035TruncationR24m

/-! DEF-035 under owner decision D2. The varying-space theorem uses convergence
in distribution, with literal UI; the probability theorem names its common space.
This is the explicit owner-approved repair, not a claim about the old wording. -/
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Topology
open scoped ENNReal
namespace QuantumNLS.Def035MomentsR24m
open QuantumNLS.Def035TruncationR24m

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
  {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]

/-- Weak convergence and literal UI imply convergence of extended expectations.
No moment of the limit is assumed. -/
theorem lintegral_convergence (G : ∀ n, Ω n → ℝ) (g : Ω' → ℝ)
    (hd : TendstoInDistribution G atTop g μ ν) (hui : TailUI μ G) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (G n x) ∂μ n) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (g x) ∂ν)) := by
  let A : ℕ → ℕ → ℝ≥0∞ := fun k n =>
    ∫⁻ x, ENNReal.ofReal (clip (k : ℝ) (by positivity) (G n x)) ∂μ n
  let B : ℕ → ℝ≥0∞ := fun k =>
    ∫⁻ x, ENNReal.ofReal (clip (k : ℝ) (by positivity) (g x)) ∂ν
  let E : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ENNReal.ofReal (G n x) ∂μ n
  let T : ℕ → ℝ≥0∞ := fun k => ⨆ n, tail (μ n) (G n) (k : ℝ)
  have hA : ∀ k, Tendsto (A k) atTop (𝓝 (B k)) := fun k =>
    clipped_integral_tendsto μ ν G g hd (k : ℝ) (by positivity)
  have hB := clipped_limit ν g hd.aemeasurable_limit
  have hT : Tendsto T atTop (𝓝 0) := hui.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_le_liminf_of_limsup_le
  · apply le_of_tendsto' hB
    intro k
    change B k ≤ liminf E atTop
    rw [← (hA k).liminf_eq]
    apply liminf_le_liminf (Eventually.of_forall fun n => ?_)
    exact (truncation_bounds (μ n) (G n) (hd.forall_aemeasurable n) (k : ℝ) (by positivity)).1
  · have hup : ∀ k, limsup E atTop ≤ B k + T k := by
      intro k
      rw [← ((hA k).add tendsto_const_nhds).limsup_eq]
      apply limsup_le_limsup (Eventually.of_forall fun n => ?_)
      exact (truncation_bounds (μ n) (G n) (hd.forall_aemeasurable n)
        (k : ℝ) (by positivity)).2.trans
        (add_le_add le_rfl (le_iSup (fun n => tail (μ n) (G n) (k : ℝ)) n))
    simpa only [add_zero] using ge_of_tendsto' (hB.add hT) hup
  · exact ⟨⊤, Eventually.of_forall (fun _ => le_top)⟩
  · exact ⟨⊥, Eventually.of_forall (fun _ => bot_le)⟩

/-- Literal UI supplies a finite bound on all expectations. -/
theorem bounded_expectations (G : ∀ n, Ω n → ℝ)
    (hm : ∀ n, AEMeasurable (G n) (μ n)) (hui : TailUI μ G) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n, (∫⁻ x, ENNReal.ofReal (G n x) ∂μ n) ≤ C := by
  have he : ∀ᶠ R : ℝ in atTop, (⨆ n, tail (μ n) (G n) R) < 1 :=
    hui.eventually_lt_const (by simp)
  obtain ⟨R, ht, hR⟩ := (he.and (eventually_ge_atTop (0 : ℝ))).exists
  refine ⟨ENNReal.ofReal R + 1, by finiteness, fun n => ?_⟩
  apply (truncation_bounds (μ n) (G n) (hm n) R hR).2.trans
  apply add_le_add
  · calc
      _ ≤ ∫⁻ _ : Ω n, ENNReal.ofReal R ∂μ n :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ = ENNReal.ofReal R := by simp
  · exact (le_iSup (fun n => tail (μ n) (G n) R) n).trans ht.le

/-- Vitali for nonnegative variables on varying probability spaces. -/
theorem expectations (G : ∀ n, Ω n → ℝ) (g : Ω' → ℝ)
    (hG : ∀ n x, 0 ≤ G n x) (hg : ∀ x, 0 ≤ g x)
    (hd : TendstoInDistribution G atTop g μ ν) (hui : TailUI μ G) :
    (∀ n, Integrable (G n) (μ n)) ∧ Integrable g ν ∧
      Tendsto (fun n => ∫ x, G n x ∂μ n) atTop (𝓝 (∫ x, g x ∂ν)) := by
  have hc := lintegral_convergence μ ν G g hd hui
  obtain ⟨C, hC, hb⟩ := bounded_expectations μ G hd.forall_aemeasurable hui
  have hfin : (∫⁻ x, ENNReal.ofReal (g x) ∂ν) ≠ ∞ :=
    ne_top_of_le_ne_top hC (le_of_tendsto' hc hb)
  have hI : ∀ n, Integrable (G n) (μ n) := fun n =>
    ⟨(hd.forall_aemeasurable n).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (hG n))).2
        (lt_top_iff_ne_top.2 (ne_top_of_le_ne_top hC (hb n)))⟩
  have hi : Integrable g ν := ⟨hd.aemeasurable_limit.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg)).2 (lt_top_iff_ne_top.2 hfin)⟩
  refine ⟨hI, hi, ?_⟩
  simpa only [Function.comp_def, ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hG _)) (hI _).aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg) hi.aestronglyMeasurable]
    using (ENNReal.tendsto_toReal hfin).comp hc

/-- DEF-035 (D2): fixed real p > 0, arbitrary probability spaces, weak convergence
of laws plus the literal power-tail condition. Limit integrability is a conclusion. -/
theorem DEF035_distribution (X : ∀ n, Ω n → ℝ) (Y : Ω' → ℝ) (p : ℝ) (hp : 0 < p)
    (hX : ∀ n x, 0 ≤ X n x) (hY : ∀ x, 0 ≤ Y x)
    (hd : TendstoInDistribution X atTop Y μ ν) (hui : UniformPowerTail μ X p) :
    (∀ n, Integrable (fun x => (X n x) ^ p) (μ n)) ∧
    Integrable (fun x => (Y x) ^ p) ν ∧
    Tendsto (fun n => ∫ x, (X n x) ^ p ∂μ n) atTop (𝓝 (∫ x, (Y x) ^ p ∂ν)) :=
  expectations μ ν _ _ (fun n x => Real.rpow_nonneg (hX n x) p)
    (fun x => Real.rpow_nonneg (hY x) p)
    (hd.continuous_comp (Real.continuous_rpow_const hp.le)) hui

/-- Positive exponents use the owner-approved convention at zero. -/
theorem zero_power (p : ℝ) (hp : 0 < p) : (0 : ℝ) ^ p = 0 := Real.zero_rpow hp.ne'

/-- Convergence in probability is used only on this explicitly named common space. -/
theorem DEF035_probability {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P] (X : ℕ → S → ℝ) (Y : S → ℝ)
    (p : ℝ) (hp : 0 < p) (hX : ∀ n x, 0 ≤ X n x) (hY : ∀ x, 0 ≤ Y x)
    (hm : ∀ n, AEMeasurable (X n) P) (hc : TendstoInMeasure P X atTop Y)
    (hui : UniformPowerTail (fun _ => P) X p) :
    (∀ n, Integrable (fun x => (X n x) ^ p) P) ∧
    Integrable (fun x => (Y x) ^ p) P ∧
    Tendsto (fun n => ∫ x, (X n x) ^ p ∂P) atTop (𝓝 (∫ x, (Y x) ^ p ∂P)) :=
  DEF035_distribution (fun _ => P) P X Y p hp hX hY (hc.tendstoInDistribution hm) hui

/-- Literal uniform tail tightness; no limiting law or centering is supplied. -/
def UniformlyTight (Y : ∀ n, Ω n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ n, μ n {x | K < |Y n x|} ≤ ENNReal.ofReal ε

theorem uniformlyTight_of_bounded (Y : ∀ n, Ω n → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ n x, |Y n x| ≤ K) : UniformlyTight μ Y := by
  intro ε hε
  refine ⟨K, hK, fun n => ?_⟩
  have hset : {x | K < |Y n x|} = ∅ := Set.eq_empty_iff_forall_notMem.2
    (fun x hx => (not_lt_of_ge (hb n x)) hx)
  simp [hset]

#print axioms lintegral_convergence
#print axioms bounded_expectations
#print axioms expectations
#print axioms DEF035_distribution
#print axioms DEF035_probability
#print axioms zero_power
#print axioms uniformlyTight_of_bounded
end QuantumNLS.Def035MomentsR24m
