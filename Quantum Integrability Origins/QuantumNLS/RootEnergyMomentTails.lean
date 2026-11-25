import QuantumNLS.RootEnergyMomentBounded

/-! The unbounded second-moment tail argument, with finite initial measures
included. No uniform-integrability conclusion is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open QuantumNLS.RootEnergyMomentBounded
namespace QuantumNLS.RootEnergyMomentTails

def excess (μ : Measure ℝ) (R : ℝ) : ℝ := ∫ t,t^2-clip R t ∂μ

def squareTail (μ : Measure ℝ) (R : ℝ) : ℝ :=
  ∫ t,({t : ℝ | R < t^2}.indicator (fun t => t^2)) t ∂μ

lemma excess_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun t : ℝ => t^2) μ) {R : ℝ} (hR : 0 ≤ R) :
    Integrable (fun t : ℝ => t^2-clip R t) μ := hi.sub (clip_integrable μ hR)

lemma excess_nonneg (μ : Measure ℝ) (R : ℝ) : 0 ≤ excess μ R :=
  integral_nonneg (fun _ => sub_nonneg.mpr (min_le_left _ _))

lemma excess_eq {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun t : ℝ => t^2) μ) {R : ℝ} (hR : 0 ≤ R) :
    excess μ R = (∫ t : ℝ,t^2 ∂μ) - ∫ t,clip R t ∂μ :=
  integral_sub hi (clip_integrable μ hR)

lemma excess_antitone {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun t : ℝ => t^2) μ) {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) :
    excess μ S ≤ excess μ R := by
  apply integral_mono_ae (excess_integrable hi (hR.trans hRS)) (excess_integrable hi hR)
  exact ae_of_all _ (fun t => sub_le_sub_left (min_le_min_left (t^2) hRS) _)

lemma excess_tendsto {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun t : ℝ => t^2) μ) :
    Tendsto (fun n : ℕ => excess μ n) atTop (nhds 0) := by
  have h := tendsto_integral_of_dominated_convergence (f := fun _ : ℝ => (0 : ℝ)) (fun t : ℝ => t^2)
    (fun n => (excess_integrable hi (Nat.cast_nonneg n)).aestronglyMeasurable) hi
    (fun n => ae_of_all μ (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (min_le_left _ _))]
      exact sub_le_self _ (clip_nonneg (Nat.cast_nonneg n) t)))
    (ae_of_all μ (fun t => by
      apply tendsto_const_nhds.congr'
      filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (t^2)] with n hn
      simp only [clip,min_eq_left hn,sub_self]))
  simpa only [integral_zero,excess] using h

lemma clip_tendsto {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun t : ℝ => t^2) μ) :
    Tendsto (fun n : ℕ => ∫ t,clip n t ∂μ) atTop (nhds (∫ t : ℝ,t^2 ∂μ)) := by
  have h := (excess_tendsto hi).const_sub (∫ t : ℝ,t^2 ∂μ)
  simpa only [excess_eq hi (Nat.cast_nonneg _),sub_sub_cancel,sub_zero] using h

lemma tail_le_excess {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun t : ℝ => t^2) μ) {R : ℝ} (hR : 0 ≤ R) :
    squareTail μ (2*R) ≤ 2 * excess μ R := by
  have hm : MeasurableSet {t : ℝ | 2*R < t^2} :=
    (isOpen_lt continuous_const (continuous_id.pow 2)).measurableSet
  have ht := hi.indicator hm
  have he := (excess_integrable hi hR).const_mul 2
  calc
    _ ≤ ∫ t : ℝ,2*(t^2-clip R t) ∂μ := by
      apply integral_mono_ae ht he
      apply ae_of_all
      intro t
      change ({t : ℝ | 2*R < t^2}.indicator (fun t => t^2)) t ≤ 2*(t^2-clip R t)
      by_cases h : 2*R < t^2
      · have hmem : t ∈ {s : ℝ | 2*R < s^2} := h
        rw [Set.indicator_of_mem hmem]
        have hr : R ≤ t^2 := by linarith
        rw [clip,min_eq_right hr]
        linarith
      · have hmem : t ∉ {s : ℝ | 2*R < s^2} := h
        rw [Set.indicator_of_notMem hmem]
        exact mul_nonneg (by norm_num) (sub_nonneg.mpr (min_le_left _ _))
    _ = _ := integral_const_mul _ _

/-- Weak convergence of bounded square truncations plus convergence of the
actual finite second moments proves uniform integrability, including every
finite prefix of the sequence. -/
theorem square_uniform_integrability (μ : ℕ → Measure ℝ) [∀ n, IsFiniteMeasure (μ n)]
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hi : ∀ n, Integrable (fun t : ℝ => t^2) (μ n))
    (hν : Integrable (fun t : ℝ => t^2) ν)
    (hm : Tendsto (fun n => ∫ t : ℝ,t^2 ∂μ n) atTop (nhds (∫ t : ℝ,t^2 ∂ν)))
    (hc : ∀ R : ℝ, 0 ≤ R → Tendsto (fun n => ∫ t,clip R t ∂μ n) atTop
      (nhds (∫ t,clip R t ∂ν))) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∀ n, squareTail (μ n) R < ε := by
  intro ε hε
  obtain ⟨r₀,hr₀⟩ := (eventually_atTop.mp
    ((excess_tendsto hν).eventually (gt_mem_nhds (show (0:ℝ) < ε/4 by positivity))))
  have hzero : excess ν r₀ < ε/4 := hr₀ r₀ le_rfl
  have hlim : Tendsto (fun n => excess (μ n) r₀) atTop (nhds (excess ν r₀)) := by
    simp_rw [excess_eq (hi _) (Nat.cast_nonneg r₀)]
    rw [excess_eq hν (Nat.cast_nonneg r₀)]
    exact hm.sub (hc r₀ (Nat.cast_nonneg r₀))
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (show excess ν r₀ < ε/2 by linarith)))
  have hp : ∀ j : Fin n₀, ∃ r : ℕ, excess (μ j) r < ε/2 := by
    intro j
    obtain ⟨r,hr⟩ := eventually_atTop.mp
      ((excess_tendsto (hi j)).eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity)))
    exact ⟨r,hr r le_rfl⟩
  choose r hr using hp
  let R : ℕ := max 1 (max r₀ (Finset.univ.sup r))
  have hR : 0 < (R : ℝ) := by
    have h : 1 ≤ R := le_max_left _ _
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h)
  refine ⟨2*(R : ℝ),by positivity,fun n => ?_⟩
  have hsmall : excess (μ n) R < ε/2 := by
    by_cases hlarge : n₀ ≤ n
    · have hle : r₀ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
      exact (excess_antitone (hi n) (Nat.cast_nonneg r₀) (by exact_mod_cast hle)).trans_lt (hn₀ n hlarge)
    · let j : Fin n₀ := ⟨n,lt_of_not_ge hlarge⟩
      have hle : r j ≤ R := (Finset.le_sup (f := r) (Finset.mem_univ j)).trans
        ((le_max_right _ _).trans (le_max_right _ _))
      exact (excess_antitone (hi n) (Nat.cast_nonneg (r j)) (by exact_mod_cast hle)).trans_lt (hr j)
  exact (tail_le_excess (hi n) hR.le).trans_lt (by linarith)

#print axioms square_uniform_integrability
end QuantumNLS.RootEnergyMomentTails

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyMomentTails." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyMomentTails." then
      pending := pending.push n
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
