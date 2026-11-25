import Mathlib

/-! Continuous boundary values for an actual positive-height cosine lift.
The lift is recovered from its exponential; no boundary phase is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set Filter Topology
namespace QuantumNLS.ComplexCosineBoundary

def upper : Set ℂ := {z | 0 < z.im}
def halfBall (x r : ℝ) : Set ℂ := Metric.ball (x : ℂ) r ∩ upper

theorem halfBall_preconnected (x r : ℝ) : IsPreconnected (halfBall x r) := by
  have hu : Convex ℝ upper := (convex_Ioi (0 : ℝ)).linear_preimage Complex.imLm
  exact ((convex_ball (x : ℂ) r).inter hu).isPreconnected

theorem halfBall_nonempty (x : ℝ) {r : ℝ} (hr : 0 < r) : (halfBall x r).Nonempty := by
  refine ⟨(x : ℂ) + (r / 2 : ℝ) * Complex.I, ?_, ?_⟩
  · simpa [Metric.mem_ball, dist_eq_norm, norm_mul, abs_of_pos hr]
      using (show r / 2 < r by linarith)
  · simpa [upper] using (show 0 < r / 2 by positivity)

theorem halfBall_mem (x : ℝ) {r : ℝ} (hr : 0 < r) : halfBall x r ∈ 𝓝[upper] (x : ℂ) :=
  inter_mem (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ hr)) self_mem_nhdsWithin

theorem upper_neBot (x : ℝ) : NeBot (𝓝[upper] (x : ℂ)) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨z, hz⟩ := halfBall_nonempty x hε
  exact ⟨z, hz.2, by simpa [dist_comm] using hz.1⟩

/-- A continuous map into a countable complex set is constant on a half disk. -/
theorem countable_constant {f : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn f (halfBall x r))
    {S : Set ℂ} (hS : S.Countable) (hm : MapsTo f (halfBall x r) S) :
    ∃ c : ℂ, ∀ z ∈ halfBall x r, f z = c := by
  have hp := (halfBall_preconnected x r).image f hc
  have hs := hS.isTotallyDisconnected (f '' halfBall x r) (image_subset_iff.mpr hm) hp
  obtain ⟨z₀, hz₀⟩ := halfBall_nonempty x hr
  exact ⟨f z₀, fun z hz => hs (mem_image_of_mem f hz) (mem_image_of_mem f hz₀)⟩

/-- Every within-neighborhood of the real point contains a half disk. -/
theorem exists_halfBall {x : ℝ} {S : Set ℂ} (hS : S ∈ 𝓝[upper] (x : ℂ)) :
    ∃ r : ℝ, 0 < r ∧ halfBall x r ⊆ S := by
  obtain ⟨V, hV, hsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hS
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
  exact ⟨r, hr, fun z hz => hsub ⟨hball hz.1, hz.2⟩⟩

/-- A convergent nonzero exponential fixes the actual lift locally, including its integer. -/
theorem phase_limit_of_exp_limit {γ : ℂ → ℂ} {x : ℝ} {a : ℂ}
    (hc : ContinuousOn γ upper) (ha : a ≠ 0)
    (hw : Tendsto (fun z => Complex.exp (Complex.I * γ z)) (𝓝[upper] (x : ℂ)) (𝓝 a)) :
    ∃ b : ℂ, Tendsto γ (𝓝[upper] (x : ℂ)) (𝓝 b) := by
  let w : ℂ → ℂ := fun z => Complex.exp (Complex.I * γ z)
  let q : ℂ → ℂ := fun z => Complex.log (w z / a)
  have hratio : Tendsto (fun z => w z / a) (𝓝[upper] (x : ℂ)) (𝓝 1) := by
    simpa [ha] using hw.div_const a
  have he : {z | 0 < (w z / a).re} ∈ 𝓝[upper] (x : ℂ) :=
    hratio.eventually ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))
  obtain ⟨r, hr, hsub⟩ := exists_halfBall he
  have hwc : ContinuousOn w upper := Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hc)
  have hqc : ContinuousOn q (halfBall x r) := by
    intro z hz
    apply (continuousAt_clog ?_).comp_continuousWithinAt
      (((hwc z hz.2).mono (inter_subset_right)).div_const a)
    exact Or.inl (hsub hz)
  let f : ℂ → ℂ := fun z => Complex.I * γ z - q z - Complex.log a
  have hfc : ContinuousOn f (halfBall x r) :=
    ((continuousOn_const.mul (hc.mono inter_subset_right)).sub hqc).sub continuousOn_const
  have hf : MapsTo f (halfBall x r) (range (fun k : ℤ => (k : ℂ) * (2 * Real.pi * Complex.I))) := by
    intro z hz
    have hz0 : w z / a ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) ha
    have heq : Complex.exp (f z) = 1 := by
      simp only [f, Complex.exp_sub, q, Complex.exp_log hz0, Complex.exp_log ha]
      change w z / (w z / a) / a = 1
      field_simp [show w z ≠ 0 from Complex.exp_ne_zero _]
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp heq
    exact ⟨k, hk.symm⟩
  obtain ⟨c, hconst⟩ := countable_constant hr hfc (countable_range _) hf
  have htq : Tendsto q (𝓝[upper] (x : ℂ)) (𝓝 0) := by
    simpa [q, Function.comp_def] using (continuousAt_clog (show (1 : ℂ) ∈ Complex.slitPlane by simp)).tendsto.comp hratio
  refine ⟨-Complex.I * (c + Complex.log a), ?_⟩
  have ht := ((htq.const_add c).add_const (Complex.log a)).const_mul (-Complex.I)
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [halfBall_mem x hr] with z hz
  have hh := hconst z hz
  dsimp [f] at hh
  calc
    -Complex.I * (c + q z + Complex.log a) = -Complex.I * (Complex.I * γ z) := by
      congr 1
      linear_combination -hh
    _ = γ z := by rw [← mul_assoc]; simp

/-- The repeated quadratic root has an unrestricted upper boundary limit. -/
theorem repeated_root_limit {D w : ℂ → ℂ} {x : ℝ} {s : ℂ}
    (hD : ContinuousAt D (x : ℂ)) (hs : s ^ 2 = 1) (hDx : D (x : ℂ) = 2 * s)
    (hw : ∀ z ∈ upper, w z ^ 2 - D z * w z + 1 = 0)
    (hb : ∀ z ∈ upper, ‖w z‖ ≤ 1) :
    Tendsto w (𝓝[upper] (x : ℂ)) (𝓝 s) := by
  have ht : Tendsto (fun z => Real.sqrt ‖D z - 2 * s‖) (𝓝[upper] (x : ℂ)) (𝓝 0) := by
    simpa [hDx] using (hD.tendsto.sub_const (2 * s)).norm.sqrt |>.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun z => norm_nonneg (w z - s))) _ ht
  filter_upwards [self_mem_nhdsWithin] with z hz
  have he : (w z - s) ^ 2 = (D z - 2 * s) * w z := by
    linear_combination hw z hz + hs
  have hn := congrArg norm he
  rw [norm_pow, norm_mul] at hn
  have hl : ‖w z - s‖ ^ 2 ≤ ‖D z - 2 * s‖ := by
    rw [hn]
    exact mul_le_of_le_one_right (norm_nonneg _) (hb z hz)
  have hsq := Real.sq_sqrt (norm_nonneg (D z - 2 * s))
  nlinarith [Real.sqrt_nonneg ‖D z - 2 * s‖, norm_nonneg (w z - s)]

/-- Distinct roots are locally separated; connectedness fixes the actual root. -/
theorem distinct_root_limit {D w : ℂ → ℂ} {x : ℝ}
    (hD : Continuous D) (hc : ContinuousOn w upper)
    (ha : D (x : ℂ) ^ 2 - 4 ≠ 0)
    (hw : ∀ z ∈ upper, w z ^ 2 - D z * w z + 1 = 0) :
    ∃ a : ℂ, Tendsto w (𝓝[upper] (x : ℂ)) (𝓝 a) := by
  let A : ℂ := D (x : ℂ) ^ 2 - 4
  have hA : A ≠ 0 := ha
  have hsqrt (z : ℂ) : Complex.sqrt z ^ 2 = z :=
    Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)
  let R : ℂ → ℂ := fun z => (D z ^ 2 - 4) / A
  let q : ℂ → ℂ := fun z => Complex.sqrt A * Complex.sqrt (R z)
  have hR : Continuous R := (hD.pow 2 |>.sub continuous_const).div_const A
  have hRx : R (x : ℂ) = 1 := div_self hA
  have hq : ContinuousAt q (x : ℂ) := by
    apply continuousAt_const.mul
    exact (Complex.continuousAt_sqrt (Or.inl (by rw [hRx]; norm_num))).comp hR.continuousAt
  have hqx : q (x : ℂ) = Complex.sqrt A := by simp [q, hRx]
  have hq0 : q (x : ℂ) ≠ 0 := by
    rw [hqx]
    intro h
    have := hsqrt A
    rw [h, zero_pow (by norm_num)] at this
    exact hA this.symm
  have hn : {z : ℂ | 0 < (R z).re ∧ q z ≠ 0} ∈ 𝓝 (x : ℂ) := by
    apply inter_mem
    · exact (Complex.continuous_re.comp hR).continuousAt.eventually
        (lt_mem_nhds (show (0 : ℝ) < (R (x : ℂ)).re by rw [hRx]; norm_num))
    · exact hq.eventually (isOpen_ne.mem_nhds hq0)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hqc : ContinuousOn q (halfBall x r) := by
    intro z hz
    apply (continuousAt_const.mul ((Complex.continuousAt_sqrt
      (Or.inl (hball hz.1).1.le)).comp hR.continuousAt)).continuousWithinAt
  have hqsq (z : ℂ) : q z ^ 2 = D z ^ 2 - 4 := by
    dsimp [q]
    rw [mul_pow, hsqrt, hsqrt]
    dsimp [R]
    field_simp
  let v : ℂ → ℂ := fun z => (2 * w z - D z) / q z
  have hvc : ContinuousOn v (halfBall x r) :=
    ((continuousOn_const.mul (hc.mono inter_subset_right)).sub hD.continuousOn).div hqc
      (fun z hz => (hball hz.1).2)
  have hv : MapsTo v (halfBall x r) ({1, -1} : Set ℂ) := by
    intro z hz
    have hv2 : v z ^ 2 = 1 := by
      have he : (2 * w z - D z) ^ 2 = D z ^ 2 - 4 := by linear_combination 4 * hw z hz.2
      dsimp [v]
      rw [div_pow, he, ← hqsq z]
      exact div_self (pow_ne_zero 2 (hball hz.1).2)
    simpa only [mem_insert_iff, mem_singleton_iff] using (sq_eq_one_iff.mp hv2)
  obtain ⟨c, hconst⟩ := countable_constant hr hvc (toFinite ({1, -1} : Set ℂ)).countable hv
  refine ⟨(D (x : ℂ) + c * q (x : ℂ)) / 2, ?_⟩
  apply ((hD.continuousAt.tendsto.add (hq.tendsto.const_mul c)).div_const 2
    |>.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [halfBall_mem x hr] with z hz
  have hh := (div_eq_iff (hball hz.1).2).mp (hconst z hz)
  linear_combination -hh / 2

/-- A bounded actual quadratic root has a nonzero boundary limit everywhere. -/
theorem quadratic_root_limit {D w : ℂ → ℂ} {x : ℝ}
    (hD : Continuous D) (hc : ContinuousOn w upper)
    (hw : ∀ z ∈ upper, w z ^ 2 - D z * w z + 1 = 0)
    (hb : ∀ z ∈ upper, ‖w z‖ ≤ 1) :
    ∃ a : ℂ, a ≠ 0 ∧ Tendsto w (𝓝[upper] (x : ℂ)) (𝓝 a) := by
  have := upper_neBot x
  have hex : ∃ a : ℂ, Tendsto w (𝓝[upper] (x : ℂ)) (𝓝 a) := by
    by_cases h : D (x : ℂ) ^ 2 - 4 = 0
    · have he : D (x : ℂ) = 2 ∨ D (x : ℂ) = -2 := by
        apply (sq_eq_sq_iff_eq_or_eq_neg).mp
        linear_combination h
      rcases he with he | he
      · exact ⟨1, repeated_root_limit hD.continuousAt (by norm_num) (by simpa using he) hw hb⟩
      · exact ⟨-1, repeated_root_limit hD.continuousAt (by norm_num) (by simpa using he) hw hb⟩
    · exact distinct_root_limit hD hc h hw
  obtain ⟨a, ht⟩ := hex
  refine ⟨a, ?_, ht⟩
  have hl := ((ht.pow 2).sub ((hD.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul ht)).add_const 1
  have hz : Tendsto (fun z => w z ^ 2 - D z * w z + 1) (𝓝[upper] (x : ℂ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hw z hz).symm
  have he := tendsto_nhds_unique hl hz
  intro ha
  simp [ha] at he

/-- The actual positive-height cosine phase has a full, uniquely lifted boundary limit. -/
theorem cosine_phase_limit {D γ : ℂ → ℂ} (hD : Continuous D)
    (hc : ContinuousOn γ upper) (hp : ∀ z ∈ upper, 0 ≤ (γ z).im)
    (he : ∀ z ∈ upper, 2 * Complex.cos (γ z) = D z) (x : ℝ) :
    ∃ b : ℂ, Tendsto γ (𝓝[upper] (x : ℂ)) (𝓝 b) := by
  let w : ℂ → ℂ := fun z => Complex.exp (Complex.I * γ z)
  have hwc : ContinuousOn w upper :=
    Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hc)
  have hw : ∀ z ∈ upper, w z ^ 2 - D z * w z + 1 = 0 := by
    intro z hz
    have hcos := he z hz
    rw [Complex.two_cos] at hcos
    have hmul : γ z * Complex.I = Complex.I * γ z := mul_comm _ _
    have hneg : -γ z * Complex.I = -(Complex.I * γ z) := by ring
    rw [hmul, hneg, Complex.exp_neg] at hcos
    have hn : w z ≠ 0 := Complex.exp_ne_zero _
    change w z + (w z)⁻¹ = D z at hcos
    field_simp at hcos
    linear_combination hcos
  have hb : ∀ z ∈ upper, ‖w z‖ ≤ 1 := by
    intro z hz
    dsimp [w]
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simpa using neg_nonpos.mpr (hp z hz)
  obtain ⟨a, ha, ht⟩ := quadratic_root_limit hD hwc hw hb
  exact phase_limit_of_exp_limit hc ha ht

/-- Boundary limits varying along the real line form a continuous function. -/
theorem continuous_boundary {f : ℂ → ℂ} {b : ℝ → ℂ}
    (ht : ∀ x : ℝ, Tendsto f (𝓝[upper] (x : ℂ)) (𝓝 (b x))) : Continuous b := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  have he := (ht x).eventually (Metric.ball_mem_nhds (b x) (show 0 < ε / 2 by positivity))
  obtain ⟨r, hr, hball⟩ := exists_halfBall he
  refine ⟨r / 2, by positivity, fun y hy => ?_⟩
  have := upper_neBot y
  have hxy : dist (y : ℂ) (x : ℂ) < r := by
    have : dist (y : ℂ) (x : ℂ) = dist y x := by rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]
    rw [this]
    linarith
  have hev : ∀ᶠ z in 𝓝[upper] (y : ℂ), dist (f z) (b x) ≤ ε / 2 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hxy),
      self_mem_nhdsWithin] with z hz hzu
    exact (hball ⟨hz, hzu⟩).le
  exact (le_of_tendsto ((ht y).dist tendsto_const_nhds) hev).trans_lt (by linarith)

/-- A continuous boundary function for the original cosine lift, with full upper limits. -/
theorem exists_boundary {D γ : ℂ → ℂ} (hD : Continuous D)
    (hc : ContinuousOn γ upper) (hp : ∀ z ∈ upper, 0 ≤ (γ z).im)
    (he : ∀ z ∈ upper, 2 * Complex.cos (γ z) = D z) :
    ∃ b : ℝ → ℂ, Continuous b ∧
      ∀ x : ℝ, Tendsto γ (𝓝[upper] (x : ℂ)) (𝓝 (b x)) := by
  choose b hb using cosine_phase_limit hD hc hp he
  exact ⟨b, continuous_boundary hb, hb⟩

end QuantumNLS.ComplexCosineBoundary

#print axioms QuantumNLS.ComplexCosineBoundary.upper
#print axioms QuantumNLS.ComplexCosineBoundary.halfBall
#print axioms QuantumNLS.ComplexCosineBoundary.halfBall_preconnected
#print axioms QuantumNLS.ComplexCosineBoundary.halfBall_nonempty
#print axioms QuantumNLS.ComplexCosineBoundary.halfBall_mem
#print axioms QuantumNLS.ComplexCosineBoundary.upper_neBot
#print axioms QuantumNLS.ComplexCosineBoundary.countable_constant
#print axioms QuantumNLS.ComplexCosineBoundary.exists_halfBall
#print axioms QuantumNLS.ComplexCosineBoundary.phase_limit_of_exp_limit
#print axioms QuantumNLS.ComplexCosineBoundary.repeated_root_limit
#print axioms QuantumNLS.ComplexCosineBoundary.distinct_root_limit
#print axioms QuantumNLS.ComplexCosineBoundary.quadratic_root_limit
#print axioms QuantumNLS.ComplexCosineBoundary.cosine_phase_limit
#print axioms QuantumNLS.ComplexCosineBoundary.continuous_boundary
#print axioms QuantumNLS.ComplexCosineBoundary.exists_boundary

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ComplexCosineBoundary." then
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
