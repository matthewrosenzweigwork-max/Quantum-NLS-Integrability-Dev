import Mathlib

/-! Surjectivity from uniform open-band windows at the free trace zeros. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter Topology Set
namespace QuantumNLS.BandWindowSurjectivity

theorem window_bands {L : ℝ} (hL : 0 < L) {d : ℝ → ℝ}
    (ha : Tendsto (fun t => d t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0)) :
    ∃ R : ℝ, ∀ x : ℝ, R ≤ |x| → Real.cos (x * L / 2) = 0 →
      ∀ t : ℝ, |t - x| ≤ (2 * L)⁻¹ → |d t| < 2 := by
  have he : {t : ℝ | |d t - 2 * Real.cos (t * L / 2)| < 1} ∈ cocompact ℝ := by
    simpa [Metric.mem_ball, Real.dist_eq] using ha.eventually (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨K, hK, hsub⟩ := mem_cocompact.mp he
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn : ContinuousOn (fun t : ℝ => t) K)
  refine ⟨C + (2 * L)⁻¹ + 1, fun x hx hcx t ht => ?_⟩
  have htK : t ∉ K := by
    intro htk
    have hb := hC t htk
    simp only [id_eq, Real.norm_eq_abs] at hb
    have hs := abs_add_le (x - t) t
    rw [sub_add_cancel] at hs
    rw [abs_sub_comm] at ht
    linarith
  have herr : |d t - 2 * Real.cos (t * L / 2)| < 1 := hsub htK
  have hcos := Real.abs_cos_sub_cos_le (t * L / 2) (x * L / 2)
  rw [hcx, sub_zero] at hcos
  have heq : |t * L / 2 - x * L / 2| = |t - x| * L / 2 := by
    rw [show t * L / 2 - x * L / 2 = (t - x) * L / 2 by ring, abs_div, abs_mul,
      abs_of_pos hL]
    norm_num
  rw [heq] at hcos
  have hc : 2 * |Real.cos (t * L / 2)| ≤ 1 / 2 := by
    have hδ : (2 * L)⁻¹ * L = 1 / 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right ht hL.le]
  have hb := abs_add_le (d t - 2 * Real.cos (t * L / 2)) (2 * Real.cos (t * L / 2))
  rw [sub_add_cancel, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hb
  linarith

def center (L : ℝ) (n : ℕ) : ℝ := (2 * (n : ℝ) + 1) * Real.pi / L

theorem center_tendsto {L : ℝ} (hL : 0 < L) : Tendsto (center L) atTop atTop := by
  exact Tendsto.atTop_div_const hL (Tendsto.atTop_mul_const Real.pi_pos
    (tendsto_atTop_add_const_right _ 1 (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)))

theorem center_cos {L : ℝ} (hL : 0 < L) (n : ℕ) : Real.cos (center L n * L / 2) = 0 := by
  have he : center L n * L / 2 = (n : ℝ) * Real.pi + Real.pi / 2 := by
    dsimp [center]; field_simp
  rw [he, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  simp

theorem step_tendsto {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hs : ∀ n, f n + c ≤ f (n + 1)) : Tendsto f atTop atTop := by
  have hb : ∀ n : ℕ, f 0 + (n : ℝ) * c ≤ f n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hs n
      push_cast
      nlinarith
  exact tendsto_atTop_mono hb
    (tendsto_atTop_add_const_left _ (f 0) (Tendsto.atTop_mul_const hc tendsto_natCast_atTop_atTop))

theorem window_step {L δ : ℝ} (_hL : 0 < L) (hδ : 0 < δ) {f d : ℝ → ℝ}
    (hc : Continuous f) (hm : Monotone f)
    (hd : ∀ x, |d x| < 2 → DifferentiableAt ℝ f x ∧ L / 2 ≤ deriv f x)
    {x y : ℝ} (hxy : x + δ ≤ y)
    (hb : ∀ t ∈ Icc x (x + δ), |d t| < 2) :
    f x + L / 2 * δ ≤ f y := by
  have hi : L / 2 * δ ≤ f (x + δ) - f x := by
    convert (convex_Icc x (x + δ)).mul_sub_le_image_sub_of_le_deriv hc.continuousOn
      (fun t ht => (hd t (hb t (interior_subset ht))).1.differentiableWithinAt)
      (fun t ht => (hd t (hb t (interior_subset ht))).2)
      x ⟨le_rfl, by linarith⟩ (x + δ) ⟨by linarith, le_rfl⟩ (by linarith) using 1; ring
  exact le_trans (by linarith) (hm hxy)

/-- A real boundary with the proved band derivative is onto; no asymptotic lift is assumed. -/
theorem surjective {L : ℝ} (hL : 0 < L) {f d : ℝ → ℝ}
    (hc : Continuous f) (hm : Monotone f)
    (hd : ∀ x, |d x| < 2 → DifferentiableAt ℝ f x ∧ L / 2 ≤ deriv f x)
    (ha : Tendsto (fun t => d t - 2 * Real.cos (t * L / 2)) (cocompact ℝ) (𝓝 0)) :
    Function.Surjective f := by
  obtain ⟨R, hR⟩ := window_bands hL ha
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((center_tendsto hL).eventually_ge_atTop (max R 0))
  let δ : ℝ := (2 * L)⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsp (n : ℕ) : center L (n + N) + δ ≤ center L (n + 1 + N) := by
    have hp := Real.pi_gt_three
    dsimp [center, δ]
    have hn : (n + 1 + N : ℕ) = n + N + 1 := by omega
    rw [hn]
    push_cast
    apply (le_div_iff₀ hL).mpr
    have he : (2 * L)⁻¹ * L = 1 / 2 := by field_simp
    field_simp
    nlinarith
  have hp (n : ℕ) : max R 0 ≤ center L (n + N) := hN _ (by omega)
  have hbp (n : ℕ) : ∀ t ∈ Icc (center L (n + N)) (center L (n + N) + δ), |d t| < 2 := by
    rintro t ⟨ht1, ht2⟩
    apply hR _ (le_trans (le_max_left _ _) ((hp n).trans (le_abs_self _))) (center_cos hL _)
    simpa [abs_of_nonneg (by linarith : 0 ≤ t - center L (n + N)), δ] using (show t - center L (n + N) ≤ δ by linarith)
  have hbm (n : ℕ) : ∀ t ∈ Icc (-center L (n + N)) (-center L (n + N) + δ), |d t| < 2 := by
    rintro t ⟨ht1, ht2⟩
    refine hR (-center L (n + N)) ?_ ?_ t ?_
    · simpa [abs_neg] using le_trans (le_max_left R 0) ((hp n).trans (le_abs_self _))
    · rw [neg_mul, neg_div, Real.cos_neg]; exact center_cos hL _
    · change |t - -center L (n + N)| ≤ δ
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hplus : Tendsto (fun n : ℕ => f (center L (n + N))) atTop atTop := by
    apply step_tendsto (show 0 < L / 2 * δ by positivity)
    intro n
    simpa [Nat.add_assoc] using window_step hL hδ hc hm hd (hsp n) (hbp n)
  have hminus : Tendsto (fun n : ℕ => -f (-center L (n + N))) atTop atTop := by
    apply step_tendsto (show 0 < L / 2 * δ by positivity)
    intro n
    have hs : -center L (n + 1 + N) + δ ≤ -center L (n + N) := by linarith [hsp n]
    have hh := window_step hL hδ hc hm hd hs (by simpa [Nat.add_assoc] using hbm (n + 1))
    simpa [Nat.add_assoc] using (show -f (-center L (n + N)) + L / 2 * δ ≤ -f (-center L (n + 1 + N)) by linarith)
  intro y
  obtain ⟨n, hn⟩ := ((hplus.eventually_ge_atTop y)).exists
  obtain ⟨m, hmy⟩ := ((hminus.eventually_ge_atTop (-y))).exists
  exact intermediate_value_univ (-center L (m + N)) (center L (n + N)) hc ⟨by linarith, hn⟩

end QuantumNLS.BandWindowSurjectivity

#print axioms QuantumNLS.BandWindowSurjectivity.window_bands
#print axioms QuantumNLS.BandWindowSurjectivity.center
#print axioms QuantumNLS.BandWindowSurjectivity.center_tendsto
#print axioms QuantumNLS.BandWindowSurjectivity.center_cos
#print axioms QuantumNLS.BandWindowSurjectivity.step_tendsto
#print axioms QuantumNLS.BandWindowSurjectivity.window_step
#print axioms QuantumNLS.BandWindowSurjectivity.surjective

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.BandWindowSurjectivity." then
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
