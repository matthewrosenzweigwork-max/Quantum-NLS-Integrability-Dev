import QuantumNLS.Local006DerivativeF

/-! LOCAL-006: collective fifth-order remainder around the actual degree-three
Taylor coefficient. Identification of that coefficient with the printed double
Fourier sum is a separate, unproved obligation, not a premise of this module. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology Asymptotics
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local006.FifthF
open QuantumNLS.PhysicalTensor QuantumNLS.Local006.CollectiveF
  QuantumNLS.Local006.FirstJetF QuantumNLS.Local006.DerivativeF

section Odd
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every even homogeneous Taylor term of a locally odd analytic map vanishes
on the diagonal. Symmetry of the chosen multilinear representative is not assumed. -/
lemma odd_even_coefficient {G : E → F} {p : FormalMultilinearSeries ℝ E F}
    (hp : HasFPowerSeriesAt G p 0) (ho : (fun u => G (-u)) =ᶠ[𝓝 0] fun u => -G u)
    (k : ℕ) (hk : Even k) (u : E) : p k (fun _ => u) = 0 := by
  have hn : HasFPowerSeriesAt G p ((-ContinuousLinearMap.id ℝ E) 0) := by simpa using hp
  have hn := hn.compContinuousLinearMap
  have he : (G ∘ (-ContinuousLinearMap.id ℝ E) + G) =ᶠ[𝓝 0] (0 : E → F) := by
    filter_upwards [ho] with x hx
    simp [Function.comp_def, hx]
  have hz := (hn.add hp).congr he
  have h := hz.apply_eq_zero k u
  change p k (fun _ => -u) + p k (fun _ => u) = 0 at h
  have hsign : p k (fun _ => -u) = p k (fun _ => u) := by
    calc p k (fun _ => -u) = (∏ _ : Fin k, (-1 : ℝ)) • p k (fun _ => u) := by
          simpa using (p k).map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => u)
      _ = p k (fun _ => u) := by simp [hk.neg_one_pow]
  rw [hsign] at h
  have h2 : (2 : ℝ) • p k (fun _ => u) = 0 := by simpa [two_smul] using h
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

lemma odd_fifth_order {G : E → F} (ha : AnalyticAt ℝ G 0) (h0 : G 0 = 0)
    (ho : (fun u => G (-u)) =ᶠ[𝓝 0] fun u => -G u) :
    ∃ p : FormalMultilinearSeries ℝ E F, HasFPowerSeriesAt G p 0 ∧
      (∀ k : ℕ, Even k → ∀ u : E, p k (fun _ => u) = 0) ∧
      (fun u => G u - fderiv ℝ G 0 u - p 3 (fun _ => u)) =O[𝓝 0] fun u : E => ‖u‖ ^ 5 := by
  obtain ⟨p, hp⟩ := ha
  have he := odd_even_coefficient hp ho
  have h1 : ∀ u : E, p 1 (fun _ => u) = fderiv ℝ G 0 u := by
    intro u
    have hc : Fin.snoc (0 : Fin 0 → E) u = (fun _ : Fin 1 => u) := by
      ext i
      fin_cases i
      rfl
    have ht := congrArg (fun T : E →L[ℝ] F => T u) hp.fderiv_eq.symm
    rw [continuousMultilinearCurryFin1_apply] at ht
    exact (congrArg (p 1) hc.symm).trans ht
  have hs : ∀ u : E, p.partialSum 5 u = fderiv ℝ G 0 u + p 3 (fun _ => u) := by
    intro u
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, hp.coeff_zero, h0, h1,
      he 2 (by norm_num) u, he 4 (by norm_num) u]
  refine ⟨p, hp, he, ?_⟩
  simpa only [zero_add, hs, sub_add_eq_sub_sub] using hp.isBigO_sub_partialSum_pow 5
end Odd

variable {L κ r : ℝ} [Fact (0 < L)]

/-- The genuine chart has a collective fifth-order remainder relative to its
actual cubic Taylor coefficient. This theorem does not identify that coefficient
with the printed g_3. -/
theorem source_fifth_order (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ (G : L2T L → Seq)
      (p : FormalMultilinearSeries ℝ (L2T L) Seq),
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧ HasFPowerSeriesAt G p 0 ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n) ∧
      G 0 = 0 ∧ fderiv ℝ G 0 = (fourierR L : L2T L →L[ℝ] Seq) ∧
      (∀ k : ℕ, Even k → ∀ u : L2T L, p k (fun _ => u) = 0) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖G u - fourierR L u - p 3 (fun _ => u)‖ ≤ C * ‖u‖ ^ 5) ∧
      (∀ u ∈ ball (0 : L2T L) ρ,
        ‖fderiv ℝ G u - (fourierR L : L2T L →L[ℝ] Seq)‖ ≤ C * ‖u‖ ^ 2) := by
  obtain ⟨ρ0, hρ0, C0, hC0, G, hG, hGe, hG0, hF, hodd, hder⟩ :=
    source_collective_derivative hL hκ hr hr2
  have ho : (fun u => G (-u)) =ᶠ[𝓝 0] fun u => -G u :=
    eventuallyEq_of_mem (ball_mem_nhds (0 : L2T L) hρ0) hodd
  obtain ⟨p, hp, heven, hb⟩ := odd_fifth_order (hG 0 (mem_ball_self hρ0)) hG0 ho
  obtain ⟨C1, hbound⟩ := isBigO_iff.mp hb
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp hbound
  let ρ := min ρ0 ε
  have hρ : 0 < ρ := lt_min hρ0 hε
  have hm : ball (0 : L2T L) ρ ⊆ ball 0 ρ0 := ball_subset_ball (min_le_left _ _)
  have hmε : ball (0 : L2T L) ρ ⊆ ball 0 ε := ball_subset_ball (min_le_right _ _)
  let C := max C0 (max C1 0)
  have hC : 0 ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨ρ, hρ, C, hC, G, p, hG.mono hm, hp, fun u hu n => hGe u (hm hu) n,
    hG0, hF, heven, ?_, ?_⟩
  · intro u hu
    have h := hεb (mem_ball.mp (hmε hu))
    rw [hF] at h
    have hn : 0 ≤ ‖u‖ ^ 5 := by positivity
    calc ‖G u - fourierR L u - p 3 (fun _ => u)‖ ≤ C1 * ‖u‖ ^ 5 := by
          simpa [Real.norm_eq_abs, abs_of_nonneg hn] using h
      _ ≤ C * ‖u‖ ^ 5 := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hn
  · intro u hu
    exact (hder u (hm hu)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

end QuantumNLS.Local006.FifthF
#print axioms QuantumNLS.Local006.FifthF.odd_even_coefficient
#print axioms QuantumNLS.Local006.FifthF.odd_fifth_order
#print axioms QuantumNLS.Local006.FifthF.source_fifth_order

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.FifthF." ||
        n.toString.startsWith "_private.QuantumNLS.Local006FifthF" then
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
  Lean.logInfo m!"Local006FifthF audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
