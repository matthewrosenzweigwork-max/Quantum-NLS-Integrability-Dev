import QuantumNLS.RB01Bridge
import QuantumNLS.Local006CompressionE

/-! LOCAL-006: assemble the actual normalized lower-left entries into an
analytic l2 map on a full profile ball, using the frozen RB01 tail and the
accepted LOCAL-003 entries. No collective estimate is inferred by summing
uniform coordinate bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local006.CollectiveF
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Bridge
  QuantumNLS.PhysicalTensor QuantumNLS.Local003Analytic QuantumNLS.Local003Isometry
  QuantumNLS.Local006.CompressionE

abbrev Seq := lp (fun _ : ℤ => ℂ) 2
variable {L κ r : ℝ} [Fact (0 < L)]

def factor (L κ : ℝ) : ℂ :=
  ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ))

def scalarG (L : ℝ) [Fact (0 < L)] (κ r : ℝ) (u : L2T L) (n : ℤ) : ℂ :=
  factor L κ * Bf L κ (circleRep u) n r (vec2 1 0) 1

/-- The frozen exact compression identity transported to DEF-001 profiles. -/
theorem profile_compression (hL : 0 < L) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (u : L2T L) (hu : ‖u‖ < goodRadius κ L r) (n : ℤ) :
    Bf L κ (circleRep u) n r - (pm L n : ℂ) • (1 : E2 →L[ℂ] E2) =
      invSqrtM (compressionMatrix L κ (circleRep u) n r) *
        (ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ (circleRep u) n r ∘L embed L n) *
        invSqrtM (compressionMatrix L κ (circleRep u) n r) := by
  have hui : ‖toInterval L u‖ < goodRadius κ L r := by rw [norm_toInterval]; exact hu
  have h := reduced_matrix_compression hL hr hr2 n (toInterval L u)
    (ctx_of_ball hL hr hr2 n (toInterval L u) hui)
  have he := toInterval_coe L u
  unfold momentMatrix at h
  rw [QuantumNLS.Local003Odd.Bf_congr he,
    QuantumNLS.RB01Bridge.compressionMatrix_congr he,
    QuantumNLS.RB01Bridge.dressedIntegral_congr he] at h
  exact h

lemma head_mem_iff (N : ℕ) (n : ℤ) :
    n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ↔ |(n : ℝ)| ≤ (N : ℝ) := by
  rw [Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨a, b⟩
    constructor
    · exact_mod_cast a
    · exact_mod_cast b
  · rintro ⟨a, b⟩
    constructor
    · exact_mod_cast a
    · exact_mod_cast b

/-- All coordinates, including the finitely many labels omitted by the RB01
construction, form one real analytic sequence-valued map on a common full ball.
The coordinate error estimate below is retained solely to identify the first
jet; its constant is not asserted to be a collective norm bound. -/
theorem exists_chart (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∃ G : L2T L → Seq,
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n) ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
        ‖G u n - QuantumNLS.Fourier.fourierL2 L u n‖ ≤ C * ‖u‖ ^ 3) ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, SmallCompression L κ (circleRep u) n r) := by
  obtain ⟨ρb, hρb, C, hC, hb⟩ := QuantumNLS.Local003Final.reset_uniform_reduction_profile hL hκ hr hr2
  choose a b ha hb hsc hmat hspec hg hcub hder using hb
  obtain ⟨N, ρt, hρt, bf, hbf, htail⟩ := QuantumNLS.RB01Bridge.tail_entries_profile (κ := κ) hL hr hr2 (0 : L2T L)
  let ρ : ℝ := min (min ρb ρt) (goodRadius κ L r)
  have hρ : 0 < ρ := lt_min (lt_min hρb hρt) (goodRadius_pos κ L r)
  have hmb : ball (0 : L2T L) ρ ⊆ ball 0 ρb := ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _))
  have hmt : ball (0 : L2T L) ρ ⊆ ball 0 ρt := ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))
  have hmg : ∀ u ∈ ball (0 : L2T L) ρ, ‖u‖ < goodRadius κ L r := fun u hu =>
    (mem_ball_zero_iff.mp hu).trans_le (min_le_right _ _)
  have hbe : ∀ n u, u ∈ ball (0 : L2T L) ρ → b n u = Bf L κ (circleRep u) n r (vec2 1 0) 1 := by
    intro n u hu
    have e := hmat n u (hmb hu) (hsc n u (hmb hu)) (vec2 1 0)
    rw [reducedMatrix2_eq] at e
    have e' := congrArg (fun w : E2 => w 1) e
    simpa [vec2] using e'.symm
  let H : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let G : L2T L → Seq := fun u => factor L κ • bf (vec2 1 0) 1 u +
    ∑ n ∈ H, lp.single 2 n (factor L κ * b n u)
  have hGa : AnalyticOnNhd ℝ G (ball 0 ρ) := by
    refine AnalyticOnNhd.add (f := fun u => factor L κ • bf (vec2 1 0) 1 u) ?_ ?_
    · exact ((hbf (vec2 1 0) 1).mono hmt).const_smul (c := factor L κ)
    · apply Finset.analyticOnNhd_fun_sum
      intro n hn u hu
      exact ((lp.singleContinuousLinearMap ℝ (fun _ : ℤ => ℂ) 2 n).analyticAt _).comp (hg n u (hmb hu))
  have hGe : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = scalarG L κ r u n := by
    intro u hu n
    have hsum : (∑ m ∈ H, lp.single 2 m (factor L κ * b m u) : Seq) n =
        if n ∈ H then factor L κ * b n u else 0 := by
      simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
      exact Finset.sum_pi_single _ _ _
    change (factor L κ • bf (vec2 1 0) 1 u + ∑ m ∈ H, lp.single 2 m (factor L κ * b m u) : Seq) n = _
    rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hsum]
    by_cases hn : n ∈ H
    · rw [if_pos hn, (htail u (hmt hu) n (vec2 1 0) 1).2 ((head_mem_iff N n).mp hn), mul_zero, zero_add]
      rw [scalarG, hbe n u hu]
    · have hn' : (N : ℝ) < |(n : ℝ)| := lt_of_not_ge (fun hh => hn ((head_mem_iff N n).mpr hh))
      rw [if_neg hn, add_zero, (htail u (hmt hu) n (vec2 1 0) 1).1 hn' |>.2.2]
      have e := congrArg (fun T : E2 →L[ℂ] E2 => T (vec2 1 0) 1)
        (profile_compression hL hr hr2 u (hmg u hu) n)
      have ee : Bf L κ (circleRep u) n r (vec2 1 0) 1 =
          ((invSqrtM (compressionMatrix L κ (circleRep u) n r) *
            (ContinuousLinearMap.adjoint (embed L n) ∘L dressedIntegral L κ (circleRep u) n r ∘L embed L n) *
            invSqrtM (compressionMatrix L κ (circleRep u) n r)) (vec2 1 0)) 1 := by
        simpa [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, vec2] using e
      exact congrArg (fun z => factor L κ * z) ee.symm
  refine ⟨ρ, hρ, C, hC, G, hGa, hGe, ?_, fun u hu n => hsc n u (hmb hu)⟩
  intro u hu n
  rw [hGe u hu n, scalarG, ← hbe n u hu, QuantumNLS.Fourier.fourierL2_apply]
  exact hcub n u (hmb hu)

end QuantumNLS.Local006.CollectiveF
#print axioms QuantumNLS.Local006.CollectiveF.profile_compression
#print axioms QuantumNLS.Local006.CollectiveF.exists_chart

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.CollectiveF." ||
        n.toString.startsWith "_private.QuantumNLS.Local006CollectiveF" then
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
  Lean.logInfo m!"Local006CollectiveF audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
