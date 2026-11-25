import QuantumNLS.Local006PhysicalRegroupI
import QuantumNLS.Local006G3Fourier

/-! Identify the total-degree sums with the genuine diagonal Taylor
coefficients of the actual chart, by uniqueness on every real line. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped BigOperators ENNReal
namespace QuantumNLS.Local006.TaylorBindingI
open QuantumNLS.PhysicalTensor QuantumNLS.Local002Bridge QuantumNLS.Local005
  QuantumNLS.Local005.SourceC QuantumNLS.Local005.SourceD
  QuantumNLS.Local006.CoefficientLiftE QuantumNLS.Local006.SequenceAlgebraE
  QuantumNLS.Local006.SequenceEvaluationE QuantumNLS.Local006.PositiveMajorantG
  QuantumNLS.Local006.SourceMajorantG QuantumNLS.Local006.NormalizedMajorantG
  QuantumNLS.Local006.SolidMajorantH QuantumNLS.Local006.SourceBindingH
  QuantumNLS.Local006.BinomialBindingH QuantumNLS.Local006.NormalizedBindingH
  QuantumNLS.Local006.WordExpansionI QuantumNLS.Local006.DegreeRegroupI
  QuantumNLS.Local006.PhysicalRegroupI QuantumNLS.Local006.CollectiveF
  QuantumNLS.ResetFreeResolventLOCAL001 QuantumNLS.ResetFreeResolventLOCAL001.CompletionB

variable {L r κ : ℝ} [Fact (0 < L)]

lemma actualCoeff_real_smul (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (kind : WordKind) (u : ScalarInterval L) (d : ℕ) (t : ℝ) :
    actualCoeff hL hκ hr hs kind (t • u) d = (t : ℂ)^(d+1) • actualCoeff hL hκ hr hs kind u d := by
  apply matrix_ext
  intro n i j
  rw [matrix_smul, Matrix.smul_apply,
    (actualCoeff_spec hL hκ hr hs kind (t • u) d).1,
    (actualCoeff_spec hL hκ hr hs kind u d).1]
  unfold coefficient
  rw [orderedSourceWord_repeat, orderedSourceWord_repeat, sourceWord_real_smul, map_smul]

lemma mul_smul_pair (c d : ℂ) (a b : Mixed) : mul (c • a) (d • b) = (c*d) • mul a b := by
  apply matrix_ext
  intro n i j
  simp only [matrix_mul, matrix_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

lemma powerTerm_scaled (a a' : ℕ → Mixed) (t : ℂ)
    (h : ∀ d, a' d = t^(d+1) • a d) (j : ℕ) (z : PowerIndex j) :
    powerTerm a' j z = t^(powerDegree j z) • powerTerm a j z := by
  induction j with
  | zero => simp [powerTerm, powerDegree]
  | succ j ih =>
    simp only [powerTerm, powerDegree, h, ih, mul_smul_pair, pow_add]

lemma physicalCoefficient_real_smul (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) (u : ScalarInterval L) (t : ℝ) (d : ℕ) :
    physicalCoefficient hL hκ hr hs (t • u) d = (t : ℂ)^d • physicalCoefficient hL hκ hr hs u d := by
  unfold physicalCoefficient degreeCoefficient
  rw [← tsum_const_smul'']
  apply tsum_congr
  intro w
  have hp := powerTerm_scaled _ _ (t : ℂ)
    (actualCoeff_real_smul hL hκ hr hs .projection u · t)
  have hk := actualCoeff_real_smul hL hκ hr hs .moment u w.1.2.1.2 t
  dsimp only [weightedTerm, rawTerm]
  rw [hp, hp, hk, mul_smul_pair, mul_smul_pair, smul_smul, smul_smul]
  congr 1
  rw [← pow_add, ← pow_add]
  change weight w.1.1 * (t : ℂ)^totalDegree w.1 = (t : ℂ)^d * weight w.1.1
  rw [w.2, mul_comm]

section Uniqueness
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma diagonal_of_line_series {G : E → F} {p : FormalMultilinearSeries ℝ E F}
    (hp : HasFPowerSeriesAt G p 0) (u : E) (c : ℕ → F)
    (hc : ∀ᶠ t : ℝ in 𝓝 0, HasSum (fun d => t^d • c d) (G (t • u))) :
    ∀ d, p d (fun _ => u) = c d := by
  let line : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight u
  let q : FormalMultilinearSeries ℝ ℝ F := fun d => ContinuousMultilinearMap.mkPiRing ℝ (Fin d) (c d)
  have hq : HasFPowerSeriesAt (fun t : ℝ => G (t • u)) q 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    simpa only [zero_add, FormalMultilinearSeries.coeff, q,
      ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Pi.one_apply, one_pow, one_smul] using hc
  have hp0 : HasFPowerSeriesAt G p (line 0) := by simpa [line] using hp
  have hp' : HasFPowerSeriesAt (G ∘ line) (p.compContinuousLinearMap line) 0 := hp0.compContinuousLinearMap
  have he := hp'.eq_formalMultilinearSeries hq
  intro d
  have hd := congrArg (fun q : FormalMultilinearSeries ℝ ℝ F => q d (fun _ => 1)) he
  simpa [FormalMultilinearSeries.compContinuousLinearMap, line, q,
    ContinuousMultilinearMap.mkPiRing_apply] using hd
end Uniqueness

/-- The regrouped physical series gives every genuine diagonal Taylor
coefficient. Uniqueness is applied on real lines, with convergence proved
from the full physical norm rather than finite-support inputs. -/
theorem actual_taylor_coefficients (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) {ρ : ℝ} (hρ : 0 < ρ)
    {G : L2T L → Seq} {p : FormalMultilinearSeries ℝ (L2T L) Seq}
    (hp : HasFPowerSeriesAt G p 0)
    (hGe : ∀ x ∈ ball (0 : L2T L) ρ, ∀ n, G x n = scalarG L κ r x n) :
    ∀ u d, p d (fun _ => u) =
      factor L κ • (physicalCoefficient hL hκ hr hs (toInterval L u) d).2.2 := by
  obtain ⟨ρn, hρn, hn⟩ := actual_normalized_majorant hL hκ hr hs
  intro u
  let C := wordConstant L r κ
  have hC : 0 < C := wordConstant_pos hL hr hκ
  let δ := min (min ρ ρn) (1 / (8 * C))
  have hδ : 0 < δ := lt_min (lt_min hρ hρn) (by positivity)
  have ht : ∀ᶠ t : ℝ in 𝓝 0, ‖t • u‖ < δ := by
    have hc : Tendsto (fun t : ℝ => t • u) (𝓝 0) (𝓝 (0 : L2T L)) := by
      have h0 : Tendsto (fun t : ℝ => t • u) (𝓝 0) (𝓝 ((0 : ℝ) • u)) :=
        (continuous_id.smul continuous_const).tendsto 0
      rwa [zero_smul] at h0
    filter_upwards [hc (ball_mem_nhds (0 : L2T L) hδ)] with t ht
    exact mem_ball_zero_iff.mp ht
  apply diagonal_of_line_series hp u _
  filter_upwards [ht] with t ht
  have htu : t • u ∈ ball (0 : L2T L) ρ :=
    mem_ball_zero_iff.mpr (ht.trans_le ((min_le_left _ _).trans (min_le_left _ _)))
  have htn : ‖toInterval L (t • u)‖ < ρn := by
    rw [norm_toInterval]
    exact ht.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hq : C * ‖toInterval L (t • u)‖ < 1/8 := by
    rw [norm_toInterval]
    have hh := mul_lt_mul_of_pos_left (ht.trans_le (min_le_right _ _)) hC
    have he : C * (1 / (8 * C)) = 1/8 := by field_simp
    rwa [he] at hh
  have hrp := physical_regroup hL hκ hr hs (toInterval L (t • u)) hq
  have he := (hn (toInterval L (t • u)) htn).2.2.2.2.2
  have hchart : G (t • u) = factor L κ • (normalizedSource hL hκ hr hs (toInterval L (t • u))).2.2 := by
    apply lp.ext
    funext n
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hGe _ htu n,
      QuantumNLS.Local006.ChartMajorantH.scalarG_normalized hL hκ hr hs (t • u) he n]
    rfl
  let extract : Mixed →L[ℂ] Seq := (ContinuousLinearMap.snd ℂ Seq2 Seq2).comp
    (ContinuousLinearMap.snd ℂ (SeqInf × SeqInf) (Seq2 × Seq2))
  have hsum := (extract.hasSum hrp.2.2.2.1).const_smul (factor L κ)
  change HasSum (fun d => factor L κ • (physicalCoefficient hL hκ hr hs (toInterval L (t • u)) d).2.2)
    (factor L κ • (normalizedSource hL hκ hr hs (toInterval L (t • u))).2.2) at hsum
  rw [← hchart] at hsum
  apply hsum.congr_fun
  intro d
  have hti : (toInterval L (t • u) : ScalarInterval L) =
      t • (toInterval L u : ScalarInterval L) := (toIntervalR L).map_smul t u
  rw [hti, physicalCoefficient_real_smul]
  let x : Seq := (physicalCoefficient hL hκ hr hs (toInterval L u) d).2.2
  change (t^d : ℝ) • (factor L κ • x) = factor L κ • ((t : ℂ)^d • x)
  rw [smul_comm (t^d) (factor L κ)]
  congr 1
  rw [← Complex.ofReal_pow]
  exact (algebraMap_smul ℂ (t^d) x).symm

/-- The genuine Taylor series of the actual chart is dominated degree by
degree by the absolutely convergent positive Fourier-path series, on a full
ball. The cubic coefficient is supplied by the independently authored G3 module.
The absolute derivative-kernel clauses are not asserted here. -/
theorem actual_taylor_majorant_stage (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hs : r < spacing L / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ (G : L2T L → Seq) (p : FormalMultilinearSeries ℝ (L2T L) Seq),
      AnalyticOnNhd ℝ G (ball 0 ρ) ∧ HasFPowerSeriesAt G p 0 ∧
      (∀ u ∈ ball (0 : L2T L) ρ, ∀ n, G u n = scalarG L κ r u n) ∧
      (∀ u d, p d (fun _ => u) =
        factor L κ • (physicalCoefficient hL hκ hr hs (toInterval L u) d).2.2) ∧
      (∀ u n, p 3 (fun _ => u) n = QuantumNLS.Local006.G3Fourier.printedG3 L κ
        (fun m => QuantumNLS.Fourier.fourierL2 L u m) n) ∧
      ∀ u ∈ ball (0 : L2T L) ρ,
        Summable (fun d => ‖physicalEnvelope hL hκ hr hs (toInterval L u) d‖) ∧
        HasSum (fun d => p d (fun _ => u)) (G u) ∧
        ∀ d, Positive (physicalEnvelope hL hκ hr hs (toInterval L u) d) ∧
          ∀ n, ‖p d (fun _ => u) n‖ ≤ ‖factor L κ‖ *
            (matrix (physicalEnvelope hL hκ hr hs (toInterval L u) d) n 1 0).re := by
  obtain ⟨ρ, hρ, G, hG, hg⟩ := chart_degree_regroup hL hκ hr hs
  obtain ⟨p, hp⟩ := hG 0 (mem_ball_self hρ)
  have hGe := fun u hu => (hg u hu).1
  have hid := actual_taylor_coefficients hL hκ hr hs hρ hp hGe
  have hr2 : r < 2 * Real.pi / L := by convert hs using 1; unfold spacing; ring
  refine ⟨ρ, hρ, G, p, hG, hp, hGe, hid,
    QuantumNLS.Local006.G3Fourier.p3_eq_printed_g3 hL hκ hr hr2 hρ hp hGe, ?_⟩
  intro u hu
  have h := hg u hu
  refine ⟨h.2.1, h.2.2.2.2.1.congr_fun (fun d => hid u d), ?_⟩
  intro d
  have hd := h.2.2.2.2.2 d
  refine ⟨hd.1, ?_⟩
  intro n
  rw [hid u d, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hd.2 n 1 0) (norm_nonneg _)

end QuantumNLS.Local006.TaylorBindingI
#print axioms QuantumNLS.Local006.TaylorBindingI.physicalCoefficient_real_smul
#print axioms QuantumNLS.Local006.TaylorBindingI.diagonal_of_line_series

#print axioms QuantumNLS.Local006.TaylorBindingI.actual_taylor_coefficients

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local006.TaylorBindingI." ||
        n.toString.startsWith "_private.QuantumNLS.Local006TaylorBindingI" then
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
  Lean.logInfo m!"Local006TaylorBindingI audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."

#print axioms QuantumNLS.Local006.TaylorBindingI.actual_taylor_majorant_stage
