import QuantumNLS.SmoothScalarMomentsPrerequisite
import QuantumNLS.SmoothScalarMomentsAsymptotic
import QuantumNLS.SmoothScalarMomentsFormal
import QuantumNLS.RiccatiChargeIdent

/-! R-275B7656 (moments:thm:moments), one named physical theorem.
The entire printed R-3FEAD88B is the single named missing-prerequisite
hypothesis. All value estimates and fixed-point existence below use frozen
RiccatiExpansions; the measure is the existing full-mass quantum measure.
No moment, coefficient reality or scalar expansion is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology
namespace QuantumNLS.SmoothScalarMomentsPhysical
open QuantumNLS.ClassicalCharges QuantumNLS.WeakDerivatives
open QuantumNLS.SmoothScalarMomentsPrerequisite QuantumNLS.SmoothScalarMomentsBinding
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE2
open QuantumNLS.RiccatiSobolevE2b QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiSobolevS
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiPointwiseDisc QuantumNLS.RiccatiPicardBall
open QuantumNLS.RiccatiMonodromy QuantumNLS.RiccatiRemainder
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.FullMass QuantumNLS.CauchyUniqueness
open QuantumNLS.SmoothScalarMomentsCauchy QuantumNLS.SmoothScalarMomentsAsymptotic

variable {L : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

/-- The L² element of the given smooth periodic field, independent of every
Riccati order, radius, or branch choice. -/
def smoothL2 (hf : SmoothPeriodic L f) : QuantumNLS.PhysicalTensor.L2T L :=
  ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ
    (liftC hf.smooth.continuous hf.periodic)

lemma fieldMap_eq_smooth {a : ℝ} (ha : 1 / 2 < a) (hf : SmoothPeriodic L f)
    (x : Ell2) (hx : physRep L a x = f) :
    fieldMap L a (by linarith) x = smoothL2 hf := by
  obtain ⟨g, _, hae, hpt, _⟩ := QuantumNLS.RiccatiPointwiseRep.fieldMap_rep L ha x
  have he : g = liftC hf.smooth.continuous hf.periodic := by
    funext t
    induction t using QuotientAddGroup.induction_on with
    | H t =>
      rw [hpt]
      change physRep L a x t = _
      rw [hx, liftC_coe]
  apply Lp.ext
  have hs := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ)
    (volume : Measure (AddCircle L)) (liftC hf.smooth.continuous hf.periodic)
  apply hae.trans
  rw [he]
  exact hs.symm

omit [Fact (0 < L)] in
lemma sum_charges (κ : ℝ) (M : ℕ) (z : ℂ) :
    (∑ n ∈ Finset.Icc 1 M, charge L κ f n * z⁻¹ ^ n) =
      series (fun r => charge L κ f (r + 1)) M z := by
  induction M with
  | zero => simp [series]
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), series_succ, ih]

omit [Fact (0 < L)] in
/-- Adapter from the native author's frozen physical recursion to the
existing ClassicalCharges sequence. No coefficient identity is assumed. -/
lemma physical_coefficients {a S : ℝ} {M : ℕ} (hL : 0 < L) (ha : 1 / 2 < a)
    (haS : a + (M : ℝ) + 1 ≤ S) (hM : 1 ≤ M) (κ : ℝ) (u : Ell2)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (hrep : physRep L a (lowT L a S u) = f) :
    ∀ j ∈ Finset.Icc 1 M, modeCoef L a (jEll (lowT L a S u))
      (coeffs L a S κ hL ha D (u, jEll u) j) = charge L κ f j := by
  let W := QuantumNLS.RiccatiChargeIdent.Wc S hL ha κ u (jEll u) D
  obtain ⟨h1, hrec⟩ := QuantumNLS.RiccatiChargeIdent.printed_recursion hL ha haS hM κ
    u (jEll u) D hD
  have he : ∀ n : ℕ, 1 ≤ n → n ≤ M → physRep L a (W n) = vseq κ f n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hnm
      rcases n with _ | n
      · omega
      rcases n with _ | n
      · simpa only [Nat.zero_add, vseq_one] using h1.trans hrep
      · funext t
        change physRep L a (QuantumNLS.RiccatiChargeIdent.Wc S hL ha κ u (jEll u) D (n + 2)) t = _
        rw [hrec n hnm t, vseq_succ, ← neg_mul]
        rw [ih (n + 1) (by omega) (by omega) (by omega)]
        have hs : Finset.Ico 1 (n + 1) = Finset.Icc 1 n := by ext j; simp
        rw [hs, lowT_jEll, physRep_jEll, hrep]
        congr 2
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_Icc.mp hj
        rw [ih j (by omega) (by omega) (by omega),
          ih (n + 1 - j) (by omega) (by omega) (by omega)]
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  change (∫ t in (0 : ℝ)..L, physRep L a (jEll (lowT L a S u)) t * physRep L a (W j) t) = _
  simp_rw [physRep_jEll, hrep, he j hj'.1 hj'.2]
  rfl

/-- Physical inverse-power estimates obtained by binding the frozen Riccati
log/branch theorem to the existing quantum measure. This helper is proved;
it is not a second hypothesis of all_smooth_scalar_moments. -/
theorem physical_expansion (κ : ℝ) (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hRiccati : RiccatiPrintedConclusion L f) :
    Expansion (fun n => cauchyTransform (Mmeas κ (smoothL2 hf)) (height n))
      (fun r => charge L κ f (r + 1)) := by
  intro M hM
  have hL : 0 < L := Fact.out
  have ha : (1 / 2 : ℝ) < 1 := by norm_num
  have hS : (1 : ℝ) + (M : ℝ) + 2 < ((M + 4 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨d⟩ := hRiccati M hM 1 1 ha (by norm_num) (by norm_num) (M + 4) hS
    {κ} (isCompact_singleton) (by simpa using hκ)
  let S : ℝ := (M + 4 : ℕ)
  have haS : 1 + (M : ℝ) + 1 ≤ S := by dsimp [S]; push_cast; linarith
  let β : ℝ := ‖d.base‖ + 1
  have hβ : 0 < β := by dsimp [β]; positivity
  have hu : ‖d.base‖ ≤ β := by dsimp [β]; linarith
  let x := lowT L 1 S d.base
  let U := fieldMap L 1 (by norm_num : (0 : ℝ) ≤ 1) x
  have hU : U = smoothL2 hf := fieldMap_eq_smooth ha hf x d.base_rep
  let B : ℝ := 1 + ‖U‖ ^ 2 + 2 * L * (physK L 1) ^ 2 * β ^ 2
  have hb0 : 0 ≤ 2 * L * (physK L 1) ^ 2 * β ^ 2 := by positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hm : ‖U‖ ^ 2 ≤ B := by dsimp [B]; linarith
  have hb : 2 * L * (physK L 1) ^ 2 * β ^ 2 ≤ B := by dsimp [B]; nlinarith [sq_nonneg ‖U‖]
  let R := max (logR L 1 S M κ β 1) (max (4 * (κ * B)) (Real.log 16 / L))
  let C := L * (physK L 1 * ‖x‖ * (physK L 1 * remC L 1 S M (κ / L) β 1))
  refine ⟨C, R, ?_⟩
  intro n hn
  have hz : 0 < (height n).im := by rw [height_im]; positivity
  have hsec : 1 * ‖height n‖ ≤ (height n).im := by rw [height_norm, height_im, one_mul]
  have hR : logR L 1 S M κ β 1 ≤ ‖height n‖ := (le_max_left _ _).trans hn
  have hhigh : QuantumNLS.RootMeasureComplex.HighHalf L (κ * B) (height n) := by
    constructor
    · rw [height_im, ← height_norm]
      exact (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    · have hh : Real.log 16 / L ≤ ‖height n‖ :=
        (le_max_right _ _).trans ((le_max_right _ _).trans hn)
      rw [div_le_iff₀ hL, height_norm] at hh
      simpa only [height_im, mul_comm] using hh
  have hRa : remR L 1 S M (κ / L) β 1 ≤ ‖height n‖ := (le_max_left _ _).trans hR
  obtain ⟨hex, her⟩ := expansion_a L hL ha haS hM (κ / L) d.base (jEll d.base) β hβ hu
    (by rw [norm_jEll]; exact hu) (derivativeExtension L) (derivativeExtension_spec L) 1 (by norm_num)
    (height n) hz hsec hRa
  obtain ⟨r, hr, hrn⟩ := hex
  have hr' : riccatiT hL ha hz (κ / L) x (jEll x) r = r := by
    simpa only [x, lowT_jEll] using hr
  obtain ⟨hid, _⟩ := physical_log_expansion hL ha haS hM κ hκ d.base β hβ hu
    (derivativeExtension L) (derivativeExtension_spec L) 1 (by norm_num) (height n) hz hsec hR r hr' hrn B hB hm hb hhigh
  let w := coeffs L 1 S κ hL ha (derivativeExtension L) (d.base, jEll d.base)
  have hrem : ‖r - rMsum w (height n)⁻¹ M‖ ≤
      remC L 1 S M (κ / L) β 1 * (‖height n‖ ^ (M + 1))⁻¹ := her r hr hrn
  have hi := integrated_remainder hL ha x r w M (height n) _ hrem
  have hcoef : ∀ j ∈ Finset.Icc 1 M, modeCoef L 1 (jEll x) (w j) = charge L κ f j :=
    physical_coefficients hL ha haS hM κ d.base (derivativeExtension L) (derivativeExtension_spec L) d.base_rep
  have hsum : (∑ j ∈ Finset.Icc 1 M, modeCoef L 1 (jEll x) (w j) * (height n)⁻¹ ^ j) =
      series (fun r => charge L κ f (r + 1)) M (height n) := by
    rw [← sum_charges κ M (height n)]
    exact Finset.sum_congr rfl fun j hj => by rw [hcoef j hj]
  rw [hid, hsum, ← mul_sub, norm_mul, Complex.norm_I, one_mul] at hi
  dsimp only [U, x] at hU
  rw [hU] at hi
  calc _ ≤ L * (physK L 1 * ‖x‖ *
        (physK L 1 * (remC L 1 S M (κ / L) β 1 * (‖height n‖ ^ (M + 1))⁻¹))) := hi
    _ = C * (‖height n‖ ^ (M + 1))⁻¹ := by dsimp [C]; ring

/-- R-275B7656, moments:thm:moments. Every smooth periodic physical field,
with arbitrary mass, has real charges and every absolute moment of its
already constructed full-mass quantum measure, with the printed identities.
The SINGLE named missing prerequisite is the ENTIRE printed R-3FEAD88B.
No coordinate inverse or action-gap comparison is used. -/
theorem all_smooth_scalar_moments (κ : ℝ) (hκ : 0 < κ) (hf : SmoothPeriodic L f)
    (hRiccati : RiccatiPrintedConclusion L f) :
    (∀ j : ℕ, (charge L κ f j).im = 0) ∧
    ∀ r : ℕ, Integrable (fun t : ℝ => |t| ^ r) (Mmeas κ (smoothL2 hf)) ∧
      ((∫ t : ℝ, t ^ r ∂(Mmeas κ (smoothL2 hf)) : ℝ) : ℂ) = charge L κ f (r + 1) := by
  have hre := QuantumNLS.SmoothScalarMomentsFormal.charge_real hκ hf
  refine ⟨hre, ?_⟩
  let c : ℕ → ℝ := fun r => (charge L κ f (r + 1)).re
  have hc : ∀ r, (c r : ℂ) = charge L κ f (r + 1) := fun r => by
    apply Complex.ext <;> simp [c, hre]
  have he := physical_expansion κ hκ hf hRiccati
  have hl := fun r => limits_of_expansion he r
  have hh := QuantumNLS.SmoothScalarMomentsMain.all_moments_of_real_cauchy_expansion
    (Mmeas κ (smoothL2 hf)) c (by simpa only [hc, cauchyTransform] using hl)
  intro r
  refine ⟨(hh r).1, ?_⟩
  calc _ = ∫ t : ℝ, (t : ℂ) ^ r ∂(Mmeas κ (smoothL2 hf)) := by
          rw [← integral_complex_ofReal]
          simp only [Complex.ofReal_pow]
    _ = charge L κ f (r + 1) := (hh r).2.trans (hc r)

#print axioms physical_expansion
#print axioms all_smooth_scalar_moments
end QuantumNLS.SmoothScalarMomentsPhysical

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.SmoothScalarMomentsPhysical." ||
        n.toString.startsWith "_private.QuantumNLS.SmoothScalarMomentsPhysical." then
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
