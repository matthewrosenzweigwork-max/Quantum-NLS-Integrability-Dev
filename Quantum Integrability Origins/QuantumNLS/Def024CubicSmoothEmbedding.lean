import QuantumNLS.Def024CubicPersistence
import QuantumNLS.ChargeEnergy

/-! DEF-024 r=2, D3: sharp absolute Fourier summability and classical reconstruction.
All series use the mass-L orthonormal modes and F04 bracket weights. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
namespace QuantumNLS.Def024CubicSmoothEmbedding
variable {L : ℝ} [Fact (0 < L)]

/-- The reciprocal bracket is summable at exactly the range needed below. -/
lemma summable_bracket {q : ℝ} (hq : 1/2 < q) :
    Summable (fun n : ℤ => (1 + freq L n ^ 2) ^ (-q)) := by
  let α : ℝ := 2 * Real.pi / L
  have hα : 0 < α := div_pos (mul_pos (by norm_num) Real.pi_pos) Fact.out
  have hq0 : 0 < q := by linarith
  have hsum := (Real.summable_abs_int_rpow (by linarith : 1 < 2*q)).mul_left (α ^ (-2*q))
  refine Summable.of_norm_bounded_eventually hsum ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn0 : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hf : freq L n = α * n := by dsimp [freq, α]; ring
  have hbase : 0 < freq L n ^ 2 := by rw [hf]; positivity
  rw [Real.norm_of_nonneg (by positivity)]
  calc (1 + freq L n ^ 2) ^ (-q) ≤ (freq L n ^ 2) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by linarith)
    _ = α ^ (-2*q) * |(n : ℝ)| ^ (-2*q) := by
      rw [hf, mul_pow, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul hα.le,
        ← sq_abs (n : ℝ), ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      congr 1 <;> congr 1 <;> ring
    _ = _ := by congr 2; ring

/-- Sharp weighted l1 embedding: s > j+1/2. -/
lemma summable_freq_pow {s : ℝ} (j : ℕ) (hs : (j : ℝ) + 1/2 < s)
    (a : h04 L s) : Summable (fun n : ℤ => |freq L n| ^ j * ‖a.val n‖) := by
  let f : ℤ → ℝ := fun n => |freq L n| ^ j / Real.sqrt (f04Weight L s n)
  let g : ℤ → ℝ := fun n => Real.sqrt (f04Weight L s n) * ‖a.val n‖
  have hw (n : ℤ) : 0 < Real.sqrt (f04Weight L s n) :=
    Real.sqrt_pos.mpr (f04Weight_pos L s n)
  have hf : Summable (fun n => f n ^ (2 : ℝ)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ (summable_bracket (L := L) (q := s-j) (by linarith))
    intro n
    have hb : 0 < 1 + freq L n ^ 2 := by positivity
    have hp : (freq L n ^ 2) ^ j ≤ (1 + freq L n ^ 2) ^ j :=
      pow_le_pow_left₀ (sq_nonneg _) (by linarith) j
    dsimp [f]
    rw [Real.rpow_two, div_pow, Real.sq_sqrt (f04Weight_pos L s n).le,
      ← pow_mul, show j * 2 = 2*j by omega, pow_mul, sq_abs]
    calc (freq L n ^ 2) ^ j / f04Weight L s n ≤
        (1 + freq L n ^ 2) ^ j / f04Weight L s n :=
          div_le_div_of_nonneg_right hp (f04Weight_pos L s n).le
      _ = (1 + freq L n ^ 2) ^ (-(s-(j : ℝ))) := by
        rw [f04Weight, ← Real.rpow_natCast, ← Real.rpow_sub hb]
        congr 1; ring
  have hg : Summable (fun n => g n ^ (2 : ℝ)) := by
    convert a.summable using 1
    funext n
    dsimp [g]
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (f04Weight_pos L s n).le]
    rfl
  obtain ⟨h, _⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two (fun n => by dsimp [f]; positivity)
    (fun n => by dsimp [g]; positivity) hf hg
  exact h.congr (fun n => by dsimp [f,g]; field_simp [(hw n).ne'])

lemma summable_natFrequency_pow {s : ℝ} (j : ℕ) (hs : (j : ℝ) + 1/2 < s)
    (a : h04 L s) : Summable (fun n : ℤ => |(n : ℝ)| ^ j * ‖a.val n‖) := by
  have hc : 0 < L / (2*Real.pi) := div_pos Fact.out (by positivity)
  convert (summable_freq_pow j hs a).mul_left ((L/(2*Real.pi)) ^ j) using 1
  funext n
  rw [← mul_assoc, ← mul_pow]
  congr 2
  rw [freq, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_pos (show 0 < L from Fact.out)]
  field_simp [(show 0 < L from Fact.out).ne']

/-- Fourier coefficient of the jth spatial derivative. -/
def jet (a : ℤ → ℂ) (j : ℕ) (n : ℤ) : ℂ :=
  (Complex.I * (freq L n : ℂ)) ^ j * a n

lemma norm_jet (a : ℤ → ℂ) (j : ℕ) (n : ℤ) :
    ‖jet (L := L) a j n‖ = |freq L n| ^ j * ‖a n‖ := by
  simp [jet, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

lemma summable_jet {s : ℝ} (j : ℕ) (hs : (j : ℝ)+1/2 < s) (a : h04 L s) :
    Summable (fun n => ‖jet (L := L) a.val j n‖) := by
  simpa only [norm_jet] using summable_freq_pow j hs a

/-- The pointwise reconstructed spatial jet, with its actual uniform Fourier series. -/
def profileJet {s : ℝ} (a : h04 L s) (j : ℕ) (x : ℝ) : ℂ :=
  seriesRep L (jet (L := L) a.val j) (x : AddCircle L)

lemma profileJet_zero {s : ℝ} (a : h04 L s) (x : ℝ) :
    profileJet a 0 x = seriesRep L a.val (x : AddCircle L) := by
  change seriesRep L (fun n => (Complex.I * (freq L n : ℂ)) ^ 0 * a.val n) _ = _
  simp only [pow_zero, one_mul]

lemma continuous_profileJet {s : ℝ} (j : ℕ) (hs : (j : ℝ)+1/2 < s) (a : h04 L s) :
    Continuous (profileJet a j) :=
  (continuous_seriesRep (summable_jet j hs a)).comp continuous_quotient_mk'

lemma hasDerivAt_mode (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => mode L n (y : AddCircle L))
      ((Complex.I * (freq L n : ℂ)) * mode L n (x : AddCircle L)) x := by
  have hd := ((hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * (freq L n : ℂ))).cexp
  have hd' := hd.const_mul (((Real.sqrt L)⁻¹ : ℝ) : ℂ)
  convert hd' using 1
  · funext y; rw [mode_coe]; congr 1; dsimp [freq]; push_cast; ring
  · rw [mode_coe]; dsimp [freq]; push_cast; ring

/-- Termwise differentiation, justified by a summable uniform bound on the derivatives. -/
theorem hasDerivAt_profileJet {s : ℝ} (j : ℕ) (hs : (j : ℝ)+1+1/2 < s)
    (a : h04 L s) (x : ℝ) :
    HasDerivAt (profileJet a j) (profileJet a (j+1) x) x := by
  have hj : (j : ℝ)+1/2 < s := by linarith
  have hj' : ((j+1 : ℕ) : ℝ)+1/2 < s := by exact_mod_cast hs
  have hsum := (summable_freq_pow (j+1) hj' a).mul_right ((Real.sqrt L)⁻¹)
  have hder (n : ℤ) (y : ℝ) :
      HasDerivAt (fun z : ℝ => jet (L := L) a.val j n * mode L n (z : AddCircle L))
        (jet (L := L) a.val (j+1) n * mode L n (y : AddCircle L)) y := by
    convert (hasDerivAt_mode (L := L) n y).const_mul (jet (L := L) a.val j n) using 1
    simp only [jet, pow_succ]; ring
  have hb (n : ℤ) (y : ℝ) :
      ‖jet (L := L) a.val (j+1) n * mode L n (y : AddCircle L)‖ ≤
        |freq L n| ^ (j+1) * ‖a.val n‖ * (Real.sqrt L)⁻¹ := by
    rw [norm_mul, norm_jet, norm_mode]
  have hstart : Summable (fun n => jet (L := L) a.val j n * mode L n (0 : AddCircle L)) :=
    Summable.of_norm_bounded ((summable_jet j hj a).mul_right ((Real.sqrt L)⁻¹))
      (fun n => by rw [norm_mul, norm_mode])
  exact hasDerivAt_tsum hsum hder hb hstart x

/-- Sharp Sobolev-to-C^k embedding with pointwise Fourier reconstruction. -/
theorem contDiff_profileJet {s : ℝ} (j k : ℕ) (hs : (j : ℝ)+(k : ℝ)+1/2 < s)
    (a : h04 L s) : ContDiff ℝ k (profileJet a j) := by
  induction k generalizing j with
  | zero => exact contDiff_zero.mpr (continuous_profileJet j (by simpa using hs) a)
  | succ k ih =>
    have hd := hasDerivAt_profileJet j (by push_cast at hs; linarith : (j:ℝ)+1+1/2<s) a
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiff_succ_iff_deriv.mpr
    refine ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
    have he : deriv (profileJet a j) = profileJet a (j+1) := funext fun x => (hd x).deriv
    rw [he]
    exact ih (j+1) (by push_cast at hs ⊢; linarith)

#print axioms summable_bracket
#print axioms summable_freq_pow
#print axioms summable_natFrequency_pow
#print axioms hasDerivAt_profileJet
#print axioms contDiff_profileJet
end QuantumNLS.Def024CubicSmoothEmbedding

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def024CubicSmoothEmbedding." ||
        n.toString.startsWith "_private.QuantumNLS.Def024CubicSmoothEmbedding." then
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
