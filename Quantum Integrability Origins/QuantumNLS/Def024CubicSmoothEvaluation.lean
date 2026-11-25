import QuantumNLS.Def024CubicSmoothEmbedding
import QuantumNLS.Def024CubicSmoothNonlinearity

/-! Operator-valued Fourier reconstruction: finite Sobolev loss gives joint smooth evaluation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Topology ContDiff
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
open QuantumNLS.Def024CubicSmoothEmbedding QuantumNLS.Def024CubicSmoothNonlinearity
namespace QuantumNLS.Def024CubicSmoothEvaluation
variable {L : ℝ} [Fact (0 < L)]

/-- Uniform convergence of every spatial jet at the sharp Sobolev threshold. -/
theorem uniform_profileJet {s : ℝ} (j : ℕ) (hs : (j:ℝ)+1/2<s) (a : h04 L s) :
    TendstoUniformly (fun F : Finset ℤ => fun x : ℝ =>
      ∑ n ∈ F, jet (L := L) a.val j n * mode L n (x : AddCircle L)) (profileJet a j) atTop :=
  tendstoUniformly_tsum ((summable_jet j hs a).mul_right ((Real.sqrt L)⁻¹))
    (fun n x => by rw [norm_mul, norm_mode])

lemma freq_power_le (j : ℕ) (n : ℤ) :
    |freq L n| ^ j  ≤  (1+freq L n ^ 2) ^ ((j:ℝ)/2) := by
  have hb : 0  ≤  1+freq L n ^ 2 := by positivity
  have h : |freq L n|  ≤  Real.sqrt (1+freq L n ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt hb]
    linarith
  have hpow := pow_le_pow_left₀ (abs_nonneg _) h j
  convert hpow using 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((1+freq L n^2)^(1/2:ℝ)) j,
    ← Real.rpow_mul hb]
  congr 1; ring

/-- The jth spatial Fourier multiplier loses j Sobolev orders and has norm at most one. -/
lemma jet_weight (s : ℝ) (j : ℕ) (n : ℤ) (z : ℂ) :
    f04Weight L (s-j) n * ‖jet (L := L) (fun _ => z) j n‖ ^ 2  ≤ 
      f04Weight L s n * ‖z‖ ^ 2 := by
  rw [norm_jet, mul_pow, ← pow_mul, show j*2=2*j by omega, pow_mul, sq_abs]
  have hp := pow_le_pow_left₀ (sq_nonneg (freq L n))
    (by linarith : freq L n ^ 2  ≤  1+freq L n ^ 2) j
  calc _  ≤  f04Weight L (s-j) n * ((1+freq L n ^ 2)^j * ‖z‖^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (sq_nonneg ‖z‖))
        (f04Weight_pos L (s-j) n).le
    _ = _ := by
      rw [f04Weight, f04Weight, ← Real.rpow_natCast (1+freq L n^2) j, ← mul_assoc,
        ← Real.rpow_add (by positivity)]
      congr 2; ring

def jetMap (s : ℝ) (j : ℕ) : h04 L s →L[ℂ] h04 L (s-j) :=
  LinearMap.mkContinuous
    { toFun a := WSeq.mk _ (jet (L := L) a.val j)
        (Summable.of_nonneg_of_le (fun n =>
          mul_nonneg ((f04W L (s-j)).pos n).le (sq_nonneg _))
          (fun n => jet_weight s j n (a.val n)) a.summable)
      map_add' a b := WSeq.ext (by
        funext n
        change (Complex.I * (freq L n : ℂ))^j * (a.val n+b.val n) = _
        change _ = (Complex.I * (freq L n : ℂ))^j*a.val n + (Complex.I * (freq L n : ℂ))^j*b.val n
        ring)
      map_smul' c a := WSeq.ext (by
        funext n
        change (Complex.I * (freq L n : ℂ))^j * (c*a.val n) = c*((Complex.I * (freq L n : ℂ))^j*a.val n)
        ring) }
    1 (fun a => by
      rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_tsum, norm_sq_eq_tsum]
      exact Summable.tsum_le_tsum (fun n => jet_weight s j n (a.val n)) (WSeq.summable _) a.summable)

@[simp] lemma jetMap_val (s : ℝ) (j : ℕ) (a : h04 L s) :
    (jetMap s j a).val = jet (L := L) a.val j := rfl

lemma norm_jetMap_le (s : ℝ) (j : ℕ) (a : h04 L s) : ‖jetMap s j a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using (jetMap s j).le_of_opNorm_le
    (LinearMap.mkContinuous_norm_le _ (by norm_num) _) a

lemma iteratedDeriv_profileJet {s : ℝ} (a : h04 L s) (j k : ℕ)
    (hs : (j:ℝ)+(k:ℝ)+1/2<s) :
    iteratedDeriv k (profileJet a j) = profileJet a (j+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih (by push_cast at hs; linarith)]
    have hd := hasDerivAt_profileJet (j+k) (by push_cast at hs ⊢; linarith) a
    simpa only [Nat.add_assoc] using funext (fun x => (hd x).deriv)

/-- Uniform classical-jet bound at any s>=j+1. -/
lemma norm_profileJet_le {s : ℝ} (a : h04 L s) (j : ℕ) (hs : (j:ℝ)+1 ≤ s) (x : ℝ) :
    ‖profileJet a j x‖  ≤  cL L * ‖a‖ := by
  let b : h04 L 1 := h04_mono L (by linarith : 1 ≤ s-j) (jetMap s j a)
  have he : profileJet a j x = S1 b (x : AddCircle L) := rfl
  rw [he]
  calc ‖S1 b (x : AddCircle L)‖  ≤  ‖S1 b‖ := ContinuousMap.norm_coe_le_norm _ _
    _  ≤  cL L * ‖b‖ := by
      exact (S1 (L := L)).le_of_opNorm_le
        (LinearMap.mkContinuous_norm_le _ (cL_nonneg L) _) b
    _  ≤  cL L * ‖a‖ := mul_le_mul_of_nonneg_left
      ((norm_h04_mono_le L _ _).trans (norm_jetMap_le s j a)) (cL_nonneg L)

/-- The mth classical spatial jet as a bounded C(T_L)-valued Fourier map. -/
def spatialEmbedding (m : ℕ) : h04 L ((m:ℝ)+1) →L[ℂ] C(AddCircle L, ℂ) :=
  S1.comp ((h04_mono L (by linarith : 1 ≤ (m:ℝ)+1-(m:ℝ))).comp (jetMap ((m:ℝ)+1) m))

@[simp] lemma spatialEmbedding_apply (m : ℕ) (a : h04 L ((m:ℝ)+1)) (x : ℝ) :
    spatialEmbedding m a (x : AddCircle L) = profileJet a m x := rfl

lemma norm_spatialEmbedding (m : ℕ) (a : h04 L ((m:ℝ)+1)) :
    ‖spatialEmbedding m a‖  ≤  cL L * ‖a‖ := by
  have h := (S1 (L := L)).le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ (cL_nonneg L) _)
    (h04_mono L (by linarith : 1 ≤ (m:ℝ)+1-(m:ℝ)) (jetMap ((m:ℝ)+1) m a))
  exact h.trans (mul_le_mul_of_nonneg_left
    ((norm_h04_mono_le L _ _).trans (norm_jetMap_le _ _ a)) (cL_nonneg L))

/-- Norm summability of Fourier evaluation operators and their spatial derivatives. -/
lemma summable_reciprocal {s : ℝ} (j : ℕ) (hs : (j:ℝ)+1<s) :
    Summable (fun n : ℤ => |freq L n| ^ j * (Real.sqrt (f04Weight L s n))⁻¹) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (summable_bracket (L := L) (q := (s-j)/2) (by linarith))
  intro n
  calc _  ≤  (1+freq L n ^ 2) ^ ((j:ℝ)/2) * (Real.sqrt (f04Weight L s n))⁻¹ :=
      mul_le_mul_of_nonneg_right (freq_power_le j n) (by positivity)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, f04Weight, ← Real.rpow_mul (by positivity),
        ← Real.rpow_neg (by positivity), ← Real.rpow_add (by positivity)]
      congr 1; ring

lemma norm_coefL (s : ℝ) (n : ℤ) :
    ‖coefL (L := L) s n‖  ≤  (Real.sqrt (f04Weight L s n))⁻¹ := by
  apply LinearMap.mkContinuous_norm_le
  positivity

/-- Classical spatial derivative as a bounded map H^s -> H^{s-1}. -/
def spatial (s : ℝ) : h04 L s →L[ℂ] h04 L (s-1) :=
  (h04_mono L (by norm_num : s-1 ≤ s-(1:ℕ))).comp (jetMap s 1)

@[simp] lemma spatial_val (s : ℝ) (a : h04 L s) (n : ℤ) :
    (spatial s a).val n = (Complex.I*(freq L n : ℂ))*a.val n := by
  change jet (L := L) a.val 1 n = _
  simp only [jet, pow_one]

/-- Evaluation after Sobolev reconstruction. -/
def ev {s : ℝ} (hs : 1  ≤  s) (x : ℝ) : h04 L s →L[ℝ] ℂ :=
  ((ContinuousMap.evalCLM (R := ℂ) (x : AddCircle L)).comp (reconstruct hs)).restrictScalars ℝ

@[simp] lemma ev_apply {s : ℝ} (hs : 1  ≤  s) (x : ℝ) (a : h04 L s) :
    ev hs x a = seriesRep L a.val (x : AddCircle L) := rfl

/-- Operator series used to justify differentiation in operator norm. -/
def term (s : ℝ) (n : ℤ) (x : ℝ) : h04 L s →L[ℝ] ℂ :=
  mode L n (x : AddCircle L) • (coefL s n).restrictScalars ℝ

lemma summable_term {s : ℝ} (hs : 1<s) (x : ℝ) : Summable (fun n => term (L := L) s n x) := by
  apply Summable.of_norm_bounded ((summable_reciprocal (L := L) 0 (by simpa using hs)).mul_left ((Real.sqrt L)⁻¹))
  intro n
  simp only [term, norm_smul, norm_mode, ContinuousLinearMap.norm_restrictScalars]
  simpa using mul_le_mul_of_nonneg_left (norm_coefL (L := L) s n) (by positivity : 0 ≤ (Real.sqrt L)⁻¹)

lemma ev_eq_tsum {s : ℝ} (hs : 1<s) (x : ℝ) :
    ev (le_of_lt hs) x = ∑' n, term (L := L) s n x := by
  ext a
  have h := (ContinuousLinearMap.apply ℝ ℂ a).map_tsum (summable_term hs x)
  rw [ContinuousLinearMap.apply_apply] at h
  rw [h]
  change (∑' n, a.val n * mode L n (x : AddCircle L)) =
    ∑' n, mode L n (x : AddCircle L) * a.val n
  apply tsum_congr
  intro n
  ring

def dterm (s : ℝ) (n : ℤ) (x : ℝ) : h04 L s →L[ℝ] ℂ :=
  ((Complex.I*(freq L n : ℂ))*mode L n (x : AddCircle L)) •
    (coefL s n).restrictScalars ℝ

lemma dterm_bound (s : ℝ) (n : ℤ) (x : ℝ) :
    ‖dterm (L := L) s n x‖ ≤
      (Real.sqrt L)⁻¹ * (|freq L n| * (Real.sqrt (f04Weight L s n))⁻¹) := by
  dsimp [dterm]
  rw [norm_smul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, norm_mode, ContinuousLinearMap.norm_restrictScalars]
  calc (|freq L n| * (Real.sqrt L)⁻¹) * ‖coefL s n‖ ≤
      (|freq L n| * (Real.sqrt L)⁻¹) * (Real.sqrt (f04Weight L s n))⁻¹ :=
        mul_le_mul_of_nonneg_left (norm_coefL s n) (by positivity)
    _ = _ := by ring

lemma summable_dterm {s : ℝ} (hs : 2<s) (x : ℝ) :
    Summable (fun n => dterm (L := L) s n x) := by
  have hb := (summable_reciprocal (L := L) (s := s) 1 (by norm_num; linarith)).mul_left ((Real.sqrt L)⁻¹)
  simp only [pow_one] at hb
  exact Summable.of_norm_bounded hb (fun n => dterm_bound s n x)

lemma hasDerivAt_term_sum {s : ℝ} (hs : 2<s) (x : ℝ) :
    HasDerivAt (fun z => ∑' n, term (L := L) s n z) (∑' n, dterm (L := L) s n x) x := by
  have hb := (summable_reciprocal (L := L) (s := s) 1 (by norm_num; linarith)).mul_left ((Real.sqrt L)⁻¹)
  simp only [pow_one] at hb
  exact hasDerivAt_tsum hb
    (fun n y => (hasDerivAt_mode (L := L) n y).smul_const ((coefL s n).restrictScalars ℝ))
    (fun n y => dterm_bound s n y) (summable_term (by linarith : 1<s) 0) x

lemma dterm_apply (s : ℝ) (n : ℤ) (x : ℝ) (a : h04 L s) :
    dterm (L := L) s n x a =
      ((Complex.I*(freq L n : ℂ))*mode L n (x : AddCircle L))*a.val n := by
  simp only [dterm, smul_apply, ContinuousLinearMap.coe_restrictScalars', coefL_apply, smul_eq_mul]

lemma ev_spatial_apply {s : ℝ} (hs : 2<s) (x : ℝ) (a : h04 L s) :
    ev (by linarith : 1 ≤ s-1) x (spatial s a) =
      ∑' n, ((Complex.I*(freq L n : ℂ))*a.val n) * mode L n (x : AddCircle L) := by
  rw [ev_apply]
  have hv : (spatial s a).val = fun n => (Complex.I*(freq L n : ℂ))*a.val n :=
    funext (spatial_val s a)
  rw [hv]
  rfl

lemma derivative_series {s : ℝ} (hs : 2<s) (x : ℝ) :
    (∑' n, dterm (L := L) s n x) =
      (ev (by linarith : 1 ≤ s-1) x).comp ((spatial s).restrictScalars ℝ) := by
  apply ContinuousLinearMap.ext
  intro a
  have hh := (ContinuousLinearMap.apply ℝ ℂ a).map_tsum (summable_dterm hs x)
  simp only [ContinuousLinearMap.apply_apply] at hh
  rw [hh, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', ev_spatial_apply hs]
  apply tsum_congr
  intro n
  rw [dterm_apply]
  ring

lemma hasDerivAt_ev {s : ℝ} (hs : 2<s) (x : ℝ) :
    HasDerivAt (ev (L := L) (by linarith : 1 ≤ s))
      ((ev (by linarith : 1 ≤ s-1) x).comp ((spatial s).restrictScalars ℝ)) x := by
  have h := hasDerivAt_term_sum (L := L) hs x
  have he : (fun y => ∑' n, term (L := L) s n y) = ev (by linarith : 1 ≤ s) :=
    funext fun y => (ev_eq_tsum (by linarith : 1<s) y).symm
  rw [he] at h
  exact h.congr_deriv (derivative_series hs x)

/-- k spatial derivatives of the evaluation operator cost any s>k+1.
Composing this with a strong time curve proves joint C^k without a separate-smoothness shortcut. -/
theorem contDiff_ev (k : ℕ) {s : ℝ} (hs : (k:ℝ)+1<s) :
    ContDiff ℝ k (ev (L := L) (by linarith : 1 ≤ s)) := by
  induction k generalizing s with
  | zero =>
    apply contDiff_zero.mpr
    have h : Continuous (fun x => ∑' n, term (L := L) s n x) := by
      refine continuous_tsum (f := fun n x => term (L := L) s n x)
        (u := fun n => (Real.sqrt L)⁻¹ * (Real.sqrt (f04Weight L s n))⁻¹) ?_ ?_ ?_
      · intro n
        exact ((continuous_iff_continuousAt.mpr fun x =>
          (hasDerivAt_mode (L := L) n x).continuousAt).smul continuous_const)
      · simpa only [pow_zero, one_mul] using
          (summable_reciprocal (L := L) (s := s) 0 (by simpa using hs)).mul_left ((Real.sqrt L)⁻¹)
      · intro n x
        simp only [term, norm_smul, norm_mode, ContinuousLinearMap.norm_restrictScalars]
        exact mul_le_mul_of_nonneg_left (norm_coefL (L := L) s n) (by positivity)
    exact h.congr (fun x => (ev_eq_tsum (by simpa using hs) x).symm)
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiff_succ_iff_deriv.mpr
    have hsk : (k:ℝ)+2<s := by push_cast at hs; linarith
    have hs2 : 2<s := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have hd := hasDerivAt_ev (L := L) hs2
    refine ⟨fun x => (hd x).differentiableAt, by simp, ?_⟩
    have he : deriv (ev (L := L) (by linarith : 1 ≤ s)) =
        fun x => (ev (by linarith : 1 ≤ s-1) x).comp ((spatial s).restrictScalars ℝ) := funext fun x => (hd x).deriv
    rw [he]
    exact (ih (by push_cast at hs; linarith : (k:ℝ)+1<s-1)).clm_comp contDiff_const

#print axioms spatialEmbedding
#print axioms norm_spatialEmbedding
#print axioms uniform_profileJet
#print axioms jet_weight
#print axioms jetMap
#print axioms iteratedDeriv_profileJet
#print axioms norm_profileJet_le
#print axioms summable_reciprocal
#print axioms spatial
#print axioms ev_eq_tsum
#print axioms dterm_bound
#print axioms hasDerivAt_term_sum
#print axioms dterm_apply
#print axioms ev_spatial_apply
#print axioms derivative_series
#print axioms hasDerivAt_ev
#print axioms contDiff_ev
end QuantumNLS.Def024CubicSmoothEvaluation

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def024CubicSmoothEvaluation." ||
        n.toString.startsWith "_private.QuantumNLS.Def024CubicSmoothEvaluation." then
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
