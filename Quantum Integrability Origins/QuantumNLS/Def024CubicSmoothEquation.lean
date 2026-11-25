import QuantumNLS.Def024CubicSmoothJoint
import QuantumNLS.Def024CubicClassical

/-! DEF-024 r=2 D3 Equation: actual global Sobolev solution reconstruction. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
open QuantumNLS.ClassicalCharges QuantumNLS.ChargeEnergy QuantumNLS.HierarchyFlow
open QuantumNLS.Def024CubicSmoothData QuantumNLS.Def024CubicSmoothEmbedding
open QuantumNLS.Def024CubicSmoothNonlinearity QuantumNLS.Def024CubicSmoothTime
open QuantumNLS.Def024CubicSmoothEvaluation QuantumNLS.Def024CubicGradient
open QuantumNLS.Def024CubicSmoothJoint
namespace QuantumNLS.Def024CubicSmoothEquation
variable {L : ℝ} [Fact (0 < L)]

lemma ev_smul {s : ℝ} (hs : 1 ≤ s) (x : ℝ) (c : ℂ) (a : h04 L s) :
    ev hs x (c • a) = c * ev hs x a :=
  seriesRep_smul' c a.val (x : AddCircle L)

/-- Reconstruction of the cubic in H^1 is pointwise. -/
lemma ev_Fh (a : h04 L 1) (x : ℝ) :
    ev (le_refl (1:ℝ)) x (Fh (le_refl (1:ℝ)) a) =
      ((‖ev (le_refl (1:ℝ)) x a‖^2 : ℝ) : ℂ) * ev (le_refl (1:ℝ)) x a := by
  have hcont := continuous_nlRep (L := L) (summable_norm_h1 a)
  have hmem : Mem04 L 1 (coeff L (nlRep L a.val)) := (Fh (le_refl (1:ℝ)) a).summable
  have he := (Continuous.ae_eq_iff_eq volume hcont
    (continuous_seriesRep (summable_norm_of_mem04 le_rfl hmem))).mp
      (ae_eq_seriesRep (memLp_of_continuous hcont) hmem)
  exact congrFun he.symm (x : AddCircle L)

lemma ev_lap (a : h04 L 3) (x : ℝ) :
    ev (le_refl (1:ℝ)) x (transport (by norm_num : (3:ℝ)-2=1) (lapOp 3 a)) = - profileJet a 2 x := by
  have hv : (transport (L := L) (by norm_num : (3:ℝ)-2=1) (lapOp 3 a)).val =
      fun n => ((freq L n ^ 2 : ℝ) : ℂ)*a.val n := by
    rw [transport_val]
    exact funext (lapOp_val 3 a)
  rw [ev_apply, hv]
  unfold profileJet seriesRep
  rw [← tsum_neg]
  apply tsum_congr
  intro n
  simp only [jet, mul_pow, Complex.I_sq, Complex.ofReal_pow]
  ring

lemma profile_second {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ}
    (hκ : 0 ≤ κ) (t x : ℝ) :
    deriv (deriv (profile hu κ t)) x = profileJet (trajectory hu (by norm_num : 1 ≤ (3:ℝ)) κ t) 2 x := by
  let a := trajectory hu (by norm_num : 1 ≤ (3:ℝ)) κ t
  have he : profile hu κ t = profileJet a 0 := by
    funext y
    rw [profileJet_zero]
    exact profile_at_order hu hκ (by norm_num : 1 ≤ (3:ℝ)) t y
  have h0 : deriv (profileJet a 0) = profileJet a 1 :=
    funext fun y => (hasDerivAt_profileJet (s := 3) 0 (by norm_num) a y).deriv
  have h1 : deriv (profileJet a 1) = profileJet a 2 :=
    funext fun y => (hasDerivAt_profileJet (s := 3) 1 (by norm_num) a y).deriv
  rw [he, h0, h1]

lemma profile_Gder {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ}
    (hκ : 0 ≤ κ) (t x : ℝ) :
    ev (L := L) (le_refl (1:ℝ)) x
      (transport (by norm_num : (3:ℝ)-2=1)
        (Gder (by norm_num : 1 ≤ (3:ℝ)) κ (trajectory hu (by norm_num : 1 ≤ (3:ℝ)) κ t))) =
      -Complex.I * cubicGrad κ (profile hu κ t) x := by
  let Q := transport (L := L) (by norm_num : (3:ℝ)-2=1)
  let a := trajectory hu (by norm_num : 1 ≤ (3:ℝ)) κ t
  have hp : Q (ι2 3 (Fh (by norm_num : 1 ≤ (3:ℝ)) a)) =
      Fh (le_refl (1:ℝ)) (h04_mono L (by norm_num : (1:ℝ) ≤ 3) a) :=
    WSeq.ext (by simp only [Q, transport_val]; rfl)
  change ev (le_refl (1:ℝ)) x
    (Q (-(Complex.I • lapOp 3 a) - (2*Complex.I*κ) • ι2 3 (Fh (by norm_num) a))) =
      -Complex.I * cubicGrad κ (profile hu κ t) x
  rw [map_sub, map_neg, map_smul, map_smul, map_sub, map_neg, ev_smul, ev_smul, hp, ev_Fh]
  rw [show Q (lapOp 3 a) = transport (by norm_num : (3:ℝ)-2=1) (lapOp 3 a) from rfl, ev_lap]
  rw [← profile_second hu hκ t x]
  have hv : ev (le_refl (1:ℝ)) x (h04_mono L (by norm_num : (1:ℝ) ≤ 3) a) = profile hu κ t x :=
    (profile_at_order hu hκ (by norm_num : 1 ≤ (3:ℝ)) t x).symm
  rw [hv]
  simp only [cubicGrad, smul_eq_mul]
  push_cast
  ring



/-- The strong mild identity implies the classical equation at every point. -/
theorem profile_equation {u : ℝ → ℂ} (hu : SmoothPeriodic L u) {κ : ℝ}
    (hκ : 0 ≤ κ) (t x : ℝ) :
    HasDerivAt (fun r => profile hu κ r x) (-Complex.I * cubicGrad κ (profile hu κ t) x) t := by
  have hm := trajectory_mild hu (by norm_num : 1 ≤ (3:ℝ)) hκ
  have hd := (mild_C1 hm).2.2.2.1 t (by simp)
  let Q := transport (L := L) (by norm_num : (3:ℝ)-2=1)
  have hd' := (((ev (L := L) (le_refl (1:ℝ)) x).comp (Q.restrictScalars ℝ)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hd
  have he : (fun r => ev (L := L) (le_refl (1:ℝ)) x
      (Q (ι2 3 (trajectory hu (by norm_num : 1 ≤ (3:ℝ)) κ r)))) = fun r => profile hu κ r x := by
    funext r
    change seriesRep L (Q (ι2 3 (trajectory hu (by norm_num : 1 ≤ (3:ℝ)) κ r))).val _ = _
    rw [show (Q (ι2 3 (trajectory hu (by norm_num : 1 ≤ (3:ℝ)) κ r))).val =
      (trajectory hu (by norm_num : 1 ≤ (3:ℝ)) κ r).val by
        simp only [Q, transport_val]; rfl]
    exact (profile_at_order hu hκ (by norm_num : 1 ≤ (3:ℝ)) r x).symm
  change HasDerivAt (fun r => ev (L := L) (le_refl (1:ℝ)) x
    (Q (ι2 3 (trajectory hu (by norm_num : 1 ≤ (3:ℝ)) κ r)))) _ t at hd'
  rw [he] at hd'
  exact hd'.congr_deriv (profile_Gder hu hκ t x)

#print axioms ev_smul
#print axioms ev_Fh
#print axioms ev_lap
#print axioms profile_second
#print axioms profile_Gder
#print axioms profile_equation
end QuantumNLS.Def024CubicSmoothEquation

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def024CubicSmoothEquation." ||
        n.toString.startsWith "_private.QuantumNLS.Def024CubicSmoothEquation." then
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
