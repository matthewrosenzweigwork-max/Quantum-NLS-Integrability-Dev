import QuantumNLS.Ext006PhysicalNormBridge

/-! Continuity of the literal physical pair exponential in each degree.
All maps below use the frozen adjoint-defined creation block. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
open scoped InnerProductSpace
open Filter Topology
namespace QuantumNLS.Ext006PhysicalContinuityR38a
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Ext005PairSector Ext006PhysicalExponentialTerms
open Ext006PhysicalNormBridge.CreationFormula
variable {L : ℝ} [Fact (0 < L)]

lemma continuous_htmul {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] :
    Continuous (fun z : E × F => htmul (𝕜 := ℂ) z.1 z.2) :=
  (UniformSpace.Completion.continuous_coe _).comp
    (TensorProduct.mkL ℂ E F).continuous₂

/-- Joint continuity includes variation of the completed pair tensor. -/
theorem continuous_creation (n : ℕ) :
    Continuous (fun z : HN L 2 × HN L n => creation z.1 n z.2) := by
  let f : HN L 2 × HN L n → HilbertTensor ℂ
      (HilbertTensorPower ℂ (L2T L) 2) (HilbertTensorPower ℂ (L2T L) n) :=
    fun z => htmul (z.1 : HilbertTensorPower ℂ (L2T L) 2)
      (z.2 : HilbertTensorPower ℂ (L2T L) n)
  have hf : Continuous f :=
    (continuous_htmul (E := HilbertTensorPower ℂ (L2T L) 2)
      (F := HilbertTensorPower ℂ (L2T L) n)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hg : Continuous (fun z => (splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n).symm
      (f z)) := (splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n).symm.continuous.comp hf
  have hp : Continuous (fun z => (physSector L (2+n)).orthogonalProjectionOnto
      ((splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n).symm (f z))) :=
    (physSector L (2+n)).orthogonalProjectionOnto.continuous.comp hg
  have h := hp.const_smul (Real.sqrt (((n : ℝ)+1)*((n : ℝ)+2)) : ℂ)
  convert h using 1
  funext z
  exact creation_eq_projection z.1 n z.2

/-- Every exact homogeneous exponential term depends continuously on b. -/
theorem continuous_term (n : ℕ) : Continuous (fun b : HN L 2 => term b n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    simp_rw [term_step]
    have hg : Continuous (fun b : HN L 2 => (b, term b n)) :=
      continuous_id.prodMk ih
    have h : Continuous (fun b : HN L 2 => creation b (2*n) (term b n)) := by
      exact Continuous.comp
        (g := fun z : HN L 2 × HN L (2*n) => creation z.1 (2*n) z.2)
        (f := fun b : HN L 2 => (b, term b n))
        (continuous_creation (L := L) (2*n)) hg
    have h' : Continuous (fun b : HN L 2 => stepScalar n • creation b (2*n) (term b n)) :=
      h.const_smul (stepScalar n)
    exact (sectorCast (L := L) (by omega : 2+2*n = 2*(n+1))).continuous.comp h'

theorem continuous_fockTerm (n : ℕ) : Continuous (fun b : HN L 2 => fockTerm b n) :=
  (inclusion L (2*n)).continuous.comp (continuous_term (L := L) n)

theorem continuous_truncation (M : ℕ) :
    Continuous (fun b : HN L 2 => truncation b M) :=
  continuous_finsetSum _ (fun n _ => continuous_fockTerm (L := L) n)

/-- Norm approximation of a completed pair tensor gives approximation of
the actual operator exponential in EVERY fixed degree, without a small-HS bound. -/
theorem term_tendsto {I : Type*} {l : Filter I} {b : I → HN L 2} {v : HN L 2}
    (hb : Tendsto b l (𝓝 v)) (n : ℕ) :
    Tendsto (fun i => term (b i) n) l (𝓝 (term v n)) :=
  (continuous_term (L := L) n).continuousAt.tendsto.comp hb

theorem truncation_tendsto {I : Type*} {l : Filter I} {b : I → HN L 2} {v : HN L 2}
    (hb : Tendsto b l (𝓝 v)) (M : ℕ) :
    Tendsto (fun i => truncation (b i) M) l (𝓝 (truncation v M)) :=
  (continuous_truncation (L := L) M).continuousAt.tendsto.comp hb

end QuantumNLS.Ext006PhysicalContinuityR38a

#print axioms QuantumNLS.Ext006PhysicalContinuityR38a.continuous_creation

#print axioms QuantumNLS.Ext006PhysicalContinuityR38a.continuous_term

#print axioms QuantumNLS.Ext006PhysicalContinuityR38a.continuous_fockTerm

#print axioms QuantumNLS.Ext006PhysicalContinuityR38a.continuous_truncation

#print axioms QuantumNLS.Ext006PhysicalContinuityR38a.term_tendsto

#print axioms QuantumNLS.Ext006PhysicalContinuityR38a.truncation_tendsto

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006PhysicalContinuityR38a." then
      pending := pending.push n
      roots := roots + 1
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
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round38a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
