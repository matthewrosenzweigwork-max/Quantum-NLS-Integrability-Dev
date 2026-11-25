import QuantumNLS.Def024CubicPersistence

/-! DEF-024 r=2 D3: the Fourier cubic is a continuous real polynomial.
The continuous trilinear map is constructed from f04_triple, not postulated. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
namespace QuantumNLS.Def024CubicSmoothNonlinearity
variable {L : ℝ} [Fact (0 < L)]

/-- Reconstruction at order s>=1 into continuous functions. -/
def reconstruct {s : ℝ} (hs : 1 ≤ s) : h04 L s →L[ℂ] C(AddCircle L, ℂ) :=
  S1.comp (h04_mono L hs)

@[simp] lemma reconstruct_apply {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) (x : AddCircle L) :
    reconstruct hs a x = seriesRep L a.val x := rfl

/-- Coefficients are a linear map on continuous functions. -/
def coefficients : C(AddCircle L, ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f := coeff L f
  map_add' f g := funext fun n => coeff_add_cont f.continuous g.continuous n
  map_smul' c f := funext fun n => coeff_const_mul L c f n

/-- The unbundled Fourier trilinear product. -/
def tripleSeq {s : ℝ} (hs : 1 ≤ s) :
    MultilinearMap ℂ (fun _ : Fin 3 => h04 L s) (ℤ → ℂ) :=
  (coefficients (L := L)).compMultilinearMap
    ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin 3) C(AddCircle L, ℂ)).toMultilinearMap.compLinearMap
      (fun _ => (reconstruct hs).toLinearMap))

lemma tripleSeq_apply {s : ℝ} (hs : 1 ≤ s) (v : Fin 3 → h04 L s) (n : ℤ) :
    tripleSeq hs v n = coeff L (fun x =>
      seriesRep L (v 0).val x * seriesRep L (v 1).val x * seriesRep L (v 2).val x) n := by
  simp [tripleSeq, coefficients, Fin.prod_univ_succ, mul_assoc]
  congr 1

lemma tripleSeq_mem {s : ℝ} (hs : 1 ≤ s) (v : Fin 3 → h04 L s) :
    tripleSeq hs v ∈ carrier (f04W L s) := by
  change Mem04 L s (tripleSeq hs v)
  simpa only [funext (tripleSeq_apply hs v)] using
    (f04_triple hs (h04_mem L s (v 0)) (h04_mem L s (v 1)) (h04_mem L s (v 2))).1

/-- Algebraic trilinear product with the actual Sobolev carrier. -/
def tripleLinear {s : ℝ} (hs : 1 ≤ s) :
    MultilinearMap ℂ (fun _ : Fin 3 => h04 L s) (h04 L s) :=
  (tripleSeq hs).codRestrict (carrier (f04W L s)) (tripleSeq_mem hs)

lemma triple_bound {s : ℝ} (hs : 1 ≤ s) (v : Fin 3 → h04 L s) :
    ‖tripleLinear hs v‖ ≤ (3 * (3:ℝ) ^ (s-1) * cL L ^ 2) * ∏ i, ‖v i‖ := by
  have hb := (f04_triple hs (h04_mem L s (v 0)) (h04_mem L s (v 1))
    (h04_mem L s (v 2))).2
  have hn : ‖tripleLinear hs v‖ = Real.sqrt (f04NormSq L s
      (coeff L (fun x => seriesRep L (v 0).val x * seriesRep L (v 1).val x *
        seriesRep L (v 2).val x))) := by
    rw [norm_eq_sqrt]
    congr 2
    exact funext (tripleSeq_apply hs v)
  rw [hn]
  have hb' := norm_one_le hs (v 0)
  have hc' := norm_one_le hs (v 1)
  have hd' := norm_one_le hs (v 2)
  rw [← norm_eq_sqrt s (v 0), ← norm_eq_sqrt s (v 1), ← norm_eq_sqrt s (v 2)] at hb
  have hpos : 0 ≤ (3:ℝ) ^ (s-1) * cL L ^ 2 := by positivity
  calc _ ≤ (3:ℝ) ^ (s-1) * cL L ^ 2 *
      (‖v 0‖ * ‖v 1‖ * ‖v 2‖ + ‖v 0‖ * ‖v 1‖ * ‖v 2‖ + ‖v 0‖ * ‖v 1‖ * ‖v 2‖) :=
        hb.trans (by gcongr)
    _ = _ := by simp [Fin.prod_univ_succ]; ring

/-- The continuous trilinear product, bounded by the proved tame estimate. -/
def triple {s : ℝ} (hs : 1 ≤ s) :
    ContinuousMultilinearMap ℂ (fun _ : Fin 3 => h04 L s) (h04 L s) :=
  (tripleLinear hs).mkContinuous (3 * (3:ℝ) ^ (s-1) * cL L ^ 2) (triple_bound hs)

/-- Conjugation of the physical field, a bounded REAL linear map. -/
def conjugate (s : ℝ) : h04 L s →L[ℝ] h04 L s :=
  LinearMap.mkContinuous
    { toFun a := WSeq.mk _ (cjSeq a.val) (mem04_cjSeq (h04_mem L s a))
      map_add' a b := WSeq.ext (by
        funext n
        change conj (a.val (-n) + b.val (-n)) = conj (a.val (-n)) + conj (b.val (-n))
        exact map_add _ _ _)
      map_smul' r a := WSeq.ext (by
        funext n
        change conj ((r:ℂ) * a.val (-n)) = (r:ℂ) * conj (a.val (-n))
        simp only [map_mul, Complex.conj_ofReal]) }
    1 (fun a => by
      rw [one_mul, norm_eq_sqrt, norm_eq_sqrt]
      change Real.sqrt (f04NormSq L s (cjSeq a.val)) ≤ Real.sqrt (f04NormSq L s a.val)
      rw [f04NormSq_cjSeq])

@[simp] lemma conjugate_val (s : ℝ) (a : h04 L s) :
    (conjugate s a).val = cjSeq a.val := rfl

lemma Fh_eq_triple {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) :
    Fh hs a = triple hs ![a, conjugate s a, a] := by
  apply WSeq.ext
  funext n
  change coeff L (nlRep L a.val) n = tripleSeq hs ![a, conjugate s a, a] n
  rw [tripleSeq_apply]
  change coeff L (nlRep L a.val) n = coeff L (fun x =>
    seriesRep L a.val x * seriesRep L (cjSeq a.val) x * seriesRep L a.val x) n
  congr 1
  exact funext (nlRep_eq a.val)

/-- The cubic map is smooth over the reals at every order s>=1. -/
theorem contDiff_Fh {s : ℝ} (hs : 1 ≤ s) : ContDiff ℝ ∞ (Fh (L := L) hs) := by
  have hv : ContDiff ℝ ∞ (fun a : h04 L s => ![a, conjugate s a, a]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    · exact contDiff_id
    · exact (conjugate s).contDiff
    · exact contDiff_id
  have h := ((triple hs).restrictScalars ℝ).contDiff.comp hv
  have he : Fh (L := L) hs = fun a => triple hs ![a, conjugate s a, a] :=
    funext (Fh_eq_triple hs)
  rw [he]
  exact h

/-- The vector field H^s -> H^{s-2} is a smooth map with a proved Frechet derivative. -/
theorem contDiff_Gder {s : ℝ} (hs : 1 ≤ s) (κ : ℝ) :
    ContDiff ℝ ∞ (Gder (L := L) hs κ) := by
  exact (((lapOp s).restrictScalars ℝ).contDiff.const_smul Complex.I).neg.sub
    ((((ι2 s).restrictScalars ℝ).contDiff.comp (contDiff_Fh hs)).const_smul (2*Complex.I*κ))

#print axioms triple_bound
#print axioms triple
#print axioms conjugate
#print axioms Fh_eq_triple
#print axioms contDiff_Fh
#print axioms contDiff_Gder
end QuantumNLS.Def024CubicSmoothNonlinearity

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Def024CubicSmoothNonlinearity." ||
        n.toString.startsWith "_private.QuantumNLS.Def024CubicSmoothNonlinearity." then
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
