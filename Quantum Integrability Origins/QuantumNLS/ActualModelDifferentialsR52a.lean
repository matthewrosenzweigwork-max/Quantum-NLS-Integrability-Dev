import QuantumNLS.Def044InterfacesR51a

/-! R-E679E41D: place every fixed charge-window differential in the
same REAL dual H^(2d+4), with a common cutoff and constant for r ≤ d.
Only the accepted R-C5645D32 numerical model bound is used. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.ActualModelDifferentialsR52a
open Def044InterfacesR51a Q07GradientRemovalR24 Q07TailBindingR24
variable {L κ : ℝ} [Fact (0 < L)]

lemma cut_nonnegative (l : ℕ) : 0 ≤ PROP017UniformN.cutSeq L l := by
  unfold PROP017UniformN.cutSeq
  exact div_nonneg (by positivity) (Fact.out : 0 < L).le

/-- Restrict the exact physical real differential along the canonical
Sobolev inclusion; its norm is at most the original norm. -/
theorem restricted_bound (hκ : 0 < κ) (d r : ℕ) (hr : r ≤ d) (B : ℝ)
    {h : ℝ} (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l →
      ∀ u : Sobolev.H02 L (regularity d), ‖u‖ ≤ B →
        DifferentiableAt ℝ (windowError hκ d r hr h l) u ∧
        ‖fderiv ℝ (windowError hκ d r hr h l) u‖ ≤
          C*(PROP017UniformN.cutSeq L l)^(-(1/2 : ℝ)) := by
  obtain ⟨C,hC,l0,hb⟩ := model_bound (L := L) hκ r B hh
  refine ⟨C,hC,l0,?_⟩
  intro l hl u hu
  let J := (Sobolev.H02.mono (L := L) (regularity_mono hr)).restrictScalars ℝ
  let A := ((Q07SobolevModelR24.coordinates (L := L) (regularity_pos r).le).toContinuousLinearEquiv.toContinuousLinearMap).restrictScalars ℝ
  have hJu : ‖J u‖ ≤ B := (Sobolev.H02.norm_mono_le (regularity_mono hr) u).trans hu
  have hAu : ‖A (J u)‖ = ‖J u‖ :=
    (Q07SobolevModelR24.coordinates (regularity_pos r).le).norm_map _
  obtain ⟨hd,hbnd⟩ := hb l hl (A (J u)) (hAu.le.trans hJu)
  have hder := (hd.hasFDerivAt.comp (J u) A.hasFDerivAt).comp u J.hasFDerivAt
  refine ⟨hder.differentiableAt,?_⟩
  change ‖fderiv ℝ ((Q07TailBindingR24.tail (L := L) hκ r h l ∘ A) ∘ J) u‖ ≤ _
  rw [hder.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hC (Real.rpow_nonneg (by
      unfold PROP017UniformN.cutSeq
      exact div_nonneg (by positivity) (Fact.out : 0 < L).le) _))
  intro v
  change ‖(fderiv ℝ (tail (L := L) hκ r h l) (A (J u))) (A (J v))‖ ≤ _
  calc
    _ ≤ ‖fderiv ℝ (tail (L := L) hκ r h l) (A (J u))‖*‖A (J v)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (C*(PROP017UniformN.cutSeq L l)^(-(1/2 : ℝ)))*‖v‖ := by
      rw [show ‖A (J v)‖ = ‖J v‖ from
        (Q07SobolevModelR24.coordinates (regularity_pos r).le).norm_map _]
      exact mul_le_mul hbnd (Sobolev.H02.norm_mono_le (regularity_mono hr) v) (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg (cut_nonnegative (L := L) l) _))

/-- Full clause (3) differential estimate, with one constant and threshold
for a fixed finite largest order. Includes every real direction. -/
theorem window_differentials (hκ : 0 < κ) : WindowDifferentials (L := L) hκ := by
  intro d hd B h hh
  have he := fun r : Fin (d+1) =>
    restricted_bound (L := L) hκ d r.val (by omega) B hh
  choose C hC l0 hb using he
  refine ⟨∑ r : Fin (d+1), C r,Finset.sum_nonneg (fun r _ => hC r),
    Finset.univ.sup l0,?_⟩
  intro l hl r hr
  let i : Fin (d+1) := ⟨r,by omega⟩
  have hli : l0 i ≤ l := (Finset.le_sup (f := l0) (Finset.mem_univ i)).trans hl
  have hsum : C i ≤ ∑ j : Fin (d+1), C j :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨fun u hu => (hb i l hli u hu).1,?_⟩
  intro u hu
  exact (hb i l hli u hu.1).2.trans (mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg (cut_nonnegative (L := L) l) _))

end QuantumNLS.ActualModelDifferentialsR52a
#print axioms QuantumNLS.ActualModelDifferentialsR52a.restricted_bound
#print axioms QuantumNLS.ActualModelDifferentialsR52a.window_differentials

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ActualModelDifferentialsR52a." ||
        n.toString.startsWith "_private.QuantumNLS.ActualModelDifferentialsR52a." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 then
        throwError "Rejected dependency: {n}"
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
  Lean.logInfo m!"Round52 aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard only."
