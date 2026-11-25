import QuantumNLS.Reg010LowEmbedding

/-! Continuous native L4 realization of the one-third Sobolev field. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.Reg010LowEmbeddingMap
open QuantumNLS.Sobolev QuantumNLS.Reg010LowEmbedding QuantumNLS.Reg010LowL4Space
variable {L : ℝ} [Fact (0<L)]

def toL4 (u : H04sp L (1/3)) : L4T L := (memLp_four u).1.toLp u.val

theorem toL4_ae (u : H04sp L (1/3)) : toL4 u =ᵐ[volume] u.val := MemLp.coeFn_toLp _

theorem toL4_norm (u : H04sp L (1/3)) : ‖toL4 u‖ ≤ embeddingConstant L*‖u‖ := by
  rw [toL4,Lp.norm_toLp]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (memLp_four u).2
  simpa only [ENNReal.toReal_ofReal (mul_nonneg constant_nonneg (norm_nonneg _))] using h

def toL4Linear : H04sp L (1/3) →ₗ[ℂ] L4T L where
  toFun := toL4
  map_add' u v := by
    apply Lp.ext
    filter_upwards [toL4_ae (u+v),toL4_ae u,toL4_ae v,Lp.coeFn_add u.val v.val,
      Lp.coeFn_add (toL4 u) (toL4 v)] with x h1 h2 h3 h4 h5
    change toL4 (u+v) x = (toL4 u+toL4 v) x
    rw [WField.val_add] at h1
    rw [h1,h5,Pi.add_apply,h4,Pi.add_apply,h2,h3]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [toL4_ae (c • u),toL4_ae u,Lp.coeFn_smul c u.val,
      Lp.coeFn_smul c (toL4 u)] with x h1 h2 h3 h4
    change toL4 (c • u) x = (c • toL4 u) x
    rw [WField.val_smul] at h1
    rw [h1,h4,Pi.smul_apply,h3,Pi.smul_apply,h2]

def embeddingF04 : H04sp L (1/3) →L[ℂ] L4T L :=
  toL4Linear.mkContinuous (embeddingConstant L) toL4_norm

def embeddingH02 : H02 L (1/3) →L[ℂ] L4T L :=
  embeddingF04.comp (H02.toH04 (by norm_num : (0:ℝ)≤1/3))

theorem H02_toH04_val (u : H02 L (1/3)) :
    (H02.toH04 (by norm_num : (0:ℝ)≤1/3) u).val = u.val :=
  fieldIncl_val (f04W L (1/3)) (def002 L (1/3)) zero_le_one
    (f04W_le_def002 L (by norm_num)) u

theorem embeddingH02_ae (u : H02 L (1/3)) : embeddingH02 u =ᵐ[volume] u.val := by
  have h := toL4_ae (H02.toH04 (by norm_num : (0:ℝ)≤1/3) u)
  rw [H02_toH04_val] at h
  exact h

theorem embeddingH02_norm (u : H02 L (1/3)) :
    ‖embeddingH02 u‖ ≤ embeddingConstant L*‖u‖ :=
  (toL4_norm _).trans (mul_le_mul_of_nonneg_left
    (H02.norm_toH04_le (by norm_num : (0:ℝ)≤1/3) u) constant_nonneg)

theorem embeddingH02_toL2 (u : H02 L (1/3)) : toL2 (embeddingH02 u) = u.val := by
  apply Lp.ext
  exact (toL2_ae _).trans (embeddingH02_ae u)

#print axioms toL4_ae
#print axioms toL4_norm
#print axioms toL4Linear
#print axioms embeddingF04
#print axioms embeddingH02
#print axioms H02_toH04_val
#print axioms embeddingH02_ae
#print axioms embeddingH02_norm
#print axioms embeddingH02_toL2
end QuantumNLS.Reg010LowEmbeddingMap

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Reg010LowEmbeddingMap." ||
        n.toString.startsWith "_private.QuantumNLS.Reg010LowEmbeddingMap." then
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
  Lean.logInfo m!"Round46 aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
