import QuantumNLS.RootH1Ratio

/-! Pointwise identities for R-F36DAC7F. All analytic hypotheses are discharged
in the physical application; no regularized energy identity is assumed here. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open ComplexConjugate
namespace QuantumNLS.RootH1PositiveAlgebra

def aux (κ : ℝ) (r d : ℂ) : ℂ :=
  (d+(κ:ℂ)*r^2*conj d) / ((1-κ^2*‖r‖^4:ℝ):ℂ)

lemma split {κ Y : ℝ} {r d u : ℂ}
    (h1 : 1-κ*‖r‖^2 ≠ 0) (h2 : 1-κ^2*‖r‖^4 ≠ 0)
    (hd : d = u-(Y:ℂ)*r-(κ:ℂ)*conj u*r^2) :
    u = (Y:ℂ)*r/((1-κ*‖r‖^2:ℝ):ℂ)+aux κ r d := by
  have hn : ‖r‖^2 = r.re^2+r.im^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]; ring
  rw [hd]
  apply Complex.ext <;>
    simp only [aux,pow_two,map_sub,map_mul,Complex.conj_ofReal,Complex.conj_conj,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im,Complex.div_ofReal_re,Complex.div_ofReal_im] <;>
    field_simp [h1,h2] <;>
    simp only [show ‖r‖^4 = (‖r‖^2)^2 by ring,hn] <;> ring

lemma real_aux {κ : ℝ} {r d : ℂ}
    (h1 : 1-κ*‖r‖^2 ≠ 0) (h2 : 1-κ^2*‖r‖^4 ≠ 0) :
    (conj r*aux κ r d).re = (conj r*d).re/(1-κ*‖r‖^2) := by
  have hn : ‖r‖^2 = r.re^2+r.im^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]; ring
  simp only [aux,pow_two,Complex.div_ofReal_re,Complex.mul_re,Complex.mul_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.conj_re,Complex.conj_im,Complex.div_ofReal_im]
  field_simp [h1,h2]
  simp only [show ‖r‖^4 = (‖r‖^2)^2 by ring,hn]
  ring

lemma norm_split {κ Y : ℝ} {r d u : ℂ}
    (h1 : 1-κ*‖r‖^2 ≠ 0) (h2 : 1-κ^2*‖r‖^4 ≠ 0)
    (hd : d = u-(Y:ℂ)*r-(κ:ℂ)*conj u*r^2) :
    ‖u‖^2 = Y^2*‖r‖^2/(1-κ*‖r‖^2)^2+‖aux κ r d‖^2+
      2*Y*(conj r*d).re/(1-κ*‖r‖^2)^2 := by
  have hs := split h1 h2 hd
  have hr := real_aux (r := r) (d := d) h1 h2
  have hnorm : ∀ z w : ℂ, ‖z+w‖^2 = ‖z‖^2+‖w‖^2+2*(conj z*w).re := by
    intro z w
    simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.conj_re,Complex.conj_im]
    ring
  rw [hs,hnorm]
  have hn : ‖(Y:ℂ)*r/((1-κ*‖r‖^2:ℝ):ℂ)‖^2 = Y^2*‖r‖^2/(1-κ*‖r‖^2)^2 := by
    simp only [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,div_pow,sq_abs]
  rw [hn]
  have hc : (conj ((Y:ℂ)*r/((1-κ*‖r‖^2:ℝ):ℂ))*aux κ r d).re =
      Y*(conj r*aux κ r d).re/(1-κ*‖r‖^2) := by
    rw [map_div₀,map_mul,Complex.conj_ofReal,Complex.conj_ofReal,
      div_mul_eq_mul_div,mul_assoc,Complex.div_ofReal_re]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hc,hr]
  field_simp [h1]

lemma pairing_split {κ Y : ℝ} {r d u : ℂ}
    (h1 : 1-κ*‖r‖^2 ≠ 0) (h2 : 1-κ^2*‖r‖^4 ≠ 0)
    (hd : d = u-(Y:ℂ)*r-(κ:ℂ)*conj u*r^2) :
    (conj u*r).re = Y*‖r‖^2/(1-κ*‖r‖^2)+(conj r*d).re/(1-κ*‖r‖^2) := by
  have hs := split h1 h2 hd
  have hr := real_aux (r := r) (d := d) h1 h2
  rw [hs,map_add,add_mul,Complex.add_re]
  have hsym : (conj (aux κ r d)*r).re = (conj r*aux κ r d).re := by
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]; ring
  rw [hsym,hr]
  congr 1
  rw [map_div₀,map_mul,Complex.conj_ofReal,Complex.conj_ofReal]
  rw [div_mul_eq_mul_div,mul_assoc,Complex.conj_mul',← Complex.ofReal_pow,← Complex.ofReal_mul,
    Complex.div_ofReal_re,Complex.ofReal_re]

lemma recover_derivative {κ : ℝ} {r d : ℂ}
    (h2 : 1-κ^2*‖r‖^4 ≠ 0) :
    d = aux κ r d-(κ:ℂ)*r^2*conj (aux κ r d) := by
  have hn : ‖r‖^2 = r.re^2+r.im^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]; ring
  apply Complex.ext <;>
    simp only [aux,pow_two,map_div₀,Complex.conj_ofReal,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.conj_re,Complex.conj_im,Complex.div_ofReal_re,Complex.div_ofReal_im] <;>
    field_simp [h2] <;>
    simp only [show ‖r‖^4 = (‖r‖^2)^2 by ring,hn] <;> ring

lemma derivative_le {κ δ : ℝ} {r d : ℂ} (hκ : 0 ≤ κ)
    (hb : κ*‖r‖^2 ≤ δ) (h2 : 1-κ^2*‖r‖^4 ≠ 0) :
    ‖d‖^2 ≤ (1+δ)^2*‖aux κ r d‖^2 := by
  have hdδ : 0 ≤ δ := (mul_nonneg hκ (sq_nonneg _)).trans hb
  have hn : ‖d‖ ≤ (1+δ)*‖aux κ r d‖ := by
    calc
      ‖d‖ = ‖aux κ r d-(κ:ℂ)*r^2*conj (aux κ r d)‖ := congrArg norm (recover_derivative h2)
      _ ≤ ‖aux κ r d‖+‖(κ:ℂ)*r^2*conj (aux κ r d)‖ := norm_sub_le _ _
      _ = (1+κ*‖r‖^2)*‖aux κ r d‖ := by
        simp only [norm_mul,norm_pow,Complex.norm_conj,Complex.norm_real,Real.norm_of_nonneg hκ]; ring
      _ ≤ (1+δ)*‖aux κ r d‖ := by gcongr
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg d) hn 2

#print axioms split
#print axioms real_aux
#print axioms norm_split
#print axioms pairing_split
#print axioms recover_derivative
#print axioms derivative_le
end QuantumNLS.RootH1PositiveAlgebra

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1PositiveAlgebra." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1PositiveAlgebra." then
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
