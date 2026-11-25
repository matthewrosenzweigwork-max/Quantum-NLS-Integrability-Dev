import QuantumNLS.Ext025B3FormSpectral
import QuantumNLS.OccupationHilbert
import Mathlib.Analysis.Normed.Group.Tannery

/-! C01 for actual maximal diagonal nonnegative multipliers on all l2,
with the square-root domain, not the operator domain. The general spectral
representation of an arbitrary selfadjoint operator is not assumed here.
Author sol_ext_b, Round 3. -/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace ENNReal ComplexConjugate
namespace QuantumNLS.Ext025B3DiagonalForms
open OccupationHilbert Ext025B3FormSpectral
variable {ι : Type*}

/-- Actual bounded spectral evolution on all l2 coordinates. -/
def evolution (ev : ι → ℝ) (t : ℝ) : L2 ι →L[ℂ] L2 ι :=
  diagonal (fun i => phase t (ev i)) 1 zero_le_one (fun i => le_of_eq (phase_norm t (ev i)))

@[simp] theorem evolution_apply (ev : ι → ℝ) (t : ℝ) (v : L2 ι) (i : ι) :
    evolution ev t v i = phase t (ev i) * v i := rfl

/-- Literal domain of the square-root multiplier. -/
def InFormDomain (ev : ι → ℝ) (v : L2 ι) : Prop :=
  Memℓp (fun i => (Real.sqrt (ev i) : ℂ) * v i) 2

/-- Actual square-root image, constructed from square summability. -/
def formRoot (ev : ι → ℝ) (v : L2 ι) (hv : InFormDomain ev v) : L2 ι :=
  ⟨fun i => (Real.sqrt (ev i) : ℂ) * v i, hv⟩

theorem norm_sq_tsum (v : L2 ι) : ‖v‖^2 = ∑' i, ‖v i‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) v

/-- Exact equivalence of the form domain and finite first spectral moment. -/
theorem formDomain_iff (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i) (v : L2 ι) :
    InFormDomain ev v ↔ Summable (fun i => ev i * ‖v i‖^2) := by
  unfold InFormDomain
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hev _)]

theorem formRoot_norm_sq (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i) (v : L2 ι)
    (hv : InFormDomain ev v) : ‖formRoot ev v hv‖^2 = ∑' i, ev i * ‖v i‖^2 := by
  rw [norm_sq_tsum]
  apply tsum_congr
  intro i
  change ‖(Real.sqrt (ev i) : ℂ) * v i‖^2 = _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hev _)]

theorem evolution_increment_norm_sq (ev : ι → ℝ) (t : ℝ) (v : L2 ι) :
    ‖evolution ev t v - v‖^2 = ∑' i, ‖phase t (ev i) - 1‖^2 * ‖v i‖^2 := by
  rw [norm_sq_tsum]
  apply tsum_congr
  intro i
  change ‖phase t (ev i) * v i - v i‖^2 = _
  have he : phase t (ev i) * v i - v i = (phase t (ev i)-1) * v i := by ring
  rw [he, norm_mul, mul_pow]

/-- Squared strong difference is o(|t|) on the exact form domain. -/
theorem «FIN-EXT025-C01-diagonal-square» (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (v : L2 ι) (hv : InFormDomain ev v) :
    Tendsto (fun t : ℝ => ‖evolution ev t v - v‖^2 / |t|) (𝓝[≠] 0) (𝓝 0) := by
  have hs := ((formDomain_iff ev hev v).mp hv).mul_left 2
  have h := tendsto_tsum_of_dominated_convergence hs
    (f := fun t i => (‖phase t (ev i) - 1‖^2 / |t|) * ‖v i‖^2)
    (g := fun _ => (0 : ℝ))
    (fun i => by simpa using (square_limit (ev i)).mul_const (‖v i‖^2))
    (Eventually.of_forall fun t i => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
        (square_bound t (ev i) (hev i)) (sq_nonneg ‖v i‖))
  simpa only [tsum_zero, evolution_increment_norm_sq, div_mul_eq_mul_div, tsum_div_const]
    using h

/-- Strong form-domain small-o estimate, including both signs of time. -/
theorem «FIN-EXT025-C01-diagonal-small-o» (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (v : L2 ι) (hv : InFormDomain ev v) :
    Tendsto (fun t : ℝ => ‖evolution ev t v - v‖ / Real.sqrt |t|)
      (𝓝[≠] 0) (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    («FIN-EXT025-C01-diagonal-square» ev hev v hv)
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_div' _ (abs_nonneg _),
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using h

/-- Mixed first moments are absolutely summable by form-domain Cauchy-Schwarz. -/
theorem mixedMoment_summable (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (w v : L2 ι) (hw : InFormDomain ev w) (hv : InFormDomain ev v) :
    Summable (fun i => ev i * ‖w i‖ * ‖v i‖) := by
  have hs := lp.summable_mul (p := (2 : ENNReal)) (q := (2 : ENNReal))
    (by rw [Real.holderConjugate_iff]; norm_num) (formRoot ev w hw) (formRoot ev v hv)
  convert hs using 1
  funext i
  change _ = ‖(Real.sqrt (ev i) : ℂ) * w i‖ * ‖(Real.sqrt (ev i) : ℂ) * v i‖
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    ev i * ‖w i‖ * ‖v i‖ = (Real.sqrt (ev i))^2 * ‖w i‖ * ‖v i‖ := by
      rw [Real.sq_sqrt (hev i)]
    _ = _ := by ring

/-- The polarized scalar form derivative on the whole square-root domain. -/
theorem «FIN-EXT025-C01-diagonal-form-derivative» (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (w v : L2 ι) (hw : InFormDomain ev w) (hv : InFormDomain ev v) :
    Tendsto (fun t : ℝ => ⟪w, evolution ev t v - v⟫_ℂ / (t : ℂ)) (𝓝[≠] 0)
      (𝓝 (-Complex.I * ⟪formRoot ev w hw, formRoot ev v hv⟫_ℂ)) := by
  have hi (i : ι) :
      (ev i : ℂ) * conj (w i) * v i =
        conj (formRoot ev w hw i) * formRoot ev v hv i := by
    change _ = conj ((Real.sqrt (ev i) : ℂ) * w i) * ((Real.sqrt (ev i) : ℂ) * v i)
    simp only [map_mul, Complex.conj_ofReal]
    have hs : (Real.sqrt (ev i) : ℂ)^2 = (ev i : ℂ) := by
      exact_mod_cast Real.sq_sqrt (hev i)
    linear_combination -(conj (w i) * v i) * hs
  have h := tendsto_tsum_of_dominated_convergence (mixedMoment_summable ev hev w v hw hv)
    (f := fun t i => conj (w i) * ((phase t (ev i) - 1) / (t : ℂ)) * v i)
    (g := fun i => -Complex.I * (conj (formRoot ev w hw i) * formRoot ev v hv i))
    (fun i => by
      convert ((quotient_limit (ev i)).const_mul (conj (w i))).mul_const (v i) using 1
      rw [← hi i]
      ring)
    (Eventually.of_forall fun t i => by
      simp only [norm_mul, RCLike.norm_conj]
      have hb := quotient_bound t (ev i)
      rw [abs_of_nonneg (hev i)] at hb
      nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (w i)),
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hb (norm_nonneg (w i))) (norm_nonneg (v i))])
  have he (t : ℝ) : ⟪w, evolution ev t v - v⟫_ℂ / (t : ℂ) =
      ∑' i, conj (w i) * ((phase t (ev i) - 1) / (t : ℂ)) * v i := by
    rw [lp.inner_eq_tsum, ← tsum_div_const]
    apply tsum_congr
    intro i
    simp only [RCLike.inner_apply, lp.coeFn_sub, Pi.sub_apply, evolution_apply]
    ring
  have hg : (∑' i, -Complex.I * (conj (formRoot ev w hw i) * formRoot ev v hv i)) =
      -Complex.I * ⟪formRoot ev w hw, formRoot ev v hv⟫_ℂ := by
    rw [tsum_mul_left, lp.inner_eq_tsum]
    congr 1
    apply tsum_congr
    intro i
    exact (RCLike.inner_apply' _ _).symm
  rw [hg] at h
  simpa only [← he] using h

end QuantumNLS.Ext025B3DiagonalForms

#print axioms QuantumNLS.Ext025B3DiagonalForms.formDomain_iff

#print axioms QuantumNLS.Ext025B3DiagonalForms.formRoot_norm_sq

#print axioms QuantumNLS.Ext025B3DiagonalForms.evolution_increment_norm_sq

#print axioms QuantumNLS.Ext025B3DiagonalForms.«FIN-EXT025-C01-diagonal-square»

#print axioms QuantumNLS.Ext025B3DiagonalForms.«FIN-EXT025-C01-diagonal-small-o»

#print axioms QuantumNLS.Ext025B3DiagonalForms.mixedMoment_summable
#print axioms QuantumNLS.Ext025B3DiagonalForms.«FIN-EXT025-C01-diagonal-form-derivative»

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants do
    if n.toString.startsWith "QuantumNLS.Ext025B3DiagonalForms." then
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
  Lean.logInfo m!"Ext025B3DiagonalForms audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
