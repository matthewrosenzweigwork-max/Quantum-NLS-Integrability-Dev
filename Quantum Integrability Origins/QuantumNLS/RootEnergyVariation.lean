import QuantumNLS.F04Regularity
import QuantumNLS.ContactProductExact

/-! Elementary H²/H¹ differential calculation for R-63A99F0E.
Only the Sobolev maps, Parseval and polynomial calculus of F04Regularity
are used; none of its solution or conservation conclusions is used. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Filter QuantumNLS.Fourier QuantumNLS.Sobolev
  QuantumNLS.Sobolev.PosWeight QuantumNLS.LocalWellPosedness
  QuantumNLS.LocalWellPosednessFull QuantumNLS.F04Regularity
namespace QuantumNLS.RootEnergyVariation
variable {L : ℝ} [Fact (0 < L)]

abbrev m21 : h04 L 2 →L[ℂ] h04 L 1 := h04_mono L (by norm_num)
def lap : h04 L 2 →L[ℂ] h04 L 0 :=
  (h04_mono L (by norm_num : (0 : ℝ) ≤ 2-2)).comp (lapOp 2)

/-- Physical H⁰ carrier, with the unnormalized mass-L torus measure. -/
def physical : h04 L 0 ≃ₗᵢ[ℂ] QuantumNLS.PhysicalTensor.L2T L :=
  (toL2ᵢ (f04W L 0)).trans (fourierL2 L).symm

lemma physical_coeff (a : h04 L 0) (n : ℤ) :
    fourierL2 L (physical a) n = a.val n := by
  change fourierL2 L ((fourierL2 L).symm (toL2 (f04W L 0) a)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply, toL2_apply, f04W_zero]
  simp

lemma physical_rep (a : h04 L 1) :
    (physical (m10 a) : AddCircle L → ℂ) =ᵐ[volume] S1 a := by
  have hm := memLp_of_continuous (S1 a).continuous
  have he : physical (m10 a) = hm.toLp (S1 a) := by
    apply (fourierL2 L).injective
    apply Subtype.ext
    funext n
    rw [fourierL2_toLp, coeff_S1, physical_coeff]
    rfl
  rw [he]
  exact hm.coeFn_toLp

lemma physical_oneH1 (a : h04 L 1) :
    QuantumNLS.ProductEnergyPreparation.OneH1 (physical (m10 a)) := by
  unfold QuantumNLS.ProductEnergyPreparation.OneH1
  change Mem04 L 1 (fun n => fourierL2 L (physical (m10 a)) n)
  simp only [physical_coeff]
  exact a.summable

lemma physical_energy (κ : ℝ) (a : h04 L 1) :
    QuantumNLS.ChargeEnergy.energyH1 κ (physical (m10 a) : AddCircle L → ℂ) =
      energy κ a := by
  rw [QuantumNLS.ChargeEnergy.energyH1_congr_ae κ (physical_rep a)]
  exact (energy_eq_energyH1 κ a).symm

/-- Periodic integration by parts at exactly H² × H¹ regularity. -/
lemma ibp (u : h04 L 2) (h : h04 L 1) :
    ⟪D (m21 u), D h⟫_ℂ = ⟪lap u, m10 h⟫_ℂ := by
  rw [inner_h0, inner_h0]
  apply tsum_congr
  intro n
  change conj (((freq L n : ℝ) : ℂ) * u.val n) *
    (((freq L n : ℝ) : ℂ) * h.val n) =
    conj (((freq L n ^ 2 : ℝ) : ℂ) * u.val n) * h.val n
  simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.ofReal_pow]
  ring

/-- The half-gradient, in the convention dE=2 Re⟨∇E,h⟩. -/
def grad (κ : ℝ) (u : h04 L 2) : h04 L 0 :=
  lap u + ((2 * κ : ℝ) : ℂ) • m10 (Fh (le_refl (1 : ℝ)) (m21 u))

def differential (κ : ℝ) (u : h04 L 2) : h04 L 1 →L[ℝ] ℝ :=
  2 • Complex.reCLM.comp
    (((innerSL ℂ (grad κ u)).comp (m10 (L := L))).restrictScalars ℝ)

lemma differential_apply (κ : ℝ) (u : h04 L 2) (h : h04 L 1) :
    differential κ u h = 2 * (⟪grad κ u, m10 h⟫_ℂ).re := by
  simp [differential, innerSL_apply_apply]

lemma quart_differentiable : Differentiable ℝ (quart (L := L)) := by
  have hS : Differentiable ℝ (S1 (L := L)) :=
    (S1 (L := L)).restrictScalars ℝ |>.differentiable
  have hP := ((hS.mul hS.star).mul hS).mul hS.star
  have hI := (intCLM (L := L)).differentiable.comp hP
  have hR := Complex.reCLM.differentiable.comp hI
  convert hR using 1
  funext a
  change quart a = (intCLM (S1 a * star (S1 a) * S1 a * star (S1 a))).re
  rw [intCLM_P, Complex.ofReal_re]

lemma energy_differentiable (κ : ℝ) : Differentiable ℝ (energy (L := L) κ) := by
  have hD : Differentiable ℝ (D (L := L)) := (D (L := L)).restrictScalars ℝ |>.differentiable
  exact (hD.norm_sq ℂ).add (quart_differentiable.const_mul κ)

lemma energy_line (κ : ℝ) (u : h04 L 2) (h : h04 L 1) :
    HasDerivAt (fun s : ℝ => energy κ (m21 u + s • h))
      (2 * (⟪grad κ u, m10 h⟫_ℂ).re) 0 := by
  have hl : HasDerivAt (fun s : ℝ => m21 u + s • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add (m21 u)
  have hd : HasDerivAt (fun s : ℝ => D (m21 u + s • h)) (D h) 0 :=
    ((D (L := L)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hl
  have hk : HasDerivAt (fun s : ℝ => ‖D (m21 u + s • h)‖ ^ 2)
      (2 * (⟪D (m21 u), D h⟫_ℂ).re) 0 := by
    simpa only [zero_smul, add_zero] using hasDerivAt_normSq hd
  have hq : HasDerivAt (fun s : ℝ => quart (m21 u + s • h))
      (4 * (⟪m10 (Fh (le_refl (1 : ℝ)) (m21 u)), m10 h⟫_ℂ).re) 0 := by
    simpa only [zero_smul, add_zero] using hasDerivAt_quart hl
  convert hk.add (hq.const_mul κ) using 1
  · rfl
  · rw [ibp]
    simp only [grad, inner_add_left, inner_smul_left, Complex.conj_ofReal,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring

lemma energy_fderiv (κ : ℝ) (u : h04 L 2) :
    HasFDerivAt (energy κ) (differential κ u) (m21 u) := by
  have hd := (energy_differentiable (L := L) κ (m21 u)).hasFDerivAt
  have he : fderiv ℝ (energy κ) (m21 u) = differential κ u := by
    ext h
    have hl : HasDerivAt (fun s : ℝ => m21 u + s • h) h 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add (m21 u)
    have hd' : HasFDerivAt (energy κ) (fderiv ℝ (energy κ) (m21 u))
        (m21 u + (0 : ℝ) • h) := by simpa only [zero_smul, add_zero] using hd
    have hh := hd'.comp_hasDerivAt 0 hl
    rw [differential_apply]
    exact hh.unique (energy_line κ u h)
  rwa [he] at hd

#print axioms energy_fderiv
#print axioms physical_energy
end QuantumNLS.RootEnergyVariation

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootEnergyVariation." ||
        n.toString.startsWith "_private.QuantumNLS.RootEnergyVariation." then
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
