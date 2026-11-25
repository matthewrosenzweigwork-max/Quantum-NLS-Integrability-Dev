import QuantumNLS.RootH1RatioL2

/-! The actual derivative resolvent acts by the printed Fourier multiplier. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open QuantumNLS.PhysicalTensor QuantumNLS.HaarResolvent
  QuantumNLS.RootH1RatioOperator
namespace QuantumNLS.RootH1RatioModes
variable {L : ℝ} [hLf : Fact (0 < L)]

def omega (L : ℝ) (n : ℤ) : ℂ := 2*Real.pi*Complex.I*n/L

def plane (L : ℝ) [Fact (0 < L)] (n : ℤ) (t : ℝ) : ℂ :=
  QuantumNLS.Fourier.mode L n (t : AddCircle L)

lemma omega_re (L : ℝ) (n : ℤ) : (omega L n).re = 0 := by
  simp [omega, Complex.div_ofReal_re, Complex.mul_re, Complex.mul_im]

lemma plane_exp (n : ℤ) (t : ℝ) :
    plane L n t = (((Real.sqrt L)⁻¹:ℝ):ℂ)*Complex.exp (omega L n*t) := by
  rw [plane, QuantumNLS.Fourier.mode_coe]
  congr 2
  unfold omega
  ring

lemma plane_deriv (n : ℤ) (t : ℝ) :
    HasDerivAt (plane L n) (omega L n*plane L n t) t := by
  have hd := (QuantumNLS.HaarResolventAnalysis.hasDerivAt_cexp_mul (omega L n) t).const_mul
    ((((Real.sqrt L)⁻¹:ℝ):ℂ))
  convert hd using 1
  · funext x
    rw [plane_exp]
  · rw [plane_exp]
    ring

lemma plane_memLp (n : ℤ) : MemLp (plane L n) 2 (volume.restrict (Ioc 0 L)) := by
  have h := (QuantumNLS.Fourier.memLp_mode (L := L) n).comp_measurePreserving
    (AddCircle.measurePreserving_mk L 0)
  change MemLp (fun x : ℝ => QuantumNLS.Fourier.mode L n (x : AddCircle L)) 2 (volume.restrict (Ioc 0 L))
  simpa only [zero_add, Function.comp_def] using h

lemma plane_periodic (n : ℤ) : plane L n L = plane L n 0 := by
  simp only [plane, AddCircle.coe_period, AddCircle.coe_zero]

lemma resolvent_mode {Y : ℝ} (hY : 0 < Y) (n : ℤ) :
    RootH1RatioOperator.resolvent Y (QuantumNLS.Fourier.modeLp L n) =
      ((Y:ℂ)+omega L n)⁻¹ • QuantumNLS.Fourier.modeLp L n := by
  let a : ℂ := (Y:ℂ)+omega L n
  have ha : a ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [a, Complex.add_re, Complex.ofReal_re, omega_re, add_zero, Complex.zero_re] at hh
    linarith
  let g : ℝ → ℂ := fun t => a⁻¹*plane L n t
  let h : ℝ → ℂ := fun t => (omega L n*a⁻¹)*plane L n t
  have hgder (t : ℝ) : HasDerivAt g (h t) t := by
    convert (plane_deriv n t).const_mul a⁻¹ using 1
    dsimp [g,h]
    ring
  have hgcon : Continuous g := continuous_iff_continuousAt.mpr
    (fun t => (hgder t).continuousAt)
  have hhcon : Continuous h := by
    exact continuous_const.mul (continuous_iff_continuousAt.mpr (fun t => (plane_deriv n t).continuousAt))
  have hrep : IsH1Rep L (a⁻¹ • QuantumNLS.Fourier.modeLp L n) g h := by
    refine ⟨?_, (plane_memLp n).const_mul _, ?_⟩
    · filter_upwards [Lp.coeFn_smul a⁻¹ (QuantumNLS.Fourier.modeLp L n),
        QuantumNLS.Fourier.coeFn_modeLp L n] with x hs hm
      rw [hs]
      simpa only [Pi.smul_apply, smul_eq_mul, g, plane, coe_rep1] using congrArg (a⁻¹*·) hm
    · intro x _
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hgder t) (hhcon.intervalIntegrable 0 x)
      dsimp [g] at he ⊢
      linear_combination -he
  have hboundary : g L = (1:ℂ)*g 0 := by
    dsimp [g]
    rw [plane_periodic, one_mul]
  have haction : ∀ᵐ x : AddCircle L,
      QuantumNLS.Fourier.modeLp L n x = h (rep1 L x) -
        Complex.I*((Y:ℂ)*Complex.I)*g (rep1 L x) := by
    filter_upwards [QuantumNLS.Fourier.coeFn_modeLp L n] with x hx
    rw [hx]
    dsimp [h,g,plane]
    rw [coe_rep1]
    have he : Complex.I*((Y:ℂ)*Complex.I) = -(Y:ℂ) := by
      linear_combination (Y:ℂ)*Complex.I_mul_I
    rw [he]
    have hei : ((Y:ℂ)+omega L n)*a⁻¹ = 1 := by exact mul_inv_cancel₀ ha
    linear_combination -(QuantumNLS.Fourier.mode L n x)*hei
  have hq : qOf L 1 ((Y:ℂ)*Complex.I) ≠ 1 := by
    rw [qOf_eq]
    have ht : Real.exp (-Y*L) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [hLf.out])
    exact_mod_cast ht.ne
  have he := resolvent_left_inverse L (ρ := 1) (z := (Y:ℂ)*Complex.I)
    (by norm_num) hq (show (a⁻¹ • QuantumNLS.Fourier.modeLp L n,
      QuantumNLS.Fourier.modeLp L n) ∈ graphD L 1 ((Y:ℂ)*Complex.I) from
        ⟨g,h,hrep,hboundary,haction⟩)
  simpa only [RootH1RatioOperator.resolvent, qOf_eq, a] using he

#print axioms omega_re
#print axioms plane_exp
#print axioms plane_deriv
#print axioms plane_memLp
#print axioms plane_periodic
#print axioms resolvent_mode
end QuantumNLS.RootH1RatioModes

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootH1RatioModes." ||
        n.toString.startsWith "_private.QuantumNLS.RootH1RatioModes." then
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
