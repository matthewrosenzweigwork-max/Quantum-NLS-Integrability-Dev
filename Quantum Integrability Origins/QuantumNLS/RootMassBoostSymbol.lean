import QuantumNLS.PlaneWaveSymbol
import QuantumNLS.RootIndexedMasses

/-! Literal Fourier-character multiplication on the physical input, and its ordered-kernel covariance. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.RootMassBoostSymbol
open PhysicalTensor (L2T L2TN prodLp prodFun memLp_prodFun torusPiMeasure)
open BetheWeakGradient (representatives)
open BetheTransferKernelAdjoint (rawPlus rawMinus)
open NormalizedTransfer (orderedKernel productSymbol symbolTerm)
open KernelDefinition (kernelProductSymbol)
open PlaneWaveSymbol (pm)
variable {L : ℝ} [Fact (0 < L)]

theorem mem_boost (k : ℤ) (u : L2T L) :
    MemLp (fun x : AddCircle L => fourier k x * u x) 2 volume := by
  apply (Lp.memLp u).of_le
  · exact (fourier (T := L) k).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable u)
  · exact Eventually.of_forall fun x => by simp [fourier_apply]

/-- Multiplication by exp(2 pi i k x/L), using its literal torus character. -/
def boost (k : ℤ) (u : L2T L) : L2T L := (mem_boost k u).toLp _

theorem coe_boost (k : ℤ) (u : L2T L) :
    (boost k u : AddCircle L → ℂ) =ᵐ[volume] fun x => fourier k x * u x :=
  (mem_boost k u).coeFn_toLp

theorem norm_boost (k : ℤ) (u : L2T L) : ‖boost k u‖ = ‖u‖ := by
  have h : ∀ᵐ x ∂volume, ‖(boost k u : AddCircle L → ℂ) x‖ = ‖u x‖ :=
    (coe_boost k u).mono fun x hx => by rw [hx,norm_mul]; simp [fourier_apply]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.ge))

def phaseN (k : ℤ) (r : ℕ) (x : Fin r → AddCircle L) : ℂ :=
  ∏ j, fourier k (x j)

theorem phaseN_coe (k : ℤ) (r : ℕ) (x : Fin r → ℝ) :
    phaseN k r (fun j => (x j : AddCircle L)) =
      Complex.exp (Complex.I * (pm L k : ℂ) * ((∑ j, x j : ℝ) : ℂ)) := by
  unfold phaseN
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  unfold pm
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem prod_boost (k : ℤ) (r : ℕ) (u : L2T L) :
    (prodLp (fun _ : Fin r => boost k u) : (Fin r → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L r]
      fun x => phaseN k r x * (prodLp (fun _ : Fin r => u) : (Fin r → AddCircle L) → ℂ) x := by
  have hc : ∀ᵐ x ∂torusPiMeasure L r, ∀ j : Fin r,
      (boost k u : AddCircle L → ℂ) (x j) = fourier k (x j) * u (x j) :=
    ae_all_iff.mpr fun j =>
      (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure (AddCircle L))) j).ae (coe_boost k u)
  filter_upwards [hc,(memLp_prodFun (fun _ : Fin r => boost k u)).coeFn_toLp,
    (memLp_prodFun (fun _ : Fin r => u)).coeFn_toLp] with x hx hb hu
  have hb' : (prodLp (fun _ : Fin r => boost k u) : L2TN L r) x = prodFun (fun _ : Fin r => boost k u) x := hb
  have hu' : (prodLp (fun _ : Fin r => u) : L2TN L r) x = prodFun (fun _ : Fin r => u) x := hu
  rw [hb',hu']
  change (∏ j, (boost k u : AddCircle L → ℂ) (x j)) = (∏ j, fourier k (x j)) * ∏ j, u (x j)
  simp_rw [hx]
  exact Finset.prod_mul_distrib

/-- Cancellation of the literal character factors in each plus/minus ordered kernel. -/
theorem integrand_shift (k : ℤ) (r : ℕ) (z : ℂ) (x y : Fin r → ℝ) :
    conj (phaseN k r (fun j => (x j : AddCircle L))) * rawPlus L z x y *
        phaseN k r (fun j => (y j : AddCircle L)) = rawPlus L (z-(pm L k : ℂ)) x y ∧
    conj (phaseN k r (fun j => (x j : AddCircle L))) * rawMinus L z x y *
        phaseN k r (fun j => (y j : AddCircle L)) = rawMinus L (z-(pm L k : ℂ)) x y := by
  have hp : conj (phaseN k r (fun j => (x j : AddCircle L))) * phaseN k r (fun j => (y j : AddCircle L)) =
      Complex.exp (Complex.I * (pm L k : ℂ) * (((∑ j,y j)-(∑ j,x j) : ℝ) : ℂ)) := by
    rw [phaseN_coe,phaseN_coe,← Complex.exp_conj,← Complex.exp_add]
    congr 1
    simp only [map_mul,Complex.conj_I,Complex.conj_ofReal]
    push_cast
    ring
  have he : Complex.exp (Complex.I*z*L) = Complex.exp (Complex.I*(z-(pm L k : ℂ))*L) := by
    have ha : Complex.I*(z-(pm L k : ℂ))*L = Complex.I*z*L + -(Complex.I*((pm L k*L : ℝ) : ℂ)) := by push_cast; ring
    rw [ha,Complex.exp_add,PlaneWaveSymbol.exp_p_L,mul_one]
  have hminus (w : ℂ) : Complex.exp (Complex.I*w*L) * rawPlus L (-w) y x = rawMinus L w x y := by
    classical
    unfold rawPlus rawMinus BetheTransferKernelAdjoint.MinusOrder BetheTransferKernelAdjoint.displacement
    split_ifs
    · rw [← Complex.exp_add]
      congr 1
      ring
    · simp
  constructor
  · calc _ = (conj (phaseN k r (fun j => (x j : AddCircle L))) * phaseN k r (fun j => (y j : AddCircle L))) * rawPlus L z x y := by ring
         _ = _ := by rw [hp,PlaneWaveSymbol.phase_plus]
  · calc _ = (conj (phaseN k r (fun j => (x j : AddCircle L))) * phaseN k r (fun j => (y j : AddCircle L))) * rawMinus L z x y := by ring
         _ = _ := by rw [hp,PlaneWaveSymbol.phase_minus,he]; exact hminus _

theorem integral_shift (k : ℤ) (r : ℕ) (u : L2T L)
    (K H : (Fin r → AddCircle L) → (Fin r → AddCircle L) → ℂ)
    (he : ∀ x y, conj (phaseN k r x) * K x y * phaseN k r y = H x y) :
    (∫ x, ∫ y, conj ((prodLp (fun _ : Fin r => boost k u) : L2TN L r) x) * K x y *
      (prodLp (fun _ : Fin r => boost k u) : L2TN L r) y ∂torusPiMeasure L r ∂torusPiMeasure L r) =
    (∫ x, ∫ y, conj ((prodLp (fun _ : Fin r => u) : L2TN L r) x) * H x y *
      (prodLp (fun _ : Fin r => u) : L2TN L r) y ∂torusPiMeasure L r ∂torusPiMeasure L r) := by
  apply integral_congr_ae
  filter_upwards [prod_boost k r u] with x hx
  apply integral_congr_ae
  filter_upwards [prod_boost k r u] with y hy
  rw [hx,hy,map_mul]
  calc _ = conj ((prodLp (fun _ : Fin r => u) : L2TN L r) x) *
      (conj (phaseN k r x) * K x y * phaseN k r y) *
      (prodLp (fun _ : Fin r => u) : L2TN L r) y := by ring
       _ = _ := by rw [he]

theorem kernel_shift (k : ℤ) (r : ℕ) (u : L2T L) (z : ℂ) :
    kernelProductSymbol (orderedKernel L r z) (boost k u) =
      kernelProductSymbol (orderedKernel L r (z-(pm L k : ℂ))) u := by
  rw [PlaneWaveSymbol.kps_eq_inner,PlaneWaveSymbol.kps_eq_inner,
    BetheTransferOperators.inner_rawOperator,BetheTransferOperators.inner_rawOperator]
  have hrep (x : Fin r → AddCircle L) :
      (fun j => ((representatives L x j : ℝ) : AddCircle L)) = x := by
    funext j; exact AddCircle.coe_equivIco
  have hp (x y : Fin r → AddCircle L) := integrand_shift (L := L) k r z (representatives L x) (representatives L y)
  simp only [hrep] at hp
  congr 1
  · exact integral_shift k r u _ _ (fun x y => (hp x y).1)
  · exact integral_shift k r u _ _ (fun x y => (hp x y).2)

theorem exp_shift (k : ℤ) (z : ℂ) :
    Complex.exp (Complex.I*z*L) = Complex.exp (Complex.I*(z-(pm L k : ℂ))*L) := by
  have ha : Complex.I*(z-(pm L k : ℂ))*L = Complex.I*z*L + -(Complex.I*((pm L k*L : ℝ) : ℂ)) := by push_cast; ring
  rw [ha,Complex.exp_add,PlaneWaveSymbol.exp_p_L,mul_one]

/-- Covariance of the full quantum-derived product symbol for arbitrary L2 input. -/
theorem symbol_shift (κ : ℝ) (k : ℤ) (u : L2T L) (z : ℂ) :
    productSymbol L κ (boost k u) z = productSymbol L κ u (z-(pm L k : ℂ)) := by
  unfold productSymbol symbolTerm
  rw [← exp_shift]
  congr 1
  apply tsum_congr
  intro j
  rw [kernel_shift]

end QuantumNLS.RootMassBoostSymbol
#print axioms QuantumNLS.RootMassBoostSymbol.integrand_shift

#print axioms QuantumNLS.RootMassBoostSymbol.symbol_shift

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootMassBoostSymbol." ||
        n.toString.startsWith "_private.QuantumNLS.RootMassBoostSymbol." then
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
  Lean.logInfo m!"RootMassBoostSymbol audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
