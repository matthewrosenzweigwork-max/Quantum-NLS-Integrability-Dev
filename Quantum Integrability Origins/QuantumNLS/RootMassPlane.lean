import QuantumNLS.RootMassScaling
import QuantumNLS.PlaneWaveSemicircle

/-! The arbitrary-amplitude plane-wave formula for the literal physical indexed masses. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootMassPlane
open PhysicalTensor (L2T)
open QuantumNLS.Fourier (modeLp)
open EmpiricalRapidity (cauchyTransform)
open PlaneWaveSymbol (pm)
variable {L κ : ℝ} [Fact (0 < L)]

theorem measure_mode (hκ : 0 < κ) (k : ℤ) :
    PhysicalQuantumMeasure.measure hκ (modeLp L k) = PlaneWaveSemicircle.nuP (κ/L) (pm L k) := by
  have hn := OneParticleBorn.norm_modeLp (L := L) k
  have hu : modeLp L k ≠ 0 := by intro he; rw [he,norm_zero] at hn; norm_num at hn
  rw [PhysicalL2Normalization.measure_eq_Mmeas,FullMass.Mmeas_of_ne _ hu,hn]
  simp only [one_pow,ENNReal.ofReal_one,one_smul,mul_one]
  simpa only [FullMass.unitDir,hn,inv_one,Complex.ofReal_one,one_smul] using
    PlaneWaveSemicircle.plane_wave_semicircle hκ k hn

/-- The boundary Cauchy value satisfies the semicircle quadratic by taking an upper limit. -/
theorem boundary_quadratic (hκ : 0 < κ) (k : ℤ) (x : ℝ) :
    let g := (((L*x/2 : ℝ) : ℂ) - PhysicalContinuousBoundary.boundary hκ (modeLp L k) x)/(κ : ℂ)
    ((κ/L : ℝ) : ℂ)*g^2 - ((x-pm L k : ℝ) : ℂ)*g + 1 = 0 := by
  let g := (((L*x/2 : ℝ) : ℂ) - PhysicalContinuousBoundary.boundary hκ (modeLp L k) x)/(κ : ℂ)
  have hz : Tendsto (fun ε : ℝ => (x : ℂ)+(ε : ℂ)*Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have h0 : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using (h0.mul_const Complex.I).const_add (x : ℂ)
  have hb := (PhysicalSourceFinal.sourceFacts hκ (modeLp L k)).boundary x
  change Tendsto (fun ε : ℝ => SpatialTransfer.boundaryPhase L κ
    (PhysicalQuantumMeasure.measure hκ (modeLp L k)) ((x : ℂ)+(ε : ℂ)*Complex.I))
    (𝓝[>] 0) (𝓝 (PhysicalContinuousBoundary.boundary hκ (modeLp L k) x)) at hb
  have hg : Tendsto (fun ε : ℝ => cauchyTransform (PhysicalQuantumMeasure.measure hκ (modeLp L k))
      ((x : ℂ)+(ε : ℂ)*Complex.I)) (𝓝[>] 0) (𝓝 g) := by
    have hh := (((hz.const_mul (L : ℂ)).div_const 2).sub hb).div_const (κ : ℂ)
    have he : (fun ε : ℝ => ((L : ℂ)*((x : ℂ)+(ε : ℂ)*Complex.I)/2 -
      SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ (modeLp L k))
        ((x : ℂ)+(ε : ℂ)*Complex.I))/(κ : ℂ)) =
        (fun ε : ℝ => cauchyTransform (PhysicalQuantumMeasure.measure hκ (modeLp L k))
        ((x : ℂ)+(ε : ℂ)*Complex.I)) := by
      funext ε
      unfold SpatialTransfer.boundaryPhase
      field_simp [show (κ : ℂ) ≠ 0 by exact_mod_cast hκ.ne']; ring
    rw [he] at hh
    simpa [g] using hh
  have ht := ((hg.pow 2).const_mul ((κ/L : ℝ) : ℂ)).sub ((hz.sub_const (pm L k : ℂ)).mul hg)
  have ht' := ht.add_const 1
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ((κ/L : ℝ) : ℂ)*(cauchyTransform (PhysicalQuantumMeasure.measure hκ (modeLp L k))
        ((x : ℂ)+(ε : ℂ)*Complex.I))^2 -
        ((x : ℂ)+(ε : ℂ)*Complex.I-(pm L k : ℂ))*
          cauchyTransform (PhysicalQuantumMeasure.measure hκ (modeLp L k))
            ((x : ℂ)+(ε : ℂ)*Complex.I) + 1 = 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hC : CauchyUniqueness.cauchyTransform (PhysicalQuantumMeasure.measure hκ (modeLp L k))
        ((x : ℂ)+(ε : ℂ)*Complex.I) = SemicircleStieltjes.hh (κ/L)
          ((x : ℂ)+(ε : ℂ)*Complex.I-(pm L k : ℂ)) := by
      rw [measure_mode]
      exact PlaneWaveSemicircle.cauchy_nuP (div_pos hκ (Fact.out : 0 < L)) _ (by simpa using hε)
    change ((κ/L : ℝ) : ℂ)*(CauchyUniqueness.cauchyTransform _ _)^2 -
      ((x : ℂ)+(ε : ℂ)*Complex.I-(pm L k : ℂ))*CauchyUniqueness.cauchyTransform _ _ + 1 = 0
    simp only [hC]
    exact SemicircleStieltjes.quadratic_hh (div_pos hκ (Fact.out : 0 < L)) (by simpa using hε)
  have hh := tendsto_nhds_unique ht' (tendsto_const_nhds.congr' (he.mono fun ε hε => hε.symm))
  simpa [g] using hh

/-- On the one positive-density interval the quantum-selected real phase is exactly k*pi. -/
theorem phase_mode (hκ : 0 < κ) (k : ℤ) {x : ℝ}
    (hx : (x-pm L k)^2 < 4*(κ/L)) :
    RootIndexedPhase.theta hκ (modeLp L k) x = (k : ℝ)*Real.pi := by
  let g := (((L*x/2 : ℝ) : ℂ) - PhysicalContinuousBoundary.boundary hκ (modeLp L k) x)/(κ : ℂ)
  have he := boundary_quadratic (L := L) hκ k x
  change ((κ/L : ℝ) : ℂ)*g^2 - ((x-pm L k : ℝ) : ℂ)*g + 1 = 0 at he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,pow_two,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.one_re,Complex.zero_re] at hre
  simp only [pow_two,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
    Complex.one_im,Complex.zero_im] at him
  have ha : 0 < κ/L := div_pos hκ (Fact.out : 0 < L)
  have hne : g.im ≠ 0 := by
    intro hzero
    rw [hzero] at hre
    have hsq := sq_nonneg (2*(κ/L)*g.re-(x-pm L k))
    have hmul := congrArg (fun t : ℝ => (4*(κ/L))*t) hre
    nlinarith
  have hgre : 2*(κ/L)*g.re = x-pm L k := by
    have hh : (2*(κ/L)*g.re-(x-pm L k))*g.im = 0 := by nlinarith [him]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hne)
  have hg : g.re = (L*x/2-RootIndexedPhase.theta hκ (modeLp L k) x)/κ := by
    simp [g,Complex.div_ofReal_re]
  rw [hg] at hgre
  have hL : L ≠ 0 := (Fact.out : 0 < L).ne'
  field_simp [hL,hκ.ne'] at hgre
  unfold pm at hgre
  field_simp [hL] at hgre
  nlinarith

/-- Almost every semicircle point has the interior phase label. -/
theorem ae_phase_mode (hκ : 0 < κ) (k : ℤ) :
    ∀ᵐ x ∂(PhysicalQuantumMeasure.measure hκ (modeLp L k)),
      RootIndexedPhase.theta hκ (modeLp L k) x = (k : ℝ)*Real.pi := by
  rw [measure_mode]
  unfold PlaneWaveSemicircle.nuP
  apply (ae_map_iff (measurable_add_const _).aemeasurable
    (by
      exact (isClosed_eq (Complex.continuous_re.comp
        (PhysicalContinuousBoundary.continuous_boundary hκ (modeLp L k))) continuous_const).measurableSet)).mpr
  unfold SemicircleStieltjes.scMeasure
  apply (ae_withDensity_iff (SemicircleStieltjes.measurable_dens (κ/L))).mpr
  apply Eventually.of_forall
  intro t ht
  apply phase_mode hκ k
  have hw : 0 < SemicircleODE.w (κ/L) t / (2*Real.pi*(κ/L)) :=
    ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr ht)
  have hp : 0 < SemicircleODE.w (κ/L) t :=
    (div_pos_iff_of_pos_right (by have hL : 0 < L := Fact.out; positivity : 0 < 2*Real.pi*(κ/L))).mp hw
  have hs := Real.sqrt_pos.mp hp
  simpa [SemicircleODE.w] using (show (t+pm L k-pm L k)^2 < 4*(κ/L) by nlinarith)

/-- All the mass of a normalized plane wave has exactly its Fourier index. -/
theorem masses_mode (hκ : 0 < κ) (k n : ℤ) :
    (RootIndexedMasses.masses hκ (modeLp L k)).1 n = if n=k then 1 else 0 := by
  classical
  let P := (PhysicalSourceFinal.sourceFacts hκ (modeLp L k)).phase
  have he : (Ioo (P.separator (n-1)) (P.separator n)) =ᵐ[
      PhysicalQuantumMeasure.measure hκ (modeLp L k)] (if n=k then univ else ∅) := by
    filter_upwards [ae_phase_mode hκ k] with t ht
    simp only [mem_Ioo,P.separator_lt_iff,P.lt_separator_iff]
    apply propext
    change (MonotoneIndexedMasses.level (n-1) < RootIndexedPhase.theta hκ (modeLp L k) t ∧
      RootIndexedPhase.theta hκ (modeLp L k) t < MonotoneIndexedMasses.level n) ↔ _
    rw [ht]
    dsimp [MonotoneIndexedMasses.level,IndexedMasses.level]
    push_cast
    by_cases hn : n=k
    · subst n
      simp only [ite_true,mem_univ,iff_true]
      constructor <;> nlinarith [Real.pi_pos]
    · simp only [ite_eq_right hn,mem_empty_iff_false,iff_false,not_and]
      intro hlo hhi
      have hk0 : (n : ℝ)-1 < k := by nlinarith [Real.pi_pos]
      have hk1 : (k : ℝ) < n+1 := by nlinarith [Real.pi_pos]
      have hh : n-1 < k ∧ k < n+1 := by exact_mod_cast And.intro hk0 hk1
      omega
  change (PhysicalQuantumMeasure.measure hκ (modeLp L k) (Ioo (P.separator (n-1)) (P.separator n))).toReal = _
  rw [measure_congr he]
  split_ifs with hn
  · rw [PhysicalQuantumMeasure.measure_univ,OneParticleBorn.norm_modeLp]
    norm_num
  · simp

/-- Arbitrary complex amplitude in the normalized mode convention. -/
theorem masses_plane (hκ : 0 < κ) (c : ℂ) (k n : ℤ) :
    (RootIndexedMasses.masses hκ (c • modeLp L k)).1 n = if n=k then ‖c‖^2 else 0 := by
  classical
  by_cases hc : c=0
  · subst c
    simp only [zero_smul]
    change (PhysicalQuantumMeasure.measure hκ (0 : L2T L) _).toReal = _
    simp
  · rw [RootMassScaling.masses_smul hκ c hc,masses_mode]
    split_ifs <;> simp

/-- Identification of the printed unnormalized plane wave on the actual L2 carrier. -/
theorem plane_coe (a : ℂ) (k : ℤ) :
    ((((Real.sqrt L : ℂ)*a) • modeLp L k : L2T L) : AddCircle L → ℂ) =ᵐ[volume]
      fun x => a * fourier k x := by
  filter_upwards [Lp.coeFn_smul ((Real.sqrt L : ℂ)*a) (modeLp L k),Fourier.coeFn_modeLp L k] with x hx hm
  rw [hx]
  change ((Real.sqrt L : ℂ)*a) * (modeLp L k : AddCircle L → ℂ) x = _
  rw [hm,Fourier.mode]
  have hs : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Fact.out : 0 < L)).ne'
  push_cast
  field_simp [hs]

/-- In the printed unnormalized convention u(x)=a exp(2*pi*i*k*x/L). -/
theorem masses_plane_amplitude (hκ : 0 < κ) (a : ℂ) (k n : ℤ) :
    (RootIndexedMasses.masses hκ (((Real.sqrt L : ℂ)*a) • modeLp L k)).1 n =
      if n=k then L*‖a‖^2 else 0 := by
  rw [masses_plane]
  split_ifs
  · rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (Fact.out : 0 < L).le]
  · rfl
end QuantumNLS.RootMassPlane
#print axioms QuantumNLS.RootMassPlane.masses_plane_amplitude

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootMassPlane." ||
        n.toString.startsWith "_private.QuantumNLS.RootMassPlane." then
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
  Lean.logInfo m!"RootMassPlane audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
