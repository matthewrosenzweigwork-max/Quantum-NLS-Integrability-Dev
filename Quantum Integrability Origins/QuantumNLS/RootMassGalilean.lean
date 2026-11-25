import QuantumNLS.RootMassBoostSymbol

/-! Galilean covariance of the canonical physical law and selected interval masses. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootMassGalilean
open PhysicalTensor (L2T)
open RootMassBoostSymbol
open PlaneWaveSymbol (pm)
open EmpiricalRapidity (cauchyTransform)
open RootMeasureComplex (fz HighHalf)
variable {L κ : ℝ} [Fact (0 < L)]

theorem cauchy_map (μ : Measure ℝ) (p : ℝ) {z : ℂ} (hz : 0 < z.im) :
    cauchyTransform (μ.map (fun t => t+p)) z = cauchyTransform μ (z-(p : ℂ)) := by
  unfold cauchyTransform
  have hc : Continuous (fun t : ℝ => (z-(t : ℂ))⁻¹) :=
    (continuous_const.sub Complex.continuous_ofReal).inv₀ (fun t he => by
      change z-(t : ℂ) = 0 at he
      have hi := congrArg Complex.im he
      simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
      linarith)
  rw [integral_map (measurable_add_const p).aemeasurable hc.aestronglyMeasurable]
  congr 1
  funext t
  congr 1
  push_cast
  ring

/-- Literal translation of the canonical full-mass quantum law under a boost. -/
theorem measure_boost (hκ : 0 < κ) (k : ℤ) (u : L2T L) :
    PhysicalQuantumMeasure.measure hκ (boost k u) =
      (PhysicalQuantumMeasure.measure hκ u).map (fun t => t+pm L k) := by
  simp_rw [PhysicalL2Normalization.measure_eq_Mmeas]
  by_cases hu : u = 0
  · have hb : boost k u = 0 := by
      apply norm_eq_zero.mp
      rw [norm_boost,hu,norm_zero]
    rw [hb,hu,FullMass.Mmeas_zero,Measure.map_zero]
  · have hb : boost k u ≠ 0 := by
      intro he
      have hh := norm_boost k u
      rw [he,norm_zero] at hh
      exact hu (norm_eq_zero.mp hh.symm)
    let η : ℝ := max 1 (max (4*(κ*‖u‖^2)) (Real.log 16/L))
    have hη : 0 < η := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    apply CauchyUniqueness.cauchy_ext _ _ hη
    intro t
    let z : ℂ := (t : ℂ)+(η : ℂ)*Complex.I
    have him : z.im = η := by simp [z]
    have hz : 0 < z.im := him ▸ hη
    have hhigh : HighHalf L (κ*‖u‖^2) z := by
      constructor
      · rw [him]; exact (le_max_left _ _).trans (le_max_right _ _)
      · rw [him]
        have hh : Real.log 16/L ≤ η := (le_max_right _ _).trans (le_max_right _ _)
        exact (div_le_iff₀ (Fact.out : 0 < L)).mp hh |>.trans_eq (mul_comm _ _)
    have hhighb : HighHalf L (κ*‖boost k u‖^2) z := by simpa only [norm_boost] using hhigh
    have hhighs : HighHalf L (κ*‖u‖^2) (z-(pm L k : ℂ)) := by simpa [HighHalf] using hhigh
    change cauchyTransform (FullMass.Mmeas κ (boost k u)) z =
      cauchyTransform ((FullMass.Mmeas κ u).map (fun s => s+pm L k)) z
    rw [cauchy_map _ _ hz]
    obtain ⟨_,_,huniq⟩ := FullMass.mass_characterization hκ hb hhighb
    obtain ⟨hbound,heq,_⟩ := FullMass.mass_characterization hκ hu hhighs
    apply Eq.symm
    apply huniq
    · simpa only [norm_boost,CauchyUniqueness.cauchyTransform,EmpiricalRapidity.cauchyTransform,Complex.sub_im,Complex.ofReal_im,sub_zero] using hbound
    · rw [symbol_shift]
      rw [fz,exp_shift k z]
      exact heq

/-- The boundary is the quantum-selected branch after shifting the spectral parameter. -/
theorem boundary_boost (hκ : 0 < κ) (k : ℤ) (u : L2T L) (x : ℝ) :
    PhysicalContinuousBoundary.boundary hκ (boost k u) x =
      PhysicalContinuousBoundary.boundary hκ u (x-pm L k) + ((pm L k*L/2 : ℝ) : ℂ) := by
  have ht := (PhysicalSourceFinal.sourceFacts hκ u).boundary (x-pm L k)
  have hb := (PhysicalSourceFinal.sourceFacts hκ (boost k u)).boundary x
  change Tendsto (fun ε : ℝ => SpatialTransfer.boundaryPhase L κ
    (PhysicalQuantumMeasure.measure hκ u) (((x-pm L k : ℝ) : ℂ)+(ε : ℂ)*Complex.I))
    (𝓝[>] 0) (𝓝 (PhysicalContinuousBoundary.boundary hκ u (x-pm L k))) at ht
  change Tendsto (fun ε : ℝ => SpatialTransfer.boundaryPhase L κ
    (PhysicalQuantumMeasure.measure hκ (boost k u)) ((x : ℂ)+(ε : ℂ)*Complex.I))
    (𝓝[>] 0) (𝓝 (PhysicalContinuousBoundary.boundary hκ (boost k u) x)) at hb
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ (boost k u)) ((x : ℂ)+(ε : ℂ)*Complex.I) =
      SpatialTransfer.boundaryPhase L κ (PhysicalQuantumMeasure.measure hκ u) (((x-pm L k : ℝ) : ℂ)+(ε : ℂ)*Complex.I) +
        ((pm L k*L/2 : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [SpatialTransfer.boundaryPhase,measure_boost,cauchy_map _ _ (by simpa using hε),SpatialTransfer.boundaryPhase]
    have hz : (x : ℂ)+(ε : ℂ)*Complex.I-(pm L k : ℂ) = (((x-pm L k : ℝ) : ℂ)+(ε : ℂ)*Complex.I) := by push_cast; ring
    rw [hz]
    push_cast
    ring
  exact tendsto_nhds_unique hb ((ht.add_const _).congr' (he.mono fun ε hε => hε.symm))

theorem separator_boost (hκ : 0 < κ) (k n : ℤ) (u : L2T L) :
    RootIndexedPhase.separator hκ (boost k u) n = RootIndexedPhase.separator hκ u (n-k)+pm L k := by
  apply Eq.symm
  apply (PhysicalSourceFinal.sourceFacts hκ (boost k u)).phase.separator_unique
  change (PhysicalContinuousBoundary.boundary hκ (boost k u) _).re = _
  rw [boundary_boost,add_sub_cancel_right,Complex.add_re,Complex.ofReal_re]
  have hs := (PhysicalSourceFinal.sourceFacts hκ u).phase.separator_spec (n-k)
  change (PhysicalContinuousBoundary.boundary hκ u _).re = _ at hs
  rw [hs]
  unfold pm MonotoneIndexedMasses.level IndexedMasses.level
  push_cast
  field_simp [(Fact.out : 0 < L).ne']
  ring

/-- A boost by exp(2 pi i k x/L) shifts the physical mass index by k. -/
theorem masses_boost (hκ : 0 < κ) (k n : ℤ) (u : L2T L) :
    (RootIndexedMasses.masses hκ (boost k u)).1 n = (RootIndexedMasses.masses hκ u).1 (n-k) := by
  change (PhysicalQuantumMeasure.measure hκ (boost k u) (Ioo
    (RootIndexedPhase.separator hκ (boost k u) (n-1))
    (RootIndexedPhase.separator hκ (boost k u) n))).toReal = _
  rw [measure_boost,separator_boost,separator_boost,
    Measure.map_apply (measurable_add_const _) measurableSet_Ioo]
  have he : (fun t : ℝ => t+pm L k) ⁻¹' (Ioo
      (RootIndexedPhase.separator hκ u (n-1-k)+pm L k)
      (RootIndexedPhase.separator hκ u (n-k)+pm L k)) =
      Ioo (RootIndexedPhase.separator hκ u ((n-k)-1)) (RootIndexedPhase.separator hκ u (n-k)) := by
    rw [show n-1-k = (n-k)-1 by ring]
    ext t
    simp only [mem_preimage,mem_Ioo,add_lt_add_iff_right]
  rw [he]
  rfl
end QuantumNLS.RootMassGalilean
#print axioms QuantumNLS.RootMassGalilean.masses_boost

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.RootMassGalilean." ||
        n.toString.startsWith "_private.QuantumNLS.RootMassGalilean." then
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
  Lean.logInfo m!"RootMassGalilean audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
