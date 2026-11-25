import Mathlib
import QuantumNLS.RootNlsInvDisc
import QuantumNLS.RootIndexedMasses
import QuantumNLS.RootDensityIdentification
import QuantumNLS.PhysicalL2Normalization
import QuantumNLS.PhysicalContinuousBoundary
import QuantumNLS.RootTraceSymbolFinal

/-!
# R-BFCC01E8 `thm:root-nls-invariance` (ROOT_nls_invariance.tex:43-135)

"Suppose `u ∈ C([-T,T];H³(𝕋_L)) ∩ C¹([-T,T];H¹(𝕋_L))` solves (eq:root-derived-nls)
`i∂ₜu = −∂ₓ²u + 2κ|u|²u`. Then its quantum-derived discriminant, full-mass spectral measure, and every
indexed spectral mass are independent of time. The same conclusion holds for a continuous `H¹`
solution which is a limit, in `C([-T,T];H¹)`, of such regular solutions."

Vocabulary (all accepted, read-only):
* `H^s(𝕋_L)` is the Fourier realization `h04 L s`; `physical : h⁰ ≃ L²(𝕋_L)` and the maps
  `m10`, `m31`, `lap = −∂ₓ²`, `Fh = |u|²u` are those of R-63A99F0E (`prop:root-energy-vector-field`),
  whose equation (eq:root-derived-nls) is `I • X = −Uxx + 2κ C`, `Uxx = −physical (lap u)`;
* the quantum-derived discriminant is the DEF-013 transfer trace `L2SpatialTransfer.discriminant`
  (equal to `exp(−izL/2)` times the quantum product symbol, R-7E0532E7 `traceSymbol_all`);
  the quantum product symbol `NormalizedTransfer.productSymbol` is also shown constant;
* the full-mass spectral measure is `FullMass.Mmeas κ u` (R-043AB9AA);
* the indexed spectral masses are `(RootIndexedMasses.masses hκ u).1 n` (R-950BFB30).
The standing hypothesis `L, κ > 0` of the ROOT chapters is used.

Route (source proof): discriminant conservation by the derived Lax pair (stages NI-1..3);
the measure by the derived density formula from the constant discriminant ("Alternatively the
derived continuous density formula gives the same conclusion directly from the constant
discriminant", R-7E0532E7); the separators and indexed masses from the measure; the `H¹` limit by
continuity of the discriminant in `L²` (R-0C33082D) at each fixed time.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set
open QuantumNLS.Sobolev QuantumNLS.LocalWellPosedness QuantumNLS.F04Regularity
  QuantumNLS.RootEnergyVariation

namespace QuantumNLS.RootNlsInvariance
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootNlsInvDisc (m32)

variable {L : ℝ} [Fact (0 < L)]

/-- The `L²(𝕋_L)` vector of an `H³` datum. -/
def U3 (a : h04 L 3) : L2T L := physical (m10 (m31 a))

/-- `u_xx` of an `H³` datum, as in R-63A99F0E (`Uxx = −physical (lap u)`). -/
def uxx (a : h04 L 3) : L2T L := -physical (lap (m32 a))

/-- `|u|²u` of an `H³` datum, as in R-63A99F0E (`C = physical (m10 (Fh u))`). -/
def cub (a : h04 L 3) : L2T L := physical (m10 (Fh (le_refl (1 : ℝ)) (m31 a)))

/-- `u ∈ C([-T,T];H³) ∩ C¹([-T,T];H¹)` (time derivative `v`) solves
`i∂ₜu = −∂ₓ²u + 2κ|u|²u` on `[-T,T]`. -/
def IsRegularNLSSolution (κ T : ℝ) (u : ℝ → h04 L 3) (v : ℝ → h04 L 1) : Prop :=
  ContinuousOn u (Icc (-T) T) ∧ ContinuousOn v (Icc (-T) T) ∧
  (∀ t ∈ Icc (-T) T, HasDerivWithinAt (fun s => m31 (u s)) (v t) (Icc (-T) T) t) ∧
  ∀ t ∈ Icc (-T) T,
    Complex.I • physical (m10 (v t)) = -uxx (u t) + ((2 * κ : ℝ) : ℂ) • cub (u t)

/-- The quantum-derived discriminant (and quantum product symbol), the full-mass spectral measure,
and every indexed spectral mass of the curve `U` are independent of `t ∈ [-T,T]`. -/
def SpectralDataConstant {κ : ℝ} (hκ : 0 < κ) (T : ℝ) (U : ℝ → L2T L) : Prop :=
  ∀ t ∈ Icc (-T) T, ∀ s ∈ Icc (-T) T,
    (∀ z : ℂ, L2SpatialTransfer.discriminant κ (U t) z = L2SpatialTransfer.discriminant κ (U s) z) ∧
    (∀ z : ℂ, NormalizedTransfer.productSymbol L κ (U t) z =
      NormalizedTransfer.productSymbol L κ (U s) z) ∧
    FullMass.Mmeas κ (U t) = FullMass.Mmeas κ (U s) ∧
    ∀ n : ℤ, (RootIndexedMasses.masses hκ (U t)).1 n = (RootIndexedMasses.masses hκ (U s)).1 n

/-- The vocabulary is the classical one: `U3 b`, `uxx b` have the continuous representatives
`q = profileJet b 0`, `q'' = profileJet b 2` (with `q' = profileJet b 1` the classical derivatives),
and `cub b = |U|²U` almost everywhere. -/
theorem regular_vocabulary (b : h04 L 3) :
    (U3 b : AddCircle L → ℂ) =ᵐ[volume] ⇑(S1 (m31 b)) ∧
    (uxx b : AddCircle L → ℂ) =ᵐ[volume] ⇑(S1 (RootNlsInvDisc.jet2 b)) ∧
    (cub b : AddCircle L → ℂ) =ᵐ[volume] (fun y => ((‖U3 b y‖ ^ 2 : ℝ) : ℂ) * U3 b y) ∧
    ∀ x : ℝ, S1 (m31 b) (x : AddCircle L) = Def024CubicSmoothEmbedding.profileJet b 0 x ∧
      S1 (RootNlsInvDisc.jet2 b) (x : AddCircle L) = Def024CubicSmoothEmbedding.profileJet b 2 x ∧
      HasDerivAt (Def024CubicSmoothEmbedding.profileJet b 0)
        (Def024CubicSmoothEmbedding.profileJet b 1 x) x ∧
      HasDerivAt (Def024CubicSmoothEmbedding.profileJet b 1)
        (Def024CubicSmoothEmbedding.profileJet b 2 x) x := by
  have hx : uxx b = physical (m10 (RootNlsInvDisc.jet2 b)) := by
    rw [uxx, RootNlsInvDisc.lap_m32, map_neg, map_neg, neg_neg]
  refine ⟨physical_rep (m31 b), ?_, RootEnergyVectorField.cubic (m31 b), fun x =>
    ⟨RootNlsInvDisc.S1_m31 b x, RootNlsInvDisc.S1_jet2 b x, RootNlsInvDisc.hasDerivAt_jet0 b x,
      RootNlsInvDisc.hasDerivAt_jet1 b x⟩⟩
  rw [hx]
  exact physical_rep _

/-- The derived density formula: the quantum measure is a function of the discriminant. -/
theorem measure_eq_of_disc {κ : ℝ} (hκ : 0 < κ) {u v : L2T L}
    (h : ∀ z : ℂ, L2SpatialTransfer.discriminant κ u z = L2SpatialTransfer.discriminant κ v z) :
    PhysicalQuantumMeasure.measure hκ u = PhysicalQuantumMeasure.measure hκ v := by
  have hd : ∀ w : L2T L, PhysicalQuantumMeasure.measure hκ w = volume.withDensity
      (fun t => ENNReal.ofReal (RootDensityIdentification.dens κ w t)) := by
    intro w
    by_cases hw : w = 0
    · subst w
      have h0 : ∀ t, RootDensityIdentification.dens κ (0 : L2T L) t = 0 := by
        intro t
        have hi := PhysicalContinuousBoundary.boundary_im hκ (0 : L2T L) t
        rw [PhysicalContinuousBoundary.boundary_zero hκ t] at hi
        have hh : RootDensity.hfun |(L2SpatialTransfer.discriminant κ (0 : L2T L) (t : ℂ)).re| = 0 := by
          rw [← hi]; simp
        unfold RootDensityIdentification.dens
        rw [hh, mul_zero]
      rw [PhysicalQuantumMeasure.measure_zero]
      simp [h0]
    · exact RootDensityIdentification.root_density hκ hw
  rw [hd u, hd v]
  congr 1
  funext t
  simp only [RootDensityIdentification.dens, h (t : ℂ)]

/-- All spectral data are functions of the discriminant. -/
theorem data_eq_of_disc {κ : ℝ} (hκ : 0 < κ) {u v : L2T L}
    (h : ∀ z : ℂ, L2SpatialTransfer.discriminant κ u z = L2SpatialTransfer.discriminant κ v z) :
    (∀ z : ℂ, NormalizedTransfer.productSymbol L κ u z = NormalizedTransfer.productSymbol L κ v z) ∧
    FullMass.Mmeas κ u = FullMass.Mmeas κ v ∧
    ∀ n : ℤ, (RootIndexedMasses.masses hκ u).1 n = (RootIndexedMasses.masses hκ v).1 n := by
  have hm := measure_eq_of_disc hκ h
  refine ⟨fun z => ?_, ?_, fun n => ?_⟩
  · have hu := RootTraceSymbolFinal.traceSymbol_all hκ.le u z
    have hv := RootTraceSymbolFinal.traceSymbol_all hκ.le v z
    rw [h z, ← hv] at hu
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hu
  · rw [← PhysicalL2Normalization.measure_eq_Mmeas hκ u, ← PhysicalL2Normalization.measure_eq_Mmeas hκ v,
      hm]
  · rw [RootIndexedMasses.masses_eq_of_measure_eq hκ hm]

/-- Continuity of the discriminant along `H¹ → L²`. -/
lemma continuous_disc_h1 (κ : ℝ) (z : ℂ) :
    Continuous (fun a : h04 L 1 => L2SpatialTransfer.discriminant κ (physical (m10 a)) z) := by
  have hc := DiscParamContinuity.continuous_discriminant_param (L := L) z
  have h1 : Continuous (fun a : h04 L 1 => physical (m10 a)) :=
    (physical (L := L)).continuous.comp (m10 (L := L)).continuous
  have hp : Continuous (fun v : L2T L => ((κ, v) : ℝ × L2T L)) :=
    (continuous_const (y := κ)).prodMk continuous_id
  have hv := hc.comp (f := fun v : L2T L => ((κ, v) : ℝ × L2T L)) hp
  have hw := hv.comp (f := fun a : h04 L 1 => physical (m10 a)) h1
  exact hw

/-- **R-BFCC01E8 `thm:root-nls-invariance`.** -/
theorem root_nls_invariance {κ : ℝ} (hκ : 0 < κ) (T : ℝ) :
    (∀ (u : ℝ → h04 L 3) (v : ℝ → h04 L 1), IsRegularNLSSolution κ T u v →
      SpectralDataConstant hκ T (fun t => U3 (u t))) ∧
    (∀ (w : ℝ → h04 L 1) (us : ℕ → ℝ → h04 L 3) (vs : ℕ → ℝ → h04 L 1),
      ContinuousOn w (Icc (-T) T) →
      (∀ k, IsRegularNLSSolution κ T (us k) (vs k)) →
      TendstoUniformlyOn (fun k t => m31 (us k t)) w atTop (Icc (-T) T) →
      SpectralDataConstant hκ T (fun t => physical (m10 (w t)))) := by
  have reg : ∀ (u : ℝ → h04 L 3) (v : ℝ → h04 L 1), IsRegularNLSSolution κ T u v →
      ∀ z : ℂ, ∀ t ∈ Icc (-T) T, ∀ s ∈ Icc (-T) T,
        L2SpatialTransfer.discriminant κ (U3 (u t)) z = L2SpatialTransfer.discriminant κ (U3 (u s)) z := by
    intro u v hsol z
    obtain ⟨_, _, hd, he⟩ := hsol
    have he' : ∀ t ∈ Icc (-T) T, Complex.I • physical (m10 (v t)) =
        physical (lap (m32 (u t))) + ((2 * κ : ℝ) : ℂ) •
          physical (m10 (Fh (le_refl (1 : ℝ)) (m31 (u t)))) := by
      intro t ht
      rw [he t ht, uxx, cub, neg_neg]
    exact RootNlsInvDisc.disc_const hκ.le hd he' z
  refine ⟨fun u v hsol t ht s hs => ?_, fun w us vs _ hsol hlim t ht s hs => ?_⟩
  · have hz : ∀ z : ℂ, L2SpatialTransfer.discriminant κ (U3 (u t)) z =
        L2SpatialTransfer.discriminant κ (U3 (u s)) z := fun z => reg u v hsol z t ht s hs
    exact ⟨hz, data_eq_of_disc hκ hz⟩
  · have hz : ∀ z : ℂ, L2SpatialTransfer.discriminant κ (physical (m10 (w t))) z =
        L2SpatialTransfer.discriminant κ (physical (m10 (w s))) z := by
      intro z
      have hcont := continuous_disc_h1 (L := L) κ z
      have lt := (hcont.tendsto (w t)).comp (hlim.tendsto_at ht)
      have ls := (hcont.tendsto (w s)).comp (hlim.tendsto_at hs)
      have heq : (fun k => L2SpatialTransfer.discriminant κ (physical (m10 (m31 (us k t)))) z) =
          fun k => L2SpatialTransfer.discriminant κ (physical (m10 (m31 (us k s)))) z :=
        funext fun k => reg (us k) (vs k) (hsol k) z t ht s hs
      have lt' : Tendsto (fun k => L2SpatialTransfer.discriminant κ (physical (m10 (m31 (us k t)))) z)
          atTop (𝓝 (L2SpatialTransfer.discriminant κ (physical (m10 (w t))) z)) := lt
      have ls' : Tendsto (fun k => L2SpatialTransfer.discriminant κ (physical (m10 (m31 (us k s)))) z)
          atTop (𝓝 (L2SpatialTransfer.discriminant κ (physical (m10 (w s))) z)) := ls
      rw [heq] at lt'
      exact tendsto_nhds_unique lt' ls'
    exact ⟨hz, data_eq_of_disc hκ hz⟩

end QuantumNLS.RootNlsInvariance

#print axioms QuantumNLS.RootNlsInvariance.regular_vocabulary
#print axioms QuantumNLS.RootNlsInvariance.measure_eq_of_disc
#print axioms QuantumNLS.RootNlsInvariance.data_eq_of_disc
#print axioms QuantumNLS.RootNlsInvariance.root_nls_invariance
