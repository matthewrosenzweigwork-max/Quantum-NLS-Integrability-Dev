import NlsGge.GK38.PairPotential
import NlsGge.Hierarchy.PlaneCoverIdentification38
import NlsGge.Hierarchy.ALPlaneConsistency38

/-!
# F1 probes: cover of a constant potential, real slice of a plane wave

Regression instances for the representative convention of `PairPotential.lean`
(plan section 6.2, F1; book Chapter I, section 1: period one on `[0,1]`, doubled interval `[0,2]`).
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis NlsGge.SpectralFoundations
open NlsGge.AblowitzLadik (planeWaveCoeff38)

local instance spatialFinite38 : IsFiniteMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

/-! ### Constant potentials -/

/-- The constant class `c` in `PhysicalL2`. -/
def constL2 (c : ℂ) : PhysicalL2 := Lp.const 2 spatialMeasure c

/-- The cover of a constant function is the constant, a.e. on all of `ℝ`. -/
theorem coverRep38_const_ae (c : ℂ) : ∀ᵐ t : ℝ, coverRep38 (constL2 c) t = c := by
  have h := ae_real_of_ae_spectral (p := fun x => naturalPhysicalCoverL2 (constL2 c) x = c) (by
    filter_upwards [naturalPhysicalCoverL2_ae (constL2 c),
      naturalPhysicalCover_preserving.quasiMeasurePreserving.ae (Lp.coeFn_const 2 spatialMeasure c)]
      with x hx hy
    rw [hx]; exact hy)
  exact h

theorem realSlice_constL2 (a : ℂ) : realSlice (constL2 a) = (constL2 a, constL2 (star a)) := by
  refine Prod.ext rfl (Lp.ext ?_)
  unfold constL2
  filter_upwards [Lp.coeFn_star (Lp.const 2 spatialMeasure a), Lp.coeFn_const 2 spatialMeasure a,
    Lp.coeFn_const 2 spatialMeasure (star a)] with x h1 h2 h3
  change ((star (Lp.const 2 spatialMeasure a) : PhysicalL2) : PhysicalCircle → ℂ) x = _
  rw [h1, Pi.star_apply, h2, h3]
  rfl

/-- The pair coefficient of a constant pair `(a, b)` is a.e. the constant matrix, so its
square is `(ab - z²) I` a.e. (compare `zsCoeffPair_const_sq`). -/
theorem zsCoeffPot38_const_ae (a b z : ℂ) :
    ∀ᵐ t : ℝ, zsCoeffPot38 (constL2 a, constL2 b) z t =
      zsCoeffPair (fun _ => a) (fun _ => b) z t := by
  filter_upwards [coverRep38_const_ae a, coverRep38_const_ae b] with t h1 h2
  unfold zsCoeffPot38 zsCoeffPair potRepFst38 potRepSnd38
  simp only [h1, h2]

theorem zsCoeffPot38_const_sq_ae (a b z : ℂ) :
    ∀ᵐ t : ℝ, zsCoeffPot38 (constL2 a, constL2 b) z t * zsCoeffPot38 (constL2 a, constL2 b) z t
      = (a * b - z ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  filter_upwards [zsCoeffPot38_const_ae a b z] with t ht
  rw [ht]; exact zsCoeffPair_const_sq a b z t

/-- Real-slice constant `u ≡ a`: the pair coefficient squares to `(|a|² - z²) I` a.e. -/
theorem zsCoeffPot38_realSlice_const_sq_ae (a z : ℂ) :
    ∀ᵐ t : ℝ, zsCoeffPot38 (realSlice (constL2 a)) z t *
        zsCoeffPot38 (realSlice (constL2 a)) z t
      = (a * star a - z ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [realSlice_constL2]
  exact zsCoeffPot38_const_sq_ae a (star a) z

/-- The `L¹` size of the constant real slice `u ≡ a` is `2|a|` (`∫₀¹ (|a| + |ā|)`). -/
theorem potL1Norm38_realSlice_const (a : ℂ) : potL1Norm38 (realSlice (constL2 a)) = 2 * ‖a‖ := by
  rw [realSlice_constL2]
  unfold potL1Norm38
  have : ∀ᵐ t : ℝ, ‖potRepFst38 (constL2 a, constL2 (star a)) t‖ +
      ‖potRepSnd38 (constL2 a, constL2 (star a)) t‖ = 2 * ‖a‖ := by
    filter_upwards [coverRep38_const_ae a, coverRep38_const_ae (star a)] with t h1 h2
    simp only [potRepFst38, potRepSnd38, h1, h2, norm_star]; ring
  rw [intervalIntegral.integral_congr_ae (by filter_upwards [this] with t ht _ using ht)]
  simp

/-! ### Plane wave `u = t e^{2πikx}` -/

/-- The plane wave `t e^{2πikx}` as a physical `L²` class. -/
def planeWaveL2 (N : ℕ) (k : ℤ) (t : ℝ) : PhysicalL2 := planeL2 N (planeWaveCoeff38 N k t)

/-- Explicit representatives of `realSlice (t e^{2πikx})` on the doubled interval `(0,2]`:
`φ₁ = t e^{2πikx}`, `φ₂ = t e^{-2πikx}` (a.e.). -/
theorem potRep_realSlice_planeWave (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t : ℝ) :
    potRepFst38 (realSlice (planeWaveL2 N k t)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 2)]
        (fun x : ℝ => (t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) ∧
    potRepSnd38 (realSlice (planeWaveL2 N k t)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 2)]
        (fun x : ℝ => (t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)))) := by
  have h1 : potRepFst38 (realSlice (planeWaveL2 N k t)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 2)]
      (fun x : ℝ => (t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))) := by
    have := NlsGge.HierarchyRiccati.Core.planeReal_cover_ae38 N (planeWaveCoeff38 N k t)
    rw [NlsGge.AblowitzLadik.planeReal_planeWave38 N k hk t] at this
    exact this
  refine ⟨h1, ?_⟩
  filter_upwards [h1, ae_restrict_of_ae (potRepSnd38_realSlice_ae (planeWaveL2 N k t))]
    with x hx hy
  have hw : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) =
      -(2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_intCast]
    ring
  rw [hy, hx, Complex.star_def, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hw]

/-- The pair coefficient of the plane wave is explicit on `(0,2]`. -/
theorem zsCoeffPot38_realSlice_planeWave (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t : ℝ) (z : ℂ) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 2)),
      zsCoeffPot38 (realSlice (planeWaveL2 N k t)) z x =
        zsCoeffPair
          (fun x : ℝ => (t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)))
          (fun x : ℝ => (t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))))
          z x := by
  obtain ⟨h1, h2⟩ := potRep_realSlice_planeWave N k hk t
  filter_upwards [h1, h2] with x hx hy
  unfold zsCoeffPot38 zsCoeffPair
  simp only [hx, hy]

end

end NlsGge.GK38
