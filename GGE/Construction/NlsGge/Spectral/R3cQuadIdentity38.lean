import NlsGge.Hierarchy.RiccatiPeriodicSolutionAsymptotic38
import NlsGge.Hierarchy.GaussianTailCovarianceBernstein38
import NlsGge.Spectral.QuadraticRiccatiRemainder38
import NlsGge.Spectral.R3cResolventCore38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.HierarchyRiccati.Core

/-! # R3c piece P4b: `quadRiccati38` is the real part of the pairing `⟪U, R Ū⟫`

For a finite Fourier plane, the resolvent `R = (∂ + 2η)⁻¹` is diagonal on the exponentials, so
`R Ū = Σ conj(z_i)/(2η - 2π i n_i) e_{-n_i}`, and orthogonality of `e_n` on `[0,1]` gives
`∫ U · R Ū = Σ |z_i|²/(2η - 2π i n_i)`, whose real part is `Σ |z_i|² 2η/(4η² + 4π²n_i²)`. -/

/-- the exponential `e_k(x) = exp(2π i k x)` -/
def expMode38 (k : ℤ) (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))

theorem continuous_expMode38 (k : ℤ) : Continuous (expMode38 k) := by
  unfold expMode38
  fun_prop

theorem expMode38_add (k l : ℤ) (x : ℝ) : expMode38 k x * expMode38 l x = expMode38 (k + l) x := by
  unfold expMode38
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem star_expMode38 (k : ℤ) (x : ℝ) : star (expMode38 k x) = expMode38 (-k) x := by
  unfold expMode38
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    Complex.conj_ofNat, Int.cast_neg]
  ring

theorem expMode38_periodic (k : ℤ) : Function.Periodic (expMode38 k) 1 := by
  intro x
  unfold expMode38
  have h : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (((x + 1 : ℝ)) : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem hasDerivAt_expMode38 (k : ℤ) (x : ℝ) :
    HasDerivAt (expMode38 k) ((2 * Real.pi * Complex.I * (k : ℂ)) * expMode38 k x) x := by
  unfold expMode38
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w))
      (Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) *
        (2 * Real.pi * Complex.I * (k : ℂ))) (x : ℂ) :=
    ((hasDerivAt_id (x : ℂ)).const_mul (2 * Real.pi * Complex.I * (k : ℂ))).cexp.congr_deriv
      (by simp)
  have h2 := h1.comp_ofReal
  convert h2 using 1
  ring

theorem integral_expMode38 (k : ℤ) :
    ∫ x in (0:ℝ)..1, expMode38 k x = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    simp [expMode38]
  · rw [show (if k = 0 then (1:ℂ) else 0) = 0 from by simp [hk]]
    have hc : (2 * Real.pi * Complex.I * (k : ℂ)) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    unfold expMode38
    rw [intervalIntegral.integral_congr (g := fun x : ℝ =>
      Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * (x : ℂ))) (fun x _ => rfl)]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * ((1 : ℝ) : ℂ)) = 1 := by
      have : (2 * Real.pi * Complex.I * (k : ℂ)) * ((1 : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [h1]
    simp

/-! ## Plane fields as exponential sums -/

theorem planeReal_eq_sum38 (N : ℕ) (z : FourierPlane N) (x : ℝ) :
    planeReal N z x = ∑ i : Fin (2 * N + 1), z i * expMode38 (modeIndex N i) x := by
  unfold planeReal planeField expMode38
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one]

theorem star_planeReal_eq_sum38 (N : ℕ) (z : FourierPlane N) (x : ℝ) :
    star (planeReal N z x) =
      ∑ i : Fin (2 * N + 1), star (z i) * expMode38 (-(modeIndex N i)) x := by
  rw [planeReal_eq_sum38, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_expMode38]

/-- the diagonal denominator `2η - 2π i n` -/
theorem denom_ne_zero38 {η : ℝ} (hη : 0 < η) (n : ℤ) :
    (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (n : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-- the explicit resolvent of `Ū` -/
def quadResolventExplicit38 (N : ℕ) (z : FourierPlane N) (η : ℝ) (x : ℝ) : ℂ :=
  ∑ i : Fin (2 * N + 1), (star (z i) / (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (modeIndex N i : ℂ))) *
    expMode38 (-(modeIndex N i)) x

theorem quadResolventExplicit38_periodic (N : ℕ) (z : FourierPlane N) (η : ℝ) :
    Function.Periodic (quadResolventExplicit38 N z η) 1 := by
  intro x
  unfold quadResolventExplicit38
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [expMode38_periodic]

theorem quadResolventExplicit38_hasDerivAt (N : ℕ) (z : FourierPlane N) {η : ℝ} (hη : 0 < η)
    (x : ℝ) :
    HasDerivAt (quadResolventExplicit38 N z η)
      (-(2 * (η : ℂ)) * quadResolventExplicit38 N z η x + star (planeReal N z x)) x := by
  unfold quadResolventExplicit38
  rw [star_planeReal_eq_sum38, Finset.mul_sum, ← Finset.sum_add_distrib]
  have h := HasDerivAt.sum (u := Finset.univ) (A := fun i y =>
      (star (z i) / (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (modeIndex N i : ℂ))) *
        expMode38 (-(modeIndex N i)) y)
    (fun i _ => (hasDerivAt_expMode38 (-(modeIndex N i)) x).const_mul
      (star (z i) / (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (modeIndex N i : ℂ))))
  convert h using 1
  · funext y
    simp only [Finset.sum_apply]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hd := denom_ne_zero38 hη (modeIndex N i)
    have h2 : 2 * (Real.pi : ℂ) * Complex.I * ((-(modeIndex N i) : ℤ) : ℂ) =
        (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (modeIndex N i : ℂ)) - 2 * (η : ℂ) := by
      push_cast; ring
    rw [h2]
    generalize (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (modeIndex N i : ℂ)) = d at hd ⊢
    field_simp
    ring

theorem quadResolventExplicit38_eq (N : ℕ) (z : FourierPlane N) {η : ℝ} (hη : 0 < η) (x : ℝ) :
    resolv38 η (fun y => star (planeReal N z y)) x = quadResolventExplicit38 N z η x := by
  have hc : Continuous (fun y => star (planeReal N z y)) := by
    have : Continuous (planeReal N z) := (contDiff_planeReal N z).continuous
    fun_prop
  have hB : ∀ y, ‖star (planeReal N z y)‖ ≤
      Real.sqrt (2 * N + 1) * Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
    intro y
    rw [norm_star]
    exact planeReal_sup_le38 N z y
  have hper : Function.Periodic (fun y => star (planeReal N z y)) 1 := by
    intro y
    simp only [planeReal_periodic N z y]
  have hd : ∀ y, HasDerivAt (fun y => resolv38 η (fun y => star (planeReal N z y)) y -
      quadResolventExplicit38 N z η y)
      (-(2 * (η : ℂ)) * (resolv38 η (fun y => star (planeReal N z y)) y -
        quadResolventExplicit38 N z η y)) y := by
    intro y
    have h1 := resolv38_hasDerivAt hη hc hB y
    have h2 := quadResolventExplicit38_hasDerivAt N z hη y
    convert h1.sub h2 using 1
    ring
  have hp : Function.Periodic (fun y => resolv38 η (fun y => star (planeReal N z y)) y -
      quadResolventExplicit38 N z η y) 1 := by
    intro y
    simp only [resolv38_periodic hper y, quadResolventExplicit38_periodic N z η y]
  have := periodic_ode_zero hη hd hp x
  exact sub_eq_zero.mp this

/-! ## The integral -/

theorem integral_planeReal_mul_explicit38 (N : ℕ) (z : FourierPlane N) (η : ℝ) :
    ∫ x in (0:ℝ)..1, planeReal N z x * quadResolventExplicit38 N z η x =
      ∑ i : Fin (2 * N + 1),
        z i * (star (z i) / (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (modeIndex N i : ℂ))) := by
  have hexp : ∀ x, planeReal N z x * quadResolventExplicit38 N z η x =
      ∑ i : Fin (2 * N + 1), ∑ j : Fin (2 * N + 1),
        (z i * (star (z j) /
          (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (modeIndex N j : ℂ)))) *
          expMode38 (modeIndex N i + -(modeIndex N j)) x := by
    intro x
    rw [planeReal_eq_sum38]
    unfold quadResolventExplicit38
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← expMode38_add]
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul, integral_expMode38]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have : modeIndex N i + -(modeIndex N j) ≠ 0 := by
          intro h
          exact hji ((modeIndex_injective N (by omega)).symm)
        simp [this]
      · simp
    · intro j _
      exact (Continuous.mul continuous_const (continuous_expMode38 _)).intervalIntegrable _ _
  · intro i _
    exact (continuous_finsetSum _ fun j _ =>
      Continuous.mul continuous_const (continuous_expMode38 _)).intervalIntegrable _ _

theorem re_diag_term38 {η : ℝ} (hη : 0 < η) (w : ℂ) (n : ℤ) :
    (w * (star w / (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (n : ℂ)))).re =
      ‖w‖ ^ 2 * (2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * (n : ℝ) ^ 2)) := by
  have hpos : 0 < 4 * η ^ 2 + 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hw : w * star w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← mul_div_assoc, hw]
  generalize ‖w‖ ^ 2 = r
  have hD : (2 * (η : ℂ) - 2 * Real.pi * Complex.I * (n : ℂ)) =
      ((2 * η : ℝ) : ℂ) + ((-(2 * Real.pi * n) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have hns : Complex.normSq (((2 * η : ℝ) : ℂ) + ((-(2 * Real.pi * n) : ℝ) : ℂ) * Complex.I) =
      4 * η ^ 2 + 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [hD, Complex.div_re, hns]
  simp
  field_simp

theorem re_integral_planeReal_mul_explicit38 (N : ℕ) (z : FourierPlane N) {η : ℝ} (hη : 0 < η) :
    (∫ x in (0:ℝ)..1, planeReal N z x * quadResolventExplicit38 N z η x).re =
      ∑ i : Fin (2 * N + 1),
        ‖z i‖ ^ 2 * (2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2)) := by
  rw [integral_planeReal_mul_explicit38, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => re_diag_term38 hη (z i) (modeIndex N i)

/-! ## The `quadRiccati38` side -/

theorem quadRiccati38_planeL2_eq_sum (N : ℕ) (z : FourierPlane N) (η : ℝ) :
    quadRiccati38 (planeL2 N z) η =
      ∑ i : Fin (2 * N + 1),
        ‖z i‖ ^ 2 * (2 * η / (4 * η ^ 2 + 4 * Real.pi ^ 2 * ((modeIndex N i : ℤ) : ℝ) ^ 2)) := by
  classical
  unfold quadRiccati38
  rw [tsum_eq_sum (s := Finset.univ.image (modeIndex N))]
  · rw [Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [physicalFourier_planeL2, physicalFourier_planeField]
  · intro n hn
    have hout : n < -(N : ℤ) ∨ (N : ℤ) < n := by
      by_contra hcon
      push Not at hcon
      obtain ⟨i, hi⟩ := modeIndex_covers N n hcon.1 hcon.2
      exact hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    rw [physicalFourier_planeL2, physicalFourier_planeField_outside N z n hout]
    simp

theorem quadRiccati38_eq_integral (N : ℕ) (z : FourierPlane N) {η : ℝ} (hη : 0 < η) :
    quadRiccati38 (planeL2 N z) η =
      (∫ x in (0:ℝ)..1, planeReal N z x *
        resolv38 η (fun y => star (planeReal N z y)) x).re := by
  rw [quadRiccati38_planeL2_eq_sum, ← re_integral_planeReal_mul_explicit38 N z hη]
  congr 2
  funext x
  rw [quadResolventExplicit38_eq N z hη]

/-- P4b: `q_η(u) = Re ⟪U, R Ū⟫` for `u = planeL2 N z`, `U = planeReal N z`. -/
theorem quadRiccati38_eq_pair38 (N : ℕ) (z : FourierPlane N) {η : ℝ} (hη : 0 < η) :
    quadRiccati38 (planeL2 N z) η =
      (pair38 (planeReal N z) (resolv38 η (fun y => star (planeReal N z y)))).re := by
  rw [quadRiccati38_eq_integral N z hη]
  rfl

end NlsGge.SpectralFoundations
