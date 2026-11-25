import Mathlib
import QuantumNLS.RootMassBoostSymbol
import QuantumNLS.RootTraceSymbolFinal
import QuantumNLS.L2DiscriminantRegularity
import QuantumNLS.DEF014DiscriminantAnalytic
import QuantumNLS.Local002Bridge

/-! LOCAL-007 stage G: the index shift (gauge) and the parity of the actual discriminant.

* `boostLI k` : the Fourier-character multiplication of `RootMassBoostSymbol.boost` as a complex-linear isometry
  of `L2T L`;
* `disc_boost` : `Δ_{boost k u}(z) = (-1)^k Δ_u(z - p_k)` (from the accepted trace-symbol identity and the
  accepted product-symbol covariance `RootMassBoostSymbol.symbol_shift`);
* `disc_shift` : `Δ_u(p_n + w) = (-1)^n Δ_{boost (-n) u}(w)`;
* `disc_neg` : `Δ_{-u} = Δ_u` (conjugation of the transfer by `diag(1,-1)`).
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Matrix Interval
namespace QuantumNLS.Local007Gauge
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.RootMassBoostSymbol (boost norm_boost coe_boost)
open QuantumNLS.SpatialTransfer (balCoef coef Mat2)
open QuantumNLS.L1SpatialTransfer QuantumNLS.L2SpatialTransfer
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L : ℝ} [Fact (0 < L)]

theorem boost_add (k : ℤ) (u v : L2T L) : boost k (u + v) = boost k u + boost k v := by
  apply Lp.ext
  filter_upwards [coe_boost k (u + v), coe_boost k u, coe_boost k v, Lp.coeFn_add u v,
    Lp.coeFn_add (boost k u) (boost k v)] with x h1 h2 h3 h4 h5
  rw [h5, Pi.add_apply, h2, h3, h1, h4, Pi.add_apply, mul_add]

theorem boost_smul (k : ℤ) (c : ℂ) (u : L2T L) : boost k (c • u) = c • boost k u := by
  apply Lp.ext
  filter_upwards [coe_boost k (c • u), coe_boost k u, Lp.coeFn_smul c u,
    Lp.coeFn_smul c (boost k u)] with x h1 h2 h3 h4
  rw [h4, Pi.smul_apply, h2, h1, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- The Fourier-character multiplication as a complex-linear isometry. -/
def boostLI (k : ℤ) : L2T L →ₗᵢ[ℂ] L2T L where
  toFun := boost k
  map_add' := boost_add k
  map_smul' := boost_smul k
  norm_map' := norm_boost k

@[simp] theorem boostLI_apply (k : ℤ) (u : L2T L) : boostLI k u = boost k u := rfl

theorem boost_boost_neg (k : ℤ) (u : L2T L) : boost (-k) (boost k u) = u := by
  apply Lp.ext
  filter_upwards [coe_boost (-k) (boost k u), coe_boost k u] with x h1 h2
  rw [h1, h2, ← mul_assoc]
  have : (fourier (T := L) (-k)) x * (fourier (T := L) k) x = 1 := by
    rw [← fourier_add]
    simp
  rw [this, one_mul]

/-- The quantum momentum `p_k = 2π k / L`. -/
abbrev pm (L : ℝ) (k : ℤ) : ℝ := QuantumNLS.PlaneWaveSymbol.pm L k

omit [Fact (0 < L)] in
theorem pm_eq (k : ℤ) : pm L k = QuantumNLS.LocalSpectral.pm L k := rfl

theorem productSymbol_eq {κ : ℝ} (hκ : 0 ≤ κ) (u : L2T L) (z : ℂ) :
    QuantumNLS.NormalizedTransfer.productSymbol L κ u z =
      Complex.exp (Complex.I * z * L / 2) * L2SpatialTransfer.discriminant κ u z := by
  rw [← QuantumNLS.RootTraceSymbolFinal.traceSymbol_all hκ u z, ← mul_assoc, ← Complex.exp_add]
  have : Complex.I * z * L / 2 + -(Complex.I * z * L / 2) = 0 := by ring
  rw [this, Complex.exp_zero, one_mul]

theorem disc_boost {κ : ℝ} (hκ : 0 ≤ κ) (k : ℤ) (u : L2T L) (z : ℂ) :
    L2SpatialTransfer.discriminant κ (boost k u) z = ((-1 : ℂ) ^ k) * L2SpatialTransfer.discriminant κ u (z - (pm L k : ℂ)) := by
  rw [← QuantumNLS.RootTraceSymbolFinal.traceSymbol_all hκ (boost k u) z,
    QuantumNLS.RootMassBoostSymbol.symbol_shift, productSymbol_eq hκ u (z - (pm L k : ℂ)),
    ← mul_assoc, ← Complex.exp_add]
  have hpm : ((pm L k : ℝ) : ℂ) * (L : ℂ) = 2 * Real.pi * k := by
    have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < L).ne'
    unfold pm QuantumNLS.PlaneWaveSymbol.pm
    push_cast
    field_simp
  have h1 : -(Complex.I * z * L / 2) + Complex.I * (z - (pm L k : ℂ)) * L / 2 =
      -(Complex.I * (k : ℂ) * Real.pi) := by
    have : Complex.I * (z - (pm L k : ℂ)) * L / 2 = Complex.I * z * L / 2 -
        Complex.I * ((pm L k : ℂ) * L) / 2 := by ring
    rw [this, hpm]; ring
  rw [h1]
  congr 1
  have : -(Complex.I * (k : ℂ) * Real.pi) = (k : ℂ) * (-(Real.pi * Complex.I)) := by ring
  rw [this, Complex.exp_int_mul]
  have : Complex.exp (-(Real.pi * Complex.I)) = -1 := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  rw [this]

theorem disc_shift {κ : ℝ} (hκ : 0 ≤ κ) (n : ℤ) (u : L2T L) (w : ℂ) :
    L2SpatialTransfer.discriminant κ u ((pm L n : ℂ) + w) = ((-1 : ℂ) ^ n) * L2SpatialTransfer.discriminant κ (boost (-n) u) w := by
  have h := disc_boost hκ (-n) u w
  have hp : pm L (-n) = -pm L n := by
    unfold pm QuantumNLS.PlaneWaveSymbol.pm; push_cast; ring
  rw [h, hp]
  have e : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ (-n)) = 1 := by
    rw [← zpow_add₀ (by norm_num)]; simp
  have e2 : w - ((-pm L n : ℝ) : ℂ) = (pm L n : ℂ) + w := by push_cast; ring
  rw [e2, ← mul_assoc, e, one_mul]

theorem sq_disc_shift {κ : ℝ} (hκ : 0 ≤ κ) (n : ℤ) (u : L2T L) (w : ℂ) :
    L2SpatialTransfer.discriminant κ u ((pm L n : ℂ) + w) ^ 2 = L2SpatialTransfer.discriminant κ (boost (-n) u) w ^ 2 := by
  rw [disc_shift hκ n u w, mul_pow, ← zpow_natCast, ← zpow_mul]
  have : ((-1 : ℂ) ^ (n * ((2 : ℕ) : ℤ))) = 1 := by
    rw [mul_comm, zpow_mul]; norm_num
  rw [this, one_mul]

/-! ### Parity `Δ_{-u} = Δ_u` -/

def Jm : Mat2 := !![1, 0; 0, -1]

theorem Jm_mul_Jm : Jm * Jm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jm, Matrix.mul_apply, Fin.sum_univ_two]

def Jc : Mat2 →L[ℝ] Mat2 := ContinuousLinearMap.mulLeftRight ℝ Mat2 Jm Jm

theorem Jc_apply (m : Mat2) : Jc m = Jm * m * Jm := rfl

theorem Jc_mul (a b : Mat2) : Jc (a * b) = Jc a * Jc b := by
  rw [Jc_apply, Jc_apply, Jc_apply]
  calc Jm * (a * b) * Jm = Jm * a * (Jm * Jm) * b * Jm := by rw [Jm_mul_Jm]; simp [mul_assoc]
    _ = Jm * a * Jm * (Jm * b * Jm) := by simp [mul_assoc]

theorem Jc_one : Jc 1 = 1 := by rw [Jc_apply]; simp [Jm_mul_Jm]

theorem trace_Jc (m : Mat2) : Matrix.trace (Jc m) = Matrix.trace m := by
  rw [Jc_apply]
  simp only [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Jm]
  simp

theorem profile_neg (u : L2T L) :
    (fun x : ℝ => profile (-u) x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)] fun x => -profile u x := by
  have h := (AddCircle.measurePreserving_mk L 0).quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_neg u)
  simpa [profile, Function.comp_def, zero_add] using h

theorem balCoef_neg (κ : ℝ) (u : L2T L) (z : ℂ) :
    (fun x => balCoef κ (profile (-u)) z x) =ᵐ[volume.restrict (Ioc (0 : ℝ) L)]
      fun x => Jc (balCoef κ (profile u) z x) := by
  filter_upwards [profile_neg u] with x hx
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Jc_apply, Jm, balCoef, coef, hx, Matrix.mul_apply,
    Fin.sum_univ_two] <;> ring

theorem transfer_neg (κ : ℝ) (u : L2T L) (z : ℂ) :
    EqOn (spatialTransfer κ (-u) z) (fun x => Jc (spatialTransfer κ u z x)) (Icc 0 L) := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  let A := balCoef κ (profile u) z
  let A' := balCoef κ (profile (-u)) z
  let U := spatialTransfer κ u z
  let U' := spatialTransfer κ (-u) z
  have hi : IntervalIntegrable A' volume 0 L :=
    intervalIntegrable_coef (intervalIntegrable_profile (-u)) _ _ z
  have hiA : IntervalIntegrable A volume 0 L :=
    intervalIntegrable_coef (intervalIntegrable_profile u) _ _ z
  have hc : ContinuousOn U (Icc 0 L) := continuousOn_transfer hL hiA
  have hc' : ContinuousOn U' (Icc 0 L) := continuousOn_transfer hL hi
  have hp : IntervalIntegrable (fun x => A x * U x) volume 0 L :=
    hiA.mul_continuousOn (by rw [uIcc_of_le hL]; exact hc)
  apply integral_solution_unique hL hi hc'
    (Jc.continuous.comp_continuousOn hc)
  · exact fun x hx => spatialTransfer_integral_eq κ (-u) z hx
  · intro x hx
    have hs : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
      rw [uIcc_of_le hx.1, uIcc_of_le hL]
      exact Icc_subset_Icc_right hx.2
    change Jc (U x) = 1 + ∫ s in (0 : ℝ)..x, A' s * Jc (U s)
    rw [show U x = 1 + ∫ s in (0 : ℝ)..x, A s * U s from
      spatialTransfer_integral_eq κ u z hx, map_add, Jc_one]
    apply congrArg (fun y : Mat2 => 1 + y)
    calc
      Jc (∫ s in (0 : ℝ)..x, A s * U s) = ∫ s in (0 : ℝ)..x, Jc (A s * U s) :=
        (Jc.intervalIntegral_comp_comm (hp.mono_set hs)).symm
      _ = ∫ s in (0 : ℝ)..x, A' s * Jc (U s) := by
        have hae : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) x → Jc (A s * U s) = A' s * Jc (U s) := by
          have h1 : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) L), Jc (A s * U s) = A' s * Jc (U s) := by
            filter_upwards [balCoef_neg κ u z] with s hs'
            rw [Jc_mul]
            exact congrArg (· * Jc (U s)) hs'.symm
          have h2 := (ae_restrict_iff' measurableSet_Ioc).1 h1
          filter_upwards [h2] with s hs2 hsI
          apply hs2
          rw [uIoc_of_le hx.1] at hsI
          exact ⟨hsI.1, hsI.2.trans hx.2⟩
        exact intervalIntegral.integral_congr_ae (by
          filter_upwards [hae] with s hs3 hs4 using hs3 hs4)

theorem disc_neg (κ : ℝ) (u : L2T L) (z : ℂ) : L2SpatialTransfer.discriminant κ (-u) z = L2SpatialTransfer.discriminant κ u z := by
  have h := transfer_neg κ u z (show L ∈ Icc 0 L from ⟨(Fact.out : 0 < L).le, le_rfl⟩)
  unfold L2SpatialTransfer.discriminant
  rw [h]
  exact trace_Jc _

end QuantumNLS.Local007Gauge
#print axioms QuantumNLS.Local007Gauge.disc_boost
#print axioms QuantumNLS.Local007Gauge.disc_shift
#print axioms QuantumNLS.Local007Gauge.sq_disc_shift
#print axioms QuantumNLS.Local007Gauge.disc_neg
#print axioms QuantumNLS.Local007Gauge.boost_boost_neg
