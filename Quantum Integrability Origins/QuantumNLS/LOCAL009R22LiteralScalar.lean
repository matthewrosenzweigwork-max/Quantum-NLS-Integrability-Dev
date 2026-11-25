import QuantumNLS.LOCAL009R22Geometry
import QuantumNLS.IndividualRootBound
import QuantumNLS.BetheLabels

/-! The literal translated square contours. All scalar analytic and
geometric margins are discharged from the source smallness and confinement.
The final theorem applies to the actual constructed roots for every array. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Complex Set Metric
namespace QuantumNLS.LOCAL009R22LiteralScalar
open QuantumNLS.LOCAL009R22ScalarContour QuantumNLS.LOCAL009R22Geometry
  QuantumNLS.LOCAL009R22Integrand QuantumNLS.BetheLabels

def halfWidth (L : ℝ) : ℝ := Real.pi/(2*L)
def momentum (L : ℝ) (n : ℤ) : ℝ := 2*Real.pi*n/L
def scalarA (κ L M ε : ℝ) (n : ℤ) {N : ℕ} (q : Fin N → ℝ) : ℂ :=
  scalarApproximation κ L M (halfWidth L/2) ε
    (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L) q
def scalarConstant (κ L M : ℝ) : ℝ :=
  ‖(2*Real.pi*I : ℂ)⁻¹‖ * (8*halfWidth L) *
    integrandConstant κ M (halfWidth L/2) (halfWidth L/16)

theorem confined_scalar_contour {κ L M ε : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) (hM : 0 < M)
    (hsmall : κ*L*M ≤ 1/1000000)
    {N : ℕ} (hN : 0 < N) (hε : 0 ≤ ε) (hεM : ε ≤ M)
    (hbudget : ε*N ≤ M) (q : Fin N → ℝ) (ℓ : Fin N → ℤ)
    (hconf : ∀ j, |q j - momentum L (ℓ j)| ≤ halfWidth L/4) (n : ℤ) :
    ‖scalarA κ L M ε n q - (ε : ℂ) *
        ((Finset.univ.filter (fun j => ℓ j = n)).card : ℂ)‖ ≤
      scalarConstant κ L M * ε^2 := by
  let a := halfWidth L
  let p := momentum L n
  let U := band p a
  have ha : 0 < a := by dsimp [a, halfWidth]; positivity
  have hd : 0 < a/2 := by positivity
  have hs : κ*M/(a/2) ≤ 1/10000 := by
    have heq : κ*M/(a/2) = 4*(κ*L*M)/Real.pi := by
      dsimp [a, halfWidth]
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ Real.pi_pos).mpr
    nlinarith [Real.pi_gt_three]
  have hgrid (j : Fin N) : ∃ k : ℤ, |q j - (p + 4*a*k)| ≤ a/4 := by
    refine ⟨ℓ j-n, ?_⟩
    have heq : p + 4*a*(ℓ j-n : ℤ) = momentum L (ℓ j) := by
      dsimp [p, a, momentum, halfWidth]
      push_cast
      field_simp
      ring
    rw [heq]
    exact hconf j
  have hsep : ∀ z ∈ U, ∀ j, a/2 ≤ ‖z-(q j : ℂ)‖ :=
    fun z hz j => band_root_separation ha (hgrid j) hz
  have hresult := scalar_contour_second_order hκ hM hd hs (band_open p a)
    (fun z hz => source_phase_bound hL n hz)
    (fun z hz => source_gap_bound hL n hz) hN hε hεM hbudget q hsep
    (show p-a < p+a by linarith) ha (show 0 < a/16 by positivity)
    (fun z hz => contour_ball_subset_band ha hz)
  have hiff (j : Fin N) : p-a < q j ∧ q j < p+a ↔ ℓ j = n := by
    constructor
    · intro hin
      by_contra hne
      have hkpos : (0 : ℤ) < |ℓ j-n| := abs_pos.mpr (sub_ne_zero.mpr hne)
      have hk1 : (1 : ℝ) ≤ |((ℓ j-n : ℤ) : ℝ)| := by exact_mod_cast (show (1 : ℤ) ≤ |ℓ j-n| by omega)
      have heq : momentum L (ℓ j) - p = 4*a*(ℓ j-n : ℤ) := by
        dsimp [momentum, p, a, halfWidth]
        push_cast
        field_simp
        ring
      have hdist : 4*a ≤ |momentum L (ℓ j)-p| := by
        rw [heq, abs_mul, abs_of_pos (by positivity : 0 < 4*a)]
        nlinarith
      have hnear : |q j-p| < a := abs_lt.mpr ⟨by linarith, by linarith⟩
      have htriangle := abs_sub_le (momentum L (ℓ j)) (q j) p
      rw [abs_sub_comm (momentum L (ℓ j)) (q j)] at htriangle
      linarith [hconf j]
    · intro he
      have h := hconf j
      rw [he] at h
      change |q j-p| ≤ a/4 at h
      have hl := (abs_le.mp h).1
      have hr := (abs_le.mp h).2
      constructor <;> linarith
  have hfilter : (Finset.univ.filter (fun j => p-a < q j ∧ q j < p+a)) =
      Finset.univ.filter (fun j => ℓ j = n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff]
  rw [hfilter] at hresult
  convert hresult using 1
  · rfl
  · unfold scalarConstant
    dsimp [a]
    ring

/-- The source root confinement estimate is instantiated on the accepted
constructed roots at c=κ ε. No root-location property is assumed here. -/
theorem actual_root_confinement {κ L M ε : ℝ}
    (hκ : 0 < κ) (hL : 0 < L)
    (hsmall : κ*L*M ≤ 1/1000000)
    {N : ℕ} (hN : 0 < N) (hε : 0 < ε) (hbudget : ε*N ≤ M)
    (m : MArr N) (j : Fin N) :
    |arrRoots L (κ*ε) m j - momentum L (correctedInt (labelsEquivArr.symm m) j)| ≤
      halfWidth L/4 := by
  let K := κ*ε*(N : ℝ)
  have hK : 0 < K := by dsimp [K]; positivity
  have hKbudget : K ≤ κ*M := by
    have h := mul_le_mul_of_nonneg_left hbudget hκ.le
    dsimp [K]
    nlinarith
  have hc : K/(N : ℝ) = κ*ε := by dsimp [K]; field_simp
  have hbound := QuantumNLS.IndividualRootBound.mean_field_root_bound_roots hN hL hK
    (correctedInt (labelsEquivArr.symm m)) (correctedInt_monotone _) j
  rw [hc] at hbound
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have harg : (K/L)*(1-1/(N : ℝ)) ≤ κ*M/L := by
    have hfactor : 1-1/(N : ℝ) ≤ 1 := by
      have : (0 : ℝ) ≤ 1/(N : ℝ) := by positivity
      linarith
    calc
      _ ≤ K/L := by nlinarith [div_pos hK hL]
      _ ≤ κ*M/L := div_le_div_of_nonneg_right hKbudget hL.le
  have hsqrt : Real.sqrt (κ*M/L) ≤ Real.pi/(16*L) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [div_pow]
      apply (div_le_div_iff₀ hL (by positivity : 0 < (16*L)^2)).mpr
      have hscaled := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ 256*L)
      have hpi : (256/1000000 : ℝ) ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
      have hscaledpi := mul_le_mul_of_nonneg_right hpi hL.le
      nlinarith
  have hs := (Real.sqrt_le_sqrt harg).trans hsqrt
  change |QuantumNLS.BetheSmooth.roots L (correctedInt (labelsEquivArr.symm m)) (κ*ε) j -
    2*Real.pi*(correctedInt (labelsEquivArr.symm m) j : ℝ)/L| ≤ _
  have hwidth : 2*(Real.pi/(16*L)) = halfWidth L/4 := by unfold halfWidth; ring
  rw [← hwidth]
  linarith

/-- Scalar second-order reconstruction for every actual Bethe configuration
on the literal Γ_n, uniformly in m, N and n. -/
theorem actual_scalar_contour {κ L M ε : ℝ}
    (hκ : 0 < κ) (hL : 0 < L) (hM : 0 < M)
    (hsmall : κ*L*M ≤ 1/1000000)
    {N : ℕ} (hN : 0 < N) (hε : 0 < ε) (hεM : ε ≤ M)
    (hbudget : ε*N ≤ M) (m : MArr N) (n : ℤ) :
    ‖scalarA κ L M ε n (arrRoots L (κ*ε) m) - (ε : ℂ) * (m.1 n : ℂ)‖ ≤
      scalarConstant κ L M * ε^2 := by
  have h := confined_scalar_contour hκ hL hM hsmall hN hε.le hεM hbudget
    (arrRoots L (κ*ε) m) (correctedInt (labelsEquivArr.symm m))
    (actual_root_confinement hκ hL hsmall hN hε hbudget m) n
  have hc := labelsEquivArr_apply (labelsEquivArr.symm m) n
  rw [labelsEquivArr.apply_symm_apply] at hc
  simpa only [← hc] using h

end QuantumNLS.LOCAL009R22LiteralScalar
#print axioms QuantumNLS.LOCAL009R22LiteralScalar.confined_scalar_contour
#print axioms QuantumNLS.LOCAL009R22LiteralScalar.actual_root_confinement
#print axioms QuantumNLS.LOCAL009R22LiteralScalar.actual_scalar_contour
