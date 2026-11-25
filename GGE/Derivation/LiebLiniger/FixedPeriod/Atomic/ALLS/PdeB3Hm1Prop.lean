import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB3Hm1Core
import NlsGge.NLS38.SeqConv38a

/-! # Track B, step B3 (review item R1 / M1): the free propagator on `h^r`

Statement-independent. `unitMul r φ hφ` multiplies the coefficients by unimodular numbers `φ n`
(a linear isometry of the real Hilbert carrier `SobolevCarrier38 r`). The free Schrödinger group
`e^{it∂ₓ²}` is `freeProp r t = unitMul r (freePhase t)`, with
`freePhase t n = exp(-i t (2πn)²) = exp(-i t · disp n)` on ORDINARY (unreflected) coefficients
(convention of `IsNLSSolM`: `i u_t = -u_xx + …` gives `û_n' = -i (2πn)² û_n + …`).
Proved: coefficient formula, isometry, group law `freeProp (s+t) = freeProp s ∘ freeProp t`,
`freeProp 0 = id`, strong continuity (dominated convergence for the weighted tsum) and joint
continuity on `ℝ × h^r`. `negIMul r` is multiplication of the coefficients by `-i`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

theorem unitMul_mem (r : ℝ) (φ : ℤ → ℂ) (hφ : ∀ n, ‖φ n‖ = 1) (x : SobolevCarrier38 r) :
    (fun n => φ n * carrierCoe38 r x n) ∈ seqSobolev38 r := by
  rw [mem_seqSobolev38_iff]
  have h := (carrier_hasSum_norm_sq38 r x).summable
  show Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * r) *
    ‖φ n * carrierCoe38 r x n‖ ^ 2)
  simp_rw [norm_mul, hφ, one_mul]
  exact h

theorem norm_unitMulMk (r : ℝ) (φ : ℤ → ℂ) (hφ : ∀ n, ‖φ n‖ = 1) (x : SobolevCarrier38 r) :
    ‖carrierMk38 r _ (unitMul_mem r φ hφ x)‖ = ‖x‖ := by
  have h1 := carrier_hasSum_norm_sq38 r (carrierMk38 r _ (unitMul_mem r φ hφ x))
  have h2 := carrier_hasSum_norm_sq38 r x
  simp only [carrierCoe38_mk, norm_mul, hφ, one_mul] at h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.unique h2)

/-- Coefficientwise multiplication by unimodular numbers, a real-linear isometry of `h^r`. -/
def unitMul (r : ℝ) (φ : ℤ → ℂ) (hφ : ∀ n, ‖φ n‖ = 1) :
    SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r :=
  LinearMap.mkContinuous
    { toFun := fun x => carrierMk38 r _ (unitMul_mem r φ hφ x)
      map_add' := fun x y => carrierExt38 (funext fun n => by
        show φ n * (carrierCoe38 r x n + carrierCoe38 r y n) =
          φ n * carrierCoe38 r x n + φ n * carrierCoe38 r y n
        ring)
      map_smul' := fun c x => carrierExt38 (funext fun n => by
        show φ n * ((c : ℂ) * carrierCoe38 r x n) = (c : ℂ) * (φ n * carrierCoe38 r x n)
        ring) }
    1 (fun x => le_of_eq (by rw [one_mul]; exact norm_unitMulMk r φ hφ x))

@[simp] theorem carrierCoe38_unitMul (r : ℝ) (φ : ℤ → ℂ) (hφ : ∀ n, ‖φ n‖ = 1)
    (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (unitMul r φ hφ x) n = φ n * carrierCoe38 r x n := rfl

theorem norm_unitMul (r : ℝ) (φ : ℤ → ℂ) (hφ : ∀ n, ‖φ n‖ = 1) (x : SobolevCarrier38 r) :
    ‖unitMul r φ hφ x‖ = ‖x‖ :=
  norm_unitMulMk r φ hφ x

/-- The free phase `exp(-i t (2πn)²)`. -/
def freePhase (t : ℝ) (n : ℤ) : ℂ := Complex.exp (-((t * disp n : ℝ) : ℂ) * Complex.I)

theorem norm_freePhase (t : ℝ) (n : ℤ) : ‖freePhase t n‖ = 1 := by
  unfold freePhase
  rw [show -((t * disp n : ℝ) : ℂ) * Complex.I = ((-(t * disp n) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem freePhase_add (s t : ℝ) (n : ℤ) : freePhase (s + t) n = freePhase s n * freePhase t n := by
  unfold freePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem freePhase_zero (n : ℤ) : freePhase 0 n = 1 := by
  simp [freePhase]

theorem continuous_freePhase (n : ℤ) : Continuous fun t : ℝ => freePhase t n := by
  unfold freePhase
  fun_prop

/-- The free Schrödinger group `e^{it∂ₓ²}` on `h^r`. -/
def freeProp (r t : ℝ) : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r :=
  unitMul r (freePhase t) (norm_freePhase t)

/-- Coefficient characterization of the free propagator. -/
@[simp] theorem carrierCoe38_freeProp (r t : ℝ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (freeProp r t x) n = freePhase t n * carrierCoe38 r x n := rfl

theorem norm_freeProp (r t : ℝ) (x : SobolevCarrier38 r) : ‖freeProp r t x‖ = ‖x‖ :=
  norm_unitMul r _ _ x

theorem freeProp_add (r s t : ℝ) (x : SobolevCarrier38 r) :
    freeProp r (s + t) x = freeProp r s (freeProp r t x) :=
  carrierExt38 (funext fun n => by
    simp only [carrierCoe38_freeProp, freePhase_add]
    ring)

theorem freeProp_zero (r : ℝ) (x : SobolevCarrier38 r) : freeProp r 0 x = x :=
  carrierExt38 (funext fun n => by simp only [carrierCoe38_freeProp, freePhase_zero, one_mul])

/-- Strong continuity of the free group. -/
theorem continuous_freeProp_apply (r : ℝ) (x : SobolevCarrier38 r) :
    Continuous fun t => freeProp r t x := by
  rw [continuous_iff_continuousAt]
  intro t0
  have hsq : ∀ t, ‖freeProp r t x - freeProp r t0 x‖ ^ 2 = ∑' n, sobolevModeWeight r n *
      ‖(freePhase t n - freePhase t0 n) * carrierCoe38 r x n‖ ^ 2 := by
    intro t
    rw [← (carrier_hasSum_norm_sq38 r (freeProp r t x - freeProp r t0 x)).tsum_eq]
    congr 1
    funext n
    congr 2
    show ‖freePhase t n * carrierCoe38 r x n - freePhase t0 n * carrierCoe38 r x n‖ = _
    congr 1
    ring
  have hT : Tendsto (fun t => ∑' n, sobolevModeWeight r n *
      ‖(freePhase t n - freePhase t0 n) * carrierCoe38 r x n‖ ^ 2) (𝓝 t0)
      (𝓝 (∑' _ : ℤ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence
      (bound := fun n => 4 * (sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2))
      ((carrier_hasSum_norm_sq38 r x).summable.mul_left 4) (fun n => ?_)
      (Eventually.of_forall fun t n => ?_)
    · have h1 := continuous_freePhase n
      have hc : Continuous fun t => sobolevModeWeight r n *
          ‖(freePhase t n - freePhase t0 n) * carrierCoe38 r x n‖ ^ 2 := by
        fun_prop
      simpa [sub_self] using hc.tendsto t0
    · have hw := (sobolevModeWeight_pos r n).le
      rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
      have h2 : ‖freePhase t n - freePhase t0 n‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by rw [norm_freePhase, norm_freePhase]; norm_num)
      have h4 : ‖freePhase t n - freePhase t0 n‖ ^ 2 ≤ 4 := by
        nlinarith [norm_nonneg (freePhase t n - freePhase t0 n)]
      rw [norm_mul, mul_pow]
      calc sobolevModeWeight r n * (‖freePhase t n - freePhase t0 n‖ ^ 2 *
            ‖carrierCoe38 r x n‖ ^ 2)
          = (sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2) *
            ‖freePhase t n - freePhase t0 n‖ ^ 2 := by ring
        _ ≤ (sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2) * 4 :=
            mul_le_mul_of_nonneg_left h4 (mul_nonneg hw (sq_nonneg _))
        _ = 4 * (sobolevModeWeight r n * ‖carrierCoe38 r x n‖ ^ 2) := by ring
  rw [tsum_zero] at hT
  have hN : Tendsto (fun t => ‖freeProp r t x - freeProp r t0 x‖) (𝓝 t0) (𝓝 0) := by
    have h := hT.sqrt
    simp_rw [← hsq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h
    exact h
  exact tendsto_iff_norm_sub_tendsto_zero.2 hN

/-- Joint continuity of `(t, x) ↦ e^{it∂ₓ²} x` on `ℝ × h^r`. -/
theorem continuous_freeProp (r : ℝ) :
    Continuous fun p : ℝ × SobolevCarrier38 r => freeProp r p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t0, x0⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hS := continuous_freeProp_apply r x0
  have hc : Continuous fun p : ℝ × SobolevCarrier38 r =>
      ‖p.2 - x0‖ + ‖freeProp r p.1 x0 - freeProp r t0 x0‖ := by fun_prop
  have h1 : Tendsto (fun p : ℝ × SobolevCarrier38 r =>
      ‖p.2 - x0‖ + ‖freeProp r p.1 x0 - freeProp r t0 x0‖) (𝓝 (t0, x0)) (𝓝 0) := by
    simpa using hc.tendsto (t0, x0)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) h1
  calc ‖freeProp r p.1 p.2 - freeProp r t0 x0‖
      = ‖freeProp r p.1 (p.2 - x0) + (freeProp r p.1 x0 - freeProp r t0 x0)‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖freeProp r p.1 (p.2 - x0)‖ + ‖freeProp r p.1 x0 - freeProp r t0 x0‖ := norm_add_le _ _
    _ = ‖p.2 - x0‖ + ‖freeProp r p.1 x0 - freeProp r t0 x0‖ := by rw [norm_freeProp]

/-- Multiplication of the coefficients by `-i`, a real-linear isometry of `h^r`. -/
def negIMul (r : ℝ) : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 r :=
  unitMul r (fun _ => -Complex.I) (fun _ => by simp)

@[simp] theorem carrierCoe38_negIMul (r : ℝ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (negIMul r x) n = -Complex.I * carrierCoe38 r x n := rfl

end LiebLiniger.FixedPeriod.ALLS.PdeB
