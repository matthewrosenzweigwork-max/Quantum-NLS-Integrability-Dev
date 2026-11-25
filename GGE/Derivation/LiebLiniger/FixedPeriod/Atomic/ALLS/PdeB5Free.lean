import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB4Defs
import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB3L43Limit

/-! # Track B, package 2: the free Schrödinger group on `L²(𝕋)`

`freeL2 t u` is the `L²` field with Fourier coefficients `freePhase t n · û(n)`
(`freePhase t n = e^{-it(2πn)²}`), i.e. `e^{it∂ₓ²} u` on ordinary coefficients, realized through
the genuine isometry `physicalFourierL2 : L²(𝕋) ≃ ℓ²(ℤ)`. Proved: coefficient formula,
compatibility `l2ToHm1 (freeL2 t u) = freeProp (-1) t (l2ToHm1 u)`, isometry, group law,
`freeL2 0 = id`, real linearity, strong continuity in `t`.
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38
open scoped ENNReal

theorem physicalFourier_sub_l2 (a b : PhysicalL2) (n : ℤ) :
    physicalFourier (⇑(a - b)) n = physicalFourier a n - physicalFourier b n := by
  have h := congrArg (fun z => carrierCoe38 (-1) z n) (map_sub l2ToHm1 a b)
  exact h

theorem physicalFourier_add_l2 (a b : PhysicalL2) (n : ℤ) :
    physicalFourier (⇑(a + b)) n = physicalFourier a n + physicalFourier b n := by
  have h := congrArg (fun z => carrierCoe38 (-1) z n) (map_add l2ToHm1 a b)
  exact h

theorem physicalFourier_smul_l2 (c : ℝ) (a : PhysicalL2) (n : ℤ) :
    physicalFourier (⇑(c • a)) n = (c : ℂ) * physicalFourier a n := by
  have h := congrArg (fun z => carrierCoe38 (-1) z n) (map_smul l2ToHm1 c a)
  exact h.trans (by
    change ((c : ℝ) • (carrierCoe38 (-1) (l2ToHm1 a))) n = _
    simp [Complex.real_smul, carrierCoe38_l2ToHm1])

theorem physicalFourier_ext_l2 {a b : PhysicalL2}
    (h : ∀ n, physicalFourier a n = physicalFourier b n) : a = b :=
  l2ToHm1_injective (carrierExt38 (funext h))

theorem memℓp_physicalFourier (u : PhysicalL2) : Memℓp (physicalFourier u) 2 := by
  have h := (physicalFourierL2 u).2
  have he : (⇑(physicalFourierL2 u) : ℤ → ℂ) = physicalFourier u :=
    funext fun n => physicalFourierL2_apply u n
  rw [he] at h
  exact h

theorem freeSeq_memℓp (t : ℝ) (u : PhysicalL2) :
    Memℓp (fun n : ℤ => freePhase t n * physicalFourier u n) 2 := by
  have h := memℓp_physicalFourier u
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)] at h ⊢
  simpa only [norm_mul, norm_freePhase, one_mul] using h

/-- **The free Schrödinger group on `L²(𝕋)`**: `e^{it∂ₓ²} u`. -/
def freeL2 (t : ℝ) (u : PhysicalL2) : PhysicalL2 :=
  physicalFourierL2.symm ⟨fun n => freePhase t n * physicalFourier u n, freeSeq_memℓp t u⟩

theorem physicalFourier_freeL2 (t : ℝ) (u : PhysicalL2) (n : ℤ) :
    physicalFourier (freeL2 t u) n = freePhase t n * physicalFourier u n := by
  rw [← physicalFourierL2_apply, freeL2, LinearIsometryEquiv.apply_symm_apply]

theorem l2ToHm1_freeL2 (t : ℝ) (u : PhysicalL2) :
    l2ToHm1 (freeL2 t u) = freeProp (-1) t (l2ToHm1 u) :=
  carrierExt38 (funext fun n => by
    rw [carrierCoe38_freeProp, carrierCoe38_l2ToHm1, carrierCoe38_l2ToHm1,
      physicalFourier_freeL2])

theorem freeL2_add (s t : ℝ) (u : PhysicalL2) : freeL2 (s + t) u = freeL2 s (freeL2 t u) :=
  physicalFourier_ext_l2 fun n => by
    rw [physicalFourier_freeL2, physicalFourier_freeL2, physicalFourier_freeL2, freePhase_add]
    ring

theorem freeL2_zero (u : PhysicalL2) : freeL2 0 u = u :=
  physicalFourier_ext_l2 fun n => by rw [physicalFourier_freeL2, freePhase_zero, one_mul]

theorem freeL2_sub (t : ℝ) (a b : PhysicalL2) : freeL2 t (a - b) = freeL2 t a - freeL2 t b :=
  physicalFourier_ext_l2 fun n => by
    rw [physicalFourier_freeL2, physicalFourier_sub_l2, physicalFourier_sub_l2,
      physicalFourier_freeL2, physicalFourier_freeL2]
    ring

theorem freeL2_add_data (t : ℝ) (a b : PhysicalL2) : freeL2 t (a + b) = freeL2 t a + freeL2 t b :=
  physicalFourier_ext_l2 fun n => by
    rw [physicalFourier_freeL2, physicalFourier_add_l2, physicalFourier_add_l2,
      physicalFourier_freeL2, physicalFourier_freeL2]
    ring

/-- Parseval comparison: an `L²` field and a weight-`0` carrier element with the same coefficients
have the same norm. -/
theorem norm_eq_of_coeff (u : PhysicalL2) (x : SobolevCarrier38 0)
    (h : ∀ n, physicalFourier u n = carrierCoe38 0 x n) : ‖u‖ = ‖x‖ := by
  have h1 := hasSum_physicalFourier_sq u
  have h2 := carrier_hasSum_norm_sq38 0 x
  have hw : ∀ n : ℤ, sobolevModeWeight 0 n = 1 := fun n => by simp [sobolevModeWeight]
  simp only [hw, one_mul, ← h] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.unique h2)

theorem physicalFourier_mem_zero (u : PhysicalL2) : physicalFourier u ∈ seqSobolev38 0 :=
  (mem_seqSobolev38_zero_iff _).2 (memℓp_physicalFourier u)

theorem norm_freeL2 (t : ℝ) (u : PhysicalL2) : ‖freeL2 t u‖ = ‖u‖ := by
  set x := carrierMk38 0 (physicalFourier u) (physicalFourier_mem_zero u)
  rw [norm_eq_of_coeff (freeL2 t u) (freeProp 0 t x) (fun n => by
      rw [physicalFourier_freeL2, carrierCoe38_freeProp]; rfl),
    norm_freeProp, ← norm_eq_of_coeff u x (fun n => rfl)]

/-- Strong continuity of the free group on `L²`. -/
theorem continuous_freeL2 (u : PhysicalL2) : Continuous fun t => freeL2 t u := by
  set x := carrierMk38 0 (physicalFourier u) (physicalFourier_mem_zero u)
  have hn : ∀ t t0, ‖freeL2 t u - freeL2 t0 u‖ = ‖freeProp 0 t x - freeProp 0 t0 x‖ :=
    fun t t0 => norm_eq_of_coeff _ _ fun n => by
      rw [physicalFourier_sub_l2, physicalFourier_freeL2, physicalFourier_freeL2]
      rfl
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [hn]
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  exact (continuous_freeProp_apply 0 x).continuousAt

theorem norm_freeL2_sub (t : ℝ) (a b : PhysicalL2) : ‖freeL2 t a - freeL2 t b‖ = ‖a - b‖ := by
  rw [← freeL2_sub, norm_freeL2]

end LiebLiniger.FixedPeriod.ALLS.PdeB
