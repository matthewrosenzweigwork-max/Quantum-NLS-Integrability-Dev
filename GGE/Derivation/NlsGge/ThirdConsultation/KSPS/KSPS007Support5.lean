import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS005Support
import NlsGge.ThirdConsultation.KSPS.KSPS007Support3

/- KSPS-007 SUPPORT05 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS007Support5.lean.
   Utilities: entrywise bounds `EB` of 2x2 matrices (and the induced sup-norm bound for mulVec), continuous matrix
   functions `Good` on [0,1], and the linear functional `Ig f x A = int_0^x A t *v g t` (g = forcingValue f)
   with linearity (integrability proved first) and the norm bound 2 b int dens. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.GK38
open scoped Matrix

namespace NlsGge.ThirdConsultation.KSPS007Support5

abbrev Mt : Type := Matrix (Fin 2) (Fin 2) ℂ

def EB (A : Mt) (b : ℝ) : Prop := ∀ i j, ‖A i j‖ ≤ b

theorem EB.nonneg {A : Mt} {b : ℝ} (h : EB A b) : 0 ≤ b := (norm_nonneg _).trans (h 0 0)

theorem EB.mono {A : Mt} {b b' : ℝ} (h : EB A b) (hb : b ≤ b') : EB A b' := fun i j => (h i j).trans hb

theorem EB.add {A B : Mt} {a b : ℝ} (hA : EB A a) (hB : EB B b) : EB (A + B) (a + b) :=
  fun i j => by
    rw [Matrix.add_apply]; exact (norm_add_le _ _).trans (add_le_add (hA i j) (hB i j))

theorem EB.sub {A B : Mt} {a b : ℝ} (hA : EB A a) (hB : EB B b) : EB (A - B) (a + b) :=
  fun i j => by
    rw [Matrix.sub_apply]; exact (norm_sub_le _ _).trans (add_le_add (hA i j) (hB i j))

theorem EB.neg {A : Mt} {a : ℝ} (hA : EB A a) : EB (-A) a :=
  fun i j => by rw [Matrix.neg_apply, norm_neg]; exact hA i j

theorem EB.smul (c : ℂ) {A : Mt} {a : ℝ} (hA : EB A a) : EB (c • A) (‖c‖ * a) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hA i j) (norm_nonneg _)

theorem EB.mul {A B : Mt} {a b : ℝ} (hA : EB A a) (hB : EB B b) : EB (A * B) (2 * (a * b)) :=
  fun i j => by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have h0 : ‖A i 0 * B 0 j‖ ≤ a * b := by
      rw [norm_mul]; exact mul_le_mul (hA i 0) (hB 0 j) (norm_nonneg _) hA.nonneg
    have h1 : ‖A i 1 * B 1 j‖ ≤ a * b := by
      rw [norm_mul]; exact mul_le_mul (hA i 1) (hB 1 j) (norm_nonneg _) hA.nonneg
    calc _ ≤ ‖A i 0 * B 0 j‖ + ‖A i 1 * B 1 j‖ := norm_add_le _ _
      _ ≤ 2 * (a * b) := by linarith

theorem EB.mulVec {A : Mt} {a : ℝ} (h : EB A a) (v : Fin 2 → ℂ) : ‖A.mulVec v‖ ≤ 2 * (a * ‖v‖) := by
  have hn : 0 ≤ 2 * (a * ‖v‖) := by have := h.nonneg; positivity
  refine (pi_norm_le_iff_of_nonneg hn).2 (fun i => ?_)
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h0 : ‖A i 0 * v 0‖ ≤ a * ‖v‖ := by
    rw [norm_mul]; exact mul_le_mul (h i 0) (norm_le_pi_norm v 0) (norm_nonneg _) h.nonneg
  have h1 : ‖A i 1 * v 1‖ ≤ a * ‖v‖ := by
    rw [norm_mul]; exact mul_le_mul (h i 1) (norm_le_pi_norm v 1) (norm_nonneg _) h.nonneg
  calc _ ≤ ‖A i 0 * v 0‖ + ‖A i 1 * v 1‖ := norm_add_le _ _
    _ ≤ 2 * (a * ‖v‖) := by linarith

theorem EB.zero : EB (0 : Mt) 0 := fun i j => by simp

theorem EB.one : EB (1 : Mt) 1 := fun i j => by
  fin_cases i <;> fin_cases j <;> simp

/-! ### continuous matrix functions -/

def Good (A : ℝ → Mt) : Prop := ∀ i j, ContinuousOn (fun t => A t i j) (Set.Icc (0 : ℝ) 1)

theorem Good.const (C : Mt) : Good (fun _ => C) := fun i j => continuousOn_const

theorem Good.add {A B : ℝ → Mt} (hA : Good A) (hB : Good B) : Good (fun t => A t + B t) :=
  fun i j => by simp only [Matrix.add_apply]; exact (hA i j).add (hB i j)

theorem Good.sub {A B : ℝ → Mt} (hA : Good A) (hB : Good B) : Good (fun t => A t - B t) :=
  fun i j => by simp only [Matrix.sub_apply]; exact (hA i j).sub (hB i j)

theorem Good.neg {A : ℝ → Mt} (hA : Good A) : Good (fun t => -A t) :=
  fun i j => by simp only [Matrix.neg_apply]; exact (hA i j).neg

theorem Good.smul (c : ℂ) {A : ℝ → Mt} (hA : Good A) : Good (fun t => c • A t) :=
  fun i j => by simp only [Matrix.smul_apply, smul_eq_mul]; exact (hA i j).const_smul c

theorem Good.mul {A B : ℝ → Mt} (hA : Good A) (hB : Good B) : Good (fun t => A t * B t) :=
  fun i j => by
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    exact ((hA i 0).mul (hB 0 j)).add ((hA i 1).mul (hB 1 j))

/-! ### the functional Ig -/

theorem ii_vec {u : ℝ → Fin 2 → ℂ} {a b : ℝ}
    (h : ∀ i, IntervalIntegrable (fun t => u t i) volume a b) : IntervalIntegrable u volume a b :=
  ⟨integrable_pi_iff.2 (fun i => (h i).1), integrable_pi_iff.2 (fun i => (h i).2)⟩

def Ig (f : PotPair) (x : ℝ) (A : ℝ → Mt) : Fin 2 → ℂ :=
  ∫ t in (0 : ℝ)..x, (A t).mulVec (KSPSVolterra.forcingValue f t)

theorem Good.mulVec_ii {A : ℝ → Mt} (hA : Good A) (f : PotPair) (i : Fin 2) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => ((A t).mulVec (KSPSVolterra.forcingValue f t)) i) volume 0 x := by
  have hc : ∀ k, ContinuousOn (fun t => A t i k) (Set.uIcc (0 : ℝ) x) := by
    intro k
    refine (hA i k).mono ?_
    rw [Set.uIcc_of_le hx.1]
    exact Set.Icc_subset_Icc le_rfl hx.2
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact ((NlsGge.ThirdConsultation.KSPS007Support3.g_ii f 0 hx.1).continuousOn_mul (hc 0)).add
    ((NlsGge.ThirdConsultation.KSPS007Support3.g_ii f 1 hx.1).continuousOn_mul (hc 1))

theorem Good.mulVec_iiV {A : ℝ → Mt} (hA : Good A) (f : PotPair) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t => (A t).mulVec (KSPSVolterra.forcingValue f t)) volume 0 x :=
  ii_vec (fun i => hA.mulVec_ii f i hx)

theorem Ig_add (f : PotPair) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {A B : ℝ → Mt}
    (hA : Good A) (hB : Good B) :
    Ig f x (fun t => A t + B t) = Ig f x A + Ig f x B := by
  unfold Ig
  simp only [Matrix.add_mulVec]
  exact intervalIntegral.integral_add (hA.mulVec_iiV f hx) (hB.mulVec_iiV f hx)

theorem Ig_sub (f : PotPair) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {A B : ℝ → Mt}
    (hA : Good A) (hB : Good B) :
    Ig f x (fun t => A t - B t) = Ig f x A - Ig f x B := by
  unfold Ig
  simp only [Matrix.sub_mulVec]
  exact intervalIntegral.integral_sub (hA.mulVec_iiV f hx) (hB.mulVec_iiV f hx)

theorem Ig_neg (f : PotPair) (x : ℝ) (A : ℝ → Mt) :
    Ig f x (fun t => -A t) = -Ig f x A := by
  unfold Ig
  simp only [Matrix.neg_mulVec]
  exact intervalIntegral.integral_neg

theorem Ig_smul (f : PotPair) (x : ℝ) (c : ℂ) (A : ℝ → Mt) :
    Ig f x (fun t => c • A t) = c • Ig f x A := by
  unfold Ig
  simp only [Matrix.smul_mulVec]
  exact intervalIntegral.integral_smul c _

theorem Ig_mul_left (f : PotPair) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (C : Mt) {A : ℝ → Mt}
    (hA : Good A) :
    Ig f x (fun t => C * A t) = C.mulVec (Ig f x A) := by
  unfold Ig
  let L : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin C)
  have h := L.intervalIntegral_comp_comm (hA.mulVec_iiV f hx)
  have hL : ∀ v, L v = C.mulVec v := fun v => by simp [L]
  simp only [hL] at h
  rw [← h]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [Matrix.mulVec_mulVec]

theorem Ig_congr (f : PotPair) (x : ℝ) {A B : ℝ → Mt} (h : ∀ t, A t = B t) :
    Ig f x A = Ig f x B := by
  have : A = B := funext h
  rw [this]

theorem vec_norm_le_dens (f : PotPair) (t : ℝ) :
    ‖KSPSVolterra.forcingValue f t‖ ≤ NlsGge.ThirdConsultation.KSPS005Support.dens f t := by
  refine (pi_norm_le_iff_of_nonneg (NlsGge.ThirdConsultation.KSPS005Support.dens_nonneg f t)).2
    (fun i => ?_)
  fin_cases i
  · simpa [KSPSVolterra.forcingValue] using NlsGge.ThirdConsultation.KSPS005Support.fst_le_dens f t
  · simpa [KSPSVolterra.forcingValue] using NlsGge.ThirdConsultation.KSPS005Support.snd_le_dens f t

theorem Ig_norm_le (f : PotPair) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) {A : ℝ → Mt} {b : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) x, EB (A t) b) :
    ‖Ig f x A‖ ≤ 2 * b * Real.sqrt (‖f.1‖ ^ 2 + ‖f.2‖ ^ 2) := by
  have hb : 0 ≤ b := (h 0 ⟨le_rfl, hx.1⟩).nonneg
  have hd1 : IntervalIntegrable (NlsGge.ThirdConsultation.KSPS005Support.dens f) volume 0 x :=
    (NlsGge.ThirdConsultation.KSPS005Support.dens_ii f).mono_set (by
      rw [Set.uIcc_of_le hx.1, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc le_rfl hx.2)
  have hden : IntervalIntegrable (fun t => 2 * b * NlsGge.ThirdConsultation.KSPS005Support.dens f t)
      volume 0 x := hd1.const_mul _
  have h1 := intervalIntegral.norm_integral_le_of_norm_le hx.1
    (f := fun t => (A t).mulVec (KSPSVolterra.forcingValue f t))
    (g := fun t => 2 * b * NlsGge.ThirdConsultation.KSPS005Support.dens f t)
    (Filter.Eventually.of_forall (fun t ht => by
      have hm := (h t ⟨ht.1.le, ht.2⟩).mulVec (KSPSVolterra.forcingValue f t)
      have hv := vec_norm_le_dens f t
      calc _ ≤ 2 * (b * ‖KSPSVolterra.forcingValue f t‖) := hm
        _ ≤ 2 * (b * NlsGge.ThirdConsultation.KSPS005Support.dens f t) :=
            by gcongr
        _ = _ := by ring)) hden
  rw [intervalIntegral.integral_const_mul] at h1
  have h2 : ∫ t in (0 : ℝ)..x, NlsGge.ThirdConsultation.KSPS005Support.dens f t ≤
      ∫ t in (0 : ℝ)..1, NlsGge.ThirdConsultation.KSPS005Support.dens f t :=
    intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
      (Filter.Eventually.of_forall fun t => NlsGge.ThirdConsultation.KSPS005Support.dens_nonneg f t)
      (NlsGge.ThirdConsultation.KSPS005Support.dens_ii f)
  have h3 := NlsGge.ThirdConsultation.KSPS005Support.integral_dens_le f
  have h4 : 0 ≤ 2 * b := by positivity
  calc ‖Ig f x A‖ ≤ 2 * b * ∫ t in (0 : ℝ)..x, NlsGge.ThirdConsultation.KSPS005Support.dens f t := h1
    _ ≤ 2 * b * Real.sqrt (‖f.1‖ ^ 2 + ‖f.2‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left (h2.trans h3) h4

end NlsGge.ThirdConsultation.KSPS007Support5
