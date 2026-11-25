import Mathlib
import QuantumNLS.Local007Statement
import QuantumNLS.Local020Cov
import QuantumNLS.Local020Rr
import QuantumNLS.Local020Mass
import QuantumNLS.Local020PlaneG
import QuantumNLS.RootIndexedMassesFull
import QuantumNLS.RootMassScaling

/-! LOCAL-020: the covariance statements for a LOCAL-007 family `(a, b, rr)` on a ball, assembled from the frozen
stages.  `Dat` records exactly the pieces of the LOCAL-007 conclusion that are used. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology ComplexConjugate BoundedContinuousFunction
open QuantumNLS.LocalSpectral
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (Pkg gcoef)
open QuantumNLS.Fourier (modeLp)
open QuantumNLS.RootIndexedMasses (masses)

namespace QuantumNLS.Local020Fin1

variable {L κ r : ℝ} [Fact (0 < L)]

/-- The pieces of the LOCAL-007 conclusion used by LOCAL-020. -/
structure Dat (L κ r ρ C : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ)
    (rr : L2T L → (ℤ →ᵇ ℝ)) : Prop where
  pkg : ∀ n, Pkg L κ r ρ C n (a n) (b n)
  hC0 : 0 ≤ C
  hρ : 0 < ρ
  ana : AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ)
  mass : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, (masses hκ u).1 n = ‖gcoef L κ * b n u‖ ^ 2 * rr u n
  pos : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, 0 < rr u n
  small : C * ρ ^ 2 < 1

variable {hκ : 0 < κ} {ρ C : ℝ} {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ} {rr : L2T L → (ℤ →ᵇ ℝ)}

/-- Covariance of `rr` for a real-linear isometry (generic form). -/
theorem rr_cov (D : Dat L κ r ρ C hκ a b rr) (T : L2T L →L[ℝ] L2T L) (hT : ∀ w, ‖T w‖ = ‖w‖) (σ : ℤ → ℤ) (n : ℤ)
    (hmass : ∀ w ∈ ball (0 : L2T L) ρ, (masses hκ (T w)).1 n = (masses hκ w).1 (σ n))
    (hmod : ∀ w ∈ ball (0 : L2T L) ρ, ‖b n (T w)‖ = ‖b (σ n) w‖) :
    ∀ w ∈ ball (0 : L2T L) ρ, rr (T w) n = rr w (σ n) :=
  QuantumNLS.Local020Rr.rr_cov_generic hκ D.pkg D.hC0 D.ana D.mass D.hρ le_rfl D.small T hT σ n hmass hmod

/-! ### The real-linear isometries as continuous linear maps -/

def Tt (y : ℝ) : L2T L →L[ℝ] L2T L :=
  ((QuantumNLS.BornTranslation.trans (L := L) y).toContinuousLinearMap).restrictScalars ℝ

def Tb (k : ℤ) : L2T L →L[ℝ] L2T L :=
  ((QuantumNLS.Local007Gauge.boostLI (L := L) k).toContinuousLinearMap).restrictScalars ℝ

def Tp (φ : ℝ) : L2T L →L[ℝ] L2T L :=
  (Complex.exp ((φ : ℂ) * Complex.I) • ContinuousLinearMap.id ℂ (L2T L)).restrictScalars ℝ

def Tr : L2T L →L[ℝ] L2T L := (QuantumNLS.ResetNormalizationUniqueness.reflectR L).toContinuousLinearMap

theorem Tt_apply (y : ℝ) (w : L2T L) : Tt y w = QuantumNLS.BornTranslation.trans y w := rfl
theorem Tb_apply (k : ℤ) (w : L2T L) : Tb k w = QuantumNLS.RootMassBoostSymbol.boost k w := rfl
theorem Tp_apply (φ : ℝ) (w : L2T L) : Tp φ w = Complex.exp ((φ : ℂ) * Complex.I) • w := rfl
theorem Tr_apply (w : L2T L) : Tr w = QuantumNLS.ResetNormalizationUniqueness.reflectR L w := rfl

theorem norm_Tt (y : ℝ) (w : L2T L) : ‖Tt y w‖ = ‖w‖ :=
  (QuantumNLS.BornTranslation.trans (L := L) y).norm_map w
theorem norm_Tb (k : ℤ) (w : L2T L) : ‖Tb k w‖ = ‖w‖ := QuantumNLS.RootMassBoostSymbol.norm_boost k w
theorem norm_Tp (φ : ℝ) (w : L2T L) : ‖Tp φ w‖ = ‖w‖ := by
  rw [Tp_apply, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
theorem norm_Tr (w : L2T L) : ‖Tr w‖ = ‖w‖ :=
  (QuantumNLS.ResetNormalizationUniqueness.reflectR L).norm_map w

theorem reflectR_reflectR (w : L2T L) :
    QuantumNLS.ResetNormalizationUniqueness.reflectR L (QuantumNLS.ResetNormalizationUniqueness.reflectR L w) = w := by
  apply Lp.ext
  have hmp := (QuantumNLS.ResetNormalizationUniqueness.negMP L).quasiMeasurePreserving
  filter_upwards [QuantumNLS.ResetNormalizationUniqueness.coeFn_reflectR L
      (QuantumNLS.ResetNormalizationUniqueness.reflectR L w),
    hmp.ae_eq_comp (QuantumNLS.ResetNormalizationUniqueness.coeFn_reflectR L w)] with x h1 h2
  rw [h1]
  simp only [Function.comp] at h2
  rw [h2, neg_neg]

def Ts : L2T L →L[ℝ] L2T L :=
  (QuantumNLS.ResetNormalizationUniqueness.Cphys L).toContinuousLinearMap.comp Tr

theorem Ts_apply (w : L2T L) : Ts w = star w := by
  show QuantumNLS.ResetNormalizationUniqueness.Cphys L (QuantumNLS.ResetNormalizationUniqueness.reflectR L w) = _
  show star (QuantumNLS.ResetNormalizationUniqueness.reflectR L
    (QuantumNLS.ResetNormalizationUniqueness.reflectR L w)) = _
  rw [reflectR_reflectR]

theorem norm_Ts (w : L2T L) : ‖Ts w‖ = ‖w‖ := by
  rw [Ts_apply]; exact QuantumNLS.ResetNormalizationUniqueness.norm_cj L w

/-! ### Covariance of `g_n = gcoef · b_n` -/

theorem norm_exp_I_mul (p y : ℝ) : ‖Complex.exp (Complex.I * (p : ℂ) * (y : ℂ))‖ = 1 := by
  have : Complex.I * (p : ℂ) * (y : ℂ) = ((p * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this]; exact Complex.norm_exp_ofReal_mul_I _

theorem g_cov (D : Dat L κ r ρ C hκ a b rr) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) (n : ℤ) :
    (∀ y : ℝ, gcoef L κ * b n (QuantumNLS.BornTranslation.trans y u) =
        Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * (gcoef L κ * b n u)) ∧
    (∀ k : ℤ, gcoef L κ * b n (QuantumNLS.RootMassBoostSymbol.boost k u) = gcoef L κ * b (n - k) u) ∧
    gcoef L κ * b n (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) = gcoef L κ * b (-n) u ∧
    gcoef L κ * b n (star u) = conj (gcoef L κ * b (-n) u) ∧
    (∀ φ : ℝ, gcoef L κ * b n (Complex.exp ((φ : ℂ) * Complex.I) • u) =
        Complex.exp ((φ : ℂ) * Complex.I) * (gcoef L κ * b n u)) := by
  refine ⟨fun y => ?_, fun k => ?_, ?_, ?_, fun φ => ?_⟩
  · rw [QuantumNLS.Local020Cov.cov_trans D.pkg y hu n]; ring
  · rw [QuantumNLS.Local020Cov.cov_boost D.pkg k hu n]
  · have := (QuantumNLS.Local020Cov.cov_refl D.pkg hu (-n)).1
    rw [neg_neg] at this
    rw [this]
  · have := (QuantumNLS.Local020Cov.cov_conj D.pkg hu (-n)).1
    rw [neg_neg] at this
    rw [this, map_mul, QuantumNLS.Local020PlaneG.conj_gcoef]
    ring
  · rw [QuantumNLS.Local020Cov.cov_phase D.pkg φ hu n]; ring

/-! ### Covariance of `rr` -/

theorem rr_covariance (D : Dat L κ r ρ C hκ a b rr)
    (hRC : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
      (masses hκ (QuantumNLS.ResetNormalizationUniqueness.reflectR L u)).1 n = (masses hκ u).1 (-n) ∧
      (masses hκ (star u)).1 n = (masses hκ u).1 (-n))
    {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) (n : ℤ) :
    (∀ y : ℝ, rr (QuantumNLS.BornTranslation.trans y u) n = rr u n) ∧
    (∀ k : ℤ, rr (QuantumNLS.RootMassBoostSymbol.boost k u) n = rr u (n - k)) ∧
    rr (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = rr u (-n) ∧
    rr (star u) n = rr u (-n) ∧
    (∀ φ : ℝ, rr (Complex.exp ((φ : ℂ) * Complex.I) • u) n = rr u n) := by
  refine ⟨fun y => ?_, fun k => ?_, ?_, ?_, fun φ => ?_⟩
  · have := rr_cov D (Tt y) (norm_Tt y) id n
      (fun w _ => by
        show (masses hκ (QuantumNLS.BornTranslation.trans y w)).1 n = _
        rw [QuantumNLS.RootIndexedMasses.masses_translation]; rfl)
      (fun w hw => by
        show ‖b n (QuantumNLS.BornTranslation.trans y w)‖ = _
        rw [QuantumNLS.Local020Cov.cov_trans D.pkg y hw n, norm_mul, norm_exp_I_mul, one_mul]; rfl) u hu
    exact this
  · have := rr_cov D (Tb k) (norm_Tb k) (fun m => m - k) n
      (fun w _ => by
        show (masses hκ (QuantumNLS.RootMassBoostSymbol.boost k w)).1 n = _
        exact QuantumNLS.RootMassGalilean.masses_boost hκ k n w)
      (fun w hw => by
        show ‖b n (QuantumNLS.RootMassBoostSymbol.boost k w)‖ = _
        rw [QuantumNLS.Local020Cov.cov_boost D.pkg k hw n]) u hu
    exact this
  · have := rr_cov D Tr norm_Tr (fun m => -m) n
      (fun w hw => (hRC w hw n).1)
      (fun w hw => by
        show ‖b n (QuantumNLS.ResetNormalizationUniqueness.reflectR L w)‖ = _
        have := (QuantumNLS.Local020Cov.cov_refl D.pkg hw (-n)).1
        rw [neg_neg] at this
        rw [this]) u hu
    exact this
  · have := rr_cov D Ts norm_Ts (fun m => -m) n
      (fun w hw => by
        show (masses hκ (Ts w)).1 n = _
        rw [Ts_apply]; exact (hRC w hw n).2)
      (fun w hw => by
        show ‖b n (Ts w)‖ = _
        rw [Ts_apply]
        have := (QuantumNLS.Local020Cov.cov_conj D.pkg hw (-n)).1
        rw [neg_neg] at this
        rw [this, norm_neg, Complex.norm_conj]) u hu
    rw [Ts_apply] at this
    exact this
  · have := rr_cov D (Tp φ) (norm_Tp φ) id n
      (fun w _ => by
        show (masses hκ (Complex.exp ((φ : ℂ) * Complex.I) • w)).1 n = _
        rw [QuantumNLS.RootIndexedMasses.masses_phase hκ w (Complex.norm_exp_ofReal_mul_I φ)]; rfl)
      (fun w hw => by
        show ‖b n (Complex.exp ((φ : ℂ) * Complex.I) • w)‖ = _
        rw [QuantumNLS.Local020Cov.cov_phase D.pkg φ hw n, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]; rfl) u hu
    exact this

end QuantumNLS.Local020Fin1

#print axioms QuantumNLS.Local020Fin1.g_cov
#print axioms QuantumNLS.Local020Fin1.rr_covariance
