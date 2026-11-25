import Mathlib
import NlsGge.GK38.IsolatingDefs
import NlsGge.GK38.TauGamma
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.Lib.ParamProductsRoot
/- H215_SEP01 (proof development, AUTHOR; not self-reviewed). Pro round 9 section 10, step 3 (G4-018).
   On the whole isolating neighbourhood: for z in the open n-th disc and m != n, the points tau_m,
   lamMinus_m, lamPlus_m (all in the m-th open disc) are at distance >= c^-1 |m-n| from z, from the
   geometry clause of IsolatingGeometry38 (ballDistance lower bound). The standard root satisfies
   w^2 = (a-z)(b-z) for the gap endpoints a,b, hence |w| >= c^-1 |m-n|. No hypothesis beyond these. -/
set_option autoImplicit false

open Set Metric
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.G4018Support

theorem dist_lower_of_geometry (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) (m n : ℤ) (hmn : m ≠ n)
    (x z : ℂ) (hx : x ∈ ball (C m) (R m)) (hz : z ∈ ball (C n) (R n)) :
    c⁻¹ * |((m - n : ℤ) : ℝ)| ≤ ‖x - z‖ := by
  have hb := (hgeom.2.2.2.1 m n hmn).1
  unfold ballDistance38 at hb
  rw [← dist_eq_norm]
  refine hb.trans (csInf_le ?_ ⟨x, hx, z, hz, rfl⟩)
  exact ⟨0, fun v hv => by obtain ⟨a, _, b, _, rfl⟩ := hv; exact dist_nonneg⟩

theorem endpoints_mem_ball (φ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ) (N : ℕ)
    (hspec : IsolatingSpectral38 φ C R) (m : ℤ) :
    lamMinus φ m ∈ ball (C m) (R m) ∧ lamPlus φ m ∈ ball (C m) (R m) := by
  have hseg := (hspec.1 m).1
  exact ⟨hseg (left_mem_segment ℝ _ _), hseg (right_mem_segment ℝ _ _)⟩

theorem tau_mem_ball (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (N : ℕ)
    (hspec : IsolatingSpectral38 φ C R) (m : ℤ) :
    tauN φ m ∈ ball (C m) (R m) := by
  have hmid : tauN φ m ∈ segment ℝ (lamMinus φ m) (lamPlus φ m) := by
    rw [tauN_value38 φ hφ m]
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    simp only [Complex.real_smul]
    push_cast
    ring
  exact (hspec.1 m).1 hmid

theorem sep_lower_all (φ : PotPair) (hφ : φ ∈ gkW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hgeom : IsolatingGeometry38 C R c N) (hspec : IsolatingSpectral38 φ C R)
    (m n : ℤ) (hmn : m ≠ n) (z : ℂ) (hz : z ∈ ball (C n) (R n)) :
    c⁻¹ * |((m - n : ℤ) : ℝ)| ≤ ‖tauN φ m - z‖ ∧
    c⁻¹ * |((m - n : ℤ) : ℝ)| ≤ ‖lamMinus φ m - z‖ ∧
    c⁻¹ * |((m - n : ℤ) : ℝ)| ≤ ‖lamPlus φ m - z‖ := by
  obtain ⟨hmin, hplus⟩ := endpoints_mem_ball φ C R N hspec m
  exact ⟨dist_lower_of_geometry C R c N hgeom m n hmn _ z (tau_mem_ball φ hφ C R N hspec m) hz,
    dist_lower_of_geometry C R c N hgeom m n hmn _ z hmin hz,
    dist_lower_of_geometry C R c N hgeom m n hmn _ z hplus hz⟩

theorem stdRoot38_sq_of (a b τ g z : ℂ) (hτ : τ = (a + b) / 2) (hg : g = (b - a) ^ 2)
    (hv : τ - z ≠ 0) : stdRoot38 τ g z ^ 2 = (a - z) * (b - z) := by
  unfold stdRoot38
  have hs := Lib.sqrt_sq (1 - (g / 4) / (τ - z) ^ 2)
  have key : (τ - z) ^ 2 * (1 - (g / 4) / (τ - z) ^ 2) = (τ - z) ^ 2 - g / 4 := by
    field_simp
  rw [mul_pow, hs, key]
  subst hτ hg
  ring

theorem stdRoot_norm_lower (a b τ g z : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hτ : τ = (a + b) / 2) (hg : g = (b - a) ^ 2) (hv : τ - z ≠ 0)
    (ha : t ≤ ‖a - z‖) (hb : t ≤ ‖b - z‖) : t ≤ ‖stdRoot38 τ g z‖ := by
  have h := congrArg norm (stdRoot38_sq_of a b τ g z hτ hg hv)
  rw [norm_pow, norm_mul] at h
  have hprod : t * t ≤ ‖a - z‖ * ‖b - z‖ := mul_le_mul ha hb ht (norm_nonneg _)
  have hprod2 : t * t ≤ ‖stdRoot38 τ g z‖ ^ 2 := by
    rw [h]
    exact hprod
  nlinarith [norm_nonneg (stdRoot38 τ g z)]

end NlsGge.G4018Support
