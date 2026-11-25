import Mathlib
import QuantumNLS.Local020Final
import QuantumNLS.RootIndexedMassesFull
import QuantumNLS.Local021Mono

/-!
# LOCAL-021, stage 7: the exact-modulus map `ζ` of LOCAL-020 as a map `K → K`, and its symmetry transport

* `Fam020` is LOCAL-020's conclusion (`Local020Final.reset_spectral_covariance`, `local_covariance.tex:23`) for a family `(a, b, rr)` on a ball `ρ`
  (verbatim body of the frozen theorem; `fam020_exists` re-derives it from the frozen theorem, so the notion is non-vacuous).
* `zetaK` : `u ↦ (ζ_n(u))_n ∈ ℓ²(ℤ)` (membership and `‖ζ(u)‖ = ‖u‖` from the mass identity `Σ I_n = ‖u‖²` of R-950BFB30).
* `SymKind` : the six symmetries translation, boost, reflection, conjugation-reflection `star`, conjugation `C`, common phase,
  with the physical action `SymKind.phys` and the sequence action (monomial operator `SymKind.mono`); `fourier_phys` proves the sequence actions
  `a_n ↦ e^{ip_n y}a_n, a_{n-k}, a_{-n}, conj a_{-n}, conj a_n, e^{iφ}a_n` of the report.
* `zetaK_cov`, `zetaK_plane`, `zetaK_scale` : the covariances, plane normalization and scaling of `ζ` in sequence variables.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric Filter Topology ComplexConjugate BoundedContinuousFunction
open QuantumNLS.LocalSpectral
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (Pkg gcoef)
open QuantumNLS.Fourier (modeLp fourierL2)
open QuantumNLS.RootIndexedMasses (masses)
open QuantumNLS.Local020Final (zeta)

namespace QuantumNLS.Local021

open QuantumNLS.D01LocalPrimitive (K)

variable {L κ r : ℝ} [Fact (0 < L)]

/-- The conclusion of LOCAL-020 (`prop:reset-spectral-covariance`) for the family `(a, b, rr)` on the ball `ρ`. -/
def Fam020 (L κ r ρ C : ℝ) [Fact (0 < L)] (hκ : 0 < κ) (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ)
    (rr : L2T L → (ℤ →ᵇ ℝ)) : Prop :=
  -- the family `g_n = gcoef · b_n` (polar-normalized Riesz reduction) and the exact-mass factors `r_n = rr_n`
  (∀ n : ℤ, Pkg L κ r ρ C n (a n) (b n)) ∧
  AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ) ∧
  (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
    (masses hκ u).1 n = ‖gcoef L κ * b n u‖ ^ 2 * rr u n) ∧
  (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, 1 / 2 < rr u n ∧ rr u n < 3 / 2) ∧
  -- covariances of `g_n`
  (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
    (∀ y : ℝ, gcoef L κ * b n (QuantumNLS.BornTranslation.trans y u) =
      Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * (gcoef L κ * b n u)) ∧
    (∀ k : ℤ, gcoef L κ * b n (QuantumNLS.RootMassBoostSymbol.boost k u) = gcoef L κ * b (n - k) u) ∧
    gcoef L κ * b n (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) = gcoef L κ * b (-n) u ∧
    gcoef L κ * b n (star u) = conj (gcoef L κ * b (-n) u) ∧
    (∀ φ : ℝ, gcoef L κ * b n (Complex.exp ((φ : ℂ) * Complex.I) • u) =
      Complex.exp ((φ : ℂ) * Complex.I) * (gcoef L κ * b n u))) ∧
  -- index permutations of `r_n`; unchanged by translations and common phase
  (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
    (∀ y : ℝ, rr (QuantumNLS.BornTranslation.trans y u) n = rr u n) ∧
    (∀ k : ℤ, rr (QuantumNLS.RootMassBoostSymbol.boost k u) n = rr u (n - k)) ∧
    rr (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = rr u (-n) ∧
    rr (star u) n = rr u (-n) ∧
    (∀ φ : ℝ, rr (Complex.exp ((φ : ℂ) * Complex.I) • u) n = rr u n)) ∧
  -- `ζ_n = g_n √r_n` has precisely the Fourier covariances
  (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
    (∀ y : ℝ, zeta L κ b rr (QuantumNLS.BornTranslation.trans y u) n =
      Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * zeta L κ b rr u n) ∧
    (∀ k : ℤ, zeta L κ b rr (QuantumNLS.RootMassBoostSymbol.boost k u) n = zeta L κ b rr u (n - k)) ∧
    zeta L κ b rr (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = zeta L κ b rr u (-n) ∧
    zeta L κ b rr (star u) n = conj (zeta L κ b rr u (-n)) ∧
    (∀ φ : ℝ, zeta L κ b rr (Complex.exp ((φ : ℂ) * Complex.I) • u) n =
      Complex.exp ((φ : ℂ) * Complex.I) * zeta L κ b rr u n)) ∧
  -- in particular `ζ_n(C R u) = conj ζ_n(u)`
  (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
    zeta L κ b rr (QuantumNLS.ResetNormalizationUniqueness.Cphys L u) n = conj (zeta L κ b rr u n)) ∧
  -- `ζ = 𝓕` on every single Fourier plane `u = c e_k`
  (∀ (k : ℤ) (c : ℂ), ‖c‖ < ρ → ∀ n : ℤ,
    zeta L κ b rr (c • modeLp L k) n =
      QuantumNLS.Fourier.coeff L (((c • modeLp L k : L2T L)) : AddCircle L → ℂ) n) ∧
  -- scaling `ζ_κ(s u) = s ζ_{κ s²}(u)` on common domains (against every LOCAL-007 family at coupling `κ s²`)
  (∀ s : ℝ, 0 < s → ∀ (hκ₂ : 0 < κ * s ^ 2) (ρ₂ C₂ : ℝ), 0 < ρ₂ → 0 ≤ C₂ →
    ∀ (a₂ : ℤ → L2T L → ℝ) (b₂ : ℤ → L2T L → ℂ) (rr₂ : L2T L → (ℤ →ᵇ ℝ)),
      (∀ n : ℤ, Pkg L (κ * s ^ 2) r ρ₂ C₂ n (a₂ n) (b₂ n)) →
      AnalyticOnNhd ℝ rr₂ (ball (0 : L2T L) ρ₂) →
      (∀ u ∈ ball (0 : L2T L) ρ₂, ∀ n : ℤ,
        (masses hκ₂ u).1 n = ‖gcoef L (κ * s ^ 2) * b₂ n u‖ ^ 2 * rr₂ u n) →
      ∀ u : L2T L, ‖u‖ < ρ₂ → s * ‖u‖ < ρ → ∀ n : ℤ,
        gcoef L κ * b n ((s : ℂ) • u) = (s : ℂ) * (gcoef L (κ * s ^ 2) * b₂ n u) ∧
        rr ((s : ℂ) • u) n = rr₂ u n ∧
        zeta L κ b rr ((s : ℂ) • u) n = (s : ℂ) * zeta L (κ * s ^ 2) b₂ rr₂ u n)

theorem fam020_exists (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)), Fam020 L κ r ρ C hκ a b rr :=
  QuantumNLS.Local020Final.reset_spectral_covariance hκ hr hr2


/-! ### `ζ` as a map into `ℓ²(ℤ)` -/

open Classical in
/-- `u ↦ (ζ_n(u))_n` as an element of `ℓ²(ℤ)` (`0` where the sequence is not square-summable). -/
def zetaK (L κ : ℝ) [Fact (0 < L)] (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)) (u : L2T L) : K :=
  if h : Memℓp (fun n => zeta L κ b rr u n) 2 then ⟨_, h⟩ else 0

variable {hκ : 0 < κ} {ρ C : ℝ} {a : ℤ → L2T L → ℝ} {b : ℤ → L2T L → ℂ} {rr : L2T L → (ℤ →ᵇ ℝ)}

theorem norm_zeta_sq (F : Fam020 L κ r ρ C hκ a b rr) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) (n : ℤ) :
    ‖zeta L κ b rr u n‖ ^ 2 = (masses hκ u).1 n := by
  have hpos : 0 ≤ rr u n := by linarith [(F.2.2.2.1 u hu n).1]
  unfold zeta
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hpos,
    F.2.2.1 u hu n]

theorem memℓp_zeta (F : Fam020 L κ r ρ C hκ a b rr) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) :
    Memℓp (fun n => zeta L κ b rr u n) 2 := by
  refine memℓp_gen ?_
  have := (QuantumNLS.RootIndexedMassesFull.root_indexed_masses hκ u).2.2.1
  refine this.congr fun n => ?_
  rw [ENNReal.toReal_ofNat, Real.rpow_two, norm_zeta_sq F hu n]

theorem zetaK_apply (F : Fam020 L κ r ρ C hκ a b rr) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) (n : ℤ) :
    zetaK L κ b rr u n = zeta L κ b rr u n := by
  unfold zetaK
  rw [dif_pos (memℓp_zeta F hu)]

theorem norm_zetaK (F : Fam020 L κ r ρ C hκ a b rr) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) :
    ‖zetaK L κ b rr u‖ = ‖u‖ := by
  have h1 : ‖zetaK L κ b rr u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [QuantumNLS.D01LocalPrimitive.norm_sq_K, ← (QuantumNLS.RootIndexedMassesFull.root_indexed_masses hκ u).2.2.2.1]
    refine tsum_congr fun n => ?_
    rw [zetaK_apply F hu, norm_zeta_sq F hu]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

theorem zetaK_mem_ball (F : Fam020 L κ r ρ C hκ a b rr) {u : L2T L} {R : ℝ} (hu : u ∈ ball (0 : L2T L) ρ)
    (hR : ‖u‖ < R) : zetaK L κ b rr u ∈ ball (0 : K) R := by
  rw [mem_ball_zero_iff, norm_zetaK F hu]; exact hR

/-! ### Fourier coefficients of the physical symmetries -/

section FourierSym

open QuantumNLS.Fourier (fourierL2 mode coeff coeff_congr_ae fourierL2_apply mode_neg)

theorem mode_neg_index (n : ℤ) (x : AddCircle L) : mode L (-n) x = conj (mode L n x) := by
  unfold mode
  rw [map_mul, Complex.conj_ofReal, fourier_neg]

theorem coeff_reflect (u : L2T L) (n : ℤ) :
    fourierL2 L (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = fourierL2 L u (-n) := by
  rw [fourierL2_apply, fourierL2_apply,
    coeff_congr_ae L (QuantumNLS.ResetNormalizationUniqueness.coeFn_reflectR L u)]
  unfold coeff
  rw [← integral_neg_eq_self (fun x : AddCircle L => conj (mode L (-n) x) * (u : AddCircle L → ℂ) x) volume]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [mode_neg, mode_neg_index, map_mul, Complex.conj_conj]

theorem coeff_star (u : L2T L) (n : ℤ) :
    fourierL2 L (star u) n = conj (fourierL2 L u (-n)) := by
  rw [fourierL2_apply, fourierL2_apply, coeff_congr_ae L (QuantumNLS.ResetNormalizationUniqueness.coeFn_cj L u)]
  unfold coeff
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [mode_neg_index, map_mul, Complex.conj_conj]

theorem fourier_unit (n : ℤ) (z : AddCircle L) : conj (fourier n z) * fourier n z = 1 := by
  rw [Complex.conj_mul', show ‖fourier n z‖ = 1 from by rw [fourier_apply]; exact Circle.norm_coe _]; simp

theorem coeff_boost (k : ℤ) (u : L2T L) (n : ℤ) :
    fourierL2 L (QuantumNLS.RootMassBoostSymbol.boost k u) n = fourierL2 L u (n - k) := by
  rw [fourierL2_apply, fourierL2_apply, coeff_congr_ae L (QuantumNLS.RootMassBoostSymbol.coe_boost k u)]
  unfold coeff
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show conj (mode L n x) * (fourier k x * u x) = conj (mode L (n - k) x) * u x
  have h1 : conj (mode L n x) * fourier k x = conj (mode L (n - k) x) := by
    unfold mode
    have e1 : fourier (n - k) x = fourier n x * conj (fourier k x) := by
      rw [sub_eq_add_neg, fourier_add, fourier_neg]
    have e2 : conj (fourier (n - k) x) = conj (fourier n x) * fourier k x := by
      rw [e1, map_mul, Complex.conj_conj]
    rw [map_mul, map_mul, Complex.conj_ofReal, e2]; ring
  rw [← h1]; ring

theorem coeff_trans (y : ℝ) (u : L2T L) (n : ℤ) :
    fourierL2 L (QuantumNLS.BornTranslation.trans y u) n =
      Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) * fourierL2 L u n := by
  rw [fourierL2_apply, fourierL2_apply, coeff_congr_ae L (QuantumNLS.BornTranslation.coeFn_trans y u)]
  unfold coeff
  set yy : AddCircle L := (y : AddCircle L) with hyy
  set c : ℂ := fourier n yy with hc
  have hcexp : c = Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)) := by
    rw [hc, hyy, fourier_coe_apply]
    congr 1
    unfold pm
    push_cast
    ring
  rw [← hcexp, ← integral_const_mul,
    ← integral_add_right_eq_self (fun z : AddCircle L => c * (conj (mode L n z) * (u : AddCircle L → ℂ) z)) yy]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show conj (mode L n x) * u (x + yy) = c * (conj (mode L n (x + yy)) * u (x + yy))
  have hadd : fourier n (x + yy) = fourier n x * c := by
    rw [hc, fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
  have hm : conj (mode L n (x + yy)) = conj (mode L n x) * conj c := by
    unfold mode
    rw [map_mul, map_mul, Complex.conj_ofReal, hadd, map_mul]; ring
  rw [hm]
  have hu := fourier_unit n yy
  rw [← hc] at hu
  linear_combination (-(conj (mode L n x) * u (x + yy))) * hu

end FourierSym

/-! ### The six symmetries and their transport to sequence variables -/

/-- translation, boost, reflection `R`, conjugation `C` (`cj`: `u ↦ \bar u`), conjugation-reflection `CR` (`cjr`: `u ↦ \bar{u(-·)}`), common phase. -/
inductive SymKind
  | phase (φ : ℝ)
  | trans (y : ℝ)
  | boost (k : ℤ)
  | refl
  | cj
  | cjr

namespace SymKind

/-- the sequence action as a monomial operator: `e^{iφ}a_n`, `e^{ip_ny}a_n`, `a_{n-k}`, `a_{-n}`, `conj a_{-n}`, `conj a_n`. -/
def mono (L : ℝ) : SymKind → Mono
  | phase φ => { σ := Equiv.refl ℤ, c := fun _ => Complex.exp ((φ : ℂ) * Complex.I),
                 hc := fun _ => Complex.norm_exp_ofReal_mul_I φ, anti := false }
  | trans y => { σ := Equiv.refl ℤ, c := fun n => Complex.exp (Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ)),
                 hc := fun n => by
                   rw [show Complex.I * ((pm L n : ℝ) : ℂ) * (y : ℂ) = ((pm L n * y : ℝ) : ℂ) * Complex.I by
                     push_cast; ring]
                   exact Complex.norm_exp_ofReal_mul_I _, anti := false }
  | boost k => { σ := Equiv.addRight k, c := fun _ => 1, hc := fun _ => by simp, anti := false }
  | refl => { σ := Equiv.neg ℤ, c := fun _ => 1, hc := fun _ => by simp, anti := false }
  | cj => { σ := Equiv.neg ℤ, c := fun _ => 1, hc := fun _ => by simp, anti := true }
  | cjr => { σ := Equiv.refl ℤ, c := fun _ => 1, hc := fun _ => by simp, anti := true }

/-- the physical action on `L²(𝕋_L)`. -/
def phys (L : ℝ) [Fact (0 < L)] : SymKind → L2T L → L2T L
  | phase φ => fun u => Complex.exp ((φ : ℂ) * Complex.I) • u
  | trans y => fun u => QuantumNLS.BornTranslation.trans y u
  | boost k => fun u => QuantumNLS.RootMassBoostSymbol.boost k u
  | refl => fun u => QuantumNLS.ResetNormalizationUniqueness.reflectR L u
  | cj => fun u => star u
  | cjr => fun u => QuantumNLS.ResetNormalizationUniqueness.Cphys L u

theorem norm_phys (s : SymKind) (u : L2T L) : ‖s.phys L u‖ = ‖u‖ := by
  cases s with
  | phase φ => simp [phys, norm_smul, Complex.norm_exp_ofReal_mul_I]
  | trans y => exact LinearIsometry.norm_map _ u
  | boost k => exact QuantumNLS.RootMassBoostSymbol.norm_boost k u
  | refl => exact LinearIsometry.norm_map _ u
  | cj => exact QuantumNLS.ResetNormalizationUniqueness.norm_cj L u
  | cjr => exact QuantumNLS.ResetNormalizationUniqueness.norm_Cphys L u

/-- the sequence actions of the report: `𝓕 (T u) = U (𝓕 u)`. -/
theorem fourier_phys (s : SymKind) (u : L2T L) :
    fourierL2 L (s.phys L u) = (s.mono L).act (fourierL2 L u) := by
  refine lp.ext (funext fun n => ?_)
  cases s with
  | phase φ =>
    show fourierL2 L (Complex.exp ((φ : ℂ) * Complex.I) • u) n = _
    rw [map_smul]; simp [mono, Mono.cj]
  | trans y =>
    show fourierL2 L (QuantumNLS.BornTranslation.trans y u) n = _
    rw [coeff_trans]; simp [mono, Mono.cj]
  | boost k =>
    show fourierL2 L (QuantumNLS.RootMassBoostSymbol.boost k u) n = _
    rw [coeff_boost]; simp [mono, Mono.cj, sub_eq_add_neg]
  | refl =>
    show fourierL2 L (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = _
    rw [coeff_reflect]; simp [mono, Mono.cj]
  | cj =>
    show fourierL2 L (star u) n = _
    rw [coeff_star]; simp [mono, Mono.cj]
  | cjr =>
    show fourierL2 L (QuantumNLS.ResetNormalizationUniqueness.Cphys L u) n = _
    rw [QuantumNLS.ResetNormalizationUniqueness.fourier_Cphys]; simp [mono, Mono.cj]

end SymKind

/-- covariance of `ζ` (in sequence variables) under the six symmetries. -/
theorem zetaK_cov (F : Fam020 L κ r ρ C hκ a b rr) (s : SymKind) {u : L2T L} (hu : u ∈ ball (0 : L2T L) ρ) :
    zetaK L κ b rr (s.phys L u) = (s.mono L).act (zetaK L κ b rr u) := by
  have hTu : s.phys L u ∈ ball (0 : L2T L) ρ := by
    rw [mem_ball_zero_iff, s.norm_phys]; exact mem_ball_zero_iff.1 hu
  refine lp.ext (funext fun n => ?_)
  rw [zetaK_apply F hTu]
  have hz := F.2.2.2.2.2.2.1 u hu n
  obtain ⟨z1, z2, z3, z4, z5⟩ := hz
  have hz' := F.2.2.2.2.2.2.2.1 u hu n
  cases s with
  | phase φ =>
    show zeta L κ b rr (Complex.exp ((φ : ℂ) * Complex.I) • u) n = _
    rw [z5 φ]; simp [SymKind.mono, Mono.cj, zetaK_apply F hu]
  | trans y =>
    show zeta L κ b rr (QuantumNLS.BornTranslation.trans y u) n = _
    rw [z1 y]; simp [SymKind.mono, Mono.cj, zetaK_apply F hu]
  | boost k =>
    show zeta L κ b rr (QuantumNLS.RootMassBoostSymbol.boost k u) n = _
    rw [z2 k]; simp [SymKind.mono, Mono.cj, zetaK_apply F hu, sub_eq_add_neg]
  | refl =>
    show zeta L κ b rr (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) n = _
    rw [z3]; simp [SymKind.mono, Mono.cj, zetaK_apply F hu]
  | cj =>
    show zeta L κ b rr (star u) n = _
    rw [z4]; simp [SymKind.mono, Mono.cj, zetaK_apply F hu]
  | cjr =>
    show zeta L κ b rr (QuantumNLS.ResetNormalizationUniqueness.Cphys L u) n = _
    rw [hz']; simp [SymKind.mono, Mono.cj, zetaK_apply F hu]

/-- `ζ = 𝓕` on every Fourier plane: `ζ(c e_k) = c e_k` in sequence variables. -/
theorem zetaK_plane (F : Fam020 L κ r ρ C hκ a b rr) (k : ℤ) (c : ℂ) (hc : ‖c‖ < ρ) :
    zetaK L κ b rr (c • modeLp L k) = lp.single 2 k c := by
  have hu : c • modeLp L k ∈ ball (0 : L2T L) ρ := by
    rw [mem_ball_zero_iff, norm_smul, QuantumNLS.Local020Rr.norm_modeLp L k, mul_one]; exact hc
  refine lp.ext (funext fun n => ?_)
  rw [zetaK_apply F hu]
  have := F.2.2.2.2.2.2.2.2.1 k c hc n
  rw [QuantumNLS.Local020Fin2.coeff_c_mode] at this
  rw [this]
  simp only [lp.single_apply, Pi.single_apply]

/-- coupling scaling: `ζ_κ(s u) = s ζ_{κ s²}(u)` in sequence variables, against a second family at coupling `κ s²`. -/
theorem zetaK_scale (F : Fam020 L κ r ρ C hκ a b rr) {s : ℝ} (hs : 0 < s) (hκ₂ : 0 < κ * s ^ 2) {ρ₂ C₂ : ℝ}
    (hρ₂ : 0 < ρ₂) (hC₂ : 0 ≤ C₂) {a₂ : ℤ → L2T L → ℝ} {b₂ : ℤ → L2T L → ℂ} {rr₂ : L2T L → (ℤ →ᵇ ℝ)}
    (F₂ : Fam020 L (κ * s ^ 2) r ρ₂ C₂ hκ₂ a₂ b₂ rr₂) {u : L2T L} (hu₂ : ‖u‖ < ρ₂) (hu : s * ‖u‖ < ρ) :
    zetaK L κ b rr ((s : ℂ) • u) = (s : ℂ) • zetaK L (κ * s ^ 2) b₂ rr₂ u := by
  have hmem : u ∈ ball (0 : L2T L) ρ₂ := mem_ball_zero_iff.2 hu₂
  have hsu : (s : ℂ) • u ∈ ball (0 : L2T L) ρ := by
    rw [mem_ball_zero_iff, norm_smul, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hu
  refine lp.ext (funext fun n => ?_)
  rw [zetaK_apply F hsu, lp.coeFn_smul, Pi.smul_apply, zetaK_apply F₂ hmem, smul_eq_mul]
  exact (F.2.2.2.2.2.2.2.2.2 s hs hκ₂ ρ₂ C₂ hρ₂ hC₂ a₂ b₂ rr₂ F₂.1 F₂.2.1 F₂.2.2.1 u hu₂ hu n).2.2

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.fam020_exists
#print axioms QuantumNLS.Local021.norm_zetaK
