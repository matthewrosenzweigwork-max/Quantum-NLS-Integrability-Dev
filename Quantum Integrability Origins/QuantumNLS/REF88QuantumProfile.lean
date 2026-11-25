import Mathlib
import QuantumNLS.REF88QuantumTangent
import QuantumNLS.REF88QuantumDef

/-!
# REF88QuantumProfile: the normalized physical profile `v(K,x)` (R-EF8C2837, item (iii))

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), printed lines 216-222:
"For a finite positive probability vector `x` and any `K > 0`, global surjectivity supplies the smooth normalized
physical profile `v(K,x) = sqrt(kappa/K) Phi_kappa^{-1}((sqrt(K x_j/kappa))_{j in F})`.  Its actual indexed probabilities at
coupling `K` are `x`, by the full-field scaling identity."

`exists_profile`: for a strongly symplectic `Phi` with exact moduli and the REG-015 input (finite action fields are `H^1`),
every probability vector `x` supported in a finite set `F` and every `K > 0` has a unit `H^1` profile `v` with
`II hK v = x` (the printed `v(K,x)`: `unitDir (Phi^{-1} z)` for `z_j = sqrt(K x_j/kappa)`; scaling identity
`REF88QuantumDef.II_unitDir`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.REF88QuantumProfile

open QuantumNLS.Fourier QuantumNLS.StrongSymplectic QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88GradStructure QuantumNLS.REF88FieldRotation QuantumNLS.REF88QuantumTangent
open QuantumNLS.REF88QuantumDef
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ProductEnergyPreparation (OneH1)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

theorem oneH1_smul' (c : ℂ) {u : L2T L} (hH : OneH1 u) : OneH1 (c • u) := by
  unfold OneH1 Fourier.Mem04 at hH ⊢
  refine (hH.mul_left (‖c‖ ^ 2)).congr fun n => ?_
  simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

theorem oneH1_unitDir' {u : L2T L} (hH : OneH1 u) : OneH1 (FullMass.unitDir u) :=
  oneH1_smul' _ hH

/-- The finitely supported point `z_j = sqrt(K x_j/κ)`. -/
def pvec (κ K' : ℝ) (x : ℤ → ℝ) (F : Finset ℤ) : K :=
  ∑ n ∈ F, sg n (((Real.sqrt (K' * x n / κ) : ℝ) : ℂ))

lemma pvec_apply (κ K' : ℝ) (x : ℤ → ℝ) (F : Finset ℤ) (m : ℤ) :
    (pvec κ K' x F : ℤ → ℂ) m = if m ∈ F then ((Real.sqrt (K' * x m / κ) : ℝ) : ℂ) else 0 := by
  unfold pvec
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [sg_apply]
  by_cases hm : m ∈ F
  · rw [Finset.sum_eq_single m]
    · simp [hm]
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd hm h
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro b hb
    have : m ≠ b := fun e => hm (e ▸ hb)
    simp [this]

theorem exists_profile (hκ : 0 < κ) {Φ : L2T L → K} (hΦ : IsStronglySymplectic Φ)
    (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
    (hR : Reg015Input L κ hκ) (F : Finset ℤ) (K' : ℝ) (hK' : 0 < K') (x : ℤ → ℝ)
    (hx0 : ∀ n, 0 ≤ x n) (hxF : ∀ n, n ∉ F → x n = 0) (hx1 : ∑ n ∈ F, x n = 1) :
    ∃ v : L2T L, ‖v‖ = 1 ∧ OneH1 v ∧ ∃ hK : 0 < K', ∀ n, II hK v n = x n := by
  set z : K := pvec κ K' x F with hz
  have hz0 : ∀ n, n ∉ F → z n = 0 := fun n hn => by rw [hz, pvec_apply, if_neg hn]
  have hzn : ∀ m, ‖z m‖ ^ 2 = K' * x m / κ := by
    intro m
    rw [hz, pvec_apply]
    by_cases hm : m ∈ F
    · rw [if_pos hm, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Real.sq_sqrt (by have := hx0 m; positivity)
    · rw [if_neg hm, hxF m hm]; simp
  set u := chartInv hΦ z with hu
  have hmu : ∀ n, (RootIndexedMasses.masses hκ u).1 n = K' * x n / κ := fun n => by
    rw [masses_chart hκ hΦ hmod, hzn]
  have hnorm : ‖u‖ ^ 2 = K' / κ := by
    rw [← (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.2.1]
    simp_rw [hmu]
    rw [tsum_eq_sum (s := F) (fun n hn => by rw [hxF n hn]; simp)]
    rw [← Finset.sum_div, ← Finset.mul_sum, hx1, mul_one]
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    have h3 : (0 : ℝ) < K' / κ := div_pos hK' hκ
    rw [← hnorm] at h3
    norm_num at h3
  have hKu : 0 < κ * ‖u‖ ^ 2 := by
    rw [hnorm]; have : κ * (K' / κ) = K' := by field_simp
    rw [this]; exact hK'
  have hKeq : κ * ‖u‖ ^ 2 = K' := by rw [hnorm]; field_simp
  refine ⟨FullMass.unitDir u, FullMass.norm_unitDir hu0,
    oneH1_unitDir' (oneH1_chartInv hκ hΦ hmod hR z F hz0), hK', fun n => ?_⟩
  have h1 := II_unitDir hκ hu0 hKu n
  have h2 := II_congr_coupling hKeq hKu hK' (FullMass.unitDir u) n
  have h3 : II hκ u n = K' * x n / κ := hmu n
  have hm : (0 : ℝ) < ‖u‖ ^ 2 := by rw [hnorm]; exact div_pos hK' hκ
  rw [← h2]
  have : ‖u‖ ^ 2 * II hKu (FullMass.unitDir u) n = K' * x n / κ := by rw [← h1, h3]
  have h4 : II hKu (FullMass.unitDir u) n = (K' * x n / κ) / ‖u‖ ^ 2 := by
    rw [eq_div_iff hm.ne', mul_comm]
    exact this
  rw [h4, hnorm]
  field_simp

end QuantumNLS.REF88QuantumProfile

#print axioms QuantumNLS.REF88QuantumProfile.exists_profile
