import Mathlib
import QuantumNLS.REF88QuantumTangent
import QuantumNLS.REF88QuantumDef
import QuantumNLS.REF88PrintedChart

/-!
# REF88QuantumReduce: from the quantum derivatives to the frequency formula (R-EF8C2837, item (iii), reduction)

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), end of the paragraph "Quantum
derivatives at arbitrary finite mass" (printed lines 296-315):
  "The physical energy is `h_F(a) = m ℰ(κ m, a/m)`.  Varying actions at fixed mass and then varying all actions
   proportionally gives `ν_a - ν_b = ω_{ab}`, `∑_j x_j ν_j = ℰ + 𝒯`.  Solving these finite linear identities proves
   (eq:global-absolute-frequency) ..."

Printed step -> Lean (this module is a REDUCTION: its hypotheses `R1`, `R2` are exactly the two printed derivative
facts `∂_{e_a-e_b} ℰ = ω_{ab}` and `K ∂_K ℰ = 𝒯`, which are the content of the printed limiting argument and are NOT
yet proved in Lean; they are NOT a named input of the node and are to be discharged by the remaining sub-lemmas):
* `curve_data`: along the rescaled finite-action curve `y(s)` (`n`-th action `(1+s c_n)|z_n|²`) the energy is
  `H_κ(Φ⁻¹ y(s)) = M(s) · ℰ(κ M(s), x(s))`, `M = ∑ (1+s c_n)|z_n|²` (printed `h_F(a) = m ℰ(κ m, a/m)`,
  `REF88QuantumDef.energy_eq_mass_mul_qEnergy`);
* `pair_identity` (fixed mass): `λ_a - λ_b = ω_{ab}` from `R1` and the tangent argument `REF88QuantumTangent.tangent`;
* `radial_identity` (proportional): `∑ |z_n|² λ_n = m(ℰ + 𝒯)` from `R2` and the tangent argument;
* `lam_formula` (the finite linear algebra): `λ_n = ℰ + 𝒯 + ∑_{j∈F} x_j ω_{nj}`, using the printed antisymmetry
  `ω_{ab} = -ω_{ba}` (`REF88QuantumDef.omega_swap`);
* `flow_rot_lamAt`, `nu_eq_lamAt`: the stage-C frequency `ν_n(a)` of the physical flow equals `λ_n` (regular-solution
  step `REF88Finite.chartFlow_eq_rotFreq` and the uniqueness clause of `stageC`).
Only `Reg015Input` (finite action in every `H^s`) is used, as in stage C.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate InnerProductSpace
open Filter Topology

namespace QuantumNLS.REF88QuantumReduce

open QuantumNLS.StrongSymplectic QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88FieldRotation QuantumNLS.REF88QuantumTangent QuantumNLS.REF88QuantumDef
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- The total action of the rescaled curve. -/
def Mcurve (F : Finset ℤ) (c : ℤ → ℝ) (z : K) (s : ℝ) : ℝ := ∑ n ∈ F, (1 + s * c n) * ‖z n‖ ^ 2

/-- The line `x + s (e_a - e_b)` in the space of indexed probabilities. -/
def lineX (x : ℤ → ℝ) (a b : ℤ) (s : ℝ) : ℤ → ℝ :=
  fun n => x n + s * ((if n = a then 1 else 0) - (if n = b then 1 else 0))

lemma eventually_pos (F : Finset ℤ) (c : ℤ → ℝ) : ∀ᶠ s : ℝ in 𝓝 0, ∀ n ∈ F, 0 < 1 + s * c n := by
  rw [Filter.eventually_all_finset]
  intro n _
  have hc : ContinuousAt (fun s : ℝ => 1 + s * c n) 0 := by fun_prop
  have h0 : (0 : ℝ) < 1 + 0 * c n := by simp
  exact hc.eventually (lt_mem_nhds h0)

section Chart

variable (hκ : 0 < κ) {Φ : L2T L → K} (hΦ : IsStronglySymplectic Φ)
  (hmod : ∀ (u : L2T L) (n : ℤ), ‖Φ u n‖ ^ 2 = (RootIndexedMasses.masses hκ u).1 n)
  (hR : Reg015Input L κ hκ)
include hmod hR

/-- Masses, mass and energy along the rescaled curve (positive actions). -/
theorem curve_data (F : Finset ℤ) (z : K) (hne : ∀ n ∈ F, z n ≠ 0)
    (hF : F.Nonempty) (c : ℤ → ℝ) (s : ℝ) (hs : ∀ n ∈ F, 0 < 1 + s * c n) :
    0 < Mcurve F c z s ∧
    (∀ n, (RootIndexedMasses.masses hκ (chartInv hΦ (curveY F c z s))).1 n =
      if n ∈ F then (1 + s * c n) * ‖z n‖ ^ 2 else 0) ∧
    ChargeEnergy.energyH1 κ ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ) =
      Mcurve F c z s * Efun L (κ * Mcurve F c z s) (fun n =>
        (if n ∈ F then (1 + s * c n) * ‖z n‖ ^ 2 else 0) / Mcurve F c z s) := by
  set y := curveY F c z s with hy
  set u := chartInv hΦ y with hu
  have hM : 0 < Mcurve F c z s := by
    unfold Mcurve
    apply Finset.sum_pos _ hF
    intro n hn
    have := hne n hn
    have : 0 < ‖z n‖ ^ 2 := by positivity
    exact mul_pos (hs n hn) this
  have hmasses : ∀ n, (RootIndexedMasses.masses hκ u).1 n =
      if n ∈ F then (1 + s * c n) * ‖z n‖ ^ 2 else 0 := by
    intro n
    rw [hu, masses_chart hκ hΦ hmod, hy, norm_sq_curveY F c z s n (fun n hn => (hs n hn).le)]
  have hnorm : ‖u‖ ^ 2 = Mcurve F c z s := by
    rw [← (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.2.1]
    rw [tsum_eq_sum (s := F) (fun n hn => by rw [hmasses n, if_neg hn])]
    unfold Mcurve
    exact Finset.sum_congr rfl fun n hn => by rw [hmasses n, if_pos hn]
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; simp at hnorm; linarith
  have hKs : 0 < κ * ‖u‖ ^ 2 := by rw [hnorm]; exact mul_pos hκ hM
  have hOne := oneH1_chartInv hκ hΦ hmod hR y F (fun n hn => curveY_supp F c z s hn)
  have hE := energy_eq_mass_mul_qEnergy hκ hu0 hOne hKs
  obtain ⟨hK', hEf⟩ := Efun_eq_unitDir (L := L) hκ hu0 hKs (K := κ * Mcurve F c z s) (by rw [hnorm])
    (x := fun n => (if n ∈ F then (1 + s * c n) * ‖z n‖ ^ 2 else 0) / Mcurve F c z s) (by
      intro n
      show (RootIndexedMasses.masses hκ u).1 n = _
      rw [hnorm, hmasses n]
      field_simp)
  refine ⟨hM, hmasses, ?_⟩
  rw [hE, hEf]
  rw [Mu_congr_coupling (by rw [hnorm]) hKs hK' (FullMass.unitDir u), hnorm]

section Main

variable (F : Finset ℤ) (z : K) (hz : ∀ n, n ∉ F → z n = 0) (hne : ∀ n ∈ F, z n ≠ 0)
  (hF : F.Nonempty) (m : ℝ) (hm : m = ∑ n ∈ F, ‖z n‖ ^ 2) (hmpos : 0 < m)
  (v : L2T L) (hv : ‖v‖ = 1) (hK : 0 < κ * m)
  (hvI : ∀ n, II hK v n = ‖z n‖ ^ 2 / m) (D : Data hK v)
include hz hne hF hm hmpos hvI hv

/-- **Pair identity**: `λ_a - λ_b = ω_{ab}` once `∂_{e_a - e_b} ℰ = ω_{ab}`. -/
theorem pair_identity {a b : ℤ} (ha : a ∈ F) (hb : b ∈ F)
    (R1 : HasDerivAt (fun s : ℝ => Efun L (κ * m) (lineX (fun n => ‖z n‖ ^ 2 / m) a b s))
      (D.omega a b) 0) :
    lamAt hκ hΦ z a - lamAt hκ hΦ z b = D.omega a b := by
  set c : ℤ → ℝ := fun n =>
    (m * ((if n = a then 1 else 0) - (if n = b then 1 else 0))) / ‖z n‖ ^ 2 with hc
  have hcz : ∀ n ∈ F, c n * ‖z n‖ ^ 2 = m * ((if n = a then 1 else 0) - (if n = b then 1 else 0)) := by
    intro n hn
    have h1 : ‖z n‖ ≠ 0 := norm_ne_zero_iff.2 (hne n hn)
    have : (‖z n‖ ^ 2 : ℝ) ≠ 0 := by positivity
    rw [hc]; field_simp
  have hsum : ∑ n ∈ F, c n * ‖z n‖ ^ 2 = 0 := by
    rw [Finset.sum_congr rfl hcz, ← Finset.mul_sum, Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq', ha, hb]
  have hMc : ∀ s, Mcurve F c z s = m := by
    intro s
    unfold Mcurve
    have : ∀ n ∈ F, (1 + s * c n) * ‖z n‖ ^ 2 = ‖z n‖ ^ 2 + s * (c n * ‖z n‖ ^ 2) := fun n _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, ← hm]; ring
  have hev : ∀ᶠ s : ℝ in 𝓝 0, ChargeEnergy.energyH1 κ
      ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ) =
      m * Efun L (κ * m) (lineX (fun n => ‖z n‖ ^ 2 / m) a b s) := by
    filter_upwards [eventually_pos F c] with s hs
    obtain ⟨-, -, hE⟩ := curve_data hκ hΦ hmod hR F z hne hF c s hs
    rw [hE, hMc s]
    congr 2
    funext n
    unfold lineX
    by_cases hn : n ∈ F
    · rw [if_pos hn]
      have hcn := hcz n hn
      have : (1 + s * c n) * ‖z n‖ ^ 2 = ‖z n‖ ^ 2 + s * (c n * ‖z n‖ ^ 2) := by ring
      rw [this, hcn]; field_simp
    · have hna : n ≠ a := fun h => hn (h ▸ ha)
      have hnb : n ≠ b := fun h => hn (h ▸ hb)
      have hz0 : z n = 0 := hz n hn
      simp [hn, hna, hnb, hz0]
  have hd : HasDerivAt (fun s : ℝ => ChargeEnergy.energyH1 κ
      ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ)) (m * D.omega a b) 0 :=
    (R1.const_mul m).congr_of_eventuallyEq hev
  have ht := tangent hκ hΦ hmod hR F z hz hne c hd
  have hsum2 : ∑ n ∈ F, c n * ‖z n‖ ^ 2 * lamAt hκ hΦ z n =
      m * (lamAt hκ hΦ z a - lamAt hκ hΦ z b) := by
    have : ∀ n ∈ F, c n * ‖z n‖ ^ 2 * lamAt hκ hΦ z n =
        m * ((if n = a then lamAt hκ hΦ z n else 0) - (if n = b then lamAt hκ hΦ z n else 0)) := by
      intro n hn
      rw [hcz n hn]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_sub_distrib]
    simp [Finset.sum_ite_eq', ha, hb]
  rw [hsum2] at ht
  have := mul_left_cancel₀ hmpos.ne' ht
  linarith

/-- **Radial identity**: `∑ |z_n|² λ_n = m (ℰ + 𝒯)` once `K ∂_K ℰ = 𝒯`. -/
theorem radial_identity
    (R2 : HasDerivAt (fun K' : ℝ => Efun L K' (fun n => ‖z n‖ ^ 2 / m))
      (qT D.bd D.F / (κ * m)) (κ * m)) :
    ∑ n ∈ F, ‖z n‖ ^ 2 * lamAt hκ hΦ z n = m * (qEnergy (Mu hK v) + qT D.bd D.F) := by
  set c : ℤ → ℝ := fun _ => 1 with hc
  have hMc : ∀ s, Mcurve F c z s = (1 + s) * m := by
    intro s
    unfold Mcurve
    rw [hm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by simp [hc]
  have hKm : (κ * m) ≠ 0 := (mul_pos hκ hmpos).ne'
  have hev : ∀ᶠ s : ℝ in 𝓝 0, ChargeEnergy.energyH1 κ
      ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ) =
      (1 + s) * m * Efun L (κ * m * (1 + s)) (fun n => ‖z n‖ ^ 2 / m) := by
    filter_upwards [eventually_pos F c] with s hs
    obtain ⟨-, -, hE⟩ := curve_data hκ hΦ hmod hR F z hne hF c s hs
    have hs1 : 0 < 1 + s := by
      obtain ⟨n0, hn0⟩ := hF
      simpa [hc] using hs n0 hn0
    rw [hE, hMc s]
    have e1 : κ * ((1 + s) * m) = κ * m * (1 + s) := by ring
    rw [e1]
    have hx : (fun n => (if n ∈ F then (1 + s * c n) * ‖z n‖ ^ 2 else 0) / ((1 + s) * m)) =
        fun n => ‖z n‖ ^ 2 / m := by
      funext n
      by_cases hn : n ∈ F
      · rw [if_pos hn]; simp only [hc, mul_one]
        field_simp
      · rw [if_neg hn, hz n hn]; simp
    rw [hx]
  have hh2 : HasDerivAt (fun K' : ℝ => Efun L K' (fun n => ‖z n‖ ^ 2 / m))
      (qT D.bd D.F / (κ * m)) (κ * m * (1 + 0)) := by simpa using R2
  have hh : HasDerivAt (fun s : ℝ => κ * m * (1 + s)) (κ * m) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).const_mul (κ * m)
  have hcomp := hh2.comp 0 hh
  have hprod : HasDerivAt (fun s : ℝ => (1 + s) * m) m 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const m
  have hmul := hprod.mul hcomp
  have hd : HasDerivAt (fun s : ℝ => ChargeEnergy.energyH1 κ
      ((chartInv hΦ (curveY F c z s) : L2T L) : AddCircle L → ℂ))
      (m * Efun L (κ * m) (fun n => ‖z n‖ ^ 2 / m) + m * qT D.bd D.F) 0 := by
    refine (hmul.congr_deriv ?_).congr_of_eventuallyEq hev
    simp only [Function.comp_apply, add_zero]
    field_simp
  have ht := tangent hκ hΦ hmod hR F z hz hne c hd
  rw [Efun_eq hK hv hvI] at ht
  simp only [hc, one_mul] at ht
  rw [← ht]; ring

/-- **The frequency formula for the chart frequencies** `λ_n = ∂_{a_n} h_F`: if
`∂_{e_a - e_b} ℰ = ω_{ab}` (`b < a`, both active) and `K ∂_K ℰ = 𝒯` at `(K, x)`, `K = κ m`, `x_j = |z_j|²/m`, then
`λ_n(z) = ℰ + 𝒯 + ∑_{j∈F} x_j ω_{nj}` for every active `n`. -/
theorem lam_formula
    (R1 : ∀ a b : ℤ, a ∈ F → b ∈ F → b < a →
      HasDerivAt (fun s : ℝ => Efun L (κ * m) (lineX (fun n => ‖z n‖ ^ 2 / m) a b s))
        (D.omega a b) 0)
    (R2 : HasDerivAt (fun K' : ℝ => Efun L K' (fun n => ‖z n‖ ^ 2 / m))
      (qT D.bd D.F / (κ * m)) (κ * m)) {n : ℤ} (hn : n ∈ F) :
    lamAt hκ hΦ z n = qEnergy (Mu hK v) + qT D.bd D.F +
      ∑ j ∈ F, (‖z j‖ ^ 2 / m) * D.omega n j := by
  have hdiff : ∀ j ∈ F, lamAt hκ hΦ z n - lamAt hκ hΦ z j = D.omega n j := by
    intro j hj
    rcases lt_trichotomy j n with h | h | h
    · exact pair_identity hκ hΦ hmod hR F z hz hne hF m hm hmpos v hv hK hvI D hn hj (R1 n j hn hj h)
    · subst h
      simp [Data.omega]
    · have h1 := pair_identity hκ hΦ hmod hR F z hz hne hF m hm hmpos v hv hK hvI D hj hn
        (R1 j n hj hn h)
      rw [omega_swap D n j]
      linarith
  have hrad := radial_identity hκ hΦ hmod hR F z hz hne hF m hm hmpos v hv hK hvI D R2
  have hsum1 : ∑ j ∈ F, ‖z j‖ ^ 2 = m := hm.symm
  have key : m * lamAt hκ hΦ z n = m * (qEnergy (Mu hK v) + qT D.bd D.F) +
      ∑ j ∈ F, ‖z j‖ ^ 2 * D.omega n j := by
    rw [← hrad]
    calc m * lamAt hκ hΦ z n = (∑ j ∈ F, ‖z j‖ ^ 2) * lamAt hκ hΦ z n := by rw [hsum1]
      _ = ∑ j ∈ F, ‖z j‖ ^ 2 * lamAt hκ hΦ z n := Finset.sum_mul _ _ _
      _ = ∑ j ∈ F, (‖z j‖ ^ 2 * lamAt hκ hΦ z j + ‖z j‖ ^ 2 * D.omega n j) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have := hdiff j hj
          have : lamAt hκ hΦ z n = lamAt hκ hΦ z j + D.omega n j := by linarith
          rw [this]; ring
      _ = _ := Finset.sum_add_distrib
  have hdiv : lamAt hκ hΦ z n = (m * (qEnergy (Mu hK v) + qT D.bd D.F) +
      ∑ j ∈ F, ‖z j‖ ^ 2 * D.omega n j) / m := by
    rw [← key]; field_simp
  rw [hdiv, add_div, mul_div_cancel_left₀ _ hmpos.ne', Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

end Main

end Chart

section Flow

open QuantumNLS.REF88Finite QuantumNLS.L2Flow QuantumNLS.REF88PrintedChart QuantumNLS.RephasingFlow QuantumNLS.ChartFrequencies

/-- On a finitely supported chart point the physical flow rotates coordinate `n` with the stage-C frequency
`λ_n(z) = lamAt` (the regular-solution step `REF88Finite.chartFlow_eq_rotFreq`). -/
theorem flow_rot_lamAt {Φ : L2T L → K} (hκ : 0 < κ) (hR : Reg015Input L κ hκ) (hΦ : PrintedChart hκ Φ)
    (F : Finset ℤ) (z : K) (hz : ∀ n, n ∉ F → z n = 0) (t : ℝ) (n : ℤ) :
    Φ (flowMap hκ.le (chartInv hΦ.symp z) t) n =
      Complex.exp (-Complex.I * ((t * lamAt hκ hΦ.symp z n : ℝ) : ℂ)) * z n := by
  have hex : ∃ F : Finset ℤ, ∀ n, n ∉ F → z n = 0 := ⟨F, hz⟩
  obtain ⟨hc1, hc2⟩ := printedChart_continuity hκ hΦ
  have hlam : ∀ (F : Finset ℤ) (z : K), (∀ n, n ∉ F → z n = 0) →
      fderiv ℝ (chartInv hΦ.symp) z
        (∑ n ∈ F, lp.single (E := fun _ : ℤ => ℂ) 2 n
          (-Complex.I * ((lamFun hκ hΦ.symp (act z) n : ℝ) : ℂ) * z n)) =
        physField κ (chartInv hΦ.symp z) := by
    intro F z hz
    have hex : ∃ F : Finset ℤ, ∀ n, n ∉ F → z n = 0 := ⟨F, hz⟩
    have := field_identity hκ hΦ.symp hΦ.moduli hR z F hz
    simp only [lamFun_act hκ hΦ.symp hΦ.moduli z hex]
    exact this
  have h := chartFlow_eq_rotFreq hκ hR hΦ.symp hc1 hc2 hΦ.moduli hlam F z hz t
  have h2 : (chartFlow hΦ.symp hκ.le t z) n = (rotFreq (lamFun hκ hΦ.symp (act z)) t z) n :=
    congrArg (fun w : K => (w : ℤ → ℂ) n) h
  unfold chartFlow at h2
  rw [h2, rotFreq_apply, lamFun_act hκ hΦ.symp hΦ.moduli z hex]

/-- The stage-C frequency `ν_n(a)` of a finitely supported field equals the chart frequency `λ_n(Φ u)`
(by the uniqueness clause of stage C). -/
theorem nu_eq_lamAt {Φ : L2T L → K} (hκ : 0 < κ) (hR : Reg015Input L κ hκ) (hΦ : PrintedChart hκ Φ)
    (ν : ℤ → ActionTorus.PosL1 → ℝ)
    (huniq : ∀ (u : L2T L) (n : ℤ), 0 < (RootIndexedMasses.masses hκ u).1 n → ∀ ν' : ℝ,
        (∀ t : ℝ, Φ (flowMap hκ.le u t) n =
          Complex.exp (-Complex.I * ((t * ν' : ℝ) : ℂ)) * Φ u n) →
          ν' = ν n (RootIndexedMasses.masses hκ u))
    (u : L2T L) (F : Finset ℤ) (hF : ∀ n, n ∉ F → (RootIndexedMasses.masses hκ u).1 n = 0) (n : ℤ)
    (hn : 0 < (RootIndexedMasses.masses hκ u).1 n) :
    ν n (RootIndexedMasses.masses hκ u) = lamAt hκ hΦ.symp (Φ u) n := by
  symm
  apply huniq u n hn
  intro t
  have hz : ∀ m, m ∉ F → (Φ u) m = 0 := by
    intro m hm
    have h0 := hΦ.moduli u m
    rw [hF m hm] at h0
    have : ‖(Φ u) m‖ = 0 := by nlinarith [norm_nonneg ((Φ u) m)]
    exact norm_eq_zero.1 this
  have := flow_rot_lamAt hκ hR hΦ F (Φ u) hz t n
  rwa [chartInv_left hΦ.symp] at this

end Flow

end QuantumNLS.REF88QuantumReduce

#print axioms QuantumNLS.REF88QuantumReduce.curve_data
#print axioms QuantumNLS.REF88QuantumReduce.pair_identity
#print axioms QuantumNLS.REF88QuantumReduce.radial_identity
#print axioms QuantumNLS.REF88QuantumReduce.lam_formula
#print axioms QuantumNLS.REF88QuantumReduce.flow_rot_lamAt
#print axioms QuantumNLS.REF88QuantumReduce.nu_eq_lamAt
