import Mathlib
import NlsGge.Atomic.G3.G3026
import NlsGge.ThirdConsultation.KO.Basic
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.DirichletRealGapIndex
import NlsGge.GK38.TauGamma
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.Lib.EntireProductsC34b

/- G5-008 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5008.lean.
   Head byte-identical to design STATEMENTS/G5.md:219 block (root/gpt6pro_followup8; rounds 9/10 do not touch G5-008);
   `finiteGap` is NlsGge.ThirdConsultation.finiteGap (opened by name, head text unchanged), as in landed G5004/G5005.
   Route: finiteGap gives finitely many open gaps; outside them lamPlus = lamMinus (lamPlus_real), the Dirichlet
   eigenvalue lies in the closed gap (gkMu_mem_gap38 = G1-057 first conjunct) and tauN = (lamPlus+lamMinus)/2
   (tauN_value38), so gk151BetaMass38 vanishes outside a finite set.  The landed G3_026 supplies the local
   inverse-distance bound ||offDiagonalBeta n m phi|| <= C ||mass m|| c3w n m and HasSum over Z to betaSum n phi
   at phi = realSlice u; HasSum with finitely supported terms gives a finite sum; c3w n m <= 2/|n| for |n| > 2 max|S|.
   l2 follows from the C/|n| tail (cofinite comparison with c3w 0 squared). No Armstrong direct import. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.ThirdConsultation (finiteGap)

namespace NlsGge.GKDefinitionDesign
namespace G5008Aux
noncomputable section

theorem mass_eq_zero (u : PhysicalL2) (n : ℤ)
    (h : actualGapLowerAllE02_38 u n = actualGapUpperAllE02_38 u n) :
    gk151BetaMass38 (realSlice u) n = 0 := by
  obtain ⟨hp, hm⟩ := lamPlus_real u n
  have hmu := muSeq_eq_gkMu38 u n
  have hg := gkMu_mem_gap38 u n
  have hmu_eq : gkMu u n = actualGapUpperAllE02_38 u n := by
    have h1 := hg.1
    have h2 := hg.2
    linarith
  have htau := tauN_value38 (realSlice u) (realSlice_mem_gkW u) n
  have h1 : lamPlus (realSlice u) n - lamMinus (realSlice u) n = 0 := by
    rw [hp, hm, h]
    ring
  have h2 : muSeq (realSlice u) n - tauN (realSlice u) n = 0 := by
    rw [htau, hmu, hmu_eq, hp, hm, h]
    ring
  unfold gk151BetaMass38
  rw [h1, h2]
  simp

theorem norm_betaSum_le (u : PhysicalL2) (hu : finiteGap u) :
    ∃ (S : Finset ℤ) (C : ℝ), 0 < C ∧ ∀ n : ℤ,
      ‖betaSum n (realSlice u)‖ ≤
        ∑ m ∈ S, C * ‖gk151BetaMass38 (realSlice u) m‖ * Lib.c3w n m := by
  obtain ⟨U, hUo, hUr, hUsub, hloc⟩ := G3_026
  obtain ⟨V, C, M, hVo, h0V, hVU, hC, hM, hV⟩ := hloc (realSlice u) (hUr ⟨u, rfl⟩)
  obtain ⟨hs, hspec, hb, hrow⟩ := hV (realSlice u) h0V
  have hfin : {m : ℤ | gk151BetaMass38 (realSlice u) m ≠ 0}.Finite :=
    hu.subset (fun m hm h => hm (mass_eq_zero u m h))
  refine ⟨hfin.toFinset, C, hC, fun n => ?_⟩
  obtain ⟨-, hH, -, -⟩ := hrow n
  have hz : ∀ m ∉ hfin.toFinset, offDiagonalBeta n m (realSlice u) = 0 := by
    intro m hm
    have h0 : gk151BetaMass38 (realSlice u) m = 0 := by
      by_contra h
      exact hm (hfin.mem_toFinset.mpr h)
    have h1 := hb n m
    rw [h0, norm_zero, mul_zero, zero_mul] at h1
    exact norm_le_zero_iff.mp h1
  have heq : betaSum n (realSlice u) =
      ∑ m ∈ hfin.toFinset, offDiagonalBeta n m (realSlice u) :=
    hH.unique (hasSum_sum_of_ne_finset_zero hz)
  rw [heq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => hb n m)

theorem c3w_le (n m : ℤ) (R : ℕ) (hm : |(m : ℝ)| ≤ R) (hn : 2 * R < n.natAbs) :
    Lib.c3w n m ≤ 2 / |(n : ℝ)| := by
  have hn1 : (2 * R : ℝ) < |(n : ℝ)| := by
    have h1 : ((2 * R : ℕ) : ℝ) < (n.natAbs : ℝ) := by exact_mod_cast hn
    rw [Nat.cast_natAbs, Int.cast_abs] at h1
    simpa using h1
  have hpos : 0 < |(n : ℝ)| / 2 := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  have hdist : |(n : ℝ)| / 2 ≤ |(m : ℝ) - n| := by
    have h1 := abs_sub_abs_le_abs_sub (n : ℝ) (m : ℝ)
    rw [abs_sub_comm (n : ℝ) (m : ℝ)] at h1
    linarith
  unfold Lib.c3w
  calc 1 / |(m : ℝ) - n| ≤ 1 / (|(n : ℝ)| / 2) :=
        one_div_le_one_div_of_le hpos hdist
    _ = 2 / |(n : ℝ)| := by
        field_simp

end
end G5008Aux

noncomputable section

theorem G5008 (u : PhysicalL2) (hu : finiteGap u) :
  Memℓp (fun n : ℤ => betaSum n (realSlice u)) 2 ∧
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℤ, N < n.natAbs →
    ‖betaSum n (realSlice u)‖ ≤ C / |(n : ℝ)| := by
  obtain ⟨S, C, hC, hle⟩ := G5008Aux.norm_betaSum_le u hu
  set K : ℝ := ∑ m ∈ S, C * ‖gk151BetaMass38 (realSlice u) m‖ with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun m _ => mul_nonneg hC.le (norm_nonneg _)
  set R : ℕ := S.sup Int.natAbs with hR
  have hdecay : ∀ n : ℤ, 2 * R < n.natAbs →
      ‖betaSum n (realSlice u)‖ ≤ (2 * K + 1) / |(n : ℝ)| := by
    intro n hn
    have hnpos : 0 < |(n : ℝ)| := by
      have : (0 : ℝ) < (n.natAbs : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hn)
      rwa [Nat.cast_natAbs, Int.cast_abs] at this
      
    have hterm : ∀ m ∈ S, C * ‖gk151BetaMass38 (realSlice u) m‖ * Lib.c3w n m ≤
        C * ‖gk151BetaMass38 (realSlice u) m‖ * (2 / |(n : ℝ)|) := by
      intro m hm
      have hmR : |(m : ℝ)| ≤ R := by
        have h1 : m.natAbs ≤ R := Finset.le_sup (f := Int.natAbs) hm
        have h2 : (m.natAbs : ℝ) ≤ R := by exact_mod_cast h1
        rwa [Nat.cast_natAbs, Int.cast_abs] at h2
      exact mul_le_mul_of_nonneg_left (G5008Aux.c3w_le n m R hmR hn)
        (mul_nonneg hC.le (norm_nonneg _))
    calc ‖betaSum n (realSlice u)‖
        ≤ ∑ m ∈ S, C * ‖gk151BetaMass38 (realSlice u) m‖ * Lib.c3w n m := hle n
      _ ≤ ∑ m ∈ S, C * ‖gk151BetaMass38 (realSlice u) m‖ * (2 / |(n : ℝ)|) :=
          Finset.sum_le_sum hterm
      _ = K * (2 / |(n : ℝ)|) := by rw [← Finset.sum_mul]
      _ ≤ (2 * K + 1) / |(n : ℝ)| := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hnpos]
          nlinarith
  refine ⟨?_, 2 * K + 1, by positivity, 2 * R, hdecay⟩
  have hev : ∀ᶠ n : ℤ in cofinite, 2 * R < n.natAbs := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_Icc (-(2 * R : ℤ)) (2 * R)).subset (fun n hn => ?_)
    have hn' : n.natAbs ≤ 2 * R := not_lt.mp hn
    rw [Set.mem_Icc]
    constructor <;> omega
  have hsq : Summable (fun n : ℤ => ‖betaSum n (realSlice u)‖ ^ 2) := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n : ℤ => (2 * K + 1) ^ 2 * Lib.c3w 0 n ^ 2)
      ((Lib.summable_c3w_sq 0).mul_left _) ?_
    filter_upwards [hev] with n hn
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hdecay n hn) 2
    refine h1.trans (le_of_eq ?_)
    unfold Lib.c3w
    simp only [Int.cast_zero, sub_zero]
    ring
  rw [memℓp_gen_iff (by simp)]
  simpa using hsq

end
end NlsGge.GKDefinitionDesign
