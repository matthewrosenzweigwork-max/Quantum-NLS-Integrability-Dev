import NlsGge.GK38.AngleWeightedQuadratic
import NlsGge.GK38.AngleWeightedPaddedMean
import NlsGge.GK38.AngleCompactWeightedSpectralMass

/-! Actual ALL-mode quadratic root square mass on ONE complex potential/input
tube. Actual zero periods and SAME-original nth placement are explicit data,
not an assumed normalized family. The genuine signed limit remains explicit
until its concrete fourteen-file proof chain is accepted. -/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem angleFullGap_common_zero_period_quadratic_square_mass_of_signed_limit38
    (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfam : IsolatingFamily38 (realSlice u) C R)
    (hlimit : ∀ s : P6RealSpace38, s ∈ p5FullRealGapCube38 u →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
        ∀ n : ℤ, (N : ℤ) < |n| →
          ‖p6PaddedJacobian38 n (realSlice u) (p6RealInclude38 s)-
            p6Qstar38 (realSlice u) (p6RealInclude38 s)‖ < ε) :
    ∃ U : Set PotPair, ∃ V : Set Lib.L2Seq, ∃ B : ℝ,
      IsOpen U ∧ IsOpen V ∧ realSlice u ∈ U ∧ U ⊆ gkW ∧
      p6RealInclude38 '' p5FullRealGapCube38 u ⊆ V ∧ 0 < B ∧
      ∀ φ ∈ U, IsolatingFamily38 φ C R ∧ ∀ s ∈ V, ∀ n : ℤ,
        Lib.sigmaOf s n ∈ closedBall (C n) (R n) →
        (∀ m : ℤ, n ≠ m → abelianPeriod38 m φ (p2FullNumerator38 n s)=0) →
        ∃ a : ℤ → ℝ, (∀ m, 0 ≤ a m) ∧
          Summable (fun m : ℤ => a m^2) ∧ (∑' m : ℤ, a m^2) ≤ B ∧
          ∀ m : ℤ, n ≠ m →
            ‖Lib.sigmaOf s m-tauN φ m‖ ≤ ‖gamma2 φ m‖*a m := by
  let K : Set Lib.L2Seq := p6RealInclude38 '' p5FullRealGapCube38 u
  have hK : IsCompact K := (p5FullRealGapCube_isCompact38 u).image p6RealInclude38.continuous
  obtain ⟨Ud,Vd,Bd,hUd,hVd,hbaseD,hUdW,hKVd,hBd,hder⟩ :=
    angleRegularFactor_compact_weighted_spectral_mass38 (realSlice u) (realSlice_mem_gkW u)
      C R hfam K hK
  obtain ⟨D,Um,Vm,hD,hUm,hVm,hbaseM,hUmW,hKVm,hmean⟩ :=
    angleFullGap_common_weighted_cosine_mean_lower_of_signed_limit38 u C R hfam hlimit
  let c : ℝ := Real.pi/(2*D)
  have hc : 0 ≤ c := (div_pos Real.pi_pos (mul_pos (by norm_num) hD)).le
  refine ⟨Ud ∩ Um,Vd ∩ Vm,c^2*Bd+1,hUd.inter hUm,hVd.inter hVm,
    ⟨hbaseD,hbaseM⟩,fun φ hφ => hUdW hφ.1,
    fun s hs => ⟨hKVd hs,hKVm hs⟩,by positivity,?_⟩
  intro φ hφ
  obtain ⟨hfamily,hb⟩ := hder φ hφ.1
  refine ⟨hfamily,?_⟩
  intro s hs n hσ hzero
  obtain ⟨b,hb0,hbs,hbB,hbcut⟩ := hb s hs.1 n hσ
  let a : ℤ → ℝ := fun m => c*b m
  have ha0 (m : ℤ) : 0 ≤ a m := mul_nonneg hc (hb0 m)
  have has : Summable (fun m : ℤ => a m^2) := by
    simpa only [a,mul_pow] using hbs.mul_left (c^2)
  refine ⟨a,ha0,has,?_,?_⟩
  · calc
      (∑' m : ℤ, a m^2) = c^2*∑' m : ℤ,b m^2 := by
        simp_rw [a,mul_pow]
        rw [tsum_mul_left]
      _ ≤ c^2*Bd := mul_le_mul_of_nonneg_left hbB (sq_nonneg c)
      _ ≤ c^2*Bd+1 := le_add_of_nonneg_right zero_le_one
  · intro m hnm
    let k : P2Index38 n := ⟨m,Ne.symm hnm⟩
    have hM := (hmean φ hφ.2 s hs.2 C R hfamily n k hσ).2
    have hq := angleActual_weighted_quadratic_bound38 φ (hUdW hφ.1) C R hfamily
      n m hnm s hσ (hzero m hnm) (b m) D (hb0 m) hD (hbcut m hnm) hM
    exact hq.trans_eq (by dsimp only [a,c]; ring)

end
end NlsGge.GK38
