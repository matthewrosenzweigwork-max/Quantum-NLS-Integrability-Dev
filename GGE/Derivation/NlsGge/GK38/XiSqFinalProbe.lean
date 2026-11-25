import NlsGge.GK38.XiSqCanonical
import NlsGge.GK38.XiSqExistencePositiveProbe

set_option autoImplicit false
open NlsGge.Pilot
open Set Filter Topology
open NlsGge.GK38
namespace A5FinalFixture
noncomputable section

theorem all_contracts : XiSqExistence38 ∧ XiSqIdentity38 ∧ OpenGapNonempty38 ∧
    XiSqNearOne38 ∧ XiSqrtL2NearOne38 ∧ XiSqrtAnalytic38 ∧ XiSqRealPositive38 ∧ ActionXiIdentity38 :=
  a5AllContracts38

theorem full_near_one : ∀ g : ℤ → PotPair → ℂ, (∀ n : ℤ, XiSqSpec38 n (g n)) →
    ∀ φ₀ ∈ gkW, ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧
      ∃ N : ℕ, ∀ φ ∈ U, ∀ n : ℤ, N < n.natAbs →
        g n φ ∈ Complex.slitPlane ∧ ‖g n φ-1‖ < (1/2:ℝ) := xiSqNearOne38_proved

theorem full_sqrt_l2 : ∀ g : ℤ → PotPair → ℂ, (∀ n : ℤ, XiSqSpec38 n (g n)) →
    ∀ φ₀ ∈ gkW, IsLocUnifL2Seq (fun φ n => Complex.sqrt (g n φ)-1) φ₀ :=
  xiSqrtL2NearOne38_proved

theorem canonical_spec (n : ℤ) : XiSqSpec38 n (xiSq38 n) := xiSq38_spec n

theorem canonical_negative_amplitude (n : ℤ) :
    xiSq38 n (realSlice ((-2:ℝ) • a5OpenWitness38 n))=1 :=
  A5ExistencePositiveFixture.candidate_actual_plane_one n (xiSq38 n) (xiSq38_spec n)
    (-2) (by norm_num)

/-- Explicit reflected negative active label, with negative real amplitude. -/
theorem negative_active_label :
    xiSq38 (-3) (realSlice ((-2:ℝ) • a5OpenWitness38 (-3)))=1 :=
  canonical_negative_amplitude (-3)

/-- Actual collapsed normalization at EVERY signed free label. -/
theorem canonical_free_one (n : ℤ) : xiSq38 n (0:PotPair)=1 :=
  A5ExistencePositiveFixture.candidate_free_one n (xiSq38 n) (xiSq38_spec n)

theorem canonical_sqrt_free_one (n : ℤ) : xiN38 n (0:PotPair)=1 := by
  simp only [xiN38,canonical_free_one,Complex.sqrt,Complex.one_cpow]

theorem all_real_collapsed_allowed (u : PhysicalL2) (n : ℤ) :
    (xiN38 n (realSlice u)).im=0 ∧ 1≤(xiN38 n (realSlice u)).re := xiN38_real_ge_one u n

theorem canonical_full_error_l2 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    IsLocUnifL2Seq (fun φ n => xiSq38 n φ-1) φ₀ := a5XiSqError_l2_38 xiSq38 xiSq38_spec φ₀ hφ₀

end
end A5FinalFixture
