/- PDE029 PRODUCTION01 (proof development kit; AUTHOR; reviewer proof development pending). Target NlsGge/Atomic/PDE/PDE029.lean.
   Source: defs3 STATEMENTS/PDE.md PDE-029. Head verbatim except the forced binders. Binders: x : ℤ → ℂ and hx : x ∈ h1 (x is the design head free name, made an explicit binder).
   Route: hn_le_Bx38 (GlobalH1_38.lean:44) with Bx x := Real.sqrt (mass x + ham x / (4*pi^2)) (GlobalH1_38.lean:28); definitional unfolding only.
   Binding h1 := seqSobolev38 ((1:ℕ):ℝ) (forced by production lemma types; not defined in defs3 DEFINITIONS/PDE.lean.md). Evidence it is v2's H^1 sequence space: v2 paper/v2.tex:85-86 defines <n>=(1+n^2)^{1/2} and ||z||_{h^r}^2=sum <n>^{2r}|z_n|^2; v2:112-113 defines h^m={z: sum <n>^{2m}|z_n|^2<infty}; v2:88 says field Sobolev norms use the same Fourier convention. Production: japaneseBracket n = sqrt(1+n^2) (PilotInterfaces.lean:106), sobolevModeWeight r n = (japaneseBracket n)^(2r) (Sobolev/SourceEmbeddings.lean:47), seqSobolev38 r = {x | x in weightedSubmodule (sobolevModeWeight r)} (Birkhoff/BirkhoffInput38.lean:33), i.e. h^r. With r = 1 this is h^1. -/
import Mathlib
import NlsGge.NLS38.GlobalH1_38

set_option autoImplicit false
open NlsGge.NLS38 NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.PDE
noncomputable section

abbrev h1 : Set (ℤ → ℂ) := seqSobolev38 ((1 : ℕ) : ℝ)

theorem h1_le_coercive_energy (x : ℤ → ℂ) (hx : x ∈ h1) :
    hn 1 x ≤ Real.sqrt (mass x + ham x / (4 * Real.pi ^ 2)) :=
  hn_le_Bx38 hx

end
end NlsGge.ThirdConsultation.PDE
