import Mathlib
import NlsGge.Atomic.G6.G6038Host

                                                                                                                          
                                                                                        
                                                                                                          
                                                                                                               
                                                                     
                                                                                                         
                                                            
set_option autoImplicit false

namespace NlsGge.GKDefinitionDesign
noncomputable section

def flipComplexCoordinate (n : ℤ) (x : ComplexDiagonalSpace) : ComplexDiagonalSpace :=
  x - lp.single 2 n (2 * x n)

def CoordinatewiseEvenOn (f : ComplexDiagonalSpace → ℂ)
    (S : Set ℤ) (U : Set ComplexDiagonalSpace) : Prop :=
  ∀ x ∈ U, ∀ n ∈ S, f (flipComplexCoordinate n x) = f x

def parametricActionDescent
    {P : Type*} (f : P × ComplexDiagonalSpace → ℂ)
    (q : P × ComplexActionSpace) : ℂ :=
  f (q.1, complexActionRoot q.2)

def complexHeadLift (F : Finset ℤ) (p : F → ℂ) : ComplexDiagonalSpace :=
  ∑ n : F, lp.single 2 (n : ℤ) (p n)

def complexTailProjection (F : Finset ℤ) (x : ComplexDiagonalSpace) :
    ComplexDiagonalSpace :=
  x - ∑ n ∈ F, lp.single 2 n (x n)

end
end NlsGge.GKDefinitionDesign
