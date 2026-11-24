module Cubical.SmithHomology.SmithHom where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.Matrix
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.Group.MorphismProperties

open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.FinData
open import Cubical.Data.Sigma

open import Cubical.SmithHomology.Utils

-- open Coefficient ℤCommRing

module SmithHomology {n m k : ℕ} (∂ₙ₊₁ : AbGroupHom ℤ[Fin n ] ℤ[Fin m ])
                                 (∂ₙ : AbGroupHom ℤ[Fin m ] ℤ[Fin k ])
                                 (∂∂ : compGroupHom ∂ₙ₊₁ ∂ₙ ≡ trivGroupHom) where

  Homology : AbGroupIso ((kerAbGroup ∂ₙ) /Im {!!}) (smithGroup ? ?)
  Homology = {!!}



       












