{-# OPTIONS --lossy-unification #-}

module Cubical.SmithHomology.Utils where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Matrix
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup renaming (ℤFinGenerator to e)
open import Cubical.Algebra.AbGroup.Instances.DirectProduct
open import Cubical.Algebra.AbGroup.Instances.IntMod
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.Ring
open import Cubical.Algebra.IntegerMatrix.Smith
open import Cubical.Algebra.Semiring.BigOps

open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Nat
open import Cubical.Data.Int
open import Cubical.Data.Int.Properties
open import Cubical.Data.List
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Sigma
open import Cubical.Data.Nat.Order.Inductive


private variable
  ℓ : Level 

module _ {G : Group ℓ} {H : AbGroup ℓ} (Φ : GroupHom G (AbGroup→Group H)) where
  coker : AbGroup ℓ
  coker = H /Im Φ

module _ {G : AbGroup ℓ} {H : AbGroup ℓ} (Φ : AbGroupHom G H) where
  kerAbGroup : AbGroup ℓ
  kerAbGroup = Group→AbGroup (Subgroup→Group (AbGroup→Group G) (kerSubgroup Φ))
                             λ {(x , p) (y , q) →
                                Σ≡Prop (λ _ → isPropIsInKer Φ _ ) (AbGroupStr.+Comm (G .snd) x y)}

open Sum 

smithGroup : List ℤ → ℕ → AbGroup ℓ-zero
smithGroup [] k = ℤ[Fin k ]
smithGroup (x ∷ l) k = AbDirProd (ℤAbGroup/ abs x) (smithGroup l k)


toMatrix : {n : ℕ} → (A : fst ℤ[Fin n ]) → FinMatrix ℤ n 1
toMatrix {n = n} A i zero = A (FinData→Fin n i) 

fromMatrix : {n : ℕ} → (A : FinMatrix ℤ n 1) → fst ℤ[Fin n ] 
fromMatrix {n = n} A i = A (Fin→FinData n i) zero

ℤRing : Ring ℓ-zero
ℤRing = CommRing→Ring ℤCommRing

FinMat→Fun : {n m : ℕ} → (FinMatrix ℤ m n) → fst ℤ[Fin n ] → fst ℤ[Fin m ]
FinMat→Fun {m = m} A X i = mulFinMatrix ℤRing A (toMatrix X) (Fin→FinData m i) zero     

inducedAbHom : {n m : ℕ} → FinMatrix ℤ m n → AbGroupHom ℤ[Fin n ] ℤ[Fin m ]
inducedAbHom {n = n} {m = m} A = (FinMat→Fun A) , isGH
  where
  
    isGH : IsGroupHom (AbGroup→Group ℤ[Fin n ] .snd) (FinMat→Fun A) (AbGroup→Group ℤ[Fin m ] .snd)
    isGH = makeIsGroupHom λ x y → cong fromMatrix (mulFinMatrixrDistrAddFinMatrix ℤRing A (toMatrix x) (toMatrix y))  

Fun→FinMat : {n m : ℕ} → (fst ℤ[Fin n ] → fst ℤ[Fin m ]) → FinMatrix ℤ m n
Fun→FinMat {n = n} {m = m} f i j = f (e (FinData→Fin n j)) (FinData→Fin m i)

inducedMatrix : {n m : ℕ}  → AbGroupHom ℤ[Fin n ] ℤ[Fin m ] → FinMatrix ℤ m n
inducedMatrix f = Fun→FinMat (f .fst)

maSuperEquiv : {n m : ℕ} → (FinMatrix ℤ m n) ≃ (AbGroupHom ℤ[Fin n ] ℤ[Fin m ])
maSuperEquiv {n = n} {m = m} = isoToEquiv (iso inducedAbHom inducedMatrix (sec n m) ret)
  where

    FinSetVec : (A : Type ℓ) → (n : ℕ) → Type _ 
    FinSetVec A n =  Σ ℕ (λ n₁ → n₁ <ᵗ n) → A

    FinSetVec≃FinVec : {n : ℕ} → {A : Type ℓ} → FinSetVec A n ≃ FinVec A n
    FinSetVec≃FinVec = {!!}

    FinSetVec→FinVec : {n : ℕ} → {A : Type ℓ} → FinSetVec A n → FinVec A n
    FinSetVec→FinVec = FinSetVec≃FinVec .fst

    sec : (n' m' : ℕ ) → section (inducedAbHom {n'} {m'}) inducedMatrix
    sec n m f = agreeOnℤFinGenerator→≡ (λ i → funExt (λ j  → {!∑Mulr1 _ m (FinSetVec→FinVec (fst f (e i))) (Fin→FinData m j) !}))
          
    ret : retract inducedAbHom inducedMatrix
    ret = {!!}
    
--  ∑ (ℤ , _S.snd_275)
--       (λ i₁ →
--          (_S.snd_275 Cubical.Algebra.Semiring.Base.SemiringStr.·
--           FinSetVec→FinVec (fst f (e i)) i₁)
--          (KroneckerDelta.δ (ℤ , _S.snd_275) i₁ (Fin→FinData m j)))
--       ≡ FinSetVec→FinVec (fst f (e i)) (Fin→FinData m j)

-- foldrFin Cubical.Data.Int._+_ (pos 0)
--       (λ j₁ →
--          f .fst
--          (λ s → e (FinData→Fin n j₁) s | fst (FinData→Fin n j₁) ≟ᵗ fst s)
--          (FinData→Fin m (Fin→FinData m j))
--          Cubical.Data.Int.·
--          (e i (FinData→Fin n j₁) | fst i ≟ᵗ fst (FinData→Fin n j₁)))
--       ≡ fst f (λ s → e i s | fst i ≟ᵗ fst s) j

-- FinData≃SumFin 

-- lemma : {m n : ℕ} {A : FinMatrix ℤ m n} (S : Smith A) →
--    AbGroupIso (coker {H = ℤ[Fin m ]} (inducedAbHom A)) (smithGroup (isSmithNormal.divs (Smith.isnormal S) .fst) (isSmithNormal.rowNull (Smith.isnormal S)))
-- lemma {m = m} {A = A} S = compGroupIso iso1 {!!}
--   where


--   iso1 : AbGroupIso (coker (inducedAbHom A)) (coker {H = ℤ[Fin m ]} (inducedAbHom (Coefficient.Sim.result (Smith.sim S))))
--   iso1 = Hom/ImIso {!!} {!!} {!!} {!!} {!!}
