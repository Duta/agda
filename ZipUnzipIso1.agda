module ZipUnzipIso1 where

open import Data.Nat
open import Data.Vec hiding (zip; unzip)
open import Relation.Binary.PropositionalEquality

open import Preamble

zip : ∀ {A B n} → Vec A n × Vec B n → Vec (A × B) n
zip ([] , []) = []
zip ((x ∷ xs) , (y ∷ ys)) = (x , y) ∷ zip (xs , ys)

unzip : ∀ {A B n} → Vec (A × B) n → Vec A n × Vec B n
unzip [] = [] , []
unzip (x₁ , x₂ ∷ xs) = (x₁ ∷ π₁ (unzip xs)) , (x₂ ∷ π₂ (unzip xs))

unzip-πs : ∀ {A B n} → (xs : Vec (A × B) n) → π₁ (unzip xs) , π₂ (unzip xs) ≡ unzip xs
unzip-πs [] = refl
unzip-πs (x₁ , x₂ ∷ xs) = refl

un-zip-iso : ∀ {A B n} → (Vec A n × Vec B n) ≅ Vec (A × B) n
un-zip-iso = zip , (unzip , (l2r , r2l))
 where
  l2r : ∀ {A B n} → (x : Vec A n × Vec B n) → unzip (zip x) ≡ x
  l2r ([] , []) = refl
  l2r ((x ∷ xs) , (y ∷ ys)) = trans
                                (cong (λ xs₁ → (x ∷ xs₁) , (y ∷ π₂ (unzip (zip (xs , ys))))) (cong π₁ IH))
                                (cong (λ ys₁ → (x ∷ xs)  , (y ∷ ys₁))                        (cong π₂ IH))
   where
    IH : unzip (zip (xs , ys)) ≡ xs , ys
    IH = l2r (xs , ys)
  r2l : ∀ {A B n} → (xs : Vec (A × B) n) → zip (unzip xs) ≡ xs
  r2l [] = refl
  r2l (x₁ , x₂ ∷ xs) = cong (λ xs' → x₁ , x₂ ∷ xs') (trans (cong zip (unzip-πs xs)) IH)
   where
    IH : zip (unzip xs) ≡ xs
    IH = r2l xs
