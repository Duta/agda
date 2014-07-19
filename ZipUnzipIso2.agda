module ZipUnzipIso2 where

open import Data.Nat
open import Data.List hiding (zip)
open import Relation.Binary.PropositionalEquality

open import Preamble

len : {A : Set} → List A → ℕ
len [] = zero
len (x ∷ xs) = suc (len xs)

suc-inj : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-inj {zero} {zero} p = refl
suc-inj {zero} {suc n} ()
suc-inj {suc m} {zero} ()
suc-inj {suc m} {suc .m} refl = refl

{-
rebuild : {A B : Set} {C : A × B → Set}
        → (d : Σ {A × B} C)
        → (let π'₁₁ = π₁ (π₁ d))
        → (let π'₁₂ = π₂ (π₁ d))
        → (let π'₂  = π₂ d)
        → (π'₁₁ , π'₁₂) , π'₂ ≡ d
rebuild ((π'₁₁ , π'₁₂) , π'₂) = refl
-}

{- Agda doesn't think this terminates
zip : ∀ {A B} → (Σ \(p : List A × List B) → len (π₁ p) ≡ len (π₂ p)) → List (A × B)
zip (([] , []) , p) = []
zip (([] , (y ∷ ys)) , ())
zip (((x ∷ xs) , []) , ())
zip (((x ∷ xs) , (y ∷ ys)) , p) = x , y ∷ zip ((xs , ys) , suc-inj p)
-}

zip' : ∀ {A B} → (p : List A × List B) → len (π₁ p) ≡ len (π₂ p) → List (A × B)
zip' ([] , []) p = []
zip' ([] , (y ∷ ys)) ()
zip' ((x ∷ xs) , []) ()
zip' ((x ∷ xs) , (y ∷ ys)) p = x , y ∷ zip' (xs , ys) (suc-inj p)

zip : ∀ {A B} → (Σ \(p : List A × List B) → len (π₁ p) ≡ len (π₂ p)) → List (A × B)
zip ((xs , ys) , p) = zip' (xs , ys) p

unzip : ∀ {A B} → List (A × B) → (Σ \(p : List A × List B) → len (π₁ p) ≡ len (π₂ p))
unzip [] = ([] , []) , refl -- [] , []
unzip (x , y ∷ xs) =   ( (x ∷ π₁ (π₁ (unzip xs)))
                       , (y ∷ π₂ (π₁ (unzip xs))))
                     , cong suc (π₂ (unzip xs))

un-zip-iso : ∀ {A B} → (Σ \(p : List A × List B) → len (π₁ p) ≡ len (π₂ p)) ≅ List (A × B)
un-zip-iso = zip , (unzip , (l2r , r2l))
 where
  l2r : ∀ {A B}
      → (xs : Σ \(p : List A × List B) → len (π₁ p) ≡ len (π₂ p))
      → unzip (zip xs) ≡ xs
  l2r (([] , []) , refl) = refl
  l2r (([] , (x ∷ ys)) , ())
  l2r (((x ∷ xs) , []) , ())
  l2r (((x ∷ xs) , (y ∷ ys)) , p) = goal
   where
    IH : unzip (zip ((xs , ys) , suc-inj p)) ≡ (xs , ys) , suc-inj p
    IH = l2r ((xs , ys) , suc-inj p)
    xs' = π₁ (π₁ (unzip (zip' (xs , ys) (suc-inj p))))
    ys' = π₂ (π₁ (unzip (zip' (xs , ys) (suc-inj p))))
    p' = cong suc (π₂ (unzip (zip' (xs , ys) (suc-inj p))))
    goal : ((x ∷ xs') , (y ∷ ys')) , p' ≡ ((x ∷ xs) , (y ∷ ys)) , p
    goal = {!!} {- trans
             (trans
               (cong (λ xs'' → ((x ∷ xs'') , (y ∷ ys'))  , p')  (cong (λ xs'' → π₁ (π₁ xs''))       IH))
               (cong (λ ys'' → ((x ∷ xs)   , (y ∷ ys'')) , p')  (cong (λ xs'' → π₂ (π₁ xs''))       IH)))
             (trans
               (cong (λ p''  → ((x ∷ xs)   , (y ∷ ys))   , p'') (cong (λ xs'' → cong suc (π₂ xs'')) IH))
               {!!}) -- This line should convert (cong suc (suc-inj p)) → p (if that's not done automatically. If it's just refl, remove it)
             -}
  r2l : ∀ {A B}
      → (xs : List (A × B))
      → zip (unzip xs) ≡ xs
  r2l [] = refl
  r2l {A} {B} (x₁ , x₂ ∷ xs) = cong (λ xs' → x₁ , x₂ ∷ xs') (goal {A} {B})
   where
    IH : zip (unzip xs) ≡ xs
    IH = r2l xs
    xs₁ = π₁ (π₁ (unzip xs))
    ys₁ = π₂ (π₁ (unzip xs))
    p₁  = π₂ (unzip xs)
    r2l₁ : {A B : Set} →  (π₁ (π₁ (unzip xs)) , π₂ (π₁ (unzip xs))) , π₂ (unzip xs) ≡ unzip xs
    r2l₁ = {!rebuild {List A} {List B} {λ p → len (π₁ p) ≡ len (π₂ p)} (unzip xs)!}
    goal : {A B : Set} → zip ((xs₁ , ys₁) , p₁)
           ≡ xs
    goal {A} {B} = trans (cong zip (r2l₁ {A} {B})) IH

