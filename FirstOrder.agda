open import Data.Nat

module FirstOrder (V : Set) (C : Set) (F : ℕ → Set) (P : ℕ → Set) where

open import Data.Vec

infixr 0 _$_

data T : Set where
  v : V → T
  c : C → T
  _$_ : ∀ {n} → F n → Vec T n → T  

data A : Set where
  _$_ : ∀ {n} → P n → Vec T n → A

postulate f₀ : F 2
postulate c₀ : C
postulate v₀ : V
postulate P₀ : P 1

T₀ : T
T₀ = f₀ $ c c₀ ∷ v v₀ ∷ []

A₀ : A
A₀ = P₀ $ [ v v₀ ]
