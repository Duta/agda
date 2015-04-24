open import Data.Nat

module FirstOrder
-- Variables
  (V : Set)
-- Constants
  (C : Set)
-- Functions
  (F : ℕ → Set)
-- Predicates
  (P : ℕ → Set)
 where

open import Data.Bool hiding (T) renaming (Bool to ₂; true to ⊤; false to ⊥)
open import Data.Vec

infixr 0 _$_

--   Terms
data T : Set where
-- Variables are terms
  v : V → T
-- Constants are terms
  c : C → T
-- Functions of arity n, given n terms, are terms
  _$_ : ∀ {n} → F n → Vec T n → T  

--   Atoms
data A : Set where
-- Predicates of arity n, given n terms, are atoms
  _$_ : ∀ {n} → P n → Vec T n → A

{- For example:
postulate f₀ : F 2
postulate c₀ : C
postulate v₀ : V
postulate P₀ : P 1

T₀ : T
T₀ = f₀ $ c c₀ ∷ v v₀ ∷ []

A₀ : A
A₀ = P₀ $ [ v v₀ ]
-}

{- Socrates gon' die
postulate Mortal   : P 1
postulate socrates : C

Mortality : A
Mortality = Mortal $ [ c socrates ]
-}

is-term-ground : T → ₂
is-term-ground (v x) = ⊥
is-term-ground (c x) = ⊤
--is-term-ground (_ $ xs) = foldr (λ _ → ₂) (λ t b → is-term-ground t ∧ b) ⊤ xs
is-term-ground (_ $ xs) = all-ground xs
 where
  all-ground : ∀ {n} → Vec T n → ₂
  all-ground [] = ⊤
  all-ground (t ∷ xs) = is-term-ground t ∧ all-ground xs
