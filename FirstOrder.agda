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

open import Data.Bool hiding (T)
open import Data.Product
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

mutual
  all-ground : ∀ {n} → Vec T n → Bool
  all-ground [] = true
  all-ground (t ∷ xs) = is-term-ground t ∧ all-ground xs
--all-ground = foldr (const Bool) (_∧_ ∘ is-term-ground) true

  is-term-ground : T → Bool
  is-term-ground (v x) = false
  is-term-ground (c x) = true
  is-term-ground (_ $ xs) = all-ground xs

is-atom-ground : A → Bool
is-atom-ground (_ $ xs) = all-ground xs

--   Well-Formed Formulae
data WFF : Set where
  ⊤` ⊥` : WFF
  _` : A → WFF
  ¬` : WFF → WFF
  _∧`_ _∨`_ _→`_ _↔`_ : WFF → WFF → WFF
  ∃`_⇒_ ∀`_⇒_ : V → WFF → WFF

{- Seriously, the dude better be careful
socrates-is-in-trouble : (Human Mortal : P 1) (socrates : C) (x : V) → WFF
socrates-is-in-trouble H M s x = (((H $ [ c s ]) `) ∧` (∀` x ⇒ (((H $ [ v x ]) `) →` ((M $ [ v x ]) `)))) →` ((M $ [ c s ]) `)
-}

-- Interpretations
I : (U : Set) → Set
I U = (C → U)
    × (∀ {n} → F n → Vec T n → (Vec U n → U))
    × (∀ {n} → P n → Vec T n → (Vec U n → Bool))
