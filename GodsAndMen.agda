module GodsAndMen (V : Set) where

open import Data.Nat

data C : Set where c₀ c₁ c₂ : C
data F : ℕ → Set where s : F 1
data P : ℕ → Set where M : P 1

open import Data.Bool hiding (T)
open import Data.Product
open import Data.Vec
open import FirstOrder (V) (C) (F) (P)

data U : Set where Socrates Zeus Heracles : U

IsMortal : U → Bool
IsMortal Socrates = true
IsMortal Zeus     = false
IsMortal Heracles = true

father-of : U → U
father-of Socrates = Socrates
father-of Zeus     = Zeus
father-of Heracles = Zeus

interpretation : I U
interpretation = constant-mapper , function-mapper , predicate-mapper
 where
  constant-mapper : C → U
  constant-mapper c₀ = Socrates
  constant-mapper c₁ = Zeus
  constant-mapper c₂ = Heracles
  function-mapper : ∀ {n} → F n → (Vec U n → U)
  function-mapper s (u ∷ []) = father-of u
  predicate-mapper : ∀ {n} → P n → (Vec U n → Bool)
  predicate-mapper M (u ∷ []) = IsMortal u
