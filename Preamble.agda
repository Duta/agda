module Preamble where

open import Level
open import Relation.Binary.PropositionalEquality

data Σ {i j} {A : Set i} (B : A → Set j) : Set (i ⊔ j) where
  _,_ : (x : A) → B x → Σ {i} {j} {A} B

π₁ : {A : Set} {B : A → Set} →
     (Σ \(x : A) → B x) → A
π₁ (x , y) = x

π₂ : {A : Set} {B : A → Set} →
     (p : Σ \(x : A) → B x) → B (π₁ p)
π₂ (x , y) = y

_×_ : Set → Set → Set
X × Y = Σ \(x : X) → Y

_≅_ : Set → Set → Set
A ≅ B = Σ \(f : A → B) →
        Σ \(g : B → A) →
        ((x : A) → g (f x) ≡ x) ×
        ((y : B) → f (g y) ≡ y)
