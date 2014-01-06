module HoTT where

{- Judgemental Equality -}
data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

sym : {X : Set} {x y : X} →
      x ≡ y → y ≡ x
sym refl = refl

trans : {X : Set} {x y z : X} →
        x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

ap : {X Y : Set} {x y : X} →
     (f : X → Y) → x ≡ y → f x ≡ f y
ap f refl = refl

{- Dependent Pair Types -}
data Σ {A : Set} (B : A → Set) : Set where
  _,_ : (x : A) (y : B x) → Σ {A} B

π₁ : {A : Set} {B : A → Set} →
     (Σ \(x : A) → B x) → A
π₁ (x , y) = x

π₂ : {A : Set} {B : A → Set} →
     (p : Σ \(x : A) → B x) → B (π₁ p)
π₂ (x , y) = y

-- Recursor
rec_deppair : {A C : Set} {B : A → Set} →
              ({x : A} → B x → C) → Σ B → C
rec_deppair g (a , b) = g {a} b

-- Induction
ind_deppair : {A : Set} {B : A → Set} {C : Σ B → Set} →
              ({a : A} {b : B a} → C (a , b)) → (p : Σ B) → C p
ind_deppair g (a , b) = g {a} {b}

{- Product Types -}
_×_ : Set → Set → Set
X × Y = Σ \(x : X) → Y

{- Coproduct Types -}
data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

-- Recursor
rec_coprod : {A B C : Set} →
             (A → C) → (B → C) → (A + B) → C
rec_coprod g₀ g₁ (inl a) = g₀ a
rec_coprod g₀ g₁ (inr b) = g₁ b

-- Induction
ind_coprod : {A B : Set} {C : A + B → Set} {x : A + B} →
             ({a : A} → C (inl a)) → ({b : B} → C (inr b)) → C x
ind_coprod {A} {B} {C} {inl a} g₀ g₁ = g₀
ind_coprod {A} {B} {C} {inr b} g₀ g₁ = g₁

{- Empty/Unit -}
data Empty : Set where

data Unit : Set where
  * : Unit

-- Recursors
rec_empty : {C : Set} →
            Empty → C
rec_empty ()

rec_unit : {C : Set} →
           C → Unit
rec_unit c = *

{- Booleans -}
data Bool : Set where
  true  : Bool
  false : Bool

-- Recursor
rec_bool : {C : Set} →
           Bool → C → C → C
rec_bool true  c₀ c₁ = c₀
rec_bool false c₀ c₁ = c₁

-- Induction
ind_bool : {C : Bool → Set} {x : Bool} →
           C true → C false → C x
ind_bool {C} {true}  c₀ c₁ = c₀
ind_bool {C} {false} c₀ c₁ = c₁

-- Example Functions
if_then_else_ : {C : Set} →
                Bool → C → C → C
if b then c₀ else c₁ = rec_bool b c₀ c₁

not : Bool → Bool
not b = rec_bool b false true

{- Natural Numbers -}
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Recursor
rec_nat : {C : Set} →
          C → (ℕ → C → C) → ℕ → C
rec_nat c₀ cs zero = c₀
rec_nat c₀ cs (succ n) = cs n (rec_nat c₀ cs n)

-- Induction
ind_nat : {C : ℕ → Set} {n : ℕ} →
          C zero → ((n : ℕ) → C n → C (succ n)) → C n
ind_nat {C} {zero} c₀ cs = c₀
ind_nat {C} {succ n} c₀ cs = cs n (ind c₀ nat cs)

-- Example functions
double = rec_nat zero (λ n → λ y → succ (succ y))
add = rec_nat (λ n → n) (λ n → λ g → λ m → succ (g m))

assoc_add : ∀ i j k → add i (add j k) ≡ add (add i j) k
assoc_add zero j k = refl
assoc_add (succ i) j k = ap succ IH
 where
  IH : add i (add j k) ≡ add (add i j) k
  IH = assoc_add i j k

{- Fins -}
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (succ n)
  succ : {n : ℕ} → Fin n → Fin (succ n)

{- Isomorphisms -}
_≅_ : Set → Set → Set
A ≅ B = Σ \(f : A → B) →
        Σ \(g : B → A) →
        ((x : A) → g (f x) ≡ x) ×
        ((y : B) → f (g y) ≡ y)
