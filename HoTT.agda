module HoTT where

id : {X : Set} →
     X → X
id x = x

{- Universe Levels -}

postulate
  Level  : Set
  zero-l : Level
  succ-l : Level → Level
  max-l  : Level → Level → Level

{-# BUILTIN LEVEL     Level  #-}
{-# BUILTIN LEVELZERO zero-l #-}
{-# BUILTIN LEVELSUC  succ-l #-}
{-# BUILTIN LEVELMAX  max-l  #-}

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
-- Simple definition
-- data Σ {A : Set} (B : A → Set) : Set where
--   _,_ : (x : A) → B x → Σ {A} B

-- Universe polymorphic definition
data Σ {i j : Level} {A : Set i} (B : A → Set j) : Set (max-l i j) where
  _,_ : (x : A) → B x → Σ {i} {j} {A} B

π₁ : {i j : Level} {A : Set i} {B : A → Set j} →
     (Σ \(x : A) → B x) → A
π₁ (x , y) = x

π₂ : {i j : Level} {A : Set i} {B : A → Set j} →
     (p : Σ \(x : A) → B x) → B (π₁ p)
π₂ (x , y) = y

-- Recursor
rec-deppair : {A C : Set} {B : A → Set} →
              ({x : A} → B x → C) → Σ B → C
rec-deppair g (a , b) = g {a} b

-- Induction
ind-deppair : {A : Set} {B : A → Set} {C : Σ B → Set} →
              ({a : A} {b : B a} → C (a , b)) → (p : Σ B) → C p
ind-deppair g (a , b) = g {a} {b}

{- Product Types -}
_×_ : Set → Set → Set
X × Y = Σ \(x : X) → Y

-- Curry/Uncurry
curry : {A B C : Set} →
        (A × B → C) → A → B → C
curry f x y = f (x , y)

uncurry : {A B C : Set} →
          (A → B → C) → A × B → C
uncurry f (x , y) = f x y

{- Coproduct Types -}
data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

-- Recursor
rec-coprod : {A B C : Set} →
             (A → C) → (B → C) → (A + B) → C
rec-coprod g₀ g₁ (inl a) = g₀ a
rec-coprod g₀ g₁ (inr b) = g₁ b

-- Induction
ind-coprod : {A B : Set} {C : A + B → Set} {x : A + B} →
             ({a : A} → C (inl a)) → ({b : B} → C (inr b)) → C x
ind-coprod {A} {B} {C} {inl a} g₀ g₁ = g₀
ind-coprod {A} {B} {C} {inr b} g₀ g₁ = g₁

{- Empty/Unit -}
data Empty : Set where

data Unit : Set where
  * : Unit

-- Recursors
rec-empty : {C : Set} →
            Empty → C
rec-empty ()

rec-unit : {C : Set} →
           C → Unit
rec-unit c = *

{- Booleans -}
data Bool : Set where
  true-b  : Bool
  false-b : Bool

-- Recursor
rec-b : {C : Set} →
           Bool → C → C → C
rec-b true-b  c₀ c₁ = c₀
rec-b false-b c₀ c₁ = c₁

-- Induction
ind-b : {C : Bool → Set} {x : Bool} →
           C true-b → C false-b → C x
ind-b {C} {true-b}  c₀ c₁ = c₀
ind-b {C} {false-b} c₀ c₁ = c₁

-- Example Functions
if_then_else_ : {C : Set} →
                Bool → C → C → C
if b then c₀ else c₁ = rec-b b c₀ c₁

not-b : Bool → Bool
not-b b = rec-b b false-b true-b

{- Natural Numbers -}
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Recursor
rec-nat : {C : Set} →
          C → (ℕ → C → C) → ℕ → C
rec-nat c₀ cs zero = c₀
rec-nat c₀ cs (succ n) = cs n (rec-nat c₀ cs n)

-- Induction
ind-nat : {C : ℕ → Set} {n : ℕ} →
          C zero → ((n : ℕ) → C n → C (succ n)) → C n
ind-nat {C} {zero} c₀ cs = c₀
ind-nat {C} {succ n} c₀ cs = cs n (ind-nat c₀ cs)

-- Example functions
double = rec-nat zero (λ _ → λ rec → succ (succ rec))
add = rec-nat id (λ _ → λ rec → λ j → succ (rec j))
mul = rec-nat (λ _ → zero) (λ _ → λ rec → λ j → add j (rec j))

-- Inequalities
_≤_ : ℕ → ℕ → Set
n ≤ m = Σ \k → (add n k ≡ m)

_<_ : ℕ → ℕ → Set
n < m = Σ \k → (add n (succ k) ≡ m)

{- Integers -}
data ℤ : Set where
  +_   : ℕ → ℤ
  -1-_ : ℕ → ℤ

-- Example functions
pred-int : ℤ → ℤ
pred-int (+ zero) = -1- zero
pred-int (+ succ i) = + i
pred-int (-1- i) = -1- succ i

succ-int : ℤ → ℤ
succ-int (+ i) = + succ i
succ-int (-1- zero) = + zero
succ-int (-1- succ i) = -1- i

sub-int : ℤ → ℤ → ℤ
sub-int i (+ zero) = i
sub-int i (+ succ j) = pred-int (sub-int i (+ j))
sub-int i (-1- zero) = succ-int i
sub-int i (-1- succ j) = succ-int (sub-int i (-1- j))

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

{- Logic with types -}
-- Propositional Logic
true = Unit
false = Empty

_and_ : Set → Set → Set
A and B = A × B

_or_ : Set → Set → Set
A or B = A + B

_implies_ : Set → Set → Set
A implies B = A → B

_iff_ : Set → Set → Set
A iff B = (A → B) × (B → A)

not : Set → Set
not A = A → Empty

postulate
 dne : {A : Set} →
       not (not A) → A

-- Predicate Logic
for-all : (A : Set) → (P : A → Set) → Set
for-all A P = (x : A) → P x

there-exists : (A : Set) → (P : A → Set) → Set
there-exists A P = Σ \x → P x

-- Examples
and-so-or : {A B : Set} →
            (A and B) implies (A or B)
and-so-or (x , y) = inl x -- Or inr y if you prefer.

de-morgan-1 : {A B : Set} →
              (not A and not B) iff not (A or B)
de-morgan-1 = l2r , r2l
 where
  l2r : {A B : Set} →
        (not A and not B) implies not (A or B)
  l2r (x , y) (inl a) = x a
  l2r (x , y) (inr b) = y b
  r2l : {A B : Set} →
        not (A or B) implies (not A and not B)
  r2l p = (λ a → p (inl a)) , (λ b → p (inr b))

de-morgan-2 : {A B : Set} →
              (not A or not B) iff not (A and B)
de-morgan-2 = l2r , r2l
 where
  l2r : {A B : Set} →
        (not A or not B) implies not (A and B)
  l2r (inl a) (x , y) = a x
  l2r (inr b) (x , y) = b y
  r2l : {A B : Set} →
        not (A and B) implies (not A or not B)
  r2l {A} {B} p = inl {!!} -- Unprovable?

and-in-out : {A : Set} {P Q : A → Set} →
             ((x : A) → P x and Q x) iff (for-all A P and for-all A Q)
and-in-out = l2r , r2l
 where
  l2r : {A : Set} {P Q : A → Set} →
        ((x : A) → P x and Q x) implies (for-all A P and for-all A Q)
  l2r p = (λ x → π₁ (p x)) , (λ x → π₂ (p x))
  r2l : {A : Set} {P Q : A → Set} →
        (for-all A P and for-all A Q) implies ((x : A) → P x and Q x)
  r2l p = λ x → π₁ p x , π₂ p x

{- Algebraic Structures -}
magma : Set₁
magma = Σ \(A : Set) → (A → A → A)

associative : (m : magma) → (x y z : π₁ m) → Set
associative m x y z = (x ∙ (y ∙ z)) ≡ ((x ∙ y) ∙ z)
 where
  _∙_ = π₂ m

commutative : (m : magma) → (x y : π₁ m) → Set
commutative m x y = (x ∙ y) ≡ (y ∙ x)
 where
  _∙_ = π₂ m

identity : (m : magma) → (x i : π₁ m) → Set
identity m x i = ((i ∙ x) ≡ x) × ((x ∙ i) ≡ x)
 where
  _∙_ = π₂ m

has-identity : (m : magma) → π₁ m → Set
has-identity m x = Σ \i → identity m x i

idempotent : (m : magma) → π₁ m → Set
idempotent m i = (i ∙ i) ≡ i
 where
  _∙_ = π₂ m

has-idempotent : (m : magma) → Set
has-idempotent m = Σ \i → idempotent m i

semigroup : Set₁
semigroup = Σ \(m : magma) →
            (x y z : π₁ m) → associative m x y z

monoid : Set₁
monoid = Σ \(s : semigroup) →
         let m = π₁ s in
         (x : π₁ m) → has-identity m x

commutative-monoid : Set₁
commutative-monoid = Σ \(mo : monoid) →
                     let m = π₁ (π₁ mo) in
                     (x y : π₁ m) → (commutative m x y)

-- Add examples
add-magma : magma
add-magma = ℕ , add

add-associative : ∀ i j k → associative add-magma i j k
add-associative i j k = ind-nat {C} {i} refl (λ _ → λ ind → ap succ ind)
 where
  C = λ i → add i (add j k) ≡ add (add i j) k

add-commutative : ∀ i j → commutative add-magma i j
add-commutative zero zero = refl
add-commutative zero (succ j) = ap succ (add-commutative zero j)
add-commutative (succ i) zero = ap succ (add-commutative i zero)
add-commutative (succ i) (succ j) = ap succ (trans p₁ p₂)
 where
  either-succ : ∀ i j → add (succ i) j ≡ add i (succ j)
  either-succ i j = ind-nat {C} {i} refl (λ _ → λ ind → ap succ ind)
   where
    C = λ i → add (succ i) j ≡ add i (succ j)
  p₁ : add i (succ j) ≡ add (succ i) j
  p₁ = sym (either-succ i j)
  p₂ : add (succ i) j ≡ add j (succ i)
  p₂ = add-commutative (succ i) j

add-has-identity : ∀ i → has-identity add-magma i
add-has-identity i = id-elem , (left-id i , right-id i)
 where
  id-elem = zero
  left-id : ∀ i → add id-elem i ≡ i
  left-id i = refl
  right-id : ∀ i → add i id-elem ≡ i
  right-id i = ind-nat {C} {i} refl (λ _ → λ ind → ap succ ind)
   where
    C = λ i → add i id-elem ≡ i

add-has-idempotent : has-idempotent add-magma
add-has-idempotent = zero , refl

add-semigroup : semigroup
add-semigroup = add-magma , add-associative

add-monoid : monoid
add-monoid = add-semigroup , add-has-identity

add-commutative-monoid : commutative-monoid
add-commutative-monoid = add-monoid , add-commutative

-- Mul examples
mul-magma : magma
mul-magma = ℕ , mul

mul-associative : ∀ i j k → associative mul-magma i j k
mul-associative zero j k = refl
mul-associative (succ i) j k = {!!}
 where
  IH = mul-associative i j k

mul-commutative : ∀ i j → commutative mul-magma i j
mul-commutative i j = {!!}

mul-has-identity : ∀ i → has-identity mul-magma i
mul-has-identity i = id-elem , (left-id i , right-id i)
 where
  id-elem = succ zero
  left-id : ∀ i → mul id-elem i ≡ i
  left-id i = {!!}
  right-id : ∀ i → mul i id-elem ≡ i
  right-id i = {!!}

mul-has-idempotent : has-idempotent mul-magma
mul-has-idempotent = succ zero , refl

mul-semigroup : semigroup
mul-semigroup = mul-magma , mul-associative

mul-monoid : monoid
mul-monoid = mul-semigroup , mul-has-identity

mul-commutative-monoid : commutative-monoid
mul-commutative-monoid = mul-monoid , mul-commutative

{- Path induction -}
path-ind : {A : Set} {C : (x y : A) → x ≡ y → Set} →
           ((x : A) → C x x refl) → (x y : A) → (p : x ≡ y) → C x y p
path-ind c .x x refl = c x

based-path-ind : {A : Set} {a : A} {C : (x : A) → a ≡ x → Set} →
                 C a refl → (x : A) → (p : a ≡ x) → C x p
based-path-ind c a refl = c
