module HoTT where

id : {X : Set} →
     X → X
id x = x

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
double = rec-nat zero (λ n → λ y → succ (succ y))
add = rec-nat id (λ n → λ g → λ m → succ (g m))

-- Inequalities
_≤_ : ℕ → ℕ → Set
n ≤ m = Σ \k → (add n k ≡ m)

_<_ : ℕ → ℕ → Set
n < m = Σ \k → (add n (succ k) ≡ m)

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

{- Semigroups -}
semigroup : {A : Set} → Set
semigroup {A} = Σ \(m : A → A → A) →
                (x y z : A) →
                m x (m y z) ≡ m (m x y) z

-- Examples
add-magma : semigroup {ℕ}
add-magma = add , assoc-add
 where
  assoc-add : ∀ i j k → add i (add j k) ≡ add (add i j) k
  assoc-add zero j k = refl
  assoc-add (succ i) j k = ap succ IH
   where
    IH : add i (add j k) ≡ add (add i j) k
    IH = assoc-add i j k
