module VectorAppend where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 20 _∷_

vec1 : Vec Nat 2
vec1 = 1 ∷ 2 ∷ []

vec2 : Vec Nat 3
vec2 = 3 ∷ 4 ∷ 5 ∷ []

length : {A : Set} {n : Nat} → Vec A n → Nat
length []       = zero
length (_ ∷ xs) = suc (length xs)

append : {A : Set} {n m : Nat} → Vec A n → Vec A m → Vec A (n + m)
append []       ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

append-length : {A : Set} {n m : Nat} (xs : Vec A n) (ys : Vec A m) →
                length (append xs ys) ≡ (n + m)
append-length []       ys = refl
append-length (x ∷ xs) ys = cong suc (append-length xs ys)

append-identity : {A : Set} {n : Nat} (xs : Vec A n) → append [] xs ≡ xs
append-identity []       = refl
append-identity (x ∷ xs) = refl
