module SimpleAddition where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

add : Nat → Nat → Nat
add zero    n = n
add (suc m) n = suc (add m n)

test1 : add 2 3 ≡ 5
test1 = refl

test2 : add 0 5 ≡ 5
test2 = refl

test3 : add 4 0 ≡ 4
test3 = refl
