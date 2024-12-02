{-# OPTIONS --cubical --allow-unsolved-metas --allow-incomplete-matches #-}
module Extra where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Agda.Builtin.String

open import Cubical.Data.Bool
open import Cubical.Data.Nat

open import Cubical.Foundations.Prelude renaming (_≡_ to _≡ᵖ_)
open import Cubical.Foundations.HLevels

open HasFromNat public
open HasFromNeg public

open import Base
open import Properties

-- Allow us to input numbers
private
  convert : ℕ → ℤₕ
  convert zero = zero
  convert (suc n) = succ (convert n)

  convert-neg : ℕ → ℤₕ
  convert-neg zero = zero
  convert-neg (suc n) = pred (convert-neg n)

instance
  ℤₕ-Num : Number ℤₕ
  Constraint ℤₕ-Num _ =  Unit
  fromNat ℤₕ-Num n = convert n

  ℤₕ-Neg : Negative ℤₕ
  Constraint ℤₕ-Neg _ = Unit
  fromNeg ℤₕ-Neg n = convert-neg n

-- Relations
_≡ᶻ_ : ℤₕ → ℤₕ → Bool
zero      ≡ᶻ zero      = true
succ n    ≡ᶻ succ m    = n ≡ᶻ m
pred n    ≡ᶻ pred m    = n ≡ᶻ m

succ-inj : ∀ m n → succ m ≡ succ n → m ≡ n
succ-inj m n eq = sym (sec m) ∙ congS pred eq ∙ sec n

pred-inj : ∀ m n → pred m ≡ pred n → m ≡ n
pred-inj m n eq = sym (ret m) ∙ congS succ eq ∙ ret n

-- Division, Modulo
record NonZero (z : ℤₕ) : Set where
  field
    nonZero : Bool→Type (not (z ≡ᶻ zero))

infixl 7 _/_ _%_

div-helper : (k m n j : ℤₕ) → ℤₕ
div-helper k m zero     j        = k
div-helper k m (succ n) zero     = div-helper (succ k) m n m
div-helper k m (succ n) (succ j) = div-helper k        m n j

_/_ : (dividend divisor : ℤₕ) . {{_ : NonZero divisor}} → ℤₕ
m / (succ n) = div-helper zero n m n

mod-helper : (k m n j : ℤₕ) → ℤₕ
mod-helper k m zero      j       = k
mod-helper k m (succ n)  zero    = mod-helper zero     m n m
mod-helper k m (succ n) (succ j) = mod-helper (succ k) m n j

_%_ : (dividend divisor : ℤₕ) . {{_ : NonZero divisor}} → ℤₕ
m % (succ n) = mod-helper zero n m n

-- Exponentiation
infixr 8 _^^_

_^^_ : ℤₕ → ℕ → ℤₕ
a          ^^ zero  = succ zero
zero       ^^ suc b = zero
x@(succ a) ^^ suc b = x * (x ^^ b)
x@(pred a) ^^ suc b = x * (x ^^ b)
