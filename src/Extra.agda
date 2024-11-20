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
_≡_ : ℤₕ → ℤₕ → Bool
zero      ≡ zero      = true
succ n    ≡ succ m    = n ≡ m
pred n    ≡ pred m    = n ≡ m
{-
sec n i   ≡ sec m j   = {!hcomp (λ k → λ { (i = i0) → pred (succ n) ≡ sec m j
                                         ; (i = i1) → n ≡ sec m j
                                         ; (j = i0) → sec n i ≡ pred (succ m)
                                         ; (j = i1) → sec n i ≡ m
                                         }) (n ≡ m)!}
ret n i   ≡ ret m j   = {!!}
coh n i j ≡ coh m k l = {!!}
-}
-- _         ≡ _         = false

succ-inj : ∀ m n → succ m ≡ᵖ succ n → m ≡ᵖ n
succ-inj = ℤₕ-ind-prop
  (λ _ → isPropΠ2 λ _ _ → isSetℤₕ _ _)
  (λ n o → sym (sec zero) ∙ congS pred o ∙ sec n)
  (λ m p n o → sym (sec (succ m)) ∙ congS pred o ∙ sec n)
  (λ m p n o → sym (sec (pred m)) ∙ congS pred o ∙ sec n)

pred-inj : ∀ m n → pred m ≡ᵖ pred n → m ≡ᵖ n
pred-inj = ℤₕ-ind-prop
  (λ _ → isPropΠ2 λ _ _ → isSetℤₕ _ _)
  (λ n o → sym (ret zero) ∙ congS succ o ∙ ret n)
  (λ m p n o → sym (ret (succ m)) ∙ congS succ o ∙ ret n)
  (λ m p n o → sym (ret (pred m)) ∙ congS succ o ∙ ret n)

_<_ : ℤₕ → ℤₕ → Bool
x < y = {!!}

-- Division, Modulo
record NonZero (z : ℤₕ) : Set where
  field
    nonZero : Bool→Type (not (z ≡ zero))

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
{-
x@(sec a i) ^^ suc b = {!!}
x@(ret a i) ^^ suc b = {!!}
x@(coh a i j) ^^ suc b = {!!}
-}
