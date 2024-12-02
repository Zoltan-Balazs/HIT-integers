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
-- Alternative definition that ℤₕ is a set
record ℤ-algebra : Set₁ where
  field
    Z : Set
    ze : Z
    su : Z ≡ Z

record ℤ-hom (m n : ℤ-algebra) : Set where
  module m = ℤ-algebra m
  module n = ℤ-algebra n
  field
    Z : m.Z → n.Z
    ze : Z (m.ze) ≡ n.ze
    su : (λ (x : m.Z) → Z (transport m.su x)) ≡ (λ x → transport n.su (Z x))

initial : ℤ-algebra → Set₁
initial m = (n : ℤ-algebra) → isProp (ℤ-hom m n)

initial-uniq : (m m' : ℤ-algebra) → initial m → initial m' → m ≡ m'
initial-uniq m m' = {!!}

-- Remaining proof that ℤₕ is a set
ℤ→ℤₕ-sucPredSuc : (z : ℤ) → ℤ→ℤₕ (sucℤ (predℤ (sucℤ z))) ≡ succ (pred (succ (ℤ→ℤₕ z)))
ℤ→ℤₕ-sucPredSuc z = ℤ→ℤₕ-sucℤ (predℤ (sucℤ z)) ∙ congS succ (ℤ→ℤₕ-predℤ (sucℤ z) ∙ congS pred (ℤ→ℤₕ-sucℤ z))

ℤ→ℤₕ-sucPredSuc-Path : (z : ℤ) → PathP (λ i → ℤ→ℤₕ (sucPred (sucℤ z) i) ≡ succ (sec (ℤ→ℤₕ z) i))
                                       (ℤ→ℤₕ-sucℤ (predℤ (sucℤ z)) ∙ congS succ (ℤ→ℤₕ-predℤ (sucℤ z) ∙ congS pred (ℤ→ℤₕ-sucℤ z)))
                                       (ℤ→ℤₕ-sucℤ z)
ℤ→ℤₕ-sucPredSuc-Path z i j = {!!}

succsec-sucPredSuc : (z : ℤ) → (i : I) → succ (sec (ℤ→ℤₕ z) i) ≡ ℤ→ℤₕ (sucPred (sucℤ z) i)
succsec-sucPredSuc z i j = hcomp (λ k → λ { (i = i0) → ℤ→ℤₕ-sucPredSuc z (~ j)
                                          ; (i = i1) → ℤ→ℤₕ-sucℤ z (~ j)
                                          ; (j = i0) → succ (sec (ℤ→ℤₕ z) i)
                                          ; (j = i1) → ℤ→ℤₕ (sucPred (sucℤ z) i)
                                          }) {!!}

{-
       101 y-----------y 111
          /|          /|
         / |         / |
        /  |        /  |
       /   |       /   |
  001 x-----------y 011|
      |    |      |    |
      |    |      |    |
      |100 y------|----y 110
      |   /       |   /
      |  /        |  /
      | /         | /
      |/          |/
  000 y-----------y 010
-}

ℤ→ℤₕ-coh : (z : ℤ) → Cube
             (λ j k → ℤ→ℤₕ-sucPredSuc-Path z j k)
             (λ j k → hcomp (λ l → λ { (j = i0) → ℤ→ℤₕ-sucPredSuc z k
                                     ; (j = i1) → ℤ→ℤₕ-sucℤ z k
                                     ; (k = i0) → ℤ→ℤₕ (cohℤ z (~ l) j)
                                     ; (k = i1) → coh (ℤ→ℤₕ z) l j
                                     }) (succsec-sucPredSuc z j (~ k)) )
             (λ i k → ℤ→ℤₕ-sucPredSuc z k)
             (λ i k → ℤ→ℤₕ-sucℤ z k)
             (λ i j → ℤ→ℤₕ (cohℤ z (~ i) j))
             (λ i j → coh (ℤ→ℤₕ z) i j)
ℤ→ℤₕ-coh z i j k = {!!}

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
