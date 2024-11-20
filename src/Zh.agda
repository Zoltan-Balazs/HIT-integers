{-# OPTIONS --cubical --no-postfix-projections #-}

open import Agda.Primitive
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Semigroup

open import Cubical.Data.Int renaming (_+_ to _+ᶻ_; _-_ to _-ᶻ_; -_ to -ᶻ_)
open import Cubical.Data.Int.MoreInts.BiInvInt.Base renaming (pred to predᵇ)
open import Cubical.Data.Nat.Base hiding (_+_)
open import Cubical.Data.Sigma

open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws

open import Cubical.HITs.PropositionalTruncation

module Zh where

-- Higher inductive type definition of ℤ
data ℤₕ : Set where
    zero : ℤₕ
    succ : ℤₕ → ℤₕ
    pred : ℤₕ → ℤₕ
    sec : (z : ℤₕ) → pred (succ z) ≡ z
    ret : (z : ℤₕ) → succ (pred z) ≡ z
    coh : (z : ℤₕ) → congS succ (sec z) ≡ ret (succ z)

open isHAEquiv

succ-inj : (a b : ℤₕ) → succ a ≡ succ b → a ≡ b
succ-inj a b eq = sym (sec a) ∙ congS pred eq ∙ sec b

pred-inj : (a b : ℤₕ) → pred a ≡ pred b → a ≡ b
pred-inj a b eq = sym (ret a) ∙ congS succ eq ∙ ret b

isHAℤₕ : isHAEquiv succ
isHAℤₕ .isHAEquiv.g    = pred
isHAℤₕ .isHAEquiv.linv = sec
isHAℤₕ .isHAEquiv.rinv = ret
isHAℤₕ .isHAEquiv.com  = coh

hoc : (z : ℤₕ) → congS pred (ret z) ≡ sec (pred z)
hoc = com-op isHAℤₕ

congS₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         (f : A → B → C) {x y : A} {x' y' : B} → x ≡ y → x' ≡ y' → f x x' ≡ f y y'
congS₂ f e1 e2 i = f (e1 i) (e2 i)
-------------------------------------------------------------------
HAℤₕ : HAEquiv ℤₕ ℤₕ
HAℤₕ = succ , isHAℤₕ

ℤₕ-ℤ : ℤₕ → ℤ
ℤₕ-ℤ zero = pos zero
ℤₕ-ℤ (succ x) = sucℤ (ℤₕ-ℤ x)
ℤₕ-ℤ (pred x) = predℤ (ℤₕ-ℤ x)
ℤₕ-ℤ (sec x i) = predSuc (ℤₕ-ℤ x) i
ℤₕ-ℤ (ret x i) = sucPred (ℤₕ-ℤ x) i
ℤₕ-ℤ (coh x i j) = isSetℤ
  (sucℤ (predℤ (sucℤ (ℤₕ-ℤ x))))
  (sucℤ (ℤₕ-ℤ x))
  (congS sucℤ (predSuc (ℤₕ-ℤ x)))
  (sucPred (sucℤ (ℤₕ-ℤ x)))
  i j

ℤ-ℤₕ : ℤ → ℤₕ
ℤ-ℤₕ (pos zero) = zero
ℤ-ℤₕ (pos (suc n)) = succ (ℤ-ℤₕ (pos n))
ℤ-ℤₕ (negsuc zero) = pred zero
ℤ-ℤₕ (negsuc (suc n)) = pred (ℤ-ℤₕ (negsuc n))

ℤ-ℤₕ-sucℤ : (z : ℤ) → ℤ-ℤₕ (sucℤ z) ≡ succ (ℤ-ℤₕ z)
ℤ-ℤₕ-sucℤ (pos n) = refl
ℤ-ℤₕ-sucℤ (negsuc zero) = sym (ret (ℤ-ℤₕ (pos zero)))
ℤ-ℤₕ-sucℤ (negsuc (suc n)) = sym (ret (ℤ-ℤₕ (negsuc n)))

ℤ-ℤₕ-predℤ : (z : ℤ) → ℤ-ℤₕ (predℤ z) ≡ pred (ℤ-ℤₕ z)
ℤ-ℤₕ-predℤ (pos zero) = refl
ℤ-ℤₕ-predℤ (pos (suc n)) = sym (sec (ℤ-ℤₕ (pos n)))
ℤ-ℤₕ-predℤ (negsuc n) = refl

sym-filler : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y)
                → Square (sym p)
                         refl
                         refl
                         p
sym-filler p i j = p (i ∨ ~ j)
{-
hcomp (λ k → λ { (j = i0) → y
                                          ; (i = i0) → p ((~ j) ∨ (~ k))
                                          ; (i = i1) → y
                                          ; (j = i1) → p (i ∨ (~ k)) }) y
-}
refl-square : ∀ {ℓ} {A : Type ℓ} {x : A} → Square {a₀₀ = x} refl refl refl refl
refl-square = refl
{-
     101 y--------y 111
        /|        /|
       / |       / |
   001x---------y011
      |  |      |  |
      |  |      |  |
      100y---------y 110
      | /       | /
      |/        |/
      y---------y
   000          010


-}


sym-filler-Cube : ∀ {ℓ} {A : Type ℓ} {x y : A}
                    (p : x ≡ y)
                    → Cube
                      (sym-filler p)
                      (refl-square {x = y})
                      (sym-filler p)
                      (refl-square {x = y})
                      (refl-square {x = y})
                      λ i j → p (i ∨ j)
sym-filler-Cube {y = y} p i j k = p (i ∨ j ∨ ~ k)


{-
hcomp (λ k → λ { (j = i0) → y
                                          ; (i = i0) → p ((~ j) ∨ (~ k))
                                          ; (i = i1) → y
                                          ; (j = i1) → p (i ∨ (~ k)) }) y
-}

ℤ-ℤₕ-sucPred : (z : ℤ) → Square (ℤ-ℤₕ-sucℤ (predℤ z) ∙ (λ j → succ (ℤ-ℤₕ-predℤ z j)))
                                (λ _ → ℤ-ℤₕ z)
                                (λ i → ℤ-ℤₕ (sucPred z i))
                                (ret (ℤ-ℤₕ z))
ℤ-ℤₕ-sucPred (pos zero) i j =
  hcomp (λ k → λ { (j = i0) → ℤ-ℤₕ (pos zero)
                 ; (i = i0) → rUnit (sym (ret (ℤ-ℤₕ (pos zero)))) k j
                 ; (i = i1) → ℤ-ℤₕ (pos zero)
                 ; (j = i1) → ret (ℤ-ℤₕ (pos zero)) i
                 })
        (sym-filler (ret (ℤ-ℤₕ (pos zero))) i j)
ℤ-ℤₕ-sucPred (pos (suc n)) i j =
  hcomp (λ k → λ { (j = i0) → succ (ℤ-ℤₕ (pos n))
                 ; (i = i0) → lUnit (λ i → succ (sym (sec (ℤ-ℤₕ (pos n))) i)) k j
                 ; (i = i1) → succ (ℤ-ℤₕ (pos n))
                 ; (j = i1) → coh (ℤ-ℤₕ (pos n)) k i
                 })
        (succ (sym-filler (sec (ℤ-ℤₕ (pos n))) i j))
ℤ-ℤₕ-sucPred (negsuc n) i j =
  hcomp (λ k → λ { (j = i0) → ℤ-ℤₕ (negsuc n)
                 ; (i = i0) → rUnit (sym (ret (ℤ-ℤₕ (negsuc n)))) k j
                 ; (i = i1) → ℤ-ℤₕ (negsuc n)
                 ; (j = i1) → ret (ℤ-ℤₕ (negsuc n)) i
                 })
        (sym-filler (ret (ℤ-ℤₕ (negsuc n))) i j)

ℤ-ℤₕ-predSuc : (x : ℤ)
              → Square (ℤ-ℤₕ-predℤ (sucℤ x) ∙ (λ i → pred (ℤ-ℤₕ-sucℤ x i)))
                       (λ _ → ℤ-ℤₕ x)
                       (λ i → ℤ-ℤₕ (predSuc x i))
                       (sec (ℤ-ℤₕ x))
ℤ-ℤₕ-predSuc (pos n) i j
  = hcomp (λ k → λ { (j = i0) → ℤ-ℤₕ (pos n)
                   ; (i = i0) → rUnit (sym (sec (ℤ-ℤₕ (pos n)))) k j
                   ; (i = i1) → ℤ-ℤₕ (pos n)
                   ; (j = i1) → sec (ℤ-ℤₕ (pos n)) i
                   })
          (sym-filler (sec (ℤ-ℤₕ (pos n))) i j)
ℤ-ℤₕ-predSuc (negsuc zero) i j
  = hcomp (λ k → λ { (j = i0) → ℤ-ℤₕ (negsuc zero)
                   ; (i = i0) → lUnit (λ i → pred (sym (ret (ℤ-ℤₕ (pos zero))) i)) k j
                   ; (i = i1) → ℤ-ℤₕ (negsuc zero)
                   ; (j = i1) → hoc (ℤ-ℤₕ (pos zero)) k i
                   })
          (pred (sym-filler (ret (ℤ-ℤₕ (pos zero))) i j))
ℤ-ℤₕ-predSuc (negsuc (suc n)) i j
  = hcomp (λ k → λ { (j = i0) → ℤ-ℤₕ (negsuc (suc n))
                   ; (i = i0) → lUnit (λ i → pred (sym (ret (ℤ-ℤₕ (negsuc n))) i)) k j
                   ; (i = i1) → ℤ-ℤₕ (negsuc (suc n))
                   ; (j = i1) → hoc (ℤ-ℤₕ (negsuc n)) k i
                   })
          (pred (sym-filler (ret (ℤ-ℤₕ (negsuc n))) i j))

ℤ-ℤₕ-ℤ : (z : ℤ) → ℤₕ-ℤ (ℤ-ℤₕ z) ≡ z
ℤ-ℤₕ-ℤ (ℤ.pos zero) = refl
ℤ-ℤₕ-ℤ (ℤ.pos (suc n)) = cong sucℤ (ℤ-ℤₕ-ℤ (ℤ.pos n))
ℤ-ℤₕ-ℤ (negsuc zero) = refl
ℤ-ℤₕ-ℤ (negsuc (suc n)) = cong predℤ (ℤ-ℤₕ-ℤ (negsuc n))

ℤₕ-ℤ-ℤₕ : (z : ℤₕ) → ℤ-ℤₕ (ℤₕ-ℤ z) ≡ z
ℤ-ℤₕ-coh : (z : ℤ) → Cube
           (λ j k → ℤₕ-ℤ-ℤₕ (coh (ℤ-ℤₕ z) i0 j) k)
           (λ j k → ℤₕ-ℤ-ℤₕ (coh (ℤ-ℤₕ z) i1 j) k)
           (λ i k → ℤₕ-ℤ-ℤₕ (coh (ℤ-ℤₕ z) i i0) k)
           (λ i k → ℤₕ-ℤ-ℤₕ (coh (ℤ-ℤₕ z) i i1) k)
           (λ i j → ℤₕ-ℤ-ℤₕ (coh (ℤ-ℤₕ z) i j) i0) -- discrete
           (coh (ℤ-ℤₕ z))
ℤ-ℤₕ-coh (pos zero) i j k =
  hcomp (λ l → λ { (i = i0) → {!!}
                 ; (i = i1) → {!!}
                 ; (j = i0) → {!!}
                 ; (j = i1) → hcomp
                               (doubleComp-faces (λ _ → succ zero) (λ i₁ → succ zero) k)
                               (succ zero)
                 ; (k = i0) → succ zero
                 ; (k = i1) → coh zero i j  })
        {!!} --sym-filler-Cube (λ l → coh (ℤ-ℤₕ (pos zero)) l) i j k
ℤ-ℤₕ-coh (pos (suc n)) i j k = {!!}
ℤ-ℤₕ-coh (negsuc n) i j k = {!!}
-- (sym-filler (ret (ℤ-ℤₕ (pos zero))) i j)
ℤₕ-ℤ-ℤₕ zero = refl
ℤₕ-ℤ-ℤₕ (succ z) = ℤ-ℤₕ-sucℤ (ℤₕ-ℤ z) ∙ (λ i → succ (ℤₕ-ℤ-ℤₕ z i))
ℤₕ-ℤ-ℤₕ (pred z) = ℤ-ℤₕ-predℤ (ℤₕ-ℤ z) ∙ (λ i → pred (ℤₕ-ℤ-ℤₕ z i))
ℤₕ-ℤ-ℤₕ (sec z i) j =
  hcomp (λ k → λ { (j = i0) → ℤ-ℤₕ (predSuc (ℤₕ-ℤ z) i)
                 ; (i = i0) → (ℤ-ℤₕ-predℤ (sucℤ (ℤₕ-ℤ z))
                              ∙ (λ i → pred (compPath-filler (ℤ-ℤₕ-sucℤ (ℤₕ-ℤ z))
                                                             (λ i' → succ (ℤₕ-ℤ-ℤₕ z i'))
                                                             k i))) j
                 ; (i = i1) → ℤₕ-ℤ-ℤₕ z (j ∧ k)
                 ; (j = i1) → sec (ℤₕ-ℤ-ℤₕ z k) i })
        (ℤ-ℤₕ-predSuc (ℤₕ-ℤ z) i j)
ℤₕ-ℤ-ℤₕ (ret z i) j =
  hcomp (λ k → λ { (j = i0) → ℤ-ℤₕ (sucPred (ℤₕ-ℤ z) i)
                 ; (i = i0) → (ℤ-ℤₕ-sucℤ (predℤ (ℤₕ-ℤ z))
                              ∙ (λ i → succ (compPath-filler (ℤ-ℤₕ-predℤ (ℤₕ-ℤ z))
                                                             (congS pred (ℤₕ-ℤ-ℤₕ z)) -- (λ i' → (fwd-bwd z i') i')
                                                             k i))) j
                 ; (i = i1) → ℤₕ-ℤ-ℤₕ z (j ∧ k)
                 ; (j = i1) → ret (ℤₕ-ℤ-ℤₕ z k) i  }) -- suc-predl≡predr (fwd-bwd z k) k i })
        (ℤ-ℤₕ-sucPred (ℤₕ-ℤ z) i j)
ℤₕ-ℤ-ℤₕ (coh z i j) k =
  hcomp (λ l → λ { (i = i0) → {! coh (ℤₕ-ℤ-ℤₕ z l) i0 l !}
                 ; (i = i1) → {! !}
                 ; (j = i0) → {! !}
                 ; (j = i1) → {!!}
                 ; (k = i0) → {!!}
                 ; (k = i1) → coh (ℤₕ-ℤ-ℤₕ z l) i j })
        (ℤ-ℤₕ-coh (ℤₕ-ℤ z) i j k)

ℤ-iso : Iso ℤₕ ℤ
ℤ-iso .Iso.fun      = ℤₕ-ℤ
ℤ-iso .Iso.inv      = ℤ-ℤₕ
ℤ-iso .Iso.rightInv = ℤ-ℤₕ-ℤ
ℤ-iso .Iso.leftInv  = ℤₕ-ℤ-ℤₕ

ℤ≡ℤₕ : ℤ ≡ ℤₕ
ℤ≡ℤₕ = isoToPath (iso ℤ-ℤₕ ℤₕ-ℤ ℤₕ-ℤ-ℤₕ ℤ-ℤₕ-ℤ)

isSetℤₕ : isSet ℤₕ
isSetℤₕ = subst isSet ℤ≡ℤₕ isSetℤ

-- Induction principle (eliminator)
ℤₕ-ind :
    ∀ {ℓ} {P : ℤₕ → Type ℓ}
  → (P-zero : P zero)
  → (P-succ : ∀ z → P z → P (succ z))
  → (P-pred : ∀ z → P z → P (pred z))
  → (P-sec : ∀ z → (pz : P z) →
           PathP
             (λ i → P (sec z i))
             (P-pred (succ z) (P-succ z pz))
             pz)
  → (P-ret : ∀ z → (pz : P z) →
           PathP
             (λ i → P (ret z i))
             (P-succ (pred z) (P-pred z pz))
             pz)
  → (P-coh : ∀ z → (pz : P z) →
           SquareP
             (λ i j → P (coh z i j))
             (congP (λ i → P-succ (sec z i)) (P-sec z pz))
             (P-ret (succ z) (P-succ z pz))
             refl
             refl)
  → (z : ℤₕ)
  → P z
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh zero = P-zero
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh (succ z) = P-succ z (ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh z)
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh (pred z) = P-pred z (ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh z)
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh (sec z i) = P-sec z (ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh z) i
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh (ret z i) = P-ret z (ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh z) i
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh (coh z i j) = P-coh z (ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh z) i j

-- Induction property
ℤₕ-ind-prop :
  ∀ {ℓ} {P : ℤₕ → Type ℓ}
  → (∀ z → isProp (P z))
  → P zero
  → (∀ z → P z → P (succ z))
  → (∀ z → P z → P (pred z))
  → (z : ℤₕ)
  → P z
ℤₕ-ind-prop {P = P} P-isProp P-zero P-succ P-pred =
  ℤₕ-ind
    P-zero
    P-succ
    P-pred
    (λ z pz → toPathP (P-isProp z _ _))
    (λ z pz → toPathP (P-isProp z _ _))
    (λ z pz → isProp→SquareP (λ i j → P-isProp (coh z i j)) _ _ _ _)

-- Iterator
ℤₕ-ite :
  ∀ {ℓ} {A : Type ℓ}
  → A
  → A ≃ A
  → ℤₕ
  → A
ℤₕ-ite {A = A} a e =
  let
    (s , isHA) = equiv→HAEquiv e
  in
    ℤₕ-ind
      {P = λ _ → A}
      a
      (λ _ → s)
      (λ _ → g isHA)
      (λ _ → linv isHA)
      (λ _ → rinv isHA)
      (λ _ → com isHA)
infixl 6 _+_ _-_
infixl 7 _*_

_+_ : ℤₕ → ℤₕ → ℤₕ
zero      + b = b
succ a    + b = succ (a + b)
pred a    + b = pred (a + b)
sec a i   + b = sec (a + b) i
ret a i   + b = ret (a + b) i
coh a i j + b = coh (a + b) i j

negate : ℤₕ → ℤₕ
negate zero        = zero
negate (succ z)    = pred (negate z)
negate (pred z)    = succ (negate z)
negate (sec z i)   = ret (negate z) i
negate (ret z i)   = sec (negate z) i
negate (coh z i j) = hoc (negate z) i j

_-_ : ℤₕ → ℤₕ → ℤₕ
a - b = a + negate b

sucr+ : (a b : ℤₕ) → a + succ b ≡ succ (a + b)
sucr+ zero        b = refl
sucr+ (succ a)    b = ap succ (sucr+ a b)
sucr+ (pred a)    b = ap pred (sucr+ a b) ∙ sec (a + b) ∙ sym (ret (a + b))
sucr+ (sec a i)   b = {! ap (λ k → sec k i) (sucr+ a b)!}
sucr+ (ret a i)   b = {!   !}
sucr+ (coh a i j) b = {!   !}

predr+ : (a b : ℤₕ) → a + pred b ≡ pred (a + b)
predr+ zero        b = refl
predr+ (succ a)    b = ap succ (predr+ a b) ∙ ret (a + b) ∙ sym (sec (a + b))
predr+ (pred a)    b = ap pred (predr+ a b)
predr+ (sec a i)   b = {!   !}
predr+ (ret a i)   b = {!   !}
predr+ (coh a i j) b = {!   !}

inv-additivity : (z : ℤₕ) → z - z ≡ zero
inv-additivity zero        = refl
inv-additivity (succ z)    = ap succ (predr+ z (negate z)) ∙ ret (z - z) ∙ inv-additivity z
inv-additivity (pred z)    = ap pred (sucr+ z (negate z)) ∙ sec (z - z) ∙ inv-additivity z
inv-additivity (sec z i)   = {!   !}
inv-additivity (ret z i)   = {!   !}
inv-additivity (coh z i j) = {!   !}

-- Properties needed for HIT Integers to form a Commutative Ring
-- Is it an Abelian Group under addition?
ℤₕ-add-is-assoc : (a b c : ℤₕ) → (a + b) + c ≡ a + (b + c)
ℤₕ-add-is-assoc zero        b c = refl
ℤₕ-add-is-assoc (succ a)    b c = ap succ (ℤₕ-add-is-assoc a b c)
ℤₕ-add-is-assoc (pred a)    b c = ap pred (ℤₕ-add-is-assoc a b c)
ℤₕ-add-is-assoc (sec a i)   b c = ap (λ k → sec k i) (ℤₕ-add-is-assoc a b c)
ℤₕ-add-is-assoc (ret a i)   b c = ap (λ k → ret k i) (ℤₕ-add-is-assoc a b c)
ℤₕ-add-is-assoc (coh a i j) b c = ap (λ k → coh k i j) (ℤₕ-add-is-assoc a b c)

-- Helping lemma for ℤₕ-add-has-right-id-elem
ℤₕ-add-right-id : (a : ℤₕ) → a + zero ≡ a
ℤₕ-add-right-id zero = refl
ℤₕ-add-right-id (succ a) = ap succ (ℤₕ-add-right-id a)
ℤₕ-add-right-id (pred a) = ap pred (ℤₕ-add-right-id a)
ℤₕ-add-right-id (sec a i) = ap (λ k → sec k i) (ℤₕ-add-right-id a)
ℤₕ-add-right-id (ret a i) = ap (λ k → ret k i) (ℤₕ-add-right-id a)
ℤₕ-add-right-id (coh a i j) = ap (λ k → coh k i j) (ℤₕ-add-right-id a)

ℤₕ-add-has-right-id-elem : ∃[ b ∈ ℤₕ ] ((a : ℤₕ) → a + b ≡ a)
ℤₕ-add-has-right-id-elem = ∣ zero , ℤₕ-add-right-id ∣₁

-- Helping lemma for ℤₕ-add-has-left-id-elem
ℤₕ-add-left-id : (a : ℤₕ) → zero + a ≡ a
ℤₕ-add-left-id a = refl

ℤₕ-add-has-left-id-elem : ∃[ b ∈ ℤₕ ] ((a : ℤₕ) → b + a ≡ a)
ℤₕ-add-has-left-id-elem = ∣ zero , ℤₕ-add-left-id ∣₁

ℤₕ-add-has-right-inv-elem : (a : ℤₕ) → a + negate a ≡ zero
ℤₕ-add-has-right-inv-elem zero = refl
ℤₕ-add-has-right-inv-elem (succ a) = {!!}
ℤₕ-add-has-right-inv-elem (pred a) = {!!}
ℤₕ-add-has-right-inv-elem (sec a i) = {!!}
ℤₕ-add-has-right-inv-elem (ret a i) = {!!}
ℤₕ-add-has-right-inv-elem (coh a i j) = {!!}

ℤₕ-add-has-left-inv-elem : (a : ℤₕ) → negate a + a ≡ zero
ℤₕ-add-has-left-inv-elem zero = refl
ℤₕ-add-has-left-inv-elem (succ a) = {! sym (predr+ (negate a) (succ a)) ∙ ℤₕ-add-has-left-inv-elem (sec a)!}
ℤₕ-add-has-left-inv-elem (pred a) = {!!}
ℤₕ-add-has-left-inv-elem (sec a i) = {!!}
ℤₕ-add-has-left-inv-elem (ret a i) = {!!}
ℤₕ-add-has-left-inv-elem (coh a i j) = {!!}

-- Helping lemmas for ℤₕ-add-is-comm
ℤₕ-add-comm-succ-helper : (a b : ℤₕ) → succ a + b ≡ a + succ b
ℤₕ-add-comm-succ-helper zero b = refl
ℤₕ-add-comm-succ-helper (succ a) b = ap succ (ℤₕ-add-comm-succ-helper a b)
ℤₕ-add-comm-succ-helper (pred a) b = ret (a + b) ∙ sym (sec (a + b)) ∙ ap pred (ℤₕ-add-comm-succ-helper a b)
ℤₕ-add-comm-succ-helper (sec a i) b = {!   !}
ℤₕ-add-comm-succ-helper (ret a i) b = {!   !}
ℤₕ-add-comm-succ-helper (coh a i j) b = {!   !}

ℤₕ-add-comm-pred-helper : (a b : ℤₕ) → pred a + b ≡ a + pred b
ℤₕ-add-comm-pred-helper zero b = refl
ℤₕ-add-comm-pred-helper (succ a) b = sec (a + b) ∙ sym (ret (a + b)) ∙ ap succ (ℤₕ-add-comm-pred-helper a b)
ℤₕ-add-comm-pred-helper (pred a) b = ap pred (ℤₕ-add-comm-pred-helper a b)
ℤₕ-add-comm-pred-helper (sec a i) b = {!   !}
ℤₕ-add-comm-pred-helper (ret a i) b = {!   !}
ℤₕ-add-comm-pred-helper (coh a i j) b = {!   !}

ℤₕ-add-is-comm : (a b : ℤₕ) → a + b ≡ b + a
ℤₕ-add-is-comm zero b = sym (ℤₕ-add-right-id b)
ℤₕ-add-is-comm (succ a) b = ap succ (ℤₕ-add-is-comm a b) ∙ ℤₕ-add-comm-succ-helper b a
ℤₕ-add-is-comm (pred a) b = ap pred (ℤₕ-add-is-comm a b) ∙ ℤₕ-add-comm-pred-helper b a
ℤₕ-add-is-comm (sec a i) b = {!   ap (λ k → sec k i) (ℤₕ-add-is-comm a b) !}
ℤₕ-add-is-comm (ret a i) b = {!   !}
ℤₕ-add-is-comm (coh a i j) b = {!   !}

isAbGroupℤₕ+ : IsAbGroup {lzero} {ℤₕ} zero _+_ negate
isAbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set = isSetℤₕ
isAbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.·Assoc = λ x y z → sym (ℤₕ-add-is-assoc x y z)
isAbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.isMonoid .IsMonoid.·IdR = ℤₕ-add-right-id
isAbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.isMonoid .IsMonoid.·IdL = ℤₕ-add-left-id
isAbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.·InvR = ℤₕ-add-has-right-inv-elem
isAbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.·InvL = ℤₕ-add-has-left-inv-elem
isAbGroupℤₕ+ .IsAbGroup.+Comm = ℤₕ-add-is-comm

_*_ : ℤₕ → ℤₕ → ℤₕ
infixr 8 _^^_

_^^_ : ℤₕ → ℕ → ℤₕ
a ^^ zero = succ zero
zero ^^ suc b = zero
x@(succ a) ^^ suc b = x * (x ^^ b)
x@(pred a) ^^ suc b = x * (x ^^ b)
x@(sec a i) ^^ suc b = {!!}
x@(ret a i) ^^ suc b = {!!}
x@(coh a i j) ^^ suc b = {!!}
