{-# OPTIONS --cubical --no-postfix-projections --allow-unsolved-metas #-}
module Base where

open import Cubical.Data.Int renaming (_+_ to _+ᶻ_; _-_ to _-ᶻ_; -_ to -ᶻ_)
open import Cubical.Data.Nat.Base hiding (_+_)

open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open isHAEquiv

congS₂ : {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
         (f : A → B → C) {x y : A} {x' y' : B} → x ≡ y → x' ≡ y' → f x x' ≡ f y y'
congS₂ f e1 e2 i = f (e1 i) (e2 i)

sym-filler : ∀ {ℓ} {A : Type ℓ} {x y : A} (p : x ≡ y)
                → Square (sym p)
                         refl
                         refl
                         p
sym-filler p i j = p (i ∨ ~ j)

cohℤ : ∀ z → congS sucℤ (predSuc z) ≡ sucPred (sucℤ z)
cohℤ (pos n)          = refl
cohℤ (negsuc zero)    = refl
cohℤ (negsuc (suc n)) = refl

-- Higher inductive type definition of ℤ
data ℤₕ : Set where
    zero : ℤₕ
    succ : ℤₕ → ℤₕ
    pred : ℤₕ → ℤₕ
    sec : (z : ℤₕ) → pred (succ z) ≡ z
    ret : (z : ℤₕ) → succ (pred z) ≡ z
    coh : (z : ℤₕ) → congS succ (sec z) ≡ ret (succ z)

isHAℤₕ : isHAEquiv succ
isHAℤₕ .isHAEquiv.g    = pred
isHAℤₕ .isHAEquiv.linv = sec
isHAℤₕ .isHAEquiv.rinv = ret
isHAℤₕ .isHAEquiv.com  = coh

hoc : (z : ℤₕ) → congS pred (ret z) ≡ sec (pred z)
hoc = com-op isHAℤₕ

-- Converting HIT Integers to Standard Integers
ℤₕ→ℤ : ℤₕ → ℤ
ℤₕ→ℤ zero        = pos zero
ℤₕ→ℤ (succ z)    = sucℤ (ℤₕ→ℤ z)
ℤₕ→ℤ (pred z)    = predℤ (ℤₕ→ℤ z)
ℤₕ→ℤ (sec z i)   = predSuc (ℤₕ→ℤ z) i
ℤₕ→ℤ (ret z i)   = sucPred (ℤₕ→ℤ z) i
ℤₕ→ℤ (coh z i j) = cohℤ (ℤₕ→ℤ z) i j

-- Converting Standard Integers to HIT Integers
ℤ→ℤₕ : ℤ → ℤₕ
ℤ→ℤₕ (pos zero)       = zero
ℤ→ℤₕ (pos (suc n))    = succ (ℤ→ℤₕ (pos n))
ℤ→ℤₕ (negsuc zero)    = pred zero
ℤ→ℤₕ (negsuc (suc n)) = pred (ℤ→ℤₕ (negsuc n))

-- Proof that converting Standard Integers to HIT Integers and back is equal to the initial value
ℤ→ℤₕ→ℤ : (z : ℤ) → ℤₕ→ℤ (ℤ→ℤₕ z) ≡ z
ℤ→ℤₕ→ℤ (pos zero)       = refl
ℤ→ℤₕ→ℤ (pos (suc n))    = cong sucℤ (ℤ→ℤₕ→ℤ (pos n))
ℤ→ℤₕ→ℤ (negsuc zero)    = refl
ℤ→ℤₕ→ℤ (negsuc (suc n)) = cong predℤ (ℤ→ℤₕ→ℤ (negsuc n))

ℤ→ℤₕ-sucℤ : (z : ℤ) → ℤ→ℤₕ (sucℤ z) ≡ succ (ℤ→ℤₕ z)
ℤ→ℤₕ-sucℤ (pos n)          = refl
ℤ→ℤₕ-sucℤ (negsuc zero)    = sym (ret (ℤ→ℤₕ (pos zero)))
ℤ→ℤₕ-sucℤ (negsuc (suc n)) = sym (ret (ℤ→ℤₕ (negsuc n)))

ℤ→ℤₕ-predℤ : (z : ℤ) → ℤ→ℤₕ (predℤ z) ≡ pred (ℤ→ℤₕ z)
ℤ→ℤₕ-predℤ (pos zero)    = refl
ℤ→ℤₕ-predℤ (pos (suc n)) = sym (sec (ℤ→ℤₕ (pos n)))
ℤ→ℤₕ-predℤ (negsuc n)    = refl

ℤ→ℤₕ-predSuc : (x : ℤ)
              → Square (ℤ→ℤₕ-predℤ (sucℤ x) ∙ (λ i → pred (ℤ→ℤₕ-sucℤ x i)))
                       (λ _ → ℤ→ℤₕ x)
                       (λ i → ℤ→ℤₕ (predSuc x i))
                       (sec (ℤ→ℤₕ x))
ℤ→ℤₕ-predSuc (pos n) i j
  = hcomp (λ k → λ { (j = i0) → ℤ→ℤₕ (pos n)
                   ; (i = i0) → rUnit (sym (sec (ℤ→ℤₕ (pos n)))) k j
                   ; (i = i1) → ℤ→ℤₕ (pos n)
                   ; (j = i1) → sec (ℤ→ℤₕ (pos n)) i
                   })
          (sym-filler (sec (ℤ→ℤₕ (pos n))) i j)
ℤ→ℤₕ-predSuc (negsuc zero) i j
  = hcomp (λ k → λ { (j = i0) → ℤ→ℤₕ (negsuc zero)
                   ; (i = i0) → lUnit (λ i → pred (sym (ret (ℤ→ℤₕ (pos zero))) i)) k j
                   ; (i = i1) → ℤ→ℤₕ (negsuc zero)
                   ; (j = i1) → hoc (ℤ→ℤₕ (pos zero)) k i
                   })
          (pred (sym-filler (ret (ℤ→ℤₕ (pos zero))) i j))
ℤ→ℤₕ-predSuc (negsuc (suc n)) i j
  = hcomp (λ k → λ { (j = i0) → ℤ→ℤₕ (negsuc (suc n))
                   ; (i = i0) → lUnit (λ i → pred (sym (ret (ℤ→ℤₕ (negsuc n))) i)) k j
                   ; (i = i1) → ℤ→ℤₕ (negsuc (suc n))
                   ; (j = i1) → hoc (ℤ→ℤₕ (negsuc n)) k i
                   })
          (pred (sym-filler (ret (ℤ→ℤₕ (negsuc n))) i j))

ℤ→ℤₕ-sucPred : (z : ℤ)
              → Square (ℤ→ℤₕ-sucℤ (predℤ z) ∙ (λ j → succ (ℤ→ℤₕ-predℤ z j)))
                       (λ _ → ℤ→ℤₕ z)
                       (λ i → ℤ→ℤₕ (sucPred z i))
                       (ret (ℤ→ℤₕ z))
ℤ→ℤₕ-sucPred (pos zero) i j =
  hcomp (λ k → λ { (j = i0) → ℤ→ℤₕ (pos zero)
                 ; (i = i0) → rUnit (sym (ret (ℤ→ℤₕ (pos zero)))) k j
                 ; (i = i1) → ℤ→ℤₕ (pos zero)
                 ; (j = i1) → ret (ℤ→ℤₕ (pos zero)) i
                 })
        (sym-filler (ret (ℤ→ℤₕ (pos zero))) i j)
ℤ→ℤₕ-sucPred (pos (suc n)) i j =
  hcomp (λ k → λ { (j = i0) → succ (ℤ→ℤₕ (pos n))
                 ; (i = i0) → lUnit (λ i → succ (sym (sec (ℤ→ℤₕ (pos n))) i)) k j
                 ; (i = i1) → succ (ℤ→ℤₕ (pos n))
                 ; (j = i1) → coh (ℤ→ℤₕ (pos n)) k i
                 })
        (succ (sym-filler (sec (ℤ→ℤₕ (pos n))) i j))
ℤ→ℤₕ-sucPred (negsuc n) i j =
  hcomp (λ k → λ { (j = i0) → ℤ→ℤₕ (negsuc n)
                 ; (i = i0) → rUnit (sym (ret (ℤ→ℤₕ (negsuc n)))) k j
                 ; (i = i1) → ℤ→ℤₕ (negsuc n)
                 ; (j = i1) → ret (ℤ→ℤₕ (negsuc n)) i
                 })
        (sym-filler (ret (ℤ→ℤₕ (negsuc n))) i j)

-- Proof that converting HIT Integers to and back is equal to the initial value
ℤₕ→ℤ→ℤₕ : (z : ℤₕ) → ℤ→ℤₕ (ℤₕ→ℤ z) ≡ z
ℤₕ→ℤ→ℤₕ zero        = refl
ℤₕ→ℤ→ℤₕ (succ z)    = ℤ→ℤₕ-sucℤ (ℤₕ→ℤ z) ∙ (λ i → succ (ℤₕ→ℤ→ℤₕ z i))
ℤₕ→ℤ→ℤₕ (pred z)    = ℤ→ℤₕ-predℤ (ℤₕ→ℤ z) ∙ (λ i → pred (ℤₕ→ℤ→ℤₕ z i))
ℤₕ→ℤ→ℤₕ (sec z i) j =
  hcomp (λ k → λ { (j = i0) → ℤ→ℤₕ (predSuc (ℤₕ→ℤ z) i)
                 ; (i = i0) → (ℤ→ℤₕ-predℤ (sucℤ (ℤₕ→ℤ z))
                              ∙ (λ i → pred (compPath-filler (ℤ→ℤₕ-sucℤ (ℤₕ→ℤ z))
                                                             (λ i' → succ (ℤₕ→ℤ→ℤₕ z i'))
                                                             k i))) j
                 ; (i = i1) → ℤₕ→ℤ→ℤₕ z (j ∧ k)
                 ; (j = i1) → sec (ℤₕ→ℤ→ℤₕ z k) i })
        (ℤ→ℤₕ-predSuc (ℤₕ→ℤ z) i j)
ℤₕ→ℤ→ℤₕ (ret z i) j =
  hcomp (λ k → λ { (j = i0) → ℤ→ℤₕ (sucPred (ℤₕ→ℤ z) i)
                 ; (i = i0) → (ℤ→ℤₕ-sucℤ (predℤ (ℤₕ→ℤ z))
                              ∙ (λ i → succ (compPath-filler (ℤ→ℤₕ-predℤ (ℤₕ→ℤ z))
                                                             (congS pred (ℤₕ→ℤ→ℤₕ z))
                                                             k i))) j
                 ; (i = i1) → ℤₕ→ℤ→ℤₕ z (j ∧ k)
                 ; (j = i1) → ret (ℤₕ→ℤ→ℤₕ z k) i  })
        (ℤ→ℤₕ-sucPred (ℤₕ→ℤ z) i j)
ℤₕ→ℤ→ℤₕ (coh z i j) k = {!  !}

-- Set truncation
ℤ-iso : Iso ℤ ℤₕ
ℤ-iso .Iso.fun      = ℤ→ℤₕ
ℤ-iso .Iso.inv      = ℤₕ→ℤ
ℤ-iso .Iso.rightInv = ℤₕ→ℤ→ℤₕ
ℤ-iso .Iso.leftInv  = ℤ→ℤₕ→ℤ

ℤ≡ℤₕ : ℤ ≡ ℤₕ
ℤ≡ℤₕ = isoToPath ℤ-iso

isSetℤₕ : isSet ℤₕ
isSetℤₕ = subst isSet ℤ≡ℤₕ isSetℤ
