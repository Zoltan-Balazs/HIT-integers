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

ℤₕ-ℤ : ℤₕ → ℤ
ℤₕ-ℤ zero        = pos zero
ℤₕ-ℤ (succ x)    = sucℤ (ℤₕ-ℤ x)
ℤₕ-ℤ (pred x)    = predℤ (ℤₕ-ℤ x)
ℤₕ-ℤ (sec x i)   = predSuc (ℤₕ-ℤ x) i
ℤₕ-ℤ (ret x i)   = sucPred (ℤₕ-ℤ x) i
ℤₕ-ℤ (coh x i j) = isSetℤ
  (sucℤ (predℤ (sucℤ (ℤₕ-ℤ x))))
  (sucℤ (ℤₕ-ℤ x))
  (congS sucℤ (predSuc (ℤₕ-ℤ x)))
  (sucPred (sucℤ (ℤₕ-ℤ x)))
  i j

ℤ-ℤₕ : ℤ → ℤₕ
ℤ-ℤₕ (pos zero)       = zero
ℤ-ℤₕ (pos (suc n))    = succ (ℤ-ℤₕ (pos n))
ℤ-ℤₕ (negsuc zero)    = pred zero
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

ℤ-iso : Iso ℤ ℤₕ
ℤ-iso .Iso.fun      = ℤ-ℤₕ
ℤ-iso .Iso.inv      = ℤₕ-ℤ
ℤ-iso .Iso.rightInv = ℤₕ-ℤ-ℤₕ
ℤ-iso .Iso.leftInv  = ℤ-ℤₕ-ℤ

isSetℤₕ : isSet ℤₕ
isSetℤₕ = subst isSet (isoToPath (ℤ-iso)) isSetℤ
