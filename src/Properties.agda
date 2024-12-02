{-# OPTIONS --cubical --allow-unsolved-metas #-}
module Properties where

open import Agda.Primitive

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Semigroup

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude

open isHAEquiv

open import Base

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
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh zero        = P-zero
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh (succ z)    = P-succ z (ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh z)
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh (pred z)    = P-pred z (ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh z)
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh (sec z i)   = P-sec z (ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh z) i
ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh (ret z i)   = P-ret z (ℤₕ-ind P-zero P-succ P-pred P-sec P-ret P-coh z) i
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

-- Addition and its properties
-- Definitionally the following hold true for addition:
-- zero   + n = n
-- succ m + n = succ (m + n)
-- pred m + n = pred (m + n)
succIso : Iso ℤₕ ℤₕ
succIso .Iso.fun      = succ
succIso .Iso.inv      = pred
succIso .Iso.rightInv = ret
succIso .Iso.leftInv  = sec

succEquiv : ℤₕ ≃ ℤₕ
succEquiv = isoToEquiv succIso

infixl 6 _+_ _-_
infixl 7 _*_

_+_ : ℤₕ → ℤₕ → ℤₕ
_+_ = ℤₕ-ite (idfun ℤₕ) (postCompEquiv succEquiv)
-- m + n = (ℤₕ-ite (idfun ℤₕ) (postCompEquiv succEquiv) m) n

+-zero : ∀ z → z + zero ≡ z
+-zero = ℤₕ-ind-prop
  (λ _ → isSetℤₕ _ _)
  refl
  (λ z p → cong succ p)
  (λ z p → cong pred p)

+-succ : ∀ m n → m + succ n ≡ succ (m + n)
+-succ = ℤₕ-ind-prop
  (λ _ → isPropΠ λ _ → isSetℤₕ _ _)
  (λ m → refl)
  (λ m p n → cong succ (p n))
  (λ m p n → cong pred (p n)
             ∙
             sec (m + n)
             ∙
             sym (ret (m + n)))

+-pred : ∀ m n → m + pred n ≡ pred (m + n)
+-pred = ℤₕ-ind-prop
  (λ _ → isPropΠ λ _ → isSetℤₕ _ _)
  (λ m → refl)
  (λ m p n → cong succ (p n)
             ∙
             ret (m + n)
             ∙
             sym (sec (m + n)))
  (λ m p n → cong pred (p n))

+-comm : ∀ m n → m + n ≡ n + m
+-comm = ℤₕ-ind-prop
  (λ _ → isPropΠ λ _ → isSetℤₕ _ _)
  (λ n → sym (+-idʳ n))
  (λ m p n → sym (+-succ m n)
             ∙
             p (succ n)
             ∙
             sym (+-succ n m))
  (λ m p n → sym (+-pred m n)
             ∙
             p (pred n)
             ∙
             sym (+-pred n m))

+-assoc : ∀ m n o → m + (n + o) ≡ (m + n) + o
+-assoc = ℤₕ-ind-prop
  (λ _ → isPropΠ2 λ _ _ → isSetℤₕ _ _)
  (λ n o → refl)
  (λ m p n o → cong succ (p n o))
  (λ m p n o → cong pred (p n o))

-- Negation
-- Definitionally the following hold true for negation:
-- - zero     = zero
-- - (succ m) = pred (- m)
-- - (pred m) = succ (- m)
-_ : ℤₕ → ℤₕ
-_ = ℤₕ-ite zero (invEquiv succEquiv)
-- - n = ℤₕ-ite zero (invEquiv succEquiv) n

_-_ : ℤₕ → ℤₕ → ℤₕ
m - n = m + (- n)

+-idˡ : ∀ z → zero + z ≡ z
+-idˡ z = refl

+-idʳ : ∀ z → z + zero ≡ z
+-idʳ = +-zero

+-invˡ : ∀ z → (- z) + z ≡ zero
+-invˡ = ℤₕ-ind-prop
  (λ _ → isSetℤₕ _ _)
  refl
  (λ z p → cong pred (+-succ (- z) z)
                      ∙
                      sec _
                      ∙
                      p)
  (λ z p → cong succ (+-pred (- z) z)
                      ∙
                      ret _
                      ∙
                      p)

+-invʳ : ∀ z → z + (- z) ≡ zero
+-invʳ = ℤₕ-ind-prop
  (λ _ → isSetℤₕ _ _)
  refl
  (λ z p → cong succ (+-pred z (- z))
                      ∙
                      ret _
                      ∙
                      p)
  (λ z p → cong pred (+-succ z (- z))
                      ∙
                      sec _
                      ∙
                      p)

inv-hom-ℤₕ : ∀ m n → - (m + n) ≡ (- m) + (- n)
inv-hom-ℤₕ = ℤₕ-ind-prop
  (λ _ → isPropΠ λ _ → isSetℤₕ _ _)
  (λ n → refl)
  (λ m p n → cong pred (p n))
  (λ m p n → cong succ (p n))

Iso-n+-ℤₕ : (z : ℤₕ) → Iso ℤₕ ℤₕ
Iso.fun (Iso-n+-ℤₕ z) = z +_
Iso.inv (Iso-n+-ℤₕ z) = - z +_
Iso.rightInv (Iso-n+-ℤₕ n) m =
  +-assoc n (- n) m
  ∙
  cong (_+ m) (+-invʳ n)
Iso.leftInv (Iso-n+-ℤₕ n) m =
  +-assoc (- n) n m
  ∙
  cong (_+ m) (+-invˡ n)

isEquiv-n+-ℤₕ : ∀ z → isEquiv (z +_)
isEquiv-n+-ℤₕ z = isoToIsEquiv (Iso-n+-ℤₕ z)

_*_ : ℤₕ → ℤₕ → ℤₕ
m * n = ℤₕ-ite zero (n +_ , isEquiv-n+-ℤₕ n) m

*-zero : ∀ z → z * zero ≡ zero
*-zero = ℤₕ-ind-prop
  (λ - → isSetℤₕ _ _)
  refl
  (λ z p → p)
  (λ z p → p)

*-succ : ∀ m n → m * succ n ≡ m + m * n
*-succ = ℤₕ-ind-prop
  (λ _ → isPropΠ λ _ → isSetℤₕ _ _)
  (λ n → refl)
  (λ m p n → cong succ
    (cong (n +_) (p n)
    ∙
    +-assoc n m (m * n)
    ∙
    cong (_+ m * n) (+-comm n m)
    ∙
    sym (+-assoc m n (m * n))))
  (λ m p n → cong pred
    (cong (- n +_) (p n)
    ∙
    +-assoc (- n) m (m * n)
    ∙
    cong (_+ m * n) (+-comm (- n) m)
    ∙
    sym (+-assoc m (- n) (m * n))))

*-pred : ∀ m n → m * pred n ≡ (- m) + m * n
*-pred = ℤₕ-ind-prop
  (λ _ → isPropΠ λ _ → isSetℤₕ _ _)
  (λ n → refl)
  (λ m p n → cong pred
    (cong (n +_) (p n)
    ∙
    +-assoc n (- m) (m * n)
    ∙
    cong (_+ m * n) (+-comm n (- m))
    ∙
    sym (+-assoc (- m) n (m * n))))
  (λ m p n → cong succ
    (cong (- n +_) (p n)
    ∙
    +-assoc (- n) (- m) (m * n)
    ∙
    cong (_+ m * n) (+-comm (- n) (- m))
    ∙
    sym (+-assoc (- m) (- n) (m * n))))

*-comm : ∀ m n → m * n ≡ n * m
*-comm = ℤₕ-ind-prop
  (λ _ → isPropΠ λ _ → isSetℤₕ _ _)
  (λ n → sym (*-zero n))
  (λ m p n → cong (n +_) (p n)
             ∙
             sym (*-succ n m))
  (λ m p n → cong (- n +_) (p n)
             ∙
             sym (*-pred n m))

*-idˡ : ∀ z → succ zero * z ≡ z
*-idˡ = +-zero

*-idʳ : ∀ z → z * succ zero ≡ z
*-idʳ z =
  *-comm z (succ zero)
  ∙
  *-idˡ z

*-distribʳ-+ : ∀ m n o → (m * o) + (n * o) ≡ (m + n) * o
*-distribʳ-+ = ℤₕ-ind-prop
  (λ _ → isPropΠ2 λ _ _ → isSetℤₕ _ _)
  (λ n o → refl)
  (λ m p n o → sym (+-assoc o (m * o) (n * o))
               ∙
               cong (o +_) (p n o))
  (λ m p n o → sym (+-assoc (- o) (m * o) (n * o))
               ∙
               cong (- o +_) (p n o))

*-distribˡ-+ : ∀ o m n → (o * m) + (o * n) ≡ o * (m + n)
*-distribˡ-+ o m n =
  cong (_+ o * n) (*-comm o m)
  ∙
  cong (m * o +_) (*-comm o n)
  ∙
  *-distribʳ-+ m n o
  ∙
  *-comm (m + n) o

*-inv : ∀ m n → m * (- n) ≡ - (m * n)
*-inv = ℤₕ-ind-prop
  (λ _ → isPropΠ λ _ → isSetℤₕ _ _)
  (λ n → refl)
  (λ m p n → cong (- n +_) (p n)
             ∙
             sym (inv-hom-ℤₕ n (m * n)))
  (λ m p n → cong (- (- n) +_) (p n)
             ∙
             sym (inv-hom-ℤₕ (- n) (m * n)))

inv-* : ∀ m n → (- m) * n ≡ - (m * n)
inv-* m n =
  *-comm (- m) n
  ∙
  *-inv n m
  ∙
  cong (-_) (*-comm n m)

*-assoc : ∀ m n o → m * (n * o) ≡ (m * n) * o
*-assoc = ℤₕ-ind-prop
  (λ _ → isPropΠ2 λ _ _ → isSetℤₕ _ _)
  (λ n o → refl)
  (λ m p n o →
    cong (n * o +_) (p n o)
    ∙
    *-distribʳ-+ n (m * n) o)
  (λ m p n o →
    cong (- (n * o) +_) (p n o)
    ∙
    cong (_+ m * n * o) (sym (inv-* n o))
    ∙
    *-distribʳ-+ (- n) (m * n) o)

AbGroupℤₕ+ : IsAbGroup {lzero} {ℤₕ} zero _+_ (-_)
AbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set = isSetℤₕ
AbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.isMonoid .IsMonoid.isSemigroup .IsSemigroup.·Assoc = +-assoc
AbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.isMonoid .IsMonoid.·IdR = +-idʳ
AbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.isMonoid .IsMonoid.·IdL = +-idˡ
AbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.·InvR = +-invʳ
AbGroupℤₕ+ .IsAbGroup.isGroup .IsGroup.·InvL = +-invˡ
AbGroupℤₕ+ .IsAbGroup.+Comm = +-comm

Monoidℤₕ* : IsMonoid {lzero} {ℤₕ} (succ zero) _*_
Monoidℤₕ* .IsMonoid.isSemigroup .IsSemigroup.is-set = isSetℤₕ
Monoidℤₕ* .IsMonoid.isSemigroup .IsSemigroup.·Assoc = *-assoc
Monoidℤₕ* .IsMonoid.·IdR = *-idʳ
Monoidℤₕ* .IsMonoid.·IdL = *-idˡ

Ringℤₕ*+ : IsRing {lzero} {ℤₕ} zero (succ zero) _+_ _*_ (-_)
Ringℤₕ*+ .IsRing.+IsAbGroup = AbGroupℤₕ+
Ringℤₕ*+ .IsRing.·IsMonoid = Monoidℤₕ*
Ringℤₕ*+ .IsRing.·DistR+ = λ m n o → sym (*-distribˡ-+ m n o)
Ringℤₕ*+ .IsRing.·DistL+ = λ m n o → sym (*-distribʳ-+ m n o)

CommRingℤₕ*+ : IsCommRing {lzero} {ℤₕ} zero (succ zero) _+_ _*_ (-_)
CommRingℤₕ*+ .IsCommRing.isRing = Ringℤₕ*+
CommRingℤₕ*+ .IsCommRing.·Comm = *-comm
