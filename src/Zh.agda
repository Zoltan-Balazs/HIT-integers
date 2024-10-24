{-# OPTIONS --cubical #-}

open import Agda.Primitive
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Group
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Ring
open import Cubical.Algebra.Semigroup
open import Cubical.Data.Int.MoreInts.BiInvInt renaming (pred to predᵇ; _+_ to _+ᵇ_; _-_ to _-ᵇ_)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude renaming (congS to ap)
open import Cubical.HITs.PropositionalTruncation

-- Higher inductive type definition of ℤ
data ℤₕ : Set where
    zero : ℤₕ
    succ : ℤₕ → ℤₕ
    pred : ℤₕ → ℤₕ
    sec : (z : ℤₕ) → pred (succ z) ≡ z
    ret : (z : ℤₕ) → succ (pred z) ≡ z
    coh : (z : ℤₕ) → ap succ (sec z) ≡ ret (succ z)

open isHAEquiv
isHAℤₕ : isHAEquiv succ
isHAℤₕ .isHAEquiv.g    = pred
isHAℤₕ .isHAEquiv.linv = sec
isHAℤₕ .isHAEquiv.rinv = ret
isHAℤₕ .isHAEquiv.com  = coh

hoc : (z : ℤₕ) → ap pred (ret z) ≡ sec (pred z)
hoc = com-op isHAℤₕ
ℤₕ-to-BiInvℤ : ℤₕ → BiInvℤ
ℤₕ-to-BiInvℤ zero        = zero
ℤₕ-to-BiInvℤ (succ z)    = suc (ℤₕ-to-BiInvℤ z)
ℤₕ-to-BiInvℤ (pred z)    = predl (ℤₕ-to-BiInvℤ z)
ℤₕ-to-BiInvℤ (sec z i)   = predl-suc (ℤₕ-to-BiInvℤ z) i
ℤₕ-to-BiInvℤ (ret z i)   = suc-predl (ℤₕ-to-BiInvℤ z) i
ℤₕ-to-BiInvℤ (coh z i j) = isSetBiInvℤ
                (suc (predl (suc (ℤₕ-to-BiInvℤ z)))) 
                (suc (ℤₕ-to-BiInvℤ z))
                (ap suc (predl-suc (ℤₕ-to-BiInvℤ z))) 
                (suc-predl (suc (ℤₕ-to-BiInvℤ z)))
                i j

BiInvℤ-to-ℤₕ : BiInvℤ → ℤₕ
BiInvℤ-to-ℤₕ zero            = zero
BiInvℤ-to-ℤₕ (suc z)         = succ (BiInvℤ-to-ℤₕ z)
BiInvℤ-to-ℤₕ (predr z)       = pred (BiInvℤ-to-ℤₕ z)
BiInvℤ-to-ℤₕ (suc-predr z i) = ret (BiInvℤ-to-ℤₕ z) i
BiInvℤ-to-ℤₕ (predl z)       = pred (BiInvℤ-to-ℤₕ z)
BiInvℤ-to-ℤₕ (predl-suc z i) = sec (BiInvℤ-to-ℤₕ z) i

ℤₕ-BiInvℤ-ℤₕ : (z : ℤₕ) -> BiInvℤ-to-ℤₕ (ℤₕ-to-BiInvℤ z) ≡ z
ℤₕ-BiInvℤ-ℤₕ zero = refl
ℤₕ-BiInvℤ-ℤₕ (succ z) = ap succ (ℤₕ-BiInvℤ-ℤₕ z)
ℤₕ-BiInvℤ-ℤₕ (pred z) = ap pred (ℤₕ-BiInvℤ-ℤₕ z)
ℤₕ-BiInvℤ-ℤₕ (sec z i) = ap (λ k → sec k i) (ℤₕ-BiInvℤ-ℤₕ z)
ℤₕ-BiInvℤ-ℤₕ (ret z i) = {!  ap (λ k → ret k i) (ℤₕ-BiInvℤ-ℤₕ z) !}
ℤₕ-BiInvℤ-ℤₕ (coh z i j) = {! ap (λ k → coh k i j) (ℤₕ-BiInvℤ-ℤₕ z)  !}

BiInv-predl≡predr : predl ≡ predr
BiInv-predl≡predr = funExt predl≡predr

BiInvℤ-ℤₕ-BiInvℤ : (z : BiInvℤ) -> ℤₕ-to-BiInvℤ (BiInvℤ-to-ℤₕ z) ≡ z
BiInvℤ-ℤₕ-BiInvℤ zero = refl
BiInvℤ-ℤₕ-BiInvℤ (suc z) = ap suc (BiInvℤ-ℤₕ-BiInvℤ z)
BiInvℤ-ℤₕ-BiInvℤ (predr z) = ap (λ f → f (ℤₕ-to-BiInvℤ (BiInvℤ-to-ℤₕ z))) BiInv-predl≡predr ∙ ap predr (BiInvℤ-ℤₕ-BiInvℤ z)
BiInvℤ-ℤₕ-BiInvℤ (suc-predr z i) = {! ap (λ k → suc-predl≡predr k i) (BiInvℤ-ℤₕ-BiInvℤ z)  !}
BiInvℤ-ℤₕ-BiInvℤ (predl z) = ap predl (BiInvℤ-ℤₕ-BiInvℤ z)
BiInvℤ-ℤₕ-BiInvℤ (predl-suc z i) = ap (λ k → predl-suc k i) (BiInvℤ-ℤₕ-BiInvℤ z)

biinv-iso : Iso ℤₕ BiInvℤ
biinv-iso .Iso.fun      = ℤₕ-to-BiInvℤ
biinv-iso .Iso.inv      = BiInvℤ-to-ℤₕ
biinv-iso .Iso.rightInv = BiInvℤ-ℤₕ-BiInvℤ
biinv-iso .Iso.leftInv  = ℤₕ-BiInvℤ-ℤₕ

BiInvℤ≡ℤₕ : BiInvℤ ≡ ℤₕ
BiInvℤ≡ℤₕ = isoToPath (iso BiInvℤ-to-ℤₕ ℤₕ-to-BiInvℤ ℤₕ-BiInvℤ-ℤₕ BiInvℤ-ℤₕ-BiInvℤ)

isSetℤₕ : isSet ℤₕ
isSetℤₕ = subst isSet BiInvℤ≡ℤₕ isSetBiInvℤ

-- Operations of HIT Integers
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
zero      * b = zero
succ a    * b = a * b + b
pred a    * b = a * b - b
sec a i   * b = ((ℤₕ-add-is-assoc (a * b) b (negate b) ∙ ap (λ k → a * b + k) (ℤₕ-add-has-right-inv-elem b)) ∙ ℤₕ-add-right-id (a * b)) i
ret a i   * b = ((ℤₕ-add-is-assoc (a * b) (negate b) b ∙ ap (λ k → a * b + k) (ℤₕ-add-has-left-inv-elem b)) ∙ ℤₕ-add-right-id (a * b)) i
coh a i j * b = {! ((ℤₕ-add-is-assoc (a * b) b (negate b) ∙ ap (λ k → a * b + k) (ℤₕ-add-has-right-inv-elem b)) ∙ ℤₕ-add-right-id (a * b)) i!}

-- Is it a Monoid under multiplication?
ℤₕ-mul-is-assoc : (a b c : ℤₕ) → (a * b) * c ≡ a * (b * c)
ℤₕ-mul-is-assoc zero b c = refl
ℤₕ-mul-is-assoc (succ a) b c = {!   !}
ℤₕ-mul-is-assoc (pred a) b c = {!   !}
ℤₕ-mul-is-assoc (sec a i) b c = {!   !}
ℤₕ-mul-is-assoc (ret a i) b c = {!   !}
ℤₕ-mul-is-assoc (coh a i i₁) b c = {!   !}

-- Helping lemma for ℤₕ-mul-has-right-id-elem
ℤₕ-mul-right-id : (a : ℤₕ) → a * succ zero ≡ a
ℤₕ-mul-right-id zero = refl
ℤₕ-mul-right-id (succ a) = ap (λ k → k + succ zero) (ℤₕ-mul-right-id a) ∙ ℤₕ-add-is-comm a (succ zero)
ℤₕ-mul-right-id (pred a) = ap (λ k → k - succ zero) (ℤₕ-mul-right-id a) ∙ ℤₕ-add-is-comm a (pred zero)
ℤₕ-mul-right-id (sec a i) = {!  ap (λ k → sec k i) (ℤₕ-mul-right-id a) !}
ℤₕ-mul-right-id (ret a i) = {!   !}
ℤₕ-mul-right-id (coh a i i₁) = {!   !}

ℤₕ-mul-has-right-id-elem : ∃[ b ∈ ℤₕ ] ((a : ℤₕ) → a * b ≡ a)
ℤₕ-mul-has-right-id-elem = ∣ succ zero , ℤₕ-mul-right-id ∣₁

-- Helping lemma for ℤₕ-mul-has-left-id-elem
ℤₕ-mul-left-id : (a : ℤₕ) → succ zero * a ≡ a
ℤₕ-mul-left-id a = refl

ℤₕ-mul-has-left-id-elem : ∃[ b ∈ ℤₕ ] ((a : ℤₕ) → b * a ≡ a)
ℤₕ-mul-has-left-id-elem = ∣ succ zero , ℤₕ-mul-left-id ∣₁

isMonoidℤₕ* : IsMonoid {lzero} {ℤₕ} (succ zero) _*_
isMonoidℤₕ* .IsMonoid.isSemigroup .IsSemigroup.is-set = isSetℤₕ
isMonoidℤₕ* .IsMonoid.isSemigroup .IsSemigroup.·Assoc = λ x y z → sym (ℤₕ-mul-is-assoc x y z)
isMonoidℤₕ* .IsMonoid.·IdR = ℤₕ-mul-right-id
isMonoidℤₕ* .IsMonoid.·IdL = ℤₕ-mul-left-id

-- Is this multiplication distributive over addition?
ℤₕ-mul-is-right-dist-to-add : (a b c : ℤₕ) → a * (b + c) ≡ (a * b) + (a * c)
ℤₕ-mul-is-right-dist-to-add zero b c = refl
ℤₕ-mul-is-right-dist-to-add (succ a) b c = {!   !}
ℤₕ-mul-is-right-dist-to-add (pred a) b c = {!   !}
ℤₕ-mul-is-right-dist-to-add (sec a i) b c = {!   !}
ℤₕ-mul-is-right-dist-to-add (ret a i) b c = {!   !}
ℤₕ-mul-is-right-dist-to-add (coh a i j) b c = {!   !}

ℤₕ-mul-is-left-dist-to-add : (a b c : ℤₕ) → (a + b) * c ≡ (a * c) + (b * c)
ℤₕ-mul-is-left-dist-to-add a b zero = {!   !}
ℤₕ-mul-is-left-dist-to-add a b (succ c) = {!   !}
ℤₕ-mul-is-left-dist-to-add a b (pred c) = {!   !}
ℤₕ-mul-is-left-dist-to-add a b (sec c i) = {!   !}
ℤₕ-mul-is-left-dist-to-add a b (ret c i) = {!   !}
ℤₕ-mul-is-left-dist-to-add a b (coh c i j) = {!   !}

isRingℤₕ : IsRing {lzero} {ℤₕ} zero (succ zero) _+_ _*_ negate
isRingℤₕ .IsRing.+IsAbGroup = isAbGroupℤₕ+
isRingℤₕ .IsRing.·IsMonoid = isMonoidℤₕ*
isRingℤₕ .IsRing.·DistR+ = ℤₕ-mul-is-right-dist-to-add
isRingℤₕ .IsRing.·DistL+ = ℤₕ-mul-is-left-dist-to-add

-- Is multiplication commutative?
ℤₕ-mul-is-comm : (a : ℤₕ) → (b : ℤₕ) → a * b ≡ b * a
ℤₕ-mul-is-comm a b = {!   !}

isCommRingℤₕ : IsCommRing {lzero} {ℤₕ} zero (succ zero) _+_ _*_ negate
isCommRingℤₕ .IsCommRing.isRing = isRingℤₕ
isCommRingℤₕ .IsCommRing.·Comm = ℤₕ-mul-is-comm

-- Inductive type definition of ℤ
data ℤω : Set where
    zero : ℤω
    strpos : ℕ → ℤω
    strneg : ℕ → ℤω

succℤω : ℤω → ℤω
succℤω zero             = strpos zero
succℤω (strpos n)       = strpos (suc n)
succℤω (strneg zero)    = zero
succℤω (strneg (suc n)) = strneg n

predℤω : ℤω → ℤω
predℤω zero             = strneg zero
predℤω (strpos zero)    = zero
predℤω (strpos (suc n)) = strpos n
predℤω (strneg n)       = strneg (suc n)

secℤω : (z : ℤω) → predℤω (succℤω z) ≡ z
secℤω zero             = refl
secℤω (strpos n)       = refl
secℤω (strneg zero)    = refl
secℤω (strneg (suc n)) = refl

retℤω : (z : ℤω) → succℤω (predℤω z) ≡ z
retℤω zero             = refl
retℤω (strpos zero)    = refl
retℤω (strpos (suc n)) = refl
retℤω (strneg n)       = refl

cohℤω : (z : ℤω) → ap succℤω (secℤω z) ≡ retℤω (succℤω z)
cohℤω zero             = refl
cohℤω (strpos n)       = refl
cohℤω (strneg zero)    = refl
cohℤω (strneg (suc n)) = refl

-- Conversions between the two type definitions
ℤₕ-to-ℤω : ℤₕ → ℤω
ℤₕ-to-ℤω zero        = zero
ℤₕ-to-ℤω (succ n)    = succℤω (ℤₕ-to-ℤω n)
ℤₕ-to-ℤω (pred n)    = predℤω (ℤₕ-to-ℤω n)
ℤₕ-to-ℤω (sec n i)   = secℤω (ℤₕ-to-ℤω n) i
ℤₕ-to-ℤω (ret n i)   = retℤω (ℤₕ-to-ℤω n) i
ℤₕ-to-ℤω (coh n i j) = cohℤω (ℤₕ-to-ℤω n) i j

ℤω-to-ℤₕ : ℤω → ℤₕ
ℤω-to-ℤₕ zero             = zero
ℤω-to-ℤₕ (strpos zero)    = succ zero
ℤω-to-ℤₕ (strpos (suc n)) = succ (ℤω-to-ℤₕ (strpos n))
ℤω-to-ℤₕ (strneg zero)    = pred zero
ℤω-to-ℤₕ (strneg (suc n)) = pred (ℤω-to-ℤₕ (strneg n))
