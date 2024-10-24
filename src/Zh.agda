{-# OPTIONS --cubical #-}

open import Cubical.Data.Int.MoreInts.BiInvInt renaming (pred to predᵇ; _+_ to _+ᵇ_; _-_ to _-ᵇ_)
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

-- Properties needed for HIT Integers to form a Commutative Ring
-- Is it an Abelian Group under addition?
ℤₕ-add-is-assoc : (a : ℤₕ) → (b : ℤₕ) → (c : ℤₕ) → (a + b) + c ≡ a + (b + c)
ℤₕ-add-is-assoc a b c = {!   !}

-- ℤₕ-add-has-id-elem :
-- ℤₕ-add-has-inv-elem :

ℤₕ-add-is-comm : (a : ℤₕ) → (b : ℤₕ) → a + b ≡ b + a
ℤₕ-add-is-comm a b = {!   !}

-- Is it a Monoid under multiplication?
ℤₕ-mul-is-assoc : (a : ℤₕ) → (b : ℤₕ) → (c : ℤₕ) → (a * b) * c ≡ a * (b * c)
ℤₕ-mul-is-assoc a b c = {!   !}

-- ℤₕ-mul-has-id-elem :

-- Is this multiplication distributive over addition?
ℤₕ-mul-is-dist-to-add : (a : ℤₕ) → (b : ℤₕ) → (c : ℤₕ) → a * (b + c) ≡ (a * b) + (a * c)
ℤₕ-mul-is-dist-to-add a b c = {!   !}

-- Is multiplication commutative?
ℤₕ-mul-is-comm : (a : ℤₕ) → (b : ℤₕ) → a * b ≡ b * a
ℤₕ-mul-is-comm a b = {!   !}

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
