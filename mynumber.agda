module mynumber where

open import Data.Integer as Int hiding (_≤?_) renaming (_≤_ to _≤ℤ_; suc to 1+)
open import Data.Nat as Nat renaming (_*_ to _ℕ*_; _+_ to _ℕ+_)
open import Data.Nat.Properties.Simple using (+-right-identity)
open import Data.Nat.Properties using (≤-steps; m≤m+n; n≤m+n)
open import Data.Nat.DivMod
open import Data.Fin as Fin hiding (_+_; _-_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _∪_)
open import Data.Vec
open import Data.Product using (_,_; ∃) renaming (_×_ to _∩_)
open import Function using (_$_; _∘_)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as PropEq

open import Relation.Binary
open DecTotalOrder Nat.decTotalOrder
 using () renaming (trans to ≤ℕ-trans)

open DecTotalOrder Int.decTotalOrder
 using () renaming (trans to ≤ℤ-trans)

Num = Fin 10
CD = Num

MyNumber = Vec Num 11

test1 : MyNumber
test1 = # 1 ∷ # 2 ∷ # 3 ∷ # 4 ∷ # 5 ∷ # 6 ∷ # 7 ∷ # 8 ∷ # 9 ∷ # 0 ∷ # 1 ∷ []

test2 : MyNumber
test2 = # 0 ∷ # 2 ∷ # 3 ∷ # 4 ∷ # 5 ∷ # 6 ∷ # 7 ∷ # 8 ∷ # 9 ∷ # 0 ∷ # 1 ∷ []

lemma₁ : ∀ n m → (-[1+ m ] ≤ℤ n - + 1) ∩ n ≤ℤ + m → suc ∣ n ∣ ≤ suc m
lemma₁ -[1+ n ] m (-≤- n≤m , -≤+) = s≤s (sub (cong suc (+-right-identity n)) n≤m)
  where
    sub : ∀ {a b c} → a ≡ b → a ≤ c → b ≤ c
    sub refl a≤c = a≤c
lemma₁ (+ n) m (proj₁ , proj₂) = s≤s (drop‿+≤+ proj₂)

a≤b⇒a+c≤b+c : ∀ a b c → a ≤ b → a ℕ+ c ≤ b ℕ+ c
a≤b⇒a+c≤b+c .0 b zero z≤n = z≤n
a≤b⇒a+c≤b+c .0 b (suc c) z≤n = n≤m+n b (suc c)
a≤b⇒a+c≤b+c ._ ._ c (s≤s a≤b) = s≤s (a≤b⇒a+c≤b+c _ _ c a≤b)

x≤y+z→x-y≤z : ∀ x y z → + x ≤ℤ + y + + z → + x - + y ≤ℤ + z
x≤y+z→x-y≤z x zero z (+≤+ m≤n) = x≤z→x-0≤z m≤n
  where
    x≤z→x+0≤z : ∀ x z → x ≤ z → x ℕ+ 0 ≤ z
    x≤z→x+0≤z zero z₁ p = z≤n
    x≤z→x+0≤z (suc x₁) zero ()
    x≤z→x+0≤z (suc x₁) (suc z₁) (s≤s p) = s≤s (x≤z→x+0≤z x₁ z₁ p)
    x+0≤z→x≤z : ∀ x z → x ℕ+ 0 ≤ z → x ≤ z
    x+0≤z→x≤z zero z₁ p = z≤n
    x+0≤z→x≤z (suc x₁) zero ()
    x+0≤z→x≤z (suc x₁) (suc z₁) (s≤s p) = s≤s (x+0≤z→x≤z x₁ z₁ p)
    x-0≤z→Sx-0≤Sz : ∀ x z → + x - + 0 ≤ℤ + z → + suc x - + 0 ≤ℤ + suc z
    x-0≤z→Sx-0≤Sz zero zero p = +≤+ (s≤s z≤n)
    x-0≤z→Sx-0≤Sz (suc x₁) zero (+≤+ ())
    x-0≤z→Sx-0≤Sz zero (suc z₁) p = +≤+ (s≤s z≤n)
    x-0≤z→Sx-0≤Sz (suc x₁) (suc z₁) (+≤+ (s≤s m≤n)) with x+0≤z→x≤z x₁ z₁ m≤n
    x-0≤z→Sx-0≤Sz (suc .0) (suc z₁) (+≤+ (s≤s m≤n₁)) | z≤n = +≤+ (s≤s (s≤s z≤n))
    x-0≤z→Sx-0≤Sz (suc ._) (suc ._) (+≤+ (s≤s m≤n₁)) | s≤s q = +≤+ (s≤s (s≤s (s≤s (x≤z→x+0≤z _ _ q))))
    x≤z→x-0≤z : ∀ {x z} → x ≤ z → + x - + 0 ≤ℤ + z
    x≤z→x-0≤z {zero} p = +≤+ z≤n
    x≤z→x-0≤z {suc x₁} {zero} ()
    x≤z→x-0≤z {suc x₁} {suc z₁} (s≤s p) = x-0≤z→Sx-0≤Sz x₁ z₁ (x≤z→x-0≤z p)
x≤y+z→x-y≤z zero (suc y) z p = -≤+
x≤y+z→x-y≤z (suc x) (suc y) z (+≤+ (s≤s m≤n)) with x ≤? y
... | yes q = x≤y→x⊝y≤z x y z q
  where
    x≤y→x⊝y≤z : ∀ x y z → x ≤ y → x ⊖ y ≤ℤ + z
    x≤y→x⊝y≤z .0 zero z₁ z≤n = +≤+ z≤n
    x≤y→x⊝y≤z .0 (suc y₁) z₁ z≤n = -≤+
    x≤y→x⊝y≤z ._ ._ z₁ (s≤s p) = x≤y→x⊝y≤z _ _ z₁ p
... | no ¬q = x≤y+z→x⊝y≤z x y z ¬q m≤n
  where
    0⊝y≤z : ∀ y₁ z₁ → 0 ⊖ y₁ ≤ℤ + z₁
    0⊝y≤z zero z₁ = +≤+ z≤n
    0⊝y≤z (suc y₁) z₁ = -≤+
    ¬Sx≤Sy→¬x≤y : ∀ x₁ y₁ → ¬ suc x₁ ≤ suc y₁ → ¬ x₁ ≤ y₁
    ¬Sx≤Sy→¬x≤y zero y₁ p z≤n = p (s≤s z≤n)
    ¬Sx≤Sy→¬x≤y (suc x₁) zero p ()
    ¬Sx≤Sy→¬x≤y (suc x₁) (suc y₁) p (s≤s x₂) = p (s≤s (s≤s x₂))
    x≤y+z→x⊝y≤z : ∀ x y z → ¬ x ≤ y → x ≤ y ℕ+ z → x ⊖ y ≤ℤ + z
    x≤y+z→x⊝y≤z zero y₁ z₁ ¬q₁ z≤n = 0⊝y≤z y₁ z₁
    x≤y+z→x⊝y≤z (suc x₁) zero z₁ ¬q₁ p = +≤+ p
    x≤y+z→x⊝y≤z (suc x₁) (suc y₁) z₁ ¬q₁ (s≤s p) = x≤y+z→x⊝y≤z x₁ y₁ z₁ (¬Sx≤Sy→¬x≤y x₁ y₁ ¬q₁) p

calcCD : MyNumber → CD
calcCD = magic ∘ acc
  where
    ms : Vec ℕ 11
    ms = 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ 7 ∷ 6 ∷ 5 ∷ 4 ∷ 3 ∷ 2 ∷ []
    acc : MyNumber → ℕ
    acc ns = sum $ zipWith (λ x y → toℕ x ℕ* y) ns ms
    prf : (r : Fin 11) → (p : 2 ≤ toℕ r) → True (suc ∣ + 11 - + toℕ r ∣ ≤? 10)
    prf r 2≤r = fromWitness $ lemma₁ (+ 11 - + toℕ r) 9 (-10≤11-r-1 r (+≤+ 2≤r) , 11-r≤9 r (+≤+ 2≤r))
      where
        11≤r+9 : (r : Fin 11) → + 2 ≤ℤ + toℕ r → 11 ≤ toℕ r ℕ+ 9
        11≤r+9 r₁ (+≤+ m≤n) = a≤b⇒a+c≤b+c _ _ 9 m≤n
        11-r≤9 : (r : Fin 11) → + 2 ≤ℤ + toℕ r → + 11 - (+ toℕ r) ≤ℤ + 9
        11-r≤9 r 2≤r = x≤y+z→x-y≤z 11 (toℕ r) 9 (+≤+ (11≤r+9 r 2≤r))
        0≤x-y-1→0≤Sx-Sy-1 : ∀ x y → + 0 ≤ℤ + x + - (+ y) + -[1+ 0 ] → + 0 ≤ℤ x ⊖ y + -[1+ 0 ]
        0≤x-y-1→0≤Sx-Sy-1 zero zero ()
        0≤x-y-1→0≤Sx-Sy-1 (suc x) zero p = +≤+ z≤n
        0≤x-y-1→0≤Sx-Sy-1 x (suc y) p = p
        0≤n-r-1 : ∀ n → (r : Fin n) → + 0 ≤ℤ + n - + toℕ r + -[1+ 0 ]
        0≤n-r-1 zero ()
        0≤n-r-1 (suc n) fzero = +≤+ z≤n
        0≤n-r-1 (suc n) (fsuc r) = 0≤x-y-1→0≤Sx-Sy-1 n (toℕ r) (0≤n-r-1 n r)
        -10≤11-r-1 : (r : Fin 11) → + 2 ≤ℤ + toℕ r → -[1+ 9 ] ≤ℤ + 11 + - (+ toℕ r) + -[1+ 0 ]
        -10≤11-r-1 r 2≤r = ≤ℤ-trans -≤+ (0≤n-r-1 11 r)
    magic : ℕ → CD
    magic x with x mod 11
    magic x | fzero = fzero
    magic x | fsuc fzero = fzero
    magic x | fsuc (fsuc r)
      = (# ∣ + 11 - + toℕ (fsuc (fsuc r)) ∣) {n = 10} {m<n = prf (fsuc (fsuc r)) (s≤s (s≤s z≤n))}

data ValidMyNumber : MyNumber → CD → Set where
  valid : ∀ {n11} → ValidMyNumber n11 (calcCD n11)

myMN1 : ValidMyNumber test1 (# 8)
myMN1 = valid

myMN2 : ValidMyNumber test2 (# 3)
myMN2 = valid

-- Properties
totality : (n : MyNumber) → ∃ λ cd → ValidMyNumber n cd
totality n = calcCD n , valid

unique : ∀ n x y → ValidMyNumber n x → ValidMyNumber n y → x ≡ y
unique n ._ ._ valid valid = refl

