module mynumber where

open import Data.Bool
open import Data.Integer as Int hiding (_≤?_) renaming (_≤_ to _≤ℤ_; suc to 1+)
open import Data.Nat as Nat renaming (_*_ to _ℕ*_; _+_ to _ℕ+_)
open import Data.Nat.Properties.Simple using (+-right-identity)
open import Data.Nat.Properties using (≤-step; ≤-steps; m≤m+n; n≤m+n; n≤1+n; 1+n≰n; ≤pred⇒≤; ≤⇒pred≤)
                                renaming (pred-mono to predℕ-mono; _+-mono_ to _ℕ+-mono_)
open import Data.Empty using (⊥-elim)
open import Data.Nat.DivMod
open import Data.Fin as Fin hiding (_+_; _-_; _≤_) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (inj₁; inj₂) renaming (_⊎_ to _∪_)
open import Data.Unit using (⊤;tt)
open import Data.Vec
open import Data.Product using (_,_) renaming (_×_ to _∩_)
open import Function using (_$_; _∘_)
open import Data.Sign renaming (+ to ⊕; - to ⊝)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality as PropEq

open import Relation.Binary
open DecTotalOrder Nat.decTotalOrder
 using () renaming (refl to ≤ℕ-refl; trans to ≤ℕ-trans; _≤?_ to _≤ℕ?_)

open DecTotalOrder Int.decTotalOrder
 using () renaming (refl to ≤ℤ-refl; trans to ≤ℤ-trans; _≤?_ to _≤ℤ?_)

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

+↔- : ℤ → ℤ
+↔- -[1+ n ] = + suc n
+↔- (+ zero) = + zero
+↔- (+ suc n) = -[1+ n ]

a≤b⇒c+a≤c+b : ∀ a b c → a ≤ b → c ℕ+ a ≤ c ℕ+ b
a≤b⇒c+a≤c+b a b zero a≤b = a≤b
a≤b⇒c+a≤c+b a b (suc c) a≤b = s≤s (a≤b⇒c+a≤c+b a b c a≤b)

a≤b⇒a+c≤b+c : ∀ a b c → a ≤ b → a ℕ+ c ≤ b ℕ+ c
a≤b⇒a+c≤b+c .0 b zero z≤n = z≤n
a≤b⇒a+c≤b+c .0 b (suc c) z≤n = n≤m+n b (suc c)
a≤b⇒a+c≤b+c ._ ._ c (s≤s a≤b) = s≤s (a≤b⇒a+c≤b+c _ _ c a≤b)

a≤b⇒a≤c+b : ∀ a b c → a ≤ b → a ≤ c ℕ+ b
a≤b⇒a≤c+b a b c = ≤-steps {a} {b} c

n≤m⇒-m≤-n : ∀ n m → + n  ≤ℤ + m → -[1+ m ] ≤ℤ -[1+ n ]
n≤m⇒-m≤-n n m (+≤+ m≤n) = -≤- m≤n

a≤b⇒a≤b+c : ∀ a b c → a ≤ b → a ≤ b ℕ+ c
a≤b⇒a≤b+c a b c a≤b = ≤ℕ-trans a≤b (m≤m+n b c)

x-y≤z→x≤y+z : ∀ x y z → + x - + y ≤ℤ + z → + x ≤ℤ + y + + z
x-y≤z→x≤y+z x zero z (+≤+ m≤n) = +≤+ (x+0≤z→x≤z m≤n)
  where
    x+0≤z→x≤z : ∀ {x z} → x ℕ+ 0 ≤ z → x ≤ z
    x+0≤z→x≤z {zero} p = z≤n
    x+0≤z→x≤z {suc x₁} {zero} ()
    x+0≤z→x≤z {suc x₁} {suc z₁} (s≤s p) = s≤s (x+0≤z→x≤z p)
x-y≤z→x≤y+z zero (suc y) z p = +≤+ z≤n
x-y≤z→x≤y+z (suc x) (suc y) z p with x ≤? y
x-y≤z→x≤y+z (suc .0) (suc y) z p | yes z≤n = +≤+ (s≤s z≤n)
x-y≤z→x≤y+z (suc ._) (suc ._) z p | yes (s≤s q) = +≤+ (s≤s (s≤s (a≤b⇒a≤b+c _ _ z q)))
... | no ¬q = +≤+ (s≤s (x⊝y≤z→x≤y+z x y z ¬q p))
  where
    ¬Sx≤Sy→¬x≤y : ∀ x y → ¬ suc x ≤ suc y → ¬ x ≤ y
    ¬Sx≤Sy→¬x≤y zero zero p₁ x₁ = p₁ (s≤s z≤n)
    ¬Sx≤Sy→¬x≤y zero (suc zero) p₁ z≤n = p₁ (s≤s z≤n)
    ¬Sx≤Sy→¬x≤y zero (suc (suc y₁)) p₁ z≤n = p₁ (s≤s z≤n)
    ¬Sx≤Sy→¬x≤y (suc x₁) y₁ p₁ x₂ = p₁ (s≤s x₂)
    x⊝y≤z→x≤y+z : ∀ x y z → ¬ x ≤ y → x ⊖ y ≤ℤ + z → x ≤ y ℕ+ z
    x⊝y≤z→x≤y+z zero y₁ z₁ ¬q₁ p₁ = z≤n
    x⊝y≤z→x≤y+z (suc x₁) zero z₁ ¬q₁ (+≤+ m≤n) = m≤n
    x⊝y≤z→x≤y+z (suc x₁) (suc y₁) z₁ ¬q₁ p₁ = s≤s (x⊝y≤z→x≤y+z x₁ y₁ z₁ (¬Sx≤Sy→¬x≤y x₁ y₁ ¬q₁) p₁)

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
        0≤11-r-1 : (r : Fin 11) → + 0 ≤ℤ + 11 - + toℕ r + -[1+ 0 ]
        0≤11-r-1 fzero = +≤+ z≤n
        0≤11-r-1 (fsuc fzero) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc fzero)) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc (fsuc fzero))) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc (fsuc (fsuc fzero)))) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = +≤+ z≤n
        0≤11-r-1 (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
        -10≤11-r-1 : (r : Fin 11) → + 2 ≤ℤ + toℕ r → -[1+ 9 ] ≤ℤ + 11 + - (+ toℕ r) + -[1+ 0 ]
        -10≤11-r-1 r 2≤r = ≤ℤ-trans -≤+ (0≤11-r-1 r)
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