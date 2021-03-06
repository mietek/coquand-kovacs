module Prelude where


--------------------------------------------------------------------------------


open import Agda.Primitive public
  using (Level ; _⊔_)
  renaming (lzero to ℓ₀)


id : ∀ {ℓ} → {X : Set ℓ}
           → X → X
id x = x

_◎_ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {P : X → Set ℓ′} {Q : ∀ {x} → P x → Set ℓ″}
                  → (g : ∀ {x} → (y : P x) → Q y) (f : (x : X) → P x) (x : X)
                  → Q (f x)
(g ◎ f) x = g (f x)

const : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                 → X → Y → X
const x y = x

flip : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : X → Y → Set ℓ″}
                   → (f : (x : X) (y : Y) → Z x y) (y : Y) (x : X)
                   → Z x y
flip f y x = f x y

_∘_ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″}
                  → (g : Y → Z) (f : X → Y)
                  → X → Z
g ∘ f = g ◎ f

_⨾_ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″}
                  → (f : X → Y) (g : Y → Z)
                  → X → Z
_⨾_ = flip _∘_


--------------------------------------------------------------------------------


open import Agda.Builtin.Equality public
  using (_≡_ ; refl)


_⁻¹≡ : ∀ {ℓ} → {X : Set ℓ} {x₁ x₂ : X}
             → x₁ ≡ x₂ → x₂ ≡ x₁
refl ⁻¹≡ = refl

_⦙≡_ : ∀ {ℓ} → {X : Set ℓ} {x₁ x₂ x₃ : X}
             → x₁ ≡ x₂ → x₂ ≡ x₃ → x₁ ≡ x₃
refl ⦙≡ refl = refl


record PER {ℓ}
           (X : Set ℓ)
           (_≈_ : X → X → Set ℓ)
         : Set ℓ where
  infix  9 _⁻¹
  infixr 4 _⦙_
  field
    _⁻¹ : ∀ {x₁ x₂} → x₁ ≈ x₂
                    → x₂ ≈ x₁

    _⦙_ : ∀ {x₁ x₂ x₃} → x₁ ≈ x₂ → x₂ ≈ x₃
                       → x₁ ≈ x₃

open PER {{…}} public

instance
  per≡ : ∀ {ℓ} {X : Set ℓ} → PER X _≡_
  per≡ =
    record
      { _⁻¹ = _⁻¹≡
      ; _⦙_ = _⦙≡_
      }


infixl 9 _&_
_&_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {x₁ x₂ : X}
               → (f : X → Y) → x₁ ≡ x₂
               → f x₁ ≡ f x₂
f & refl = refl

infixl 8 _⊗_
_⊗_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {f₁ f₂ : X → Y} {x₁ x₂ : X}
               → f₁ ≡ f₂ → x₁ ≡ x₂
               → f₁ x₁ ≡ f₂ x₂
refl ⊗ refl = refl


case_of_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                    → X → (X → Y) → Y
case x of f = f x

coe : ∀ {ℓ} → {X Y : Set ℓ}
            → X ≡ Y → X → Y
coe refl x = x


postulate
  fext! : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′} {f₁ f₂ : (x : X) → P x}
                   → ((x : X) → f₁ x ≡ f₂ x)
                   → f₁ ≡ f₂

  fext¡ : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′} {f₁ f₂ : {x : X} → P x}
                   → ({x : X} → f₁ {x} ≡ f₂ {x})
                   → (λ {x} → f₁ {x}) ≡ (λ {x} → f₂ {x})


--------------------------------------------------------------------------------


open import Agda.Builtin.Unit public
  using (⊤ ; tt)


data ⊥ : Set where

elim⊥ : ∀ {ℓ} → {X : Set ℓ}
               → ⊥ → X
elim⊥ ()

¬_ : ∀ {ℓ} → Set ℓ → Set ℓ
¬ X = X → ⊥


Π : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
Π X Y = X → Y


infixl 6 _,_
record Σ {ℓ ℓ′}
         (X : Set ℓ) (P : X → Set ℓ′)
       : Set (ℓ ⊔ ℓ′) where
  instance
    constructor _,_
  field
    proj₁ : X

    proj₂ : P proj₁

open Σ public

infixl 5 _⁏_
pattern _⁏_ x y = x , y

infixl 2 _×_
_×_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
X × Y = Σ X (λ x → Y)

mapΣ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {P : X → Set ℓ″} {Q : Y → Set ℓ‴}
                      → (f : X → Y) (g : ∀ {x} → P x → Q (f x)) → Σ X P
                      → Σ Y Q
mapΣ f g (x , y) = f x , g y

caseΣ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {P : X → Set ℓ″} {Q : Y → Set ℓ‴}
                       → Σ X P → (f : X → Y) (g : ∀ {x} → P x → Q (f x))
                       → Σ Y Q
caseΣ p f g = mapΣ f g p


infixl 1 _⊎_
data _⊎_ {ℓ ℓ′}
         (X : Set ℓ) (Y : Set ℓ′)
       : Set (ℓ ⊔ ℓ′) where
  inj₁ : (x : X) → X ⊎ Y
  inj₂ : (y : Y) → X ⊎ Y

elim⊎ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″}
                    → X ⊎ Y → (X → Z) → (Y → Z)
                    → Z
elim⊎ (inj₁ x) f g = f x
elim⊎ (inj₂ y) f g = g y

map⊎ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {Z₁ : Set ℓ″} {Z₂ : Set ℓ‴}
                      → (X → Z₁) → (Y → Z₂) → X ⊎ Y
                      → Z₁ ⊎ Z₂
map⊎ f g s = elim⊎ s (inj₁ ∘ f) (inj₂ ∘ g)

case⊎ : ∀ {ℓ ℓ′ ℓ″ ℓ‴} → {X : Set ℓ} {Y : Set ℓ′} {Z₁ : Set ℓ″} {Z₂ : Set ℓ‴}
                       → X ⊎ Y → (X → Z₁) → (Y → Z₂)
                       → Z₁ ⊎ Z₂
case⊎ s f g = map⊎ f g s


--------------------------------------------------------------------------------


open import Agda.Builtin.Bool public
  using (Bool ; false ; true)


if_then_else_ : ∀ {ℓ} → {X : Set ℓ}
                      → Bool → X → X
                      → X
if_then_else_ true  t f = t
if_then_else_ false t f = f

not : Bool → Bool
not true  = false
not false = true

and : Bool → Bool → Bool
and true  b = b
and false b = false

or : Bool → Bool → Bool
or true  b = true
or false b = b

xor : Bool → Bool → Bool
xor true  b = not b
xor false b = b


data True : Bool → Set
  where
    instance
      yes : True true


--------------------------------------------------------------------------------


open import Agda.Builtin.Nat public
  using (Nat ; zero ; suc)
open import Agda.Builtin.FromNat public
  using (Number ; fromNat)


instance
  numNat : Number Nat
  numNat =
    record
      { Constraint = λ n → ⊤
      ; fromNat    = λ n → n
      }


_>?_ : Nat → Nat → Bool
zero  >? k     = false
suc n >? zero  = true
suc n >? suc k = n >? k


--------------------------------------------------------------------------------


data Fin : Nat → Set
  where
    zero : ∀ {n} → Fin (suc n)

    suc  : ∀ {n} → Fin n
                 → Fin (suc n)


Nat→Fin : ∀ {n} → (k : Nat) {{_ : True (n >? k)}}
                 → Fin n
Nat→Fin {n = zero}  k       {{()}}
Nat→Fin {n = suc n} zero    {{is-true}} = zero
Nat→Fin {n = suc n} (suc k) {{p}}       = suc (Nat→Fin k {{p}})

instance
  numFin : ∀ {n} → Number (Fin n)
  numFin {n} =
    record
      { Constraint = λ k → True (n >? k)
      ; fromNat    = Nat→Fin
      }


--------------------------------------------------------------------------------
