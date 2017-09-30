module Prelude where


open import Agda.Primitive public
  using (Level ; _⊔_)
  renaming (lzero to ℓ₀)

open import Agda.Builtin.Equality public
  using (_≡_ ; refl)

open import Agda.Builtin.Unit public
  using (⊤ ; tt)


id : ∀ {ℓ} → {X : Set ℓ}
           → X → X
id x = x

_◎_ : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {P : X → Set ℓ′} {Q : ∀ {x} → P x → Set ℓ″}
                  → (g : ∀ {x} → (y : P x) → Q y) (f : (x : X) → P x) (x : X)
                  → Q (f x)
(g ◎ f) x = g (f x)

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


infix 6 _⁻¹
_⁻¹ : ∀ {ℓ} → {X : Set ℓ} {x x′ : X}
            → x ≡ x′ → x′ ≡ x
refl ⁻¹ = refl

infixr 4 _⦙_
_⦙_ : ∀ {ℓ} → {X : Set ℓ} {x x′ x″ : X}
            → x ≡ x′ → x′ ≡ x″ → x ≡ x″
refl ⦙ refl = refl

infixl 9 _&_
_&_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {x x′ : X}
               → (f : X → Y) → x ≡ x′
               → f x ≡ f x′
f & refl = refl

infixl 8 _⊗_
_⊗_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {f f′ : X → Y} {x x′ : X}
               → f ≡ f′ → x ≡ x′
               → f x ≡ f′ x′
refl ⊗ refl = refl


sym : ∀ {ℓ} → {X : Set ℓ} {x x′ : X}
            → x ≡ x′ → x′ ≡ x
sym = _⁻¹

trans : ∀ {ℓ} → {X : Set ℓ} {x x′ x″ : X}
            → x ≡ x′ → x′ ≡ x″ → x ≡ x″
trans = _⦙_

cong : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′} {x x′ : X}
                → (f : X → Y) → x ≡ x′
                → f x ≡ f x′
cong = _&_

cong² : ∀ {ℓ ℓ′ ℓ″} → {X : Set ℓ} {Y : Set ℓ′} {Z : Set ℓ″} {x x′ : X} {y y′ : Y}
                    → (f : X → Y → Z) → x ≡ x′ → y ≡ y′
                    → f x y ≡ f x′ y′
cong² f p q = f & p ⊗ q


module ≡-Reasoning {ℓ} {X : Set ℓ} where
  infix 1 begin_
  begin_ : ∀ {x x′ : X} → x ≡ x′ → x ≡ x′
  begin p = p

  infixr 2 _≡⟨⟩_
  _≡⟨⟩_ : ∀ (x {x′} : X) → x ≡ x′ → x ≡ x′
  x ≡⟨⟩ p = p

  infixr 2 _≡⟨_⟩_
  _≡⟨_⟩_ : ∀ (x {x′ x″} : X) → x ≡ x′ → x′ ≡ x″ → x ≡ x″
  x ≡⟨ p ⟩ q = p ⦙ q

  infix 3 _∎
  _∎ : ∀ (x : X) → x ≡ x
  x ∎ = refl


case_of_ : ∀ {ℓ ℓ′} → {X : Set ℓ} {Y : Set ℓ′}
                    → X → (X → Y) → Y
case x of f = f x

cast_via_ : ∀ {ℓ} → {X Y : Set ℓ}
                 → X → X ≡ Y → Y
cast x via refl = x


postulate
  fext! : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′} {f g : (x : X) → P x}
                   → ((x : X) → f x ≡ g x)
                   → f ≡ g

  fext¡ : ∀ {ℓ ℓ′} → {X : Set ℓ} {P : X → Set ℓ′} {f g : {x : X} → P x}
                   → ({x : X} → f {x} ≡ g {x})
                   → (λ {x} → f {x}) ≡ (λ {x} → g {x})


data ⊥ : Set where

elim⊥ : ∀ {ℓ} → {X : Set ℓ}
               → ⊥ → X
elim⊥ ()


Π : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
Π X Y = X → Y


infixl 5 _,_
record Σ {ℓ ℓ′}
         (X : Set ℓ) (P : X → Set ℓ′)
       : Set (ℓ ⊔ ℓ′) where
  constructor _,_
  field
    π₁ : X
    π₂ : P π₁

open Σ public

infixl 2 _×_
_×_ : ∀ {ℓ ℓ′} → Set ℓ → Set ℓ′ → Set (ℓ ⊔ ℓ′)
X × Y = Σ X (λ x → Y)
