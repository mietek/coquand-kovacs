module Category where

open import Prelude


--------------------------------------------------------------------------------


record Category {ℓ ℓ′}
                (𝒪 : Set ℓ) (_▹_ : 𝒪 → 𝒪 → Set ℓ′)
              : Set (ℓ ⊔ ℓ′) where
  field
    idₓ    : ∀ {x} → x ▹ x

    _⋄_    : ∀ {x y z} → y ▹ x → z ▹ y → z ▹ x

    lid⋄   : ∀ {x y} → (f : y ▹ x)
                     → idₓ ⋄ f ≡ f

    rid⋄   : ∀ {x y} → (f : y ▹ x)
                     → f ⋄ idₓ ≡ f

    assoc⋄ : ∀ {x y z a} → (h : a ▹ z) (g : z ▹ y) (f : y ▹ x)
                         → (f ⋄ g) ⋄ h ≡ f ⋄ (g ⋄ h)


𝗦𝗲𝘁 : (ℓ : Level) → Category (Set ℓ) Π
𝗦𝗲𝘁 ℓ =
  record
    { idₓ    = id
    ; _⋄_    = _∘_
    ; lid⋄   = λ f → refl
    ; rid⋄   = λ f → refl
    ; assoc⋄ = λ h g f → refl
    }

𝗦𝗲𝘁₀ : Category (Set ℓ₀) Π
𝗦𝗲𝘁₀ = 𝗦𝗲𝘁 ℓ₀


record Functor {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′}
               {𝒪₁ : Set ℓ₁} {_▹₁_ : 𝒪₁ → 𝒪₁ → Set ℓ₁′}
               {𝒪₂ : Set ℓ₂} {_▹₂_ : 𝒪₂ → 𝒪₂ → Set ℓ₂′}
               (𝗖 : Category 𝒪₁ _▹₁_) (𝗗 : Category 𝒪₂ _▹₂_)
             : Set (ℓ₁ ⊔ ℓ₁′ ⊔ ℓ₂ ⊔ ℓ₂′) where
  private
    module C = Category 𝗖
    module D = Category 𝗗

  field
    Fₓ  : 𝒪₁ → 𝒪₂

    F   : ∀ {x y} → y ▹₁ x → Fₓ y ▹₂ Fₓ x

    idF : ∀ {x} → F (C.idₓ {x = x}) ≡ D.idₓ

    F⋄  : ∀ {x y z} → (g : z ▹₁ y) (f : y ▹₁ x)
                    → F (f C.⋄ g) ≡ F f D.⋄ F g


record NaturalTransformation {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′}
                             {𝒪₁ : Set ℓ₁} {_▹₁_ : 𝒪₁ → 𝒪₁ → Set ℓ₁′}
                             {𝒪₂ : Set ℓ₂} {_▹₂_ : 𝒪₂ → 𝒪₂ → Set ℓ₂′}
                             {𝗖 : Category 𝒪₁ _▹₁_} {𝗗 : Category 𝒪₂ _▹₂_}
                             (𝗙 𝗚 : Functor 𝗖 𝗗)
                           : Set (ℓ₁ ⊔ ℓ₁′ ⊔ ℓ₂ ⊔ ℓ₂′) where
  private
    open module D = Category 𝗗 using (_⋄_)
    open module F = Functor 𝗙 using (Fₓ ; F)
    open module G = Functor 𝗚 using () renaming (Fₓ to Gₓ ; F to G)

  field
    N    : ∀ {x} → Fₓ x ▹₂ Gₓ x

    natN : ∀ {x y} → (f : y ▹₁ x)
                   → (N ⋄ F f) ≡ (G f ⋄ N)


Opposite : ∀ {ℓ ℓ′} → {𝒪 : Set ℓ} {_▹_ : 𝒪 → 𝒪 → Set ℓ′}
                    → Category 𝒪 _▹_
                    → Category 𝒪 (flip _▹_)
Opposite 𝗖 =
  record
    { idₓ    = C.idₓ
    ; _⋄_    = flip C._⋄_
    ; lid⋄   = C.rid⋄
    ; rid⋄   = C.lid⋄
    ; assoc⋄ = λ f g h → C.assoc⋄ h g f ⁻¹
    }
  where
    module C = Category 𝗖


Presheaf : ∀ ℓ {ℓ′ ℓ″} → {𝒪 : Set ℓ′} {_▹_ : 𝒪 → 𝒪 → Set ℓ″}
                       → (𝗖 : Category 𝒪 _▹_)
                       → Set _
Presheaf ℓ 𝗖 = Functor (Opposite 𝗖) (𝗦𝗲𝘁 ℓ)

Presheaf₀ : ∀ {ℓ ℓ′} → {𝒪 : Set ℓ} {_▹_ : 𝒪 → 𝒪 → Set ℓ′}
                     → (𝗖 : Category 𝒪 _▹_)
                     → Set _
Presheaf₀ 𝗖 = Presheaf ℓ₀ 𝗖


--------------------------------------------------------------------------------
