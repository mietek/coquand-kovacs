module Category where

open import Prelude


record Category {ℓ ℓ′}
                (𝒪 : Set ℓ) (_▹_ : 𝒪 → 𝒪 → Set ℓ′)
              : Set (ℓ ⊔ ℓ′) where
  field
    idₓ    : ∀ {x} → x ▹ x

    _⋄_    : ∀ {x x′ x″} → x′ ▹ x → x″ ▹ x′ → x″ ▹ x

    id₁⋄   : ∀ {x x′} → (ξ : x′ ▹ x)
                      → idₓ ⋄ ξ ≡ ξ

    id₂⋄   : ∀ {x x′} → (ξ : x′ ▹ x)
                      → ξ ⋄ idₓ ≡ ξ

    assoc⋄ : ∀ {x x′ x″ x‴} → (ξ₁ : x‴ ▹ x″) (ξ₂ : x″ ▹ x′) (ξ₃ : x′ ▹ x)
                            → (ξ₃ ⋄ ξ₂) ⋄ ξ₁ ≡ ξ₃ ⋄ (ξ₂ ⋄ ξ₁)


𝗦𝗲𝘁 : (ℓ : Level) → Category (Set ℓ) Π
𝗦𝗲𝘁 ℓ =
  record
    { idₓ    = id
    ; _⋄_    = λ g f → g ∘ f
    ; id₁⋄   = λ f → refl
    ; id₂⋄   = λ f → refl
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
    φₓ   : 𝒪₁ → 𝒪₂

    φₘ   : ∀ {x x′} → x′ ▹₁ x → φₓ x′ ▹₂ φₓ x

    idφₘ : ∀ {x} → φₘ (C.idₓ {x = x}) ≡ D.idₓ

    φₘ⋄  : ∀ {x x′ x″} → (ξ₁ : x″ ▹₁ x′) (ξ₂ : x′ ▹₁ x)
                       → φₘ (ξ₂ C.⋄ ξ₁) ≡ φₘ ξ₂ D.⋄ φₘ ξ₁


record NaturalTransformation {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′}
                             {𝒪₁ : Set ℓ₁} {_▹₁_ : 𝒪₁ → 𝒪₁ → Set ℓ₁′}
                             {𝒪₂ : Set ℓ₂} {_▹₂_ : 𝒪₂ → 𝒪₂ → Set ℓ₂′}
                             {𝗖 : Category 𝒪₁ _▹₁_} {𝗗 : Category 𝒪₂ _▹₂_}
                             (𝗙 𝗚 : Functor 𝗖 𝗗)
                           : Set (ℓ₁ ⊔ ℓ₁′ ⊔ ℓ₂ ⊔ ℓ₂′) where
  private
    module C = Category 𝗖
    module D = Category 𝗗
    module F = Functor 𝗙
    module G = Functor 𝗚
  field
    ϕ    : ∀ {x} → F.φₓ x ▹₂ G.φₓ x

    natϕ : ∀ {x x′} → (m : x′ ▹₁ x)
                    → (ϕ D.⋄ F.φₘ m) ≡ (G.φₘ m D.⋄ ϕ)


Opposite : ∀ {ℓ ℓ′} → {𝒪 : Set ℓ} {_▹_ : 𝒪 → 𝒪 → Set ℓ′}
                    → Category 𝒪 _▹_
                    → Category 𝒪 (flip _▹_)
Opposite 𝗖 =
  record
    { idₓ    = C.idₓ
    ; _⋄_    = flip C._⋄_
    ; id₁⋄   = C.id₂⋄
    ; id₂⋄   = C.id₁⋄
    ; assoc⋄ = λ ξ₁ ξ₂ ξ₃ → C.assoc⋄ ξ₃ ξ₂ ξ₁ ⁻¹
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
