module Category where

open import Prelude


record Category {ℓ ℓ′}
                (𝒪 : Set ℓ) (_▹_ : 𝒪 → 𝒪 → Set ℓ′)
              : Set (ℓ ⊔ ℓ′) where
  field
    idₓ    : ∀ {x} → x ▹ x

    _⋄_    : ∀ {x x′ x″} → x′ ▹ x → x″ ▹ x′ → x″ ▹ x

    lid⋄   : ∀ {x x′} → (ξ : x′ ▹ x)
                      → idₓ ⋄ ξ ≡ ξ

    rid⋄   : ∀ {x x′} → (ξ : x′ ▹ x)
                      → ξ ⋄ idₓ ≡ ξ

    assoc⋄ : ∀ {x x′ x″ x‴} → (ξ₁ : x‴ ▹ x″) (ξ₂ : x″ ▹ x′) (ξ₃ : x′ ▹ x)
                            → (ξ₃ ⋄ ξ₂) ⋄ ξ₁ ≡ ξ₃ ⋄ (ξ₂ ⋄ ξ₁)


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
    Fₓ   : 𝒪₁ → 𝒪₂

    Fₘ   : ∀ {x x′} → x′ ▹₁ x → Fₓ x′ ▹₂ Fₓ x

    idFₘ : ∀ {x} → Fₘ (C.idₓ {x = x}) ≡ D.idₓ

    Fₘ⋄  : ∀ {x x′ x″} → (ξ₁ : x″ ▹₁ x′) (ξ₂ : x′ ▹₁ x)
                       → Fₘ (ξ₂ C.⋄ ξ₁) ≡ Fₘ ξ₂ D.⋄ Fₘ ξ₁


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
    N    : ∀ {x} → F.Fₓ x ▹₂ G.Fₓ x

    natN : ∀ {x x′} → (m : x′ ▹₁ x)
                    → (N D.⋄ F.Fₘ m) ≡ (G.Fₘ m D.⋄ N)


Opposite : ∀ {ℓ ℓ′} → {𝒪 : Set ℓ} {_▹_ : 𝒪 → 𝒪 → Set ℓ′}
                    → Category 𝒪 _▹_
                    → Category 𝒪 (flip _▹_)
Opposite 𝗖 =
  record
    { idₓ    = C.idₓ
    ; _⋄_    = flip C._⋄_
    ; lid⋄   = C.rid⋄
    ; rid⋄   = C.lid⋄
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
