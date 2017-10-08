module Category where

open import Prelude


--------------------------------------------------------------------------------


record Category {ℓ ℓ′}
                (𝒪 : Set ℓ) (_▹_ : 𝒪 → 𝒪 → Set ℓ′)
              : Set (ℓ ⊔ ℓ′) where
  field
    idₓ    : ∀ {x} → x ▹ x

    _⋄_    : ∀ {x x′ x″} → x′ ▹ x → x″ ▹ x′ → x″ ▹ x

    lid⋄   : ∀ {x x′} → (m : x′ ▹ x)
                      → idₓ ⋄ m ≡ m

    rid⋄   : ∀ {x x′} → (m : x′ ▹ x)
                      → m ⋄ idₓ ≡ m

    assoc⋄ : ∀ {x x′ x″ x‴} → (m₁ : x‴ ▹ x″) (m₂ : x″ ▹ x′) (m₃ : x′ ▹ x)
                            → (m₃ ⋄ m₂) ⋄ m₁ ≡ m₃ ⋄ (m₂ ⋄ m₁)


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

    Fₘ⋄  : ∀ {x x′ x″} → (m₁ : x″ ▹₁ x′) (m₂ : x′ ▹₁ x)
                       → Fₘ (m₂ C.⋄ m₁) ≡ Fₘ m₂ D.⋄ Fₘ m₁


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
    ; assoc⋄ = λ m₁ m₂ m₃ → C.assoc⋄ m₃ m₂ m₁ ⁻¹
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
