module STLC1.Kovacs.Soundness where

open import STLC1.Kovacs.Convertibility public
open import STLC1.Kovacs.PresheafRefinement public


--------------------------------------------------------------------------------


infix 3 _≈_
_≈_ : ∀ {A Γ} → Γ ⊩ A → Γ ⊩ A → Set

_≈_ {⎵}      {Γ} M₁ M₂ = M₁ ≡ M₂

_≈_ {A ⇒ B} {Γ} f₁ f₂ = ∀ {Γ′} → (η : Γ′ ⊇ Γ) {a₁ a₂ : Γ′ ⊩ A}
                                → (p : a₁ ≈ a₂) (u₁ : 𝒰 a₁) (u₂ : 𝒰 a₂)
                                → f₁ η a₁ ≈ f₂ η a₂

_≈_ {A ⩕ B}  {Γ} s₁ s₂ = proj₁ s₁ ≈ proj₁ s₂ × proj₂ s₁ ≈ proj₂ s₂

_≈_ {⫪}     {Γ} s₁ s₂ = ⊤


-- (≈ᶜ ; ∙ ; _,_)
infix 3 _≈⋆_
data _≈⋆_ : ∀ {Γ Ξ} → Γ ⊩⋆ Ξ → Γ ⊩⋆ Ξ → Set
  where
    ∅   : ∀ {Γ} → ∅ {Γ} ≈⋆ ∅

    _,_ : ∀ {Γ Ξ A} → {ρ₁ ρ₂ : Γ ⊩⋆ Ξ} {M₁ M₂ : Γ ⊩ A}
                    → (χ : ρ₁ ≈⋆ ρ₂) (p : M₁ ≈ M₂)
                    → ρ₁ , M₁ ≈⋆ ρ₂ , M₂


-- (_≈⁻¹)
_⁻¹≈ : ∀ {A Γ} → {a₁ a₂ : Γ ⊩ A}
               → a₁ ≈ a₂
               → a₂ ≈ a₁
_⁻¹≈ {⎵}      p = p ⁻¹
_⁻¹≈ {A ⇒ B} F = λ η p u₁ u₂ →
                    F η (p ⁻¹≈) u₂ u₁ ⁻¹≈
_⁻¹≈ {A ⩕ B}  p = proj₁ p ⁻¹≈ , proj₂ p ⁻¹≈
_⁻¹≈ {⫪}     p = tt


-- (_≈ᶜ⁻¹)
_⁻¹≈⋆ : ∀ {Γ Ξ} → {ρ₁ ρ₂ : Γ ⊩⋆ Ξ}
                → ρ₁ ≈⋆ ρ₂
                → ρ₂ ≈⋆ ρ₁
∅       ⁻¹≈⋆ = ∅
(χ , p) ⁻¹≈⋆ = χ ⁻¹≈⋆ , p ⁻¹≈


-- (_≈◾_)
_⦙≈_ : ∀ {A Γ} → {a₁ a₂ a₃ : Γ ⊩ A}
               → a₁ ≈ a₂ → a₂ ≈ a₃
               → a₁ ≈ a₃
_⦙≈_ {⎵}      p q = p ⦙ q
_⦙≈_ {A ⇒ B} F G = λ η p u₁ u₂ →
                       F η (p ⦙≈ (p ⁻¹≈)) u₁ u₁
                    ⦙≈ G η p u₁ u₂
_⦙≈_ {A ⩕ B}  p q = proj₁ p ⦙≈ proj₁ q , proj₂ p ⦙≈ proj₂ q
_⦙≈_ {⫪}     p q = tt

-- (_≈ᶜ◾_)
_⦙≈⋆_ : ∀ {Γ Ξ} → {ρ₁ ρ₂ ρ₃ : Γ ⊩⋆ Ξ}
                → ρ₁ ≈⋆ ρ₂ → ρ₂ ≈⋆ ρ₃
                → ρ₁ ≈⋆ ρ₃
∅        ⦙≈⋆ ∅        = ∅
(χ₁ , p) ⦙≈⋆ (χ₂ , q) = χ₁ ⦙≈⋆ χ₂ , p ⦙≈ q


instance
  per≈ : ∀ {Γ A} → PER (Γ ⊩ A) _≈_
  per≈ =
    record
      { _⁻¹ = _⁻¹≈
      ; _⦙_ = _⦙≈_
      }

instance
  per≈⋆ : ∀ {Γ Ξ} → PER (Γ ⊩⋆ Ξ) _≈⋆_
  per≈⋆ =
    record
      { _⁻¹ = _⁻¹≈⋆
      ; _⦙_ = _⦙≈⋆_
      }


--------------------------------------------------------------------------------


-- (≈ₑ)
acc≈ : ∀ {A Γ Γ′} → {a₁ a₂ : Γ ⊩ A}
                  → (η : Γ′ ⊇ Γ) → a₁ ≈ a₂
                  → acc η a₁ ≈ acc η a₂
acc≈ {⎵}      η p = renⁿᶠ η & p
acc≈ {A ⇒ B} η F = λ η′ → F (η ○ η′)
acc≈ {A ⩕ B}  η p = acc≈ η (proj₁ p) , acc≈ η (proj₂ p)
acc≈ {⫪}     η p = tt

-- (≈ᶜₑ)
_⬖≈_ : ∀ {Γ Γ′ Ξ} → {ρ₁ ρ₂ : Γ ⊩⋆ Ξ}
                  → ρ₁ ≈⋆ ρ₂ → (η : Γ′ ⊇ Γ)
                  → ρ₁ ⬖ η ≈⋆ ρ₂ ⬖ η
∅       ⬖≈ η = ∅
(χ , p) ⬖≈ η = χ ⬖≈ η , acc≈ η p


-- (∈≈)
get≈ : ∀ {Γ Ξ A} → {ρ₁ ρ₂ : Γ ⊩⋆ Ξ}
                 → ρ₁ ≈⋆ ρ₂ → (i : Ξ ∋ A)
                 → getᵥ ρ₁ i ≈ getᵥ ρ₂ i
get≈ (χ , p) zero    = p
get≈ (χ , p) (suc i) = get≈ χ i

-- (Tm≈)
eval≈ : ∀ {Γ Ξ A} → {ρ₁ ρ₂ : Γ ⊩⋆ Ξ}
                  → ρ₁ ≈⋆ ρ₂ → 𝒰⋆ ρ₁ → 𝒰⋆ ρ₂ → (M : Ξ ⊢ A)
                  → eval ρ₁ M ≈ eval ρ₂ M
eval≈ χ υ₁ υ₂ (` i)   = get≈ χ i
eval≈ χ υ₁ υ₂ (ƛ M)   = λ η p u₁ u₂ →
                          eval≈ (χ ⬖≈ η , p)
                                (υ₁ ⬖𝒰 η , u₁)
                                (υ₂ ⬖𝒰 η , u₂)
                                M
eval≈ χ υ₁ υ₂ (M ∙ N) = eval≈ χ υ₁ υ₂ M idₑ
                              (eval≈ χ υ₁ υ₂ N)
                              (eval𝒰 υ₁ N)
                              (eval𝒰 υ₂ N)
eval≈ χ υ₁ υ₂ (M , N) = eval≈ χ υ₁ υ₂ M , eval≈ χ υ₁ υ₂ N
eval≈ χ υ₁ υ₂ (π₁ M)  = proj₁ (eval≈ χ υ₁ υ₂ M)
eval≈ χ υ₁ υ₂ (π₂ M)  = proj₂ (eval≈ χ υ₁ υ₂ M)
eval≈ χ υ₁ υ₂ τ       = tt


--------------------------------------------------------------------------------


-- (Subᴺᴾ)
-- NOTE: _◆𝒰_ = eval𝒰⋆
_◆𝒰_ : ∀ {Γ Ξ Φ} → {ρ : Γ ⊩⋆ Ξ}
                 → (σ : Ξ ⊢⋆ Φ) → 𝒰⋆ ρ
                 → 𝒰⋆ (σ ◆ ρ)
∅       ◆𝒰 υ = ∅
(σ , M) ◆𝒰 υ = σ ◆𝒰 υ , eval𝒰 υ M

-- (Subᴺ≈ᶜ)
-- NOTE: _◆≈_ = eval≈⋆
_◆≈_ : ∀ {Γ Ξ Φ} → {ρ₁ ρ₂ : Γ ⊩⋆ Ξ}
                 → (σ : Ξ ⊢⋆ Φ) → ρ₁ ≈⋆ ρ₂ → 𝒰⋆ ρ₁ → 𝒰⋆ ρ₂
                 → σ ◆ ρ₁ ≈⋆ σ ◆ ρ₂
(∅ ◆≈ χ)       υ₁ υ₂ = ∅
((σ , M) ◆≈ χ) υ₁ υ₂ = (σ ◆≈ χ) υ₁ υ₂ , eval≈ χ υ₁ υ₂ M


--------------------------------------------------------------------------------


-- (Tmₛᴺ)
eval◆ : ∀ {Γ Ξ Φ A} → {ρ : Γ ⊩⋆ Ξ}
                    → ρ ≈⋆ ρ → 𝒰⋆ ρ → (σ : Ξ ⊢⋆ Φ) (M : Φ ⊢ A)
                    → eval ρ (sub σ M) ≈ eval (σ ◆ ρ) M

eval◆ {ρ = ρ} χ υ σ (` i)
  rewrite get◆ ρ σ i
  = eval≈ χ υ υ (getₛ σ i)

eval◆ {ρ = ρ} χ υ σ (ƛ M) η {a₁} {a₂} p u₁ u₂
  rewrite comp◆⬖ η υ σ
  = let
      υ′ = υ ⬖𝒰 η
    in
      eval◆ {ρ = ρ ⬖ η , a₁}
            ((χ ⬖≈ η) , (p ⦙ p ⁻¹))
            (υ ⬖𝒰 η , u₁)
            (liftₛ σ)
            M
    ⦙ coe ((λ ρ′ → eval (ρ′ , a₁) M ≈ _)
           & ( comp◆⬗ (ρ ⬖ η , a₁) (wkₑ idₑ) σ
             ⦙ (σ ◆_) & lid⬗ (ρ ⬖ η)
             ) ⁻¹)
          (eval≈ ((σ ◆≈ (χ ⬖≈ η)) υ′ υ′ , p)
                 (σ ◆𝒰 υ′ , u₁)
                 (σ ◆𝒰 υ′ , u₂)
                 M)

eval◆ {ρ = ρ} χ υ σ (M ∙ N)
  = eval◆ χ υ σ M
          idₑ
          (eval◆ χ υ σ N)
          (eval𝒰 υ (sub σ N))
          (eval𝒰 (σ ◆𝒰 υ) N)

eval◆ {ρ = ρ} χ υ σ (M , N) = eval◆ χ υ σ M , eval◆ χ υ σ N
eval◆ {ρ = ρ} χ υ σ (π₁ M)  = proj₁ (eval◆ χ υ σ M)
eval◆ {ρ = ρ} χ υ σ (π₂ M)  = proj₂ (eval◆ χ υ σ M)
eval◆ {ρ = ρ} χ υ σ τ       = tt


--------------------------------------------------------------------------------


-- (~≈)
eval∼ : ∀ {Γ Ξ A} → {ρ₁ ρ₂ : Γ ⊩⋆ Ξ}
                  → ρ₁ ≈⋆ ρ₂ → 𝒰⋆ ρ₁ → 𝒰⋆ ρ₂
                  → {M₁ M₂ : Ξ ⊢ A}
                  → M₁ ∼ M₂
                  → eval ρ₁ M₁ ≈ eval ρ₂ M₂

eval∼ χ υ₁ υ₂ {M} refl∼ = eval≈ χ υ₁ υ₂ M
eval∼ χ υ₁ υ₂ (p ⁻¹∼)   = eval∼ (χ ⁻¹) υ₂ υ₁ p ⁻¹
eval∼ χ υ₁ υ₂ (p ⦙∼ q)  = eval∼ (χ ⦙ χ ⁻¹) υ₁ υ₁ p
                        ⦙ eval∼ χ υ₁ υ₂ q

eval∼ χ υ₁ υ₂ (ƛ∼ p)
  = λ η q u₁ u₂ →
      eval∼ (χ ⬖≈ η , q)
            (υ₁ ⬖𝒰 η , u₁)
            (υ₂ ⬖𝒰 η , u₂)
            p

eval∼ χ υ₁ υ₂ (_∙∼_ {N₁ = N₁} {N₂} p q)
  = eval∼ χ υ₁ υ₂ p
          idₑ
          (eval∼ χ υ₁ υ₂ q)
          (eval𝒰 υ₁ N₁)
          (eval𝒰 υ₂ N₂)

eval∼ χ υ₁ υ₂ (p ,∼ q) = eval∼ χ υ₁ υ₂ p , eval∼ χ υ₁ υ₂ q
eval∼ χ υ₁ υ₂ (π₁∼ p ) = proj₁ (eval∼ χ υ₁ υ₂ p)
eval∼ χ υ₁ υ₂ (π₂∼ p ) = proj₂ (eval∼ χ υ₁ υ₂ p)

eval∼ {ρ₁ = ρ₁} {ρ₂} χ υ₁ υ₂ (red⇒ M N)
  = coe ((λ ρ₁′ ρ₂′ → eval (ρ₁′ , eval ρ₁ N) M ≈ eval (ρ₂′ , eval ρ₂ N) M)
         & (lid⬖ ρ₁ ⁻¹)
         ⊗ (lid◆ ρ₂ ⁻¹))
        (eval≈ (χ , eval≈ χ υ₁ υ₂ N)
               (υ₁ , eval𝒰 υ₁ N)
               (υ₂ , eval𝒰 υ₂ N)
               M)
  ⦙ eval◆ (χ ⁻¹ ⦙ χ) υ₂ (idₛ , N) M ⁻¹

eval∼ χ υ₁ υ₂ (red⩕₁ M N) = eval≈ χ υ₁ υ₂ M
eval∼ χ υ₁ υ₂ (red⩕₂ M N) = eval≈ χ υ₁ υ₂ N

eval∼ {ρ₂ = ρ₂} χ υ₁ υ₂ (exp⇒ M) η {a₂ = a₂} p u₁ u₂
  rewrite eval⬗ (ρ₂ ⬖ η , a₂) (wkₑ idₑ) M ⁻¹
        | lid⬗ (ρ₂ ⬖ η)
        | eval⬖ η υ₂ M
        | rid○ η
  = eval≈ χ υ₁ υ₂ M η p u₁ u₂

eval∼ χ υ₁ υ₂ (exp⩕ M)  = eval≈ χ υ₁ υ₂ M
eval∼ χ υ₁ υ₂ (exp⫪ M) = tt


--------------------------------------------------------------------------------


mutual
  -- (q≈)
  reify≈ : ∀ {A Γ} → {a₁ a₂ : Γ ⊩ A}
                   → a₁ ≈ a₂
                   → reify a₁ ≡ reify a₂
  reify≈ {⎵}      p = p
  reify≈ {A ⇒ B} F = ƛ & reify≈ (F (wkₑ {A = A} idₑ)
                                    (reflect≈ refl)
                                    (reflect𝒰 {A} 0)
                                    (reflect𝒰 {A} 0))
  reify≈ {A ⩕ B}  p = _,_ & reify≈ (proj₁ p)
                          ⊗ reify≈ (proj₂ p)
  reify≈ {⫪}     p = refl

  -- (u≈)
  reflect≈ : ∀ {A Γ} → {M₁ M₂ : Γ ⊢ⁿᵉ A}
                     → M₁ ≡ M₂
                     → reflect M₁ ≈ reflect M₂
  reflect≈ {⎵}      p = ne & p
  reflect≈ {A ⇒ B} p = λ η q u₁ u₂ →
                          reflect≈ (_∙_ & (renⁿᵉ η & p)
                                        ⊗ reify≈ q)
  reflect≈ {A ⩕ B}  p = reflect≈ (π₁ & p) , reflect≈ (π₂ & p)
  reflect≈ {⫪}     p = tt


-- (uᶜ≈)
id≈ : ∀ {Γ} → idᵥ {Γ} ≈⋆ idᵥ
id≈ {∅}     = ∅
id≈ {Γ , A} = id≈ ⬖≈ wkₑ idₑ , reflect≈ refl


sound : ∀ {Γ A} → {M₁ M₂ : Γ ⊢ A}
                → M₁ ∼ M₂
                → nf M₁ ≡ nf M₂
sound p = reify≈ (eval∼ id≈ id𝒰 id𝒰 p)


--------------------------------------------------------------------------------
