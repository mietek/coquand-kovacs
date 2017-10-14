module STLCP.Kovacs.Normalisation where

open import STLCP.Kovacs.NormalForm public


--------------------------------------------------------------------------------


-- (Tyᴺ)
infix 3 _⊩_
_⊩_ : 𝒞 → 𝒯 → Set

Γ ⊩ ⎵      = Γ ⊢ⁿᶠ ⎵

Γ ⊩ A ⇒ B = ∀ {Γ′} → (η : Γ′ ⊇ Γ) (a : Γ′ ⊩ A)
                     → Γ′ ⊩ B

Γ ⊩ A ⩕ B  = Γ ⊩ A × Γ ⊩ B

Γ ⊩ ⫪     = ⊤


-- (Conᴺ ; ∙ ; _,_)
infix 3 _⊩⋆_
data _⊩⋆_ : 𝒞 → 𝒞 → Set
  where
    ∅   : ∀ {Γ} → Γ ⊩⋆ ∅

    _,_ : ∀ {Γ Ξ A} → (ρ : Γ ⊩⋆ Ξ) (a : Γ ⊩ A)
                    → Γ ⊩⋆ Ξ , A


--------------------------------------------------------------------------------


-- (Tyᴺₑ)
acc : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ⊩ A → Γ′ ⊩ A
acc {⎵}      η M = renⁿᶠ η M
acc {A ⇒ B} η f = λ η′ a → f (η ○ η′) a
acc {A ⩕ B}  η s = acc η (proj₁ s) , acc η (proj₂ s)
acc {⫪}     η s = tt

-- (Conᴺₑ)
-- NOTE: _⬖_ = acc⋆
_⬖_ : ∀ {Γ Γ′ Ξ} → Γ ⊩⋆ Ξ → Γ′ ⊇ Γ → Γ′ ⊩⋆ Ξ
∅       ⬖ η = ∅
(ρ , a) ⬖ η = ρ ⬖ η , acc η a


--------------------------------------------------------------------------------


-- (∈ᴺ)
getᵥ : ∀ {Γ Ξ A} → Γ ⊩⋆ Ξ → Ξ ∋ A → Γ ⊩ A
getᵥ (ρ , a) zero    = a
getᵥ (ρ , a) (suc i) = getᵥ ρ i

-- (Tmᴺ)
eval : ∀ {Γ Ξ A} → Γ ⊩⋆ Ξ → Ξ ⊢ A → Γ ⊩ A
eval ρ (` i)   = getᵥ ρ i
eval ρ (ƛ M)   = λ η a → eval (ρ ⬖ η , a) M
eval ρ (M ∙ N) = eval ρ M idₑ (eval ρ N)
eval ρ (M , N) = eval ρ M , eval ρ N
eval ρ (π₁ M)  = proj₁ (eval ρ M)
eval ρ (π₂ M)  = proj₂ (eval ρ M)
eval ρ τ       = tt


mutual
  -- (qᴺ)
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reify {⎵}      M = M
  reify {A ⇒ B} f = ƛ (reify (f (wkₑ idₑ) (reflect 0)))
  reify {A ⩕ B}  s = reify (proj₁ s) , reify (proj₂ s)
  reify {⫪}     s = τ

  -- (uᴺ)
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflect {⎵}      M = ne M
  reflect {A ⇒ B} M = λ η a → reflect (renⁿᵉ η M ∙ reify a)
  reflect {A ⩕ B}  M = reflect (π₁ M) , reflect (π₂ M)
  reflect {⫪}     M = tt


-- (uᶜᴺ)
idᵥ : ∀ {Γ} → Γ ⊩⋆ Γ
idᵥ {∅}     = ∅
idᵥ {Γ , A} = idᵥ ⬖ wkₑ idₑ , reflect 0

-- (nf)
nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ⁿᶠ A
nf M = reify (eval idᵥ M)


--------------------------------------------------------------------------------
