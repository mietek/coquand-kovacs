module KovacsNormalisation where

open import KovacsNormalForm public


--------------------------------------------------------------------------------


-- (Tyᴺ)
infix 3 _⊩_
_⊩_ : 𝒞 → 𝒯 → Set

Γ ⊩ ⎵      = Γ ⊢ⁿᶠ ⎵

Γ ⊩ A ⇒ B = ∀ {Γ′} → (η : Γ′ ⊇ Γ) (a : Γ′ ⊩ A)
                     → Γ′ ⊩ B


-- (Tyᴺₑ)
acc : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ⊩ A → Γ′ ⊩ A
acc {⎵}      η M = renⁿᶠ η M
acc {A ⇒ B} η f = λ η′ a → f (η ○ η′) a


--------------------------------------------------------------------------------


-- (Conᴺ ; ∙ ; _,_)
infix 3 _⊩⋆_
data _⊩⋆_ : 𝒞 → 𝒞 → Set
  where
    ∅   : ∀ {Γ} → Γ ⊩⋆ ∅

    _,_ : ∀ {Γ Ξ A} → (ρ : Γ ⊩⋆ Ξ) (a : Γ ⊩ A)
                    → Γ ⊩⋆ Ξ , A


-- (Conᴺₑ)
-- NOTE: _⬖_ = acc⋆
_⬖_ : ∀ {Γ Γ′ Ξ} → Γ ⊩⋆ Ξ → Γ′ ⊇ Γ → Γ′ ⊩⋆ Ξ
∅       ⬖ η = ∅
(ρ , a) ⬖ η = ρ ⬖ η , acc η a


-- (∈ᴺ)
getᵥ : ∀ {Γ Ξ A} → Γ ⊩⋆ Ξ → Ξ ∋ A → Γ ⊩ A
getᵥ (ρ , a) zero    = a
getᵥ (ρ , a) (suc i) = getᵥ ρ i

-- (Tmᴺ)
eval : ∀ {Γ Ξ A} → Γ ⊩⋆ Ξ → Ξ ⊢ A → Γ ⊩ A
eval ρ (` i)   = getᵥ ρ i
eval ρ (ƛ M)   = λ η a → eval (ρ ⬖ η , a) M
eval ρ (M ∙ N) = eval ρ M idₑ (eval ρ N)


mutual
  -- (qᴺ)
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reify {⎵}      a = a
  reify {A ⇒ B} f = ƛ (reify (f (wkₑ idₑ) (reflect (` zero))))

  -- (uᴺ)
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflect {⎵}      M = ne M
  reflect {A ⇒ B} M = λ η a → reflect (renⁿᵉ η M ∙ reify a)

-- (uᶜᴺ)
idᵥ : ∀ {Γ} → Γ ⊩⋆ Γ
idᵥ {∅}     = ∅
idᵥ {Γ , A} = idᵥ ⬖ wkₑ idₑ , reflect (` zero)


-- (nf)
nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ⁿᶠ A
nf M = reify (eval idᵥ M)


--------------------------------------------------------------------------------
