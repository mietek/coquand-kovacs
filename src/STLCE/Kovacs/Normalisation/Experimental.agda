module STLCE.Kovacs.Normalisation.Experimental where

open import STLCE.Kovacs.NormalForm public


--------------------------------------------------------------------------------


-- (Tyᴺ)
infix 3 _⊩_
_⊩_ : 𝒞 → 𝒯 → Set

Γ ⊩ ⎵      = Γ ⊢ⁿᶠ ⎵

Γ ⊩ A ⇒ B = ∀ {Γ′} → (η : Γ′ ⊇ Γ) (a : Γ′ ⊩ A)
                     → Γ′ ⊩ B

Γ ⊩ A ⩕ B  = Γ ⊩ A × Γ ⊩ B

Γ ⊩ ⫪     = ⊤

Γ ⊩ ⫫     = Γ ⊢ⁿᵉ ⫫

Γ ⊩ A ⩖ B  = Γ ⊢ⁿᵉ A ⩖ B ⊎ (Γ ⊩ A ⊎ Γ ⊩ B)


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
acc {⫫}     η M = renⁿᵉ η M
acc {A ⩖ B}  η s = case⊎ s (λ M → renⁿᵉ η M)
                           (λ t → case⊎ t (λ a → acc η a)
                                           (λ b → acc η b))

-- (Conᴺₑ)
-- NOTE: _⬖_ = acc⋆
_⬖_ : ∀ {Γ Γ′ Ξ} → Γ ⊩⋆ Ξ → Γ′ ⊇ Γ → Γ′ ⊩⋆ Ξ
∅       ⬖ η = ∅
(ρ , a) ⬖ η = ρ ⬖ η , acc η a


--------------------------------------------------------------------------------


mutual
  -- (qᴺ)
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reify {⎵}      M = M
  reify {A ⇒ B} f = ƛ (reify (f (wkₑ idₑ) (reflect 0)))
  reify {A ⩕ B}  s = reify (proj₁ s) , reify (proj₂ s)
  reify {⫪}     s = τ
  reify {⫫}     M = ne M
  reify {A ⩖ B}  s = elim⊎ s (λ M → ne M)
                             (λ t → elim⊎ t (λ a → ι₁ (reify a))
                                             (λ b → ι₂ (reify b)))

  -- (uᴺ)
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflect {⎵}      M = ne M
  reflect {A ⇒ B} M = λ η a → reflect (renⁿᵉ η M ∙ reify a)
  reflect {A ⩕ B}  M = reflect (π₁ M) , reflect (π₂ M)
  reflect {⫪}     M = tt
  reflect {⫫}     M = M
  reflect {A ⩖ B}  M = inj₁ M


-- (∈ᴺ)
getᵥ : ∀ {Γ Ξ A} → Γ ⊩⋆ Ξ → Ξ ∋ A → Γ ⊩ A
getᵥ (ρ , a) zero    = a
getᵥ (ρ , a) (suc i) = getᵥ ρ i

-- (Tmᴺ)
eval : ∀ {Γ Ξ A} → Γ ⊩⋆ Ξ → Ξ ⊢ A → Γ ⊩ A
eval ρ (` i)         = getᵥ ρ i
eval ρ (ƛ M)         = λ η a → eval (ρ ⬖ η , a) M
eval ρ (M ∙ N)       = eval ρ M idₑ (eval ρ N)
eval ρ (M , N)       = eval ρ M , eval ρ N
eval ρ (π₁ M)        = proj₁ (eval ρ M)
eval ρ (π₂ M)        = proj₂ (eval ρ M)
eval ρ τ             = tt
eval ρ (φ M)         = reflect (φ (eval ρ M))
eval ρ (ι₁ M)        = inj₂ (inj₁ (eval ρ M))
eval ρ (ι₂ M)        = inj₂ (inj₂ (eval ρ M))
eval ρ (M ⁇ N₁ ∥ N₂)
  = elim⊎ (eval ρ M)
          (λ M′ →
            reflect (M′ ⁇ reify (eval (ρ ⬖ wkₑ idₑ , reflect 0) N₁)
                        ∥ reify (eval (ρ ⬖ wkₑ idₑ , reflect 0) N₂)))
          (λ t →
            elim⊎ t (λ a → eval (ρ , a) N₁)
                    (λ b → eval (ρ , b) N₂))


-- (uᶜᴺ)
idᵥ : ∀ {Γ} → Γ ⊩⋆ Γ
idᵥ {∅}     = ∅
idᵥ {Γ , A} = idᵥ ⬖ wkₑ idₑ , reflect 0

-- (nf)
nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ⁿᶠ A
nf M = reify (eval idᵥ M)


--------------------------------------------------------------------------------
