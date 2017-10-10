module STLCE.Kovacs.Normalisation where

open import STLCE.Kovacs.NormalForm public


--------------------------------------------------------------------------------


-- (Tyᴺ)
mutual
  infix 3 _⊩_
  _⊩_ : 𝒞 → 𝒯 → Set

  Γ ⊩ ⎵      = Γ ⊢ⁿᶠ ⎵

  Γ ⊩ A ⇒ B = ∀ {Γ′} → (η : Γ′ ⊇ Γ) (a : Γ′ ∂⊩ A)
                       → Γ′ ∂⊩ B

  Γ ⊩ A ⩕ B  = Γ ∂⊩ A × Γ ∂⊩ B

  Γ ⊩ ⫪     = ⊤

  Γ ⊩ ⫫     = ⊥

  Γ ⊩ A ⩖ B  = Γ ∂⊩ A ⊎ Γ ∂⊩ B


  infix 3 _∂⊩_
  _∂⊩_ : 𝒞 → 𝒯 → Set
  Γ ∂⊩ A = ∀ {Γ′ C} → (η : Γ′ ⊇ Γ) (f : ∀ {Γ″} → Γ″ ⊇ Γ′ → Γ″ ⊩ A → Γ″ ⊢ⁿᶠ C)
                     → Γ′ ⊢ⁿᶠ C


-- (Tyᴺₑ)
mutual
  acc : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ⊩ A → Γ′ ⊩ A
  acc {⎵}      η M        = renⁿᶠ η M
  acc {A ⇒ B} η f        = λ η′ a → f (η ○ η′) a
  acc {A ⩕ B}  η s        = ∂acc η (proj₁ s) , ∂acc η (proj₂ s)
  acc {⫪}     η s        = tt
  acc {⫫}     η s        = elim⊥ s
  acc {A ⩖ B}  η (inj₁ a) = inj₁ (∂acc η a)
  acc {A ⩖ B}  η (inj₂ b) = inj₂ (∂acc η b)
-- TODO: Report Agda bug
-- acc {A ⩖ B}  η s = elim⊎ s (λ a → inj₁ (acc η a))
--                            (λ b → inj₂ (acc η b))

  ∂acc : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ∂⊩ A → Γ′ ∂⊩ A
  ∂acc η κ = λ η′ f →
               κ (η ○ η′) f


return : ∀ {A Γ} → Γ ⊩ A → Γ ∂⊩ A
return {A} a = λ η f →
                 f idₑ (acc {A} η a)

bind : ∀ {A C Γ} → Γ ∂⊩ A → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ⊩ A → Γ′ ∂⊩ C)
                 → Γ ∂⊩ C
bind κ f = λ η f′ →
             κ η (λ η′ a →
               f (η ○ η′) a idₑ (λ η″ b →
                 f′ (η′ ○ η″) b))


--------------------------------------------------------------------------------


-- (Conᴺ ; ∙ ; _,_)
infix 3 _∂⊩⋆_
data _∂⊩⋆_ : 𝒞 → 𝒞 → Set
  where
    ∅   : ∀ {Γ} → Γ ∂⊩⋆ ∅

    _,_ : ∀ {Γ Ξ A} → (ρ : Γ ∂⊩⋆ Ξ) (a : Γ ∂⊩ A)
                    → Γ ∂⊩⋆ Ξ , A


-- (Conᴺₑ)
-- NOTE: _⬖_ = ∂acc⋆
_⬖_ : ∀ {Γ Γ′ Ξ} → Γ ∂⊩⋆ Ξ → Γ′ ⊇ Γ → Γ′ ∂⊩⋆ Ξ
∅       ⬖ η = ∅
(ρ , a) ⬖ η = ρ ⬖ η , ∂acc η a


-- (∈ᴺ)
getᵥ : ∀ {Γ Ξ A} → Γ ∂⊩⋆ Ξ → Ξ ∋ A → Γ ∂⊩ A
getᵥ (ρ , a) zero    = a
getᵥ (ρ , a) (suc i) = getᵥ ρ i

-- (Tmᴺ)
eval : ∀ {Γ Ξ A} → Γ ∂⊩⋆ Ξ → Ξ ⊢ A → Γ ∂⊩ A
eval ρ (` i)          = getᵥ ρ i
eval ρ (ƛ {A = A} M)  = return {A ⇒ _} (λ η a → eval (ρ ⬖ η , a) M)
eval ρ (M ∙ N)        = bind (eval ρ M) (λ η f →
                          f idₑ (eval (ρ ⬖ η) N))
eval ρ (M , N)        = return (eval ρ M , eval ρ N)
eval ρ (π₁ M)         = bind (eval ρ M) (λ η s →
                          proj₁ s)
eval ρ (π₂ M)         = bind (eval ρ M) (λ η s →
                          proj₂ s)
eval ρ τ              = return tt
eval ρ (φ M)          = bind (eval ρ M) (λ η s →
                          elim⊥ s)
eval ρ (ι₁ {B = B} M) = return {_ ⩖ B} (inj₁ (eval ρ M))
eval ρ (ι₂ {A = A} M) = return {A ⩖ _} (inj₂ (eval ρ M))
eval ρ (M ⁇ N₁ ∥ N₂)  = bind (eval ρ M) (λ η s →
                          elim⊎ s (λ a → eval (ρ ⬖ η , a) N₁)
                                  (λ b → eval (ρ ⬖ η , b) N₂))


mutual
  -- (qᴺ)
  reify : ∀ {A Γ} → Γ ∂⊩ A → Γ ⊢ⁿᶠ A
  reify {⎵}      κ = κ idₑ (λ η M → M)
  reify {A ⇒ B} κ = κ idₑ (λ η f → ƛ (reify (f (wkₑ idₑ) (reflect 0))))
  reify {A ⩕ B}  κ = κ idₑ (λ η s → reify (proj₁ s) , reify (proj₂ s))
  reify {⫪}     κ = κ idₑ (λ η s → τ)
  reify {⫫}     κ = κ idₑ (λ η s → elim⊥ s)
  reify {A ⩖ B}  κ = κ idₑ (λ η s → elim⊎ s (λ a → ι₁ (reify a))
                                             (λ b → ι₂ (reify b)))

  -- (uᴺ)
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ∂⊩ A
  reflect {⎵}      M = return (ne M)
  reflect {A ⇒ B} M = return {A ⇒ _} (λ η a → reflect (renⁿᵉ η M ∙ reify a))
  reflect {A ⩕ B}  M = return (reflect (π₁ M) , reflect (π₂ M))
  reflect {⫪}     M = return tt
  reflect {⫫}     M = λ η f →
                         ne (φ (renⁿᵉ η M))
  reflect {A ⩖ B}  M = λ η f →
                         ne (renⁿᵉ η M ⁇ f (wkₑ idₑ) (inj₁ (reflect 0))
                                       ∥ f (wkₑ idₑ) (inj₂ (reflect 0)))

-- (uᶜᴺ)
idᵥ : ∀ {Γ} → Γ ∂⊩⋆ Γ
idᵥ {∅}     = ∅
idᵥ {Γ , A} = idᵥ ⬖ wkₑ idₑ , reflect 0


-- (nf)
nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ⁿᶠ A
nf M = reify (eval idᵥ M)


--------------------------------------------------------------------------------
