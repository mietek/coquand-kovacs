module STLC2.Kovacs.Normalisation where

open import STLC2.Kovacs.NormalForm public


--------------------------------------------------------------------------------


-- (Tyᴺ)
mutual
  infix 3 _⊩_
  _⊩_ : 𝒞 → 𝒯 → Set

  Γ ⊩ ⎵      = Γ ⊢ⁿᶠ ⎵

  Γ ⊩ A ⇒ B = ∀ {Γ′} → (η : Γ′ ⊇ Γ) (∂a : Γ′ ∂⊩ A)
                       → Γ′ ∂⊩ B

  Γ ⊩ A ⩕ B  = Γ ∂⊩ A × Γ ∂⊩ B

  Γ ⊩ ⫪     = ⊤

  Γ ⊩ ⫫     = ⊥

  Γ ⊩ A ⩖ B  = Γ ∂⊩ A ⊎ Γ ∂⊩ B


  infix 3 _∂⊩_
  _∂⊩_ : 𝒞 → 𝒯 → Set
  Γ ∂⊩ A = ∀ {Γ′ C} → (η : Γ′ ⊇ Γ)
                     → (f : ∀ {Γ″} → Γ″ ⊇ Γ′ → Γ″ ⊩ A → Γ″ ⊢ⁿᶠ C)
                     → Γ′ ⊢ⁿᶠ C


-- (Conᴺ ; ∙ ; _,_)
infix 3 _∂⊩⋆_
data _∂⊩⋆_ : 𝒞 → 𝒞 → Set
  where
    ∅   : ∀ {Γ} → Γ ∂⊩⋆ ∅

    _,_ : ∀ {Γ Ξ A} → (ρ : Γ ∂⊩⋆ Ξ) (∂a : Γ ∂⊩ A)
                    → Γ ∂⊩⋆ Ξ , A


--------------------------------------------------------------------------------


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
  -- TODO: Why doesn’t this work?
  -- acc {A ⩖ B}  η s = case⊎ s (λ a → ∂acc η a)
  --                            (λ b → ∂acc η b)

  ∂acc : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ∂⊩ A → Γ′ ∂⊩ A
  ∂acc η ∂a = λ η′ f → ∂a (η ○ η′) f


-- (Conᴺₑ)
-- NOTE: _⬖_ = ∂acc⋆
_⬖_ : ∀ {Γ Γ′ Ξ} → Γ ∂⊩⋆ Ξ → Γ′ ⊇ Γ → Γ′ ∂⊩⋆ Ξ
∅        ⬖ η = ∅
(ρ , ∂a) ⬖ η = ρ ⬖ η , ∂acc η ∂a


--------------------------------------------------------------------------------


!ƛ : ∀ {Γ A B} → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ∂⊩ A → Γ′ ∂⊩ B)
               → Γ ⊩ A ⇒ B
!ƛ f = λ η ∂a → f η ∂a

_!∙_ : ∀ {Γ A B} → Γ ⊩ A ⇒ B → Γ ∂⊩ A
                 → Γ ∂⊩ B
f !∙ ∂a = f idₑ ∂a

_!,_ : ∀ {Γ A B} → Γ ∂⊩ A → Γ ∂⊩ B
                 → Γ ⊩ A ⩕ B
∂a !, ∂b = ∂a , ∂b

!π₁ : ∀ {Γ A B} → Γ ⊩ A ⩕ B
                → Γ ∂⊩ A
!π₁ s = proj₁ s

!π₂ : ∀ {Γ A B} → Γ ⊩ A ⩕ B
                → Γ ∂⊩ B
!π₂ s = proj₂ s

!τ : ∀ {Γ} → Γ ⊩ ⫪
!τ = tt

!φ : ∀ {Γ C} → Γ ⊩ ⫫
             → Γ ∂⊩ C
!φ s = elim⊥ s

!ι₁ : ∀ {Γ A B} → Γ ∂⊩ A
                → Γ ⊩ A ⩖ B
!ι₁ ∂a = inj₁ ∂a

!ι₂ : ∀ {Γ A B} → Γ ∂⊩ B
                → Γ ⊩ A ⩖ B
!ι₂ ∂b = inj₂ ∂b

_!⁇_!∥_ : ∀ {Γ A B C} → Γ ⊩ A ⩖ B
                      → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ∂⊩ A → Γ′ ∂⊩ C)
                      → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ∂⊩ B → Γ′ ∂⊩ C)
                      → Γ ∂⊩ C
s !⁇ f !∥ g = elim⊎ s (λ ∂a → f idₑ ∂a)
                      (λ ∂b → g idₑ ∂b)


--------------------------------------------------------------------------------


return : ∀ {A Γ} → Γ ⊩ A → Γ ∂⊩ A
return {A} a = λ η f →
                 f idₑ (acc {A} η a)

bind : ∀ {A C Γ} → Γ ∂⊩ A → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ⊩ A → Γ′ ∂⊩ C)
                 → Γ ∂⊩ C
bind ∂a f = λ η f′ →
              ∂a η (λ η′ a →
                f (η ○ η′) a idₑ (λ η″ b →
                  f′ (η′ ○ η″) b))


--------------------------------------------------------------------------------


∂!λ : ∀ {Γ A B} → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ∂⊩ A → Γ′ ∂⊩ B)
                → Γ ∂⊩ A ⇒ B
∂!λ {A = A} f = return {A ⇒ _}
                       (!ƛ f)

_∂!∙_ : ∀ {Γ A B} → Γ ∂⊩ A ⇒ B → Γ ∂⊩ A
                  → Γ ∂⊩ B
∂f ∂!∙ ∂a = bind ∂f (λ η f → f !∙ ∂acc η ∂a)

_∂!,_ : ∀ {Γ A B} → Γ ∂⊩ A → Γ ∂⊩ B
                  → Γ ∂⊩ A ⩕ B
∂a ∂!, ∂b = return (∂a !, ∂b)

∂!π₁ : ∀ {Γ A B} → Γ ∂⊩ A ⩕ B
                 → Γ ∂⊩ A
∂!π₁ ∂s = bind ∂s (λ η s → !π₁ s)

∂!π₂ : ∀ {Γ A B} → Γ ∂⊩ A ⩕ B
                 → Γ ∂⊩ B
∂!π₂ ∂s = bind ∂s (λ η s → !π₂ s)

∂!τ : ∀ {Γ} → Γ ∂⊩ ⫪
∂!τ {Γ} = return (!τ {Γ})

∂!φ : ∀ {Γ C} → Γ ∂⊩ ⫫
              → Γ ∂⊩ C
∂!φ ∂s = bind ∂s (λ η s → !φ s)

∂!ι₁ : ∀ {Γ A B} → Γ ∂⊩ A
                 → Γ ∂⊩ A ⩖ B
∂!ι₁ {B = B} ∂a = return {_ ⩖ B}
                         (!ι₁ ∂a)

∂!ι₂ : ∀ {Γ A B} → Γ ∂⊩ B
                 → Γ ∂⊩ A ⩖ B
∂!ι₂ {A = A} ∂b = return {A ⩖ _}
                         (!ι₂ ∂b)

_∂!⁇_∂!∥_ : ∀ {Γ A B C} → Γ ∂⊩ A ⩖ B
                        → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ∂⊩ A → Γ′ ∂⊩ C)
                        → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ∂⊩ B → Γ′ ∂⊩ C)
                        → Γ ∂⊩ C
∂s ∂!⁇ f ∂!∥ g = bind ∂s (λ η s → s !⁇ (λ η′ → f (η ○ η′))
                                     !∥ (λ η′ → g (η ○ η′)))


--------------------------------------------------------------------------------


-- (∈ᴺ)
getᵥ : ∀ {Γ Ξ A} → Γ ∂⊩⋆ Ξ → Ξ ∋ A → Γ ∂⊩ A
getᵥ (ρ , ∂a) zero    = ∂a
getᵥ (ρ , ∂a) (suc i) = getᵥ ρ i

-- (Tmᴺ)
eval : ∀ {Γ Ξ A} → Γ ∂⊩⋆ Ξ → Ξ ⊢ A → Γ ∂⊩ A
eval ρ (𝓋 i)         = getᵥ ρ i
eval ρ (ƛ M)         = ∂!λ (λ η ∂a → eval (ρ ⬖ η , ∂a) M)
eval ρ (M ∙ N)       = eval ρ M ∂!∙ eval ρ N
eval ρ (M , N)       = eval ρ M ∂!, eval ρ N
eval ρ (π₁ M)        = ∂!π₁ (eval ρ M)
eval ρ (π₂ M)        = ∂!π₂ (eval ρ M)
eval ρ τ             = ∂!τ
eval ρ (φ M)         = ∂!φ (eval ρ M)
eval ρ (ι₁ M)        = ∂!ι₁ (eval ρ M)
eval ρ (ι₂ M)        = ∂!ι₂ (eval ρ M)
eval ρ (M ⁇ N₁ ∥ N₂) = eval ρ M ∂!⁇ (λ η ∂a → eval (ρ ⬖ η , ∂a) N₁)
                                ∂!∥ (λ η ∂b → eval (ρ ⬖ η , ∂b) N₂)


--------------------------------------------------------------------------------


mutual
  -- (qᴺ)
  reify : ∀ {A Γ} → Γ ∂⊩ A → Γ ⊢ⁿᶠ A
  reify {⎵}      ∂a = ∂a idₑ (λ η M → M)
  reify {A ⇒ B} ∂a = ∂a idₑ (λ η f → ƛ (reify (f (wkₑ idₑ) (reflect 0))))
  reify {A ⩕ B}  ∂a = ∂a idₑ (λ η s → reify (proj₁ s) , reify (proj₂ s))
  reify {⫪}     ∂a = ∂a idₑ (λ η s → τ)
  reify {⫫}     ∂a = ∂a idₑ (λ η s → elim⊥ s)
  reify {A ⩖ B}  ∂a = ∂a idₑ (λ η s → elim⊎ s (λ a → ι₁ (reify a))
                                              (λ b → ι₂ (reify b)))

  -- (uᴺ)
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ∂⊩ A
  reflect {⎵}      M = return (ne M)
  reflect {A ⇒ B} M = return {A ⇒ _}
                              (λ η ∂a → reflect (renⁿᵉ η M ∙ reify ∂a))
  reflect {A ⩕ B}  M = return (reflect (π₁ M) , reflect (π₂ M))
  reflect {⫪}     M = return tt
  reflect {⫫}     M = λ η f →
                         ne (φ (renⁿᵉ η M))
  reflect {A ⩖ B}  M = λ η f →
                         ne (renⁿᵉ η M ⁇ f (wkₑ idₑ) (inj₁ (reflect 0))
                                       ∥ f (wkₑ idₑ) (inj₂ (reflect 0)))


--------------------------------------------------------------------------------


-- (uᶜᴺ)
idᵥ : ∀ {Γ} → Γ ∂⊩⋆ Γ
idᵥ {∅}     = ∅
idᵥ {Γ , A} = idᵥ ⬖ wkₑ idₑ , reflect 0


-- (nf)
nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ⁿᶠ A
nf M = reify (eval idᵥ M)


--------------------------------------------------------------------------------
