module STLCE.Kovacs.Normalisation where

open import STLCE.Kovacs.NormalForm public


--------------------------------------------------------------------------------


-- (Tyᴺ)
mutual
  infix 3 _‼⊩_
  _‼⊩_ : 𝒞 → 𝒯 → Set

  Γ ‼⊩ ⎵      = Γ ⊢ⁿᶠ ⎵

  Γ ‼⊩ A ⇒ B = ∀ {Γ′} → (η : Γ′ ⊇ Γ) (a : Γ′ ⊩ A)
                        → Γ′ ⊩ B

  Γ ‼⊩ A ⩕ B  = Γ ⊩ A × Γ ⊩ B

  Γ ‼⊩ ⫪     = ⊤

  Γ ‼⊩ ⫫     = ⊥

  Γ ‼⊩ A ⩖ B  = Γ ⊩ A ⊎ Γ ⊩ B

  infix 3 _⊩_
  _⊩_ : 𝒞 → 𝒯 → Set
  Γ ⊩ A = ∀ {Γ′ C} → Γ′ ⊇ Γ
                    → (∀ {Γ″} → Γ″ ⊇ Γ′ → Γ″ ‼⊩ A → Γ″ ⊢ⁿᶠ C)
                    → Γ′ ⊢ⁿᶠ C


-- (Tyᴺₑ)
mutual
  ‼acc : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ‼⊩ A → Γ′ ‼⊩ A
  ‼acc {⎵}      η M = renⁿᶠ η M
  ‼acc {A ⇒ B} η f = λ η′ a → f (η ○ η′) a
  ‼acc {A ⩕ B}  η s = acc η (proj₁ s) , acc η (proj₂ s)
  ‼acc {⫪}     η s = tt
  ‼acc {⫫}     η s = elim⊥ s
  ‼acc {A ⩖ B}  η (inj₁ a) = inj₁ (acc η a)
  ‼acc {A ⩖ B}  η (inj₂ b) = inj₂ (acc η b)
-- TODO: Report Agda bug
-- ‼acc {A ⩖ B}  η s = elim⊎ s (λ a → inj₁ (acc η a))
--                             (λ b → inj₂ (acc η b))

  acc : ∀ {A Γ Γ′} → Γ′ ⊇ Γ → Γ ⊩ A → Γ′ ⊩ A
  acc η f = λ η′ k → f (η ○ η′) k


return : ∀ {A Γ} → Γ ‼⊩ A → Γ ⊩ A
return {A} a = λ η k → k idₑ (‼acc {A} η a)

bind : ∀ {A C Γ} → Γ ⊩ A
                 → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ‼⊩ A → Γ′ ⊩ C)
                 → Γ ⊩ C
bind f k = λ η k′ → f η
             λ η′ a → k (η ○ η′) a idₑ
               λ η″ b → k′ (η′ ○ η″) b

call : ∀ {Γ A C} → (∀ {Γ′} → Γ′ ⊇ Γ → Γ′ ‼⊩ A → Γ′ ⊢ⁿᶠ C)
                 → Γ ⊩ A
                 → Γ ⊢ⁿᶠ C
call g f = f idₑ g


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
eval ρ (` i)                           = getᵥ ρ i
eval ρ (ƛ {A = A} {B} M)               = return {A ⇒ B}
                                           λ η a → eval (ρ ⬖ η , a) M
eval ρ (_∙_ {A = A} {B} M N)           = bind {A ⇒ B} {B} (eval ρ M)
                                           λ η f → f idₑ (eval (ρ ⬖ η) N)
eval ρ (_,_ {A = A} {B} M N)           = return {A ⩕ B} (eval ρ M , eval ρ N)
eval ρ (π₁ {A = A} {B} M)              = bind {A ⩕ B} {A} (eval ρ M)
                                           λ η s → proj₁ s
eval ρ (π₂ {A = A} {B} M)              = bind {A ⩕ B} {B} (eval ρ M)
                                           λ η s → proj₂ s
eval ρ τ                               = return {⫪} tt
eval ρ (φ {C = C} M)                   = bind {⫫} {C} (eval ρ M)
                                           λ η s → elim⊥ s
eval ρ (ι₁ {A = A} {B} M)              = return {A ⩖ B} (inj₁ (eval ρ M))
eval ρ (ι₂ {A = A} {B} M)              = return {A ⩖ B} (inj₂ (eval ρ M))
eval ρ (_⁇_∥_ {A = A} {B} {C} M N₁ N₂) = bind {A ⩖ B} {C} (eval ρ M)
                                           λ η s → elim⊎ s (λ a → eval (ρ ⬖ η , a) N₁)
                                                            (λ b → eval (ρ ⬖ η , b) N₂)


mutual
  -- (qᴺ)
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ⁿᶠ A
  reify {⎵}      = call λ η M → M
  reify {A ⇒ B} = call λ η f → ƛ (reify (f (wkₑ idₑ) (reflect (` zero))))
  reify {A ⩕ B}  = call λ η s → reify (proj₁ s) , reify (proj₂ s)
  reify {⫪}     = call λ η s → τ
  reify {⫫}     = call λ η s → elim⊥ s
  reify {A ⩖ B}  = call λ η s → elim⊎ s (λ a → ι₁ (reify a))
                                         (λ b → ι₂ (reify b))

  -- (uᴺ)
  reflect : ∀ {A Γ} → Γ ⊢ⁿᵉ A → Γ ⊩ A
  reflect {⎵}      M = return {⎵} (ne M)
  reflect {A ⇒ B} M = return {A ⇒ B} λ η a → reflect (renⁿᵉ η M ∙ reify a)
  reflect {A ⩕ B}  M = return {A ⩕ B} (reflect (π₁ M) , reflect (π₂ M))
  reflect {⫪}     M = return {⫪} tt
  reflect {⫫}     M = λ η k → ne (φ (renⁿᵉ η M))
  reflect {A ⩖ B}  M = λ η k → ne (renⁿᵉ η M ⁇ k (wkₑ idₑ) (inj₁ (reflect (` zero)))
                                              ∥ k (wkₑ idₑ) (inj₂ (reflect (` zero))))

-- (uᶜᴺ)
idᵥ : ∀ {Γ} → Γ ⊩⋆ Γ
idᵥ {∅}     = ∅
idᵥ {Γ , A} = idᵥ ⬖ wkₑ idₑ , reflect (` zero)


-- (nf)
nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ⁿᶠ A
nf M = reify (eval idᵥ M)


--------------------------------------------------------------------------------
