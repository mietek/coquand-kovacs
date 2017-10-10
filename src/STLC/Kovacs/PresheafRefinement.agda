module STLC.Kovacs.PresheafRefinement where

open import STLC.Kovacs.Substitution public
open import STLC.Kovacs.Normalisation public
open import Category


--------------------------------------------------------------------------------


-- (Tyᴺ-idₑ)
idacc : ∀ {A Γ} → (a : Γ ⊩ A)
                → acc idₑ a ≡ a
idacc {⎵}      M = idrenⁿᶠ M
idacc {A ⇒ B} f = fext¡ (fext! (λ η → f & lid○ η))

-- (Tyᴺ-∘ₑ)
acc○ : ∀ {A Γ Γ′ Γ″} → (η₁ : Γ″ ⊇ Γ′) (η₂ : Γ′ ⊇ Γ) (a : Γ ⊩ A)
                     → acc (η₂ ○ η₁) a ≡ (acc η₁ ∘ acc η₂) a
acc○ {⎵}      η₁ η₂ M = renⁿᶠ○ η₁ η₂ M
acc○ {A ⇒ B} η₁ η₂ f = fext¡ (fext! (λ η′ → f & assoc○ η′ η₁ η₂))

-- (Conᴺ-idₑ)
lid⬖ : ∀ {Γ Ξ} → (ρ : Γ ⊩⋆ Ξ)
               → ρ ⬖ idₑ ≡ ρ
lid⬖ ∅       = refl
lid⬖ (ρ , a) = _,_ & lid⬖ ρ
                   ⊗ idacc a

-- (Conᴺ-∘ₑ)
comp⬖○ : ∀ {Γ Γ′ Γ″ Ξ} → (η₁ : Γ″ ⊇ Γ′) (η₂ : Γ′ ⊇ Γ) (ρ : Γ ⊩⋆ Ξ)
                       → (ρ ⬖ η₂) ⬖ η₁ ≡ ρ ⬖ (η₂ ○ η₁)
comp⬖○ η₁ η₂ ∅       = refl
comp⬖○ η₁ η₂ (ρ , a) = _,_ & comp⬖○ η₁ η₂ ρ
                           ⊗ (acc○ η₁ η₂ a ⁻¹)

-- (∈ᴺ-nat)
get⬖ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ρ : Γ ⊩⋆ Ξ) (i : Ξ ∋ A)
                    → getᵥ (ρ ⬖ η) i ≡ (acc η ∘ getᵥ ρ) i
get⬖ η (ρ , a) zero    = refl
get⬖ η (ρ , a) (suc i) = get⬖ η ρ i


--------------------------------------------------------------------------------


-- (Tyᴾ)
𝒰 : ∀ {A Γ} → Γ ⊩ A → Set

𝒰 {⎵}      {Γ} M = ⊤

𝒰 {A ⇒ B} {Γ} f = ∀ {Γ′} → (η : Γ′ ⊇ Γ) {a : Γ′ ⊩ A} (u : 𝒰 a)
                          → (∀ {Γ″} → (η′ : Γ″ ⊇ Γ′)
                                     → (f (η ○ η′) ∘ acc η′) a ≡
                                        (acc η′ ∘ f η) a)
                           × 𝒰 (f η a)


-- (Tyᴾₑ)
acc𝒰 : ∀ {A Γ Γ′} → {a : Γ ⊩ A}
                  → (η : Γ′ ⊇ Γ) → 𝒰 a
                  → 𝒰 (acc η a)
acc𝒰 {⎵}      {a = M} η tt = tt
acc𝒰 {A ⇒ B} {a = f} η u  = λ η′ {a} u′ →
                               let
                                 natf , u″ = u (η ○ η′) u′
                               in
                                 (λ η″ → (λ η‴ → (f η‴ ∘ acc η″) a)
                                          & (assoc○ η″ η′ η ⁻¹)
                                        ⦙ natf η″)
                               , u″

-- (Conᴾ ; ∙ ; _,_)
data 𝒰⋆ : ∀ {Γ Ξ} → Γ ⊩⋆ Ξ → Set where
  ∅   : ∀ {Γ} → 𝒰⋆ (∅ {Γ})

  _,_ : ∀ {Γ Ξ A} → {ρ : Γ ⊩⋆ Ξ} {a : Γ ⊩ A}
                  → (υ : 𝒰⋆ ρ) (u : 𝒰 a)
                  → 𝒰⋆ (ρ , a)

-- (Conᴾₑ)
-- NOTE _⬖𝒰_ = acc𝒰⋆
_⬖𝒰_ : ∀ {Γ Γ′ Ξ} → {ρ : Γ ⊩⋆ Ξ}
                  → 𝒰⋆ ρ → (η : Γ′ ⊇ Γ)
                  → 𝒰⋆ (ρ ⬖ η)
∅       ⬖𝒰 η = ∅
(υ , u) ⬖𝒰 η = υ ⬖𝒰 η , acc𝒰 η u


--------------------------------------------------------------------------------

-- (∈ᴾ)
get𝒰 : ∀ {Γ Ξ A} → {ρ : Γ ⊩⋆ Ξ}
                 → 𝒰⋆ ρ → (i : Ξ ∋ A)
                 → 𝒰 (getᵥ ρ i)
get𝒰 (υ , u) zero    = u
get𝒰 (υ , u) (suc i) = get𝒰 υ i


mutual
  -- (Tmᴾ)
  eval𝒰 : ∀ {Γ Ξ A} → {ρ : Γ ⊩⋆ Ξ}
                    → 𝒰⋆ ρ → (M : Ξ ⊢ A)
                    → 𝒰 (eval ρ M)
  eval𝒰 {ρ = ρ} υ (` i)   = get𝒰 υ i
  eval𝒰 {ρ = ρ} υ (ƛ M)   = λ η {a} u →
                              (λ η′ → (λ ρ′ → eval (ρ′ , acc η′ a) M)
                                       & (comp⬖○ η′ η ρ ⁻¹)
                                     ⦙ eval⬖ η′ (υ ⬖𝒰 η , u) M)
                            , eval𝒰 (υ ⬖𝒰 η , u) M
  eval𝒰 {ρ = ρ} υ (M ∙ N) = proj₂ (eval𝒰 υ M idₑ (eval𝒰 υ N))

  -- (Tmᴺ-nat)
  eval⬖ : ∀ {Γ Γ′ Ξ A} → {ρ : Γ ⊩⋆ Ξ}
                       → (η : Γ′ ⊇ Γ) → 𝒰⋆ ρ → (M : Ξ ⊢ A)
                       → eval (ρ ⬖ η) M ≡ (acc η ∘ eval ρ) M
  eval⬖ {ρ = ρ} η υ (` i)   = get⬖ η ρ i
  eval⬖ {ρ = ρ} η υ (ƛ M)   = fext¡ (fext! (λ η′ → fext! (λ a →
                                (λ ρ′ → eval ρ′ M)
                                & ((_, a) & comp⬖○ η′ η ρ))))
  eval⬖ {ρ = ρ} η υ (M ∙ N) rewrite eval⬖ η υ M | eval⬖ η υ N
                            = (λ η′ → eval ρ M η′ (acc η (eval ρ N)))
                              & (rid○ η ⦙ lid○ η ⁻¹)
                            ⦙ proj₁ (eval𝒰 υ M idₑ (eval𝒰 υ N)) η


mutual
  -- (uᴾ)
  reflect𝒰 : ∀ {A Γ} → (M : Γ ⊢ⁿᵉ A)
                     → 𝒰 (reflect M)
  reflect𝒰 {⎵}      M = tt
  reflect𝒰 {A ⇒ B} M = λ η {a} u →
                          (λ η′ → (λ M′ N′ → reflect (M′ ∙ N′))
                                   & renⁿᵉ○ η′ η M
                                   ⊗ (natreify η′ a u)
                                 ⦙ natreflect η′ (renⁿᵉ η M ∙ reify a))
                        , reflect𝒰 (renⁿᵉ η M ∙ reify a)

  -- (qᴺ-nat)
  natreify : ∀ {A Γ Γ′} → (η : Γ′ ⊇ Γ) (a : Γ ⊩ A) → 𝒰 a
                        → (reify ∘ acc η) a ≡ (renⁿᶠ η ∘ reify) a
  natreify {⎵}      η M u = refl
  natreify {A ⇒ B} η f u =
    let
      natf , u′ = u (wkₑ idₑ) (reflect𝒰 0)
    in
      ƛ & ( reify & ( f & (wkₑ & ( rid○ η
                                 ⦙ lid○ η ⁻¹
                                 ))
                        ⊗ natreflect (liftₑ η) 0
                    ⦙ natf (liftₑ η)
                    )
          ⦙ natreify (liftₑ η) (f (wkₑ idₑ) (reflect 0)) u′
          )

  -- (uᴺ-nat)
  natreflect : ∀ {A Γ Γ′} → (η : Γ′ ⊇ Γ) (M : Γ ⊢ⁿᵉ A)
                          → (reflect ∘ renⁿᵉ η) M ≡ (acc η ∘ reflect) M
  natreflect {⎵}      η M = refl
  natreflect {A ⇒ B} η M = fext¡ (fext! (λ η′ → fext! (λ a →
                              (λ M′ → reflect (M′ ∙ reify a))
                              & (renⁿᵉ○ η′ η M ⁻¹))))

-- (uᶜᴾ)
id𝒰 : ∀ {Γ} → 𝒰⋆ (idᵥ {Γ})
id𝒰 {∅}     = ∅
id𝒰 {Γ , A} = id𝒰 ⬖𝒰 wkₑ idₑ , reflect𝒰 0


--------------------------------------------------------------------------------


-- (OPEᴺ)
_⬗_ : ∀ {Γ Ξ Ξ′} → Ξ′ ⊇ Ξ → Γ ⊩⋆ Ξ′ → Γ ⊩⋆ Ξ
done    ⬗ ρ       = ρ
wkₑ η   ⬗ (ρ , a) = η ⬗ ρ
liftₑ η ⬗ (ρ , a) = η ⬗ ρ , a

-- (OPEᴺ-nat)
nat⬗ : ∀ {Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ρ : Γ ⊩⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                     → η₂ ⬗ (ρ ⬖ η₁) ≡ (η₂ ⬗ ρ) ⬖ η₁
nat⬗ η₁ ρ       done       = refl
nat⬗ η₁ (ρ , a) (wkₑ η₂)   = nat⬗ η₁ ρ η₂
nat⬗ η₁ (ρ , a) (liftₑ η₂) = (_, acc η₁ a) & nat⬗ η₁ ρ η₂

-- (OPEᴺ-idₑ)
lid⬗ : ∀ {Γ Ξ} → (ρ : Γ ⊩⋆ Ξ)
               → idₑ ⬗ ρ ≡ ρ
lid⬗ ∅       = refl
lid⬗ (ρ , a) = (_, a) & lid⬗ ρ


--------------------------------------------------------------------------------


-- (∈ₑᴺ)
get⬗ : ∀ {Γ Ξ Ξ′ A} → (ρ : Γ ⊩⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (i : Ξ ∋ A)
                    → getᵥ (η ⬗ ρ) i ≡ (getᵥ ρ ∘ getₑ η) i
get⬗ ρ       done      i       = refl
get⬗ (ρ , a) (wkₑ η)   i       = get⬗ ρ η i
get⬗ (ρ , a) (liftₑ η) zero    = refl
get⬗ (ρ , a) (liftₑ η) (suc i) = get⬗ ρ η i

-- (Tmₑᴺ)
eval⬗ : ∀ {Γ Ξ Ξ′ A} → (ρ : Γ ⊩⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (M : Ξ ⊢ A)
                     → eval (η ⬗ ρ) M ≡ (eval ρ ∘ ren η) M
eval⬗ ρ η (` i)   = get⬗ ρ η i
eval⬗ ρ η (ƛ M)   = fext¡ (fext! (λ η′ → fext! (λ a →
                      (λ ρ′ → eval (ρ′ , a) M) & nat⬗ η′ ρ η ⁻¹
                    ⦙ eval⬗ (ρ ⬖ η′ , a) (liftₑ η) M)))
eval⬗ ρ η (M ∙ N) rewrite eval⬗ ρ η M | eval⬗ ρ η N
                  = refl


--------------------------------------------------------------------------------


-- (Subᴺ)
-- NOTE: _◆_ = eval⋆
_◆_ : ∀ {Γ Ξ Φ} → Ξ ⊢⋆ Φ → Γ ⊩⋆ Ξ → Γ ⊩⋆ Φ
∅       ◆ ρ = ∅
(σ , M) ◆ ρ = σ ◆ ρ , eval ρ M

-- (Subᴺ-nat)
comp◆⬖ : ∀ {Γ Γ′ Ξ Φ} → {ρ : Γ ⊩⋆ Ξ}
                      → (η : Γ′ ⊇ Γ) → 𝒰⋆ ρ → (σ : Ξ ⊢⋆ Φ)
                      → (σ ◆ ρ) ⬖ η ≡ σ ◆ (ρ ⬖ η)
comp◆⬖ η υ ∅       = refl
comp◆⬖ η υ (σ , M) = _,_ & comp◆⬖ η υ σ
                         ⊗ (eval⬖ η υ M ⁻¹)

-- (Subᴺ-ₛ∘ₑ)
comp◆⬗ : ∀ {Γ Ξ Ξ′ Φ} → (ρ : Γ ⊩⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (σ : Ξ ⊢⋆ Φ)
                      → (σ ◐ η) ◆ ρ ≡ σ ◆ (η ⬗ ρ)
comp◆⬗ ρ η ∅       = refl
comp◆⬗ ρ η (σ , M) = _,_ & comp◆⬗ ρ η σ
                         ⊗ (eval⬗ ρ η M ⁻¹)

-- (∈ₛᴺ)
get◆ : ∀ {Γ Ξ Φ A} → (ρ : Γ ⊩⋆ Ξ) (σ : Ξ ⊢⋆ Φ) (i : Φ ∋ A)
                   → getᵥ (σ ◆ ρ) i ≡ (eval ρ ∘ getₛ σ) i
get◆ ρ (σ , M) zero    = refl
get◆ ρ (σ , M) (suc i) = get◆ ρ σ i

-- (Subᴺ-idₛ)
lid◆ : ∀ {Γ Ξ} → (ρ : Γ ⊩⋆ Ξ)
               → idₛ ◆ ρ ≡ ρ
lid◆ ∅       = refl
lid◆ (ρ , a) = (_, a) & ( comp◆⬗ (ρ , a) (wkₑ idₑ) idₛ
                        ⦙ lid◆ (idₑ ⬗ ρ)
                        ⦙ lid⬗ ρ
                        )


--------------------------------------------------------------------------------


accPsh : 𝒯 → Presheaf₀ 𝗢𝗣𝗘
accPsh A =
  record
    { Fₓ  = _⊩ A
    ; F   = acc
    ; idF = fext! idacc
    ; F⋄  = λ η₁ η₂ → fext! (acc○ η₂ η₁)
    }

flip⬖Psh : 𝒞 → Presheaf₀ 𝗢𝗣𝗘
flip⬖Psh Ξ =
  record
    { Fₓ  = _⊩⋆ Ξ
    ; F   = flip _⬖_
    ; idF = fext! lid⬖
    ; F⋄  = λ η₁ η₂ → fext! (λ ρ → comp⬖○ η₂ η₁ ρ ⁻¹)
    }


getᵥNT : ∀ {Ξ A} → (i : Ξ ∋ A)
                 → NaturalTransformation (flip⬖Psh Ξ) (accPsh A)
getᵥNT i =
  record
    { N    = flip getᵥ i
    ; natN = λ η → fext! (λ ρ → get⬖ η ρ i)
    }

-- TODO
-- evalNT : ∀ {Ξ A} → (M : Ξ ⊢ A)
--                  → NaturalTransformation (flip⬖Psh Ξ) (accPsh A)
-- evalNT M =
--   record
--     { N    = flip eval M
--     ; natN = λ η → fext! (λ ρ → eval⬖ {ρ = ρ} η {!!} M)
--     }

-- TODO
-- reifyNT : ∀ {A} → NaturalTransformation (accPsh A) (renⁿᶠPsh A)
-- reifyNT =
--   record
--     { N    = reify
--     ; natN = λ η → fext! (λ a → natreify η a {!!})
--     }

reflectNT : ∀ {A} → NaturalTransformation (renⁿᵉPsh A) (accPsh A)
reflectNT =
  record
    { N    = reflect
    ; natN = λ η → fext! (λ M → natreflect η M)
    }


--------------------------------------------------------------------------------
