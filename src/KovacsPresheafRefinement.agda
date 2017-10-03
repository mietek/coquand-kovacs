module KovacsPresheafRefinement where

open import KovacsSubstitution public
open import KovacsNormalisation public
open import Category


-- (Tyᴺ-idₑ)
idacc : ∀ {A Γ} → (a : Γ ⊩ A)
                → acc idₑ a ≡ a
idacc {⎵}     M = idrenⁿᶠ M
idacc {A ⊃ B} f = fext¡ (fext! (λ η → f & id₁○ η))

-- (Tyᴺ-∘ₑ)
acc○ : ∀ {A Γ Γ′ Γ″} → (η₁ : Γ″ ⊇ Γ′) (η₂ : Γ′ ⊇ Γ) (a : Γ ⊩ A)
                     → acc (η₂ ○ η₁) a ≡ (acc η₁ ∘ acc η₂) a
acc○ {⎵}     η₁ η₂ M = renⁿᶠ○ η₁ η₂ M
acc○ {A ⊃ B} η₁ η₂ f = fext¡ (fext! (λ η′ → f & assoc○ η′ η₁ η₂))

-- (Tyᴺ-∘ₑ)
id₁◐ᵥ : ∀ {Γ Ξ} → (ρ : Γ ⊩⋆ Ξ)
                → ρ ◐ᵥ idₑ ≡ ρ
id₁◐ᵥ []        = refl
id₁◐ᵥ [ ρ , a ] = [_,_] & id₁◐ᵥ ρ ⊗ idacc a

-- (Conᴺ-∘ₑ)
comp◐○ᵥ : ∀ {Γ Γ′ Γ″ Ξ} → (η₁ : Γ″ ⊇ Γ′) (η₂ : Γ′ ⊇ Γ) (ρ : Γ ⊩⋆ Ξ)
                        → (ρ ◐ᵥ η₂) ◐ᵥ η₁ ≡ ρ ◐ᵥ (η₂ ○ η₁)
comp◐○ᵥ η₁ η₂ []        = refl
comp◐○ᵥ η₁ η₂ [ ρ , a ] = [_,_] & comp◐○ᵥ η₁ η₂ ρ ⊗ (acc○ η₁ η₂ a ⁻¹)

-- (∈ᴺ-nat)
get◐ᵥ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (ρ : Γ ⊩⋆ Ξ) (i : Ξ ∋ A)
                     → getᵥ (ρ ◐ᵥ η) i ≡ (acc η ∘ getᵥ ρ) i
get◐ᵥ η [ ρ , a ] zero    = refl
get◐ᵥ η [ ρ , a ] (suc i) = get◐ᵥ η ρ i


--------------------------------------------------------------------------------


-- (Tyᴾ)
𝒰 : ∀ {A Γ} → Γ ⊩ A → Set

𝒰 {⎵}     {Γ} M = ⊤

𝒰 {A ⊃ B} {Γ} f = ∀ {Γ′} → (η : Γ′ ⊇ Γ) {a : Γ′ ⊩ A} (u : 𝒰 a)
                         →   (∀ {Γ″} → (η′ : Γ″ ⊇ Γ′)
                                      → (f (η ○ η′) ∘ acc η′) a ≡
                                         (acc η′ ∘ f η) a)
                            × 𝒰 (f η a)


-- (Tyᴾₑ)
𝒰acc : ∀ {A Γ Γ′} → {a : Γ ⊩ A}
                  → (η : Γ′ ⊇ Γ) → 𝒰 a
                  → 𝒰 (acc η a)
𝒰acc {⎵}     {a = M} η tt = tt
𝒰acc {A ⊃ B} {a = f} η u  = λ η′ {a} u′ →
                              let
                                natf , u″ = u (η ○ η′) u′
                              in
                                (λ η″ → (λ η‴ → (f η‴ ∘ acc η″) a)
                                         & (assoc○ η″ η′ η ⁻¹)
                                       ⦙ natf η″)
                              , u″

-- (Conᴾ)
data 𝒰⋆ : ∀ {Γ Ξ} → Γ ⊩⋆ Ξ → Set where
  -- ∙
  []    : ∀ {Γ} → 𝒰⋆ ([] {Γ})

  -- _,_
  [_,_] : ∀ {Γ Ξ A} → {ρ : Γ ⊩⋆ Ξ} {a : Γ ⊩ A}
                    → (υ : 𝒰⋆ ρ) (u : 𝒰 a)
                    → 𝒰⋆ [ ρ , a ]

-- (Conᴾₑ)
_𝒰◐ᵥ_ : ∀ {Γ Γ′ Ξ} → {ρ : Γ ⊩⋆ Ξ}
                   → 𝒰⋆ ρ → (η : Γ′ ⊇ Γ)
                   → 𝒰⋆ (ρ ◐ᵥ η)
[]        𝒰◐ᵥ η = []
[ υ , u ] 𝒰◐ᵥ η = [ υ 𝒰◐ᵥ η , 𝒰acc η u ]

-- (∈ᴾ)
𝒰getᵥ : ∀ {Γ Ξ A} → {ρ : Γ ⊩⋆ Ξ}
                  → 𝒰⋆ ρ → (i : Ξ ∋ A)
                  → 𝒰 (getᵥ ρ i)
𝒰getᵥ [ υ , u ] zero    = u
𝒰getᵥ [ υ , u ] (suc i) = 𝒰getᵥ υ i


mutual
  -- (Tmᴾ)
  𝒰eval : ∀ {Γ Ξ A} → {ρ : Γ ⊩⋆ Ξ}
                    → 𝒰⋆ ρ → (M : Ξ ⊢ A)
                    → 𝒰 (eval ρ M)
  𝒰eval {ρ = ρ} υ (` i)   = 𝒰getᵥ υ i
  𝒰eval {ρ = ρ} υ (ƛ M)   = λ η {a} u →
                              (λ η′ → (λ ρ′ → eval [ ρ′ , acc η′ a ] M)
                                       & (comp◐○ᵥ η′ η ρ ⁻¹)
                                     ⦙ eval◐ᵥ η′ [ υ 𝒰◐ᵥ η , u ] M)
                            , 𝒰eval [ υ 𝒰◐ᵥ η , u ] M
  𝒰eval {ρ = ρ} υ (M ∙ N) = π₂ (𝒰eval υ M idₑ (𝒰eval υ N))

  -- (Tmᴺ-nat)
  eval◐ᵥ : ∀ {Γ Γ′ Ξ A} → {ρ : Γ ⊩⋆ Ξ}
                        → (η : Γ′ ⊇ Γ) → 𝒰⋆ ρ → (M : Ξ ⊢ A)
                        → eval (ρ ◐ᵥ η) M ≡ (acc η ∘ eval ρ) M
  eval◐ᵥ {ρ = ρ} η υ (` i)   = get◐ᵥ η ρ i
  eval◐ᵥ {ρ = ρ} η υ (ƛ M)   = fext¡ (fext! (λ η′ → fext! (λ a →
                                 (λ ρ′ → eval ρ′ M)
                                 & ([_, a ] & comp◐○ᵥ η′ η ρ))))
  eval◐ᵥ {ρ = ρ} η υ (M ∙ N) rewrite eval◐ᵥ η υ M | eval◐ᵥ η υ N
                             = (λ η′ → eval ρ M η′ (acc η (eval ρ N)))
                               & (id₂○ η ⦙ id₁○ η ⁻¹)
                             ⦙ π₁ (𝒰eval υ M idₑ (𝒰eval υ N)) η


mutual
  -- (uᴾ)
  𝒰reflect : ∀ {A Γ} → (M : Γ ⊢ⁿᵉ A)
                     → 𝒰 (reflect M)
  𝒰reflect {⎵}     M = tt
  𝒰reflect {A ⊃ B} M = λ η {a} u →
                         (λ η′ → (λ M′ N′ → reflect (M′ ∙ N′))
                                  & renⁿᵉ○ η′ η M ⊗ (natreify η′ a u)
                                ⦙ natreflect η′ (renⁿᵉ η M ∙ reify a))
                       , 𝒰reflect (renⁿᵉ η M ∙ reify a)

  -- (qᴺ-nat)
  natreify : ∀ {A Γ Γ′} → (η : Γ′ ⊇ Γ) (a : Γ ⊩ A) → 𝒰 a
                        → (reify ∘ acc η) a ≡ (renⁿᶠ η ∘ reify) a
  natreify {⎵}     η M u = refl
  natreify {A ⊃ B} η f u =
    let
      natf , u′ = u (wkₑ idₑ) (𝒰reflect (` zero))
    in
      ƛ & ( reify & ( f & (wkₑ & ( id₂○ η
                                 ⦙ id₁○ η ⁻¹
                                 ))
                        ⊗ natreflect (liftₑ η) (` zero)
                    ⦙ natf (liftₑ η)
                    )
          ⦙ natreify (liftₑ η) (f (wkₑ idₑ) (reflect (` zero))) u′
          )

  -- (uᴺ-nat)
  natreflect : ∀ {A Γ Γ′} → (η : Γ′ ⊇ Γ) (M : Γ ⊢ⁿᵉ A)
                          → (reflect ∘ renⁿᵉ η) M ≡ (acc η ∘ reflect) M
  natreflect {⎵}     η M = refl
  natreflect {A ⊃ B} η M = fext¡ (fext! (λ η′ → fext! (λ a →
                             (λ M′ → reflect (M′ ∙ reify a))
                             & (renⁿᵉ○ η′ η M ⁻¹))))

-- (uᶜᴾ)
𝒰idᵥ : ∀ {Γ} → 𝒰⋆ (idᵥ {Γ})
𝒰idᵥ {[]}        = []
𝒰idᵥ {[ Γ , A ]} = [ 𝒰idᵥ 𝒰◐ᵥ wkₑ idₑ , 𝒰reflect (` zero) ]


--------------------------------------------------------------------------------


-- (OPEᴺ)
_◑ᵥ_ : ∀ {Γ Ξ Ξ′} → Ξ′ ⊇ Ξ → Γ ⊩⋆ Ξ′ → Γ ⊩⋆ Ξ
done    ◑ᵥ ρ         = ρ
wkₑ η   ◑ᵥ [ ρ , a ] = η ◑ᵥ ρ
liftₑ η ◑ᵥ [ ρ , a ] = [ η ◑ᵥ ρ , a ]

-- (OPEᴺ-nat)
nat◑ᵥ : ∀ {Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (ρ : Γ ⊩⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                      → η₂ ◑ᵥ (ρ ◐ᵥ η₁) ≡ (η₂ ◑ᵥ ρ) ◐ᵥ η₁
nat◑ᵥ η₁ ρ         done       = refl
nat◑ᵥ η₁ [ ρ , a ] (wkₑ η₂)   = nat◑ᵥ η₁ ρ η₂
nat◑ᵥ η₁ [ ρ , a ] (liftₑ η₂) = [_, acc η₁ a ] & nat◑ᵥ η₁ ρ η₂

-- (OPEᴺ-idₑ)
id₁◑ᵥ : ∀ {Γ Ξ} → (ρ : Γ ⊩⋆ Ξ)
                → idₑ ◑ᵥ ρ ≡ ρ
id₁◑ᵥ []        = refl
id₁◑ᵥ [ ρ , a ] = [_, a ] & id₁◑ᵥ ρ

-- (∈ₑᴺ)
get◑ᵥ : ∀ {Γ Ξ Ξ′ A} → (ρ : Γ ⊩⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (i : Ξ ∋ A)
                     → getᵥ (η ◑ᵥ ρ) i ≡ (getᵥ ρ ∘ getₑ η) i
get◑ᵥ ρ         done      i       = refl
get◑ᵥ [ ρ , a ] (wkₑ η)   i       = get◑ᵥ ρ η i
get◑ᵥ [ ρ , a ] (liftₑ η) zero    = refl
get◑ᵥ [ ρ , a ] (liftₑ η) (suc i) = get◑ᵥ ρ η i

-- (Tmₑᴺ)
eval◑ᵥ : ∀ {Γ Ξ Ξ′ A} → (ρ : Γ ⊩⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (M : Ξ ⊢ A)
                      → eval (η ◑ᵥ ρ) M ≡ (eval ρ ∘ ren η) M
eval◑ᵥ ρ η (` i)   = get◑ᵥ ρ η i
eval◑ᵥ ρ η (ƛ M)   = fext¡ (fext! (λ η′ → fext! (λ a →
                       (λ ρ′ → eval [ ρ′ , a ] M) & nat◑ᵥ η′ ρ η ⁻¹
                     ⦙ eval◑ᵥ [ ρ ◐ᵥ η′ , a ] (liftₑ η) M)))
eval◑ᵥ ρ η (M ∙ N) rewrite eval◑ᵥ ρ η M | eval◑ᵥ ρ η N
                   = refl


--------------------------------------------------------------------------------


-- (Subᴺ)
_●ᵥ_ : ∀ {Γ Ξ Φ} → Ξ ⊢⋆ Φ → Γ ⊩⋆ Ξ → Γ ⊩⋆ Φ
[]        ●ᵥ ρ = []
[ σ , M ] ●ᵥ ρ = [ σ ●ᵥ ρ , eval ρ M ]

-- (Subᴺ-nat)
comp●◐ᵥ : ∀ {Γ Γ′ Ξ Φ} → {ρ : Γ ⊩⋆ Ξ}
                       → (η : Γ′ ⊇ Γ) → 𝒰⋆ ρ → (σ : Ξ ⊢⋆ Φ)
                       → (σ ●ᵥ ρ) ◐ᵥ η ≡ σ ●ᵥ (ρ ◐ᵥ η)
comp●◐ᵥ η υ []        = refl
comp●◐ᵥ η υ [ σ , M ] = [_,_] & comp●◐ᵥ η υ σ ⊗ (eval◐ᵥ η υ M ⁻¹)

-- (Subᴺ-ₛ∘ₑ)
comp●◑ᵥ : ∀ {Γ Ξ Ξ′ Φ} → (ρ : Γ ⊩⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (σ : Ξ ⊢⋆ Φ)
                       → (σ ◐ η) ●ᵥ ρ ≡ σ ●ᵥ (η ◑ᵥ ρ)
comp●◑ᵥ ρ η []        = refl
comp●◑ᵥ ρ η [ σ , M ] = [_,_] & comp●◑ᵥ ρ η σ ⊗ (eval◑ᵥ ρ η M ⁻¹)

-- (∈ₛᴺ)
eval●ᵥ : ∀ {Γ Ξ Φ A} → (ρ : Γ ⊩⋆ Ξ) (σ : Ξ ⊢⋆ Φ) (i : Φ ∋ A)
                     → getᵥ (σ ●ᵥ ρ) i ≡ (eval ρ ∘ getₛ σ) i
eval●ᵥ ρ [ σ , M ] zero    = refl
eval●ᵥ ρ [ σ , M ] (suc i) = eval●ᵥ ρ σ i

-- (Subᴺ-idₛ)
id₁●ᵥ : ∀ {Γ Ξ} → (ρ : Γ ⊩⋆ Ξ)
                → idₛ ●ᵥ ρ ≡ ρ
id₁●ᵥ []        = refl
id₁●ᵥ [ ρ , a ] = [_, a ] & ( comp●◑ᵥ [ ρ , a ] (wkₑ idₑ) idₛ
                            ⦙ id₁●ᵥ (idₑ ◑ᵥ ρ)
                            ⦙ id₁◑ᵥ ρ
                            )


--------------------------------------------------------------------------------


accPsh : 𝒯 → Presheaf₀ 𝗢𝗣𝗘
accPsh A =
  record
    { φₓ   = _⊩ A
    ; φₘ   = acc
    ; idφₘ = fext! idacc
    ; φₘ⋄  = λ η₁ η₂ → fext! (acc○ η₂ η₁)
    }

flip◐ᵥPsh : 𝒞 → Presheaf₀ 𝗢𝗣𝗘
flip◐ᵥPsh Ξ =
  record
    { φₓ   = _⊩⋆ Ξ
    ; φₘ   = flip _◐ᵥ_
    ; idφₘ = fext! id₁◐ᵥ
    ; φₘ⋄  = λ η₁ η₂ → fext! (λ ρ → comp◐○ᵥ η₂ η₁ ρ ⁻¹)
    }


getᵥNT : ∀ {Ξ A} → (i : Ξ ∋ A)
                 → NaturalTransformation (flip◐ᵥPsh Ξ) (accPsh A)
getᵥNT i =
  record
    { ϕ    = flip getᵥ i
    ; natϕ = λ η → fext! (λ ρ → get◐ᵥ η ρ i)
    }


-- TODO
-- evalNT : ∀ {Ξ A} → (M : Ξ ⊢ A)
--                  → NaturalTransformation (flip◐ᵥPsh Ξ) (accPsh A)
-- evalNT M =
--   record
--     { ϕ    = flip eval M
--     ; natϕ = λ η → fext! (λ ρ → eval◐ᵥ {ρ = ρ} η {!!} M)
--     }

-- TODO
-- reifyNT : ∀ {A} → NaturalTransformation (accPsh A) (renⁿᶠPsh A)
-- reifyNT =
--   record
--     { ϕ    = reify
--     ; natϕ = λ η → fext! (λ a → natreify η a {!!})
--     }

reflectNT : ∀ {A} → NaturalTransformation (renⁿᵉPsh A) (accPsh A)
reflectNT =
  record
    { ϕ    = reflect
    ; natϕ = λ η → fext! (λ M → natreflect η M)
    }
