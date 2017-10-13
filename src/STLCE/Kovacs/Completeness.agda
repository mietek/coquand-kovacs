module STLCE.Kovacs.Completeness where

open import STLCE.Kovacs.Normalisation public
open import STLCE.Kovacs.Convertibility public


postulate
  oops : ∀ {ℓ} → {X : Set ℓ} → X


--------------------------------------------------------------------------------


-- (_≈_)
mutual
  infix 3 _≫_
  _≫_ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A → Set
  _≫_ {⎵}      {Γ} M N = M ∼ embⁿᶠ N
  _≫_ {A ⇒ B} {Γ} M f = ∀ {Γ′} → (η : Γ′ ⊇ Γ)
                                → {N : Γ′ ⊢ A} {∂a : Γ′ ∂⊩ A}
                                → N ∂≫ ∂a
                                → ren η M ∙ N ∂≫ f η ∂a
  _≫_ {A ⩕ B}  {Γ} M s = π₁ M ∂≫ proj₁ s × π₂ M ∂≫ proj₂ s
  _≫_ {⫪}     {Γ} M s = ⊤
  _≫_ {⫫}     {Γ} M s = ⊥
  _≫_ {A ⩖ B}  {Γ} M s = elim⊎ s (λ ∂a → Σ (Γ ⊢ A) (λ M₁ → M₁ ∂≫ ∂a))
                                 (λ ∂b → Σ (Γ ⊢ B) (λ M₂ → M₂ ∂≫ ∂b))

  infix 3 _∂≫_
  _∂≫_ : ∀ {Γ A} → Γ ⊢ A → Γ ∂⊩ A → Set
  _∂≫_ {Γ} {A} M ∂a = ∀ {Γ′ C} → (η : Γ′ ⊇ Γ)
                               → {N : Γ′ ⊢ C} {Nⁿᶠ : Γ′ ⊢ⁿᶠ C}
                               → (f : ∀ {Γ″} → (η′ : Γ″ ⊇ Γ′)
                                              → {a : Γ″ ⊩ A}
                                              → ren (η ○ η′) M ≫ a
                                              → ren η′ N ∼ embⁿᶠ (renⁿᶠ η′ Nⁿᶠ))
                               → N ∼ embⁿᶠ Nⁿᶠ


-- (_∼◾≈_)
mutual
  coe≫ : ∀ {A Γ} → {M₁ M₂ : Γ ⊢ A}
                 → M₁ ∼ M₂ → {a : Γ ⊩ A} → M₁ ≫ a
                 → M₂ ≫ a
  coe≫ {⎵}      p {N}      q = p ⁻¹ ⦙ q
  coe≫ {A ⇒ B} p {f}      g = λ η {N} {∂a} ∂q →
                                 ∂coe≫ {∂a = λ η′ f′ → f η ∂a η′ f′}
                                       (ren∼ η p ∙∼ (refl∼ {M = N}))
                                       (g η {N} {∂a} ∂q)
  coe≫ {A ⩕ B}  p {s}      q = ∂coe≫ {∂a = proj₁ s} (π₁∼ p) (proj₁ q) ,
                               ∂coe≫ {∂a = proj₂ s} (π₂∼ p) (proj₂ q)
  coe≫ {⫪}     p {s}      q = tt
  coe≫ {⫫}     p {s}      q = elim⊥ s
  coe≫ {A ⩖ B}  p {inj₁ a} q = q
  coe≫ {A ⩖ B}  p {inj₂ b} q = q

  ∂coe≫ : ∀ {A Γ} → {M₁ M₂ : Γ ⊢ A} {∂a : Γ ∂⊩ A}
                  → M₁ ∼ M₂ → M₁ ∂≫ ∂a
                  → M₂ ∂≫ ∂a
  ∂coe≫ p ∂q =
    λ η {N} {Nⁿᶠ} f →
      ∂q η {N} {Nⁿᶠ} (λ η′ {a} q →
        f η′ (coe≫ (ren∼ (η ○ η′) p)
                   q))


--------------------------------------------------------------------------------


-- (≈ₑ)
mutual
  acc≫ : ∀ {A Γ Γ′} → (η : Γ′ ⊇ Γ)
                    → {M : Γ ⊢ A} {a : Γ ⊩ A}
                    → M ≫ a
                    → ren η M ≫ acc η a
  acc≫ {⎵}      η {M} {N}      p         = coe ((λ N′ → ren η M ∼ N′)
                                                & natembⁿᶠ η N ⁻¹)
                                               (ren∼ η p)
  acc≫ {A ⇒ B} η {M} {f}      g         η′ {N} {∂a} rewrite ren○ η′ η M ⁻¹
                                         = g (η ○ η′) {N} {∂a}
  acc≫ {A ⩕ B}  η {M} {s}      q         = ∂acc≫ η {π₁ M} {proj₁ s} (proj₁ q)
                                         , ∂acc≫ η {π₂ M} {proj₂ s} (proj₂ q)
  acc≫ {⫪}     η {M} {s}      q         = tt
  acc≫ {⫫}     η {M} {s}      q         = elim⊥ s
  acc≫ {A ⩖ B}  η {M} {inj₁ a} (M₁ , ∂a) = ren η M₁ , ∂acc≫ η {M₁} {a} ∂a
  acc≫ {A ⩖ B}  η {M} {inj₂ b} (M₂ , ∂b) = ren η M₂ , ∂acc≫ η {M₂} {b} ∂b

  ∂acc≫ : ∀ {A Γ Γ′} → (η : Γ′ ⊇ Γ)
                     → {M : Γ ⊢ A} {∂a : Γ ∂⊩ A}
                     → M ∂≫ ∂a
                     → ren η M ∂≫ ∂acc η ∂a
  ∂acc≫ η {M} ∂q =
    λ η′ {N} {Nⁿᶠ} f →
      ∂q (η ○ η′) {N} {Nⁿᶠ} (λ η″ {a} q →
        f η″ (coe≫ (coe (( (λ M′ → M′ ∼ ren (η ○ (η′ ○ η″)) M)
                            & ((λ η′ → ren η′ M)
                               & assoc○ η″ η′ η ⁻¹)
                         ⦙ (λ M′ → ren ((η ○ η′) ○ η″) M ∼ M′)
                            & ren○ (η′ ○ η″) η M
                         )) refl∼)
                   q))


--------------------------------------------------------------------------------


-- (_≈ᶜ_)
infix 3 _∂≫⋆_
data _∂≫⋆_ : ∀ {Γ Ξ} → Γ ⊢⋆ Ξ → Γ ∂⊩⋆ Ξ → Set
  where
    ∅   : ∀ {Γ} → ∅ {Γ} ∂≫⋆ ∅

    _,_ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ∂⊩⋆ Ξ}
                    → (χ : σ ∂≫⋆ ρ)
                    → {M : Γ ⊢ A} {∂a : Γ ∂⊩ A}
                    → (∂q : M ∂≫ ∂a)
                    → σ , M ∂≫⋆ ρ , ∂a

-- (≈ᶜₑ)
_⬖≫_ : ∀ {Γ Γ′ Ξ} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ∂⊩⋆ Ξ}
                  → (χ : σ ∂≫⋆ ρ) (η : Γ′ ⊇ Γ)
                  → σ ◐ η ∂≫⋆ ρ ⬖ η
∅                 ⬖≫ η = ∅
_,_ χ {M} {∂a} ∂q ⬖≫ η = χ ⬖≫ η , ∂acc≫ η {M} {∂a} ∂q


--------------------------------------------------------------------------------


return≫ : ∀ {A Γ} → {M : Γ ⊢ A} {a : Γ ⊩ A}
                  → M ≫ a → M ∂≫ return a
return≫ {M = M} {a} q =
  λ η {N} {Nⁿᶠ} f →
    coe (_∼_ & idren N
             ⊗ embⁿᶠ & idrenⁿᶠ Nⁿᶠ)
        (f idₑ {acc η a}
               (coe≫ (coe ((λ η′ → ren η M ∼ ren η′ M)
                           & (rid○ η ⁻¹))
                          refl∼)
                     (acc≫ η {M} {a} q)))

bind≫ : ∀ {A C Γ} → {M : Γ ⊢ A} {∂a : Γ ∂⊩ A}
                     {N : Γ ⊢ C} {∂c : Γ ∂⊩ C}
                  → M ∂≫ ∂a → (∀ {Γ′} → (η : Γ′ ⊇ Γ)
                                        → {a : Γ′ ⊩ A}
                                        → ren η M ≫ a
                                        → ren η N ∂≫ ∂acc η ∂c)
                  → N ∂≫ ∂c
bind≫ {M = M} {∂a} {N} {∂c} ∂q f =
  λ η {N′} {Nⁿᶠ′} f′ →
    ∂q η {N′} {Nⁿᶠ′} (λ η′ {a} q →
      f (η ○ η′) {a} q idₑ {ren η′ N′} {renⁿᶠ η′ Nⁿᶠ′} (λ η″ {c} q′ →
        coe (_∼_ & ren○ η″ η′ N′
                 ⊗ embⁿᶠ & renⁿᶠ○ η″ η′ Nⁿᶠ′)
            (f′ (η′ ○ η″) {c} (coe≫ {M₁ = ren (idₑ ○ η″) (ren (η ○ η′) N)}
                                    {M₂ = ren (η ○ (η′ ○ η″)) N}
                                    (coe (_∼_ & ren○ (idₑ ○ η″) (η ○ η′) N
                                              ⊗ (λ ‵η → ren ‵η N)
                                                & ( (λ ‶η → (η ○ η′) ○ ‶η)
                                                    & lid○ η″
                                                  ⦙ assoc○ η″ η′ η
                                                  ))
                                         refl∼)
                                    {c}
                                    q′))))


--------------------------------------------------------------------------------


-- (∈≈)
get≫ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ∂⊩⋆ Ξ}
                 → σ ∂≫⋆ ρ → (i : Ξ ∋ A)
                 → getₛ σ i ∂≫ getᵥ ρ i
get≫ (χ , p) zero    = p
get≫ (χ , p) (suc i) = get≫ χ i


-- (Tm≈)
eval≫ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ∂⊩⋆ Ξ}
                 → σ ∂≫⋆ ρ → (M : Ξ ⊢ A)
                 → sub σ M ∂≫ eval ρ M

eval≫ {σ = σ} {ρ} χ (` i) = get≫ χ i

eval≫ {σ = σ} {ρ} χ (ƛ M) =
  return≫ {M = ƛ (sub (liftₛ σ) M)}
          {a = λ {Γ′} η ∂a → eval (ρ ⬖ η , ∂a) M}
    (λ {Γ′} η {N} {∂a} ∂q →
      ∂coe≫ {∂a = eval (ρ ⬖ η , ∂a) M}
            ((coe (((ƛ (ren (liftₑ η) (sub (liftₛ σ) M)) ∙ N) ∼_)
                   & ( sub◑ (idₛ , N) (liftₑ η) (sub (liftₛ σ) M) ⁻¹
                     ⦙ sub● (liftₑ η ◑ (idₛ , N)) (liftₛ σ) M ⁻¹
                     ⦙ (λ σ′ → sub (σ′ , N) M)
                       & ( comp●◑ (η ◑ idₛ , N) (wkₑ idₑ) σ
                         ⦙ (σ ●_) & lid◑ (η ◑ idₛ)
                         ⦙ comp●◑ idₛ η σ ⁻¹
                         ⦙ rid● (σ ◐ η)
                         )
                     ))
                  (red⇒ (ren (liftₑ η) (sub (liftₛ σ) M)) N) ⁻¹))
            (eval≫ (_,_ (χ ⬖≫ η) {∂a = ∂a} (∂q)) M))

eval≫ {σ = σ} {ρ} χ (M ∙ N) =
  bind≫ {M  = sub σ M}
        {∂a = eval ρ M}
        {N  = sub σ M ∙ sub σ N}
        {∂c = eval ρ M ∂!∙ eval ρ N}
    (eval≫ χ M)
    oops
    -- (λ η q → coe ?
    --               (q idₑ (coe ?
    --                           (eval≫ χ N))))

eval≫ {σ = σ} {ρ} χ (M , N) =
  return≫ {M = sub σ M , sub σ N}
          {a = eval ρ M , eval ρ N}
    ( ∂coe≫ {∂a = eval ρ M}
            (red⩕₁ (sub σ M) (sub σ N) ⁻¹)
            (eval≫ χ M)
    , ∂coe≫ {∂a = eval ρ N}
            (red⩕₂ (sub σ M) (sub σ N) ⁻¹)
            (eval≫ χ N)
    )

eval≫ {σ = σ} {ρ} χ (π₁ M) =
  bind≫ {M  = sub σ M}
        {∂a = eval ρ M}
        {N  = π₁ (sub σ M)}
        {∂c = ∂!π₁ (eval ρ M)}
    (eval≫ χ M)
    (λ η q → proj₁ q)

eval≫ {σ = σ} {ρ} χ (π₂ M) =
  bind≫ {M  = sub σ M}
        {∂a = eval ρ M}
        {N  = π₂ (sub σ M)}
        {∂c = ∂!π₂ (eval ρ M)}
    (eval≫ χ M)
    (λ η q → proj₂ q)

eval≫ {σ = σ} {ρ} χ τ =
  return≫ {M = τ} tt

eval≫ {σ = σ} {ρ} χ (φ M) =
  bind≫ {M  = sub σ M}
        {∂a = eval ρ M}
        {N  = φ (sub σ M)}
        {∂c = ∂!φ (eval ρ M)}
    (eval≫ χ M)
    (λ η q → elim⊥ q)

eval≫ {σ = σ} {ρ} χ (ι₁ M) =
  return≫ {M = ι₁ (sub σ M)}
          {a = inj₁ (eval ρ M)}
    (sub σ M , eval≫ χ M)

eval≫ {σ = σ} {ρ} χ (ι₂ M) =
  return≫ {M = ι₂ (sub σ M)}
          {a = inj₂ (eval ρ M)}
  (sub σ M , eval≫ χ M)

eval≫ {σ = σ} {ρ} χ (M ⁇ N₁ ∥ N₂) =
  oops


mutual
  -- (q≈)
  reify≫ : ∀ {A Γ} → {M : Γ ⊢ A} {a : Γ ∂⊩ A}
                   → (∂q : M ∂≫ a)
                   → M ∼ embⁿᶠ (reify a)
  reify≫ = oops

  -- (u≈)
  reflect≫ : ∀ {A Γ} → (M : Γ ⊢ⁿᵉ A)
                     → embⁿᵉ M ∂≫ reflect M
  reflect≫ = oops


-- (uᶜ≈)
id≫⋆ : ∀ {Γ} → idₛ {Γ} ∂≫⋆ idᵥ
id≫⋆ {∅}     = ∅
id≫⋆ {Γ , A} = id≫⋆ ⬖≫ wkₑ idₑ , reflect≫ 0


complete : ∀ {Γ A} → (M : Γ ⊢ A)
                   → M ∼ embⁿᶠ (nf M)
complete M = coe ((_∼ embⁿᶠ (reify (eval idᵥ M))) & idsub M)
                 (reify≫ (eval≫ id≫⋆ M))


--------------------------------------------------------------------------------
