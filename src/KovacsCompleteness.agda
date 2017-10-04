module KovacsCompleteness where

open import KovacsNormalisation public
open import KovacsConvertibility public


--------------------------------------------------------------------------------


-- (_≈_)
infix 3 _≫_
_≫_ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A → Set

_≫_ {⎵}     {Γ} M N = M ∼ embⁿᶠ N

_≫_ {A ⊃ B} {Γ} M f = ∀ {Γ′} → (η : Γ′ ⊇ Γ) {N : Γ′ ⊢ A} {a : Γ′ ⊩ A}
                                (p : N ≫ a)
                             → ren η M ∙ N ≫ f η a


-- (_≈ᶜ_)
infix 3 _≫⋆_
data _≫⋆_ : ∀ {Γ Ξ} → Γ ⊢⋆ Ξ → Γ ⊩⋆ Ξ → Set
  where
    ∅   : ∀ {Γ} → ∅ {Γ = Γ} ≫⋆ ∅

    _,_ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ} {M : Γ ⊢ A} {a : Γ ⊩ A}
                    → (χ : σ ≫⋆ ρ) (p : M ≫ a)
                    → σ , M ≫⋆ ρ , a


--------------------------------------------------------------------------------


-- (≈ₑ)
acc≫ : ∀ {A Γ Γ′} → {M : Γ ⊢ A} {a : Γ ⊩ A}
                  → (η : Γ′ ⊇ Γ) → M ≫ a
                  → ren η M ≫ acc η a
acc≫ {⎵}     {M = M} {N} η p = cast
                                 ren∼ η p
                               via
                                 ((λ N′ → ren η M ∼ N′) & (natembⁿᶠ η N ⁻¹))
acc≫ {A ⊃ B} {M = M} {f} η g η′ rewrite ren○ η′ η M ⁻¹
                             = g (η ○ η′)

-- (≈ᶜₑ)
_⬖≫_ : ∀ {Γ Γ′ Ξ} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                  → (χ : σ ≫⋆ ρ) (η : Γ′ ⊇ Γ)
                  → σ ◐ η ≫⋆ ρ ⬖ η
∅       ⬖≫ η = ∅
(χ , p) ⬖≫ η = χ ⬖≫ η , acc≫ η p


-- (_∼◾≈_)
cast≫_via_ : ∀ {A Γ} → {M₁ M₂ : Γ ⊢ A} {a : Γ ⊩ A}
                     → M₁ ≫ a → M₁ ∼ M₂
                     → M₂ ≫ a
cast≫_via_ {⎵}     p q = q ⁻¹ ⦙ p
cast≫_via_ {A ⊃ B} f p = λ η q →
                            cast≫
                              f η q
                            via
                              (ren∼ η p ∙∼ refl∼)


--------------------------------------------------------------------------------


-- (∈≈)
get≫ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                 → σ ≫⋆ ρ → (i : Ξ ∋ A)
                 → getₛ σ i ≫ getᵥ ρ i
get≫ (χ , p) zero    = p
get≫ (χ , p) (suc i) = get≫ χ i


-- (Tm≈)
eval≫ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                  → σ ≫⋆ ρ → (M : Ξ ⊢ A)
                  → sub σ M ≫ eval ρ M

eval≫ χ (` i) = get≫ χ i

eval≫ {σ = σ} χ (ƛ M) η {N} q =
  cast≫
    eval≫ (χ ⬖≫ η , q) M
  via
    (cast
       βred∼ (ren (liftₑ η) (sub (liftₛ σ) M)) N
     via
       (((ƛ (ren (liftₑ η) (sub (liftₛ σ) M)) ∙ N) ∼_)
        & ( sub◑ (idₛ , N) (liftₑ η) (sub (liftₛ σ) M) ⁻¹
          ⦙ sub● (liftₑ η ◑ (idₛ , N)) (liftₛ σ) M ⁻¹
          ⦙ (λ σ′ → sub (σ′ , N) M)
            & ( comp●◑ (η ◑ idₛ , N) (wkₑ idₑ) σ
              ⦙ (σ ●_) & lid◑ (η ◑ idₛ)
              ⦙ comp●◑ idₛ η σ ⁻¹
              ⦙ rid● (σ ◐ η)
              )
          )) ⁻¹)

eval≫ {σ = σ} χ (M ∙ N)
  rewrite idren (sub σ M) ⁻¹
  = eval≫ χ M idₑ (eval≫ χ N)


mutual
  -- (q≈)
  reify≫ : ∀ {A Γ} → {M : Γ ⊢ A} {a : Γ ⊩ A}
                   → (p : M ≫ a)
                   → M ∼ embⁿᶠ (reify a)
  reify≫ {⎵}     {M = M} p = p
  reify≫ {A ⊃ B} {M = M} f = ηexp∼ M
                           ⦙ ƛ∼ (reify≫ (f (wkₑ idₑ) (reflect≫ (` zero))))

  -- (u≈)
  reflect≫ : ∀ {A Γ} → (M : Γ ⊢ⁿᵉ A)
                     → embⁿᵉ M ≫ reflect M
  reflect≫ {⎵}     M = refl∼
  reflect≫ {A ⊃ B} M η {N} {a} p rewrite natembⁿᵉ η M ⁻¹
                     = cast≫
                         reflect≫ (renⁿᵉ η M ∙ reify a)
                       via
                         (refl∼ ∙∼ reify≫ p ⁻¹)


-- (uᶜ≈)
id≫⋆ : ∀ {Γ} → idₛ {Γ} ≫⋆ idᵥ
id≫⋆ {∅}     = ∅
id≫⋆ {Γ , A} = id≫⋆ ⬖≫ wkₑ idₑ , reflect≫ (` zero)


complete : ∀ {Γ A} → (M : Γ ⊢ A)
                   → M ∼ embⁿᶠ (nf M)
complete M = cast
               reify≫ (eval≫ id≫⋆ M)
             via
               ((_∼ embⁿᶠ (reify (eval idᵥ M))) & idsub M)


--------------------------------------------------------------------------------
