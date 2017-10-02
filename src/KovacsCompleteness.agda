module KovacsCompleteness where

open import KovacsNormalisation public
open import KovacsConvertibility public


infix 3 _≫_
_≫_ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A → Set

_≫_ {⎵}     {Γ} M N = M ∼ embⁿᶠ N

_≫_ {A ⊃ B} {Γ} M f = ∀ {Γ′} → (η : Γ′ ⊇ Γ) {N : Γ′ ⊢ A} {a : Γ′ ⊩ A} (p : N ≫ a)
                             → (ren η M ∙ N) ≫ f η a


-- (_≈ᶜ_ ; _∙_ ; _,_)
infix 3 _≫⋆_
data _≫⋆_ : ∀ {Γ Ξ} → Γ ⊢⋆ Ξ → Γ ⊩⋆ Ξ → Set
  where
    []    : ∀ {Γ} → ([] {Γ = Γ}) ≫⋆ []

    [_,_] : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                      → (χ : σ ≫⋆ ρ) {M : Γ ⊢ A} {a : Γ ⊩ A} (p : M ≫ a)
                      → [ σ , M ] ≫⋆ [ ρ , a ]


-- (≈ₑ)
con : ∀ {A Γ Γ′} → {M : Γ ⊢ A} {a : Γ ⊩ A}
                 → (η : Γ′ ⊇ Γ) → M ≫ a
                 → ren η M ≫ acc η a
con {⎵}     {M = M} {N} η p = cast ren∼ η p via
                                ((λ N′ → ren η M ∼ N′) & (natembⁿᶠ η N ⁻¹))
con {A ⊃ B} {M = M} {f} η g η′ rewrite ren○ η′ η M ⁻¹
                            = g (η ○ η′)

-- (≈ᶜₑ)
_◧_ : ∀ {Γ Γ′ Ξ} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                 → (χ : σ ≫⋆ ρ) (η : Γ′ ⊇ Γ)
                 → σ ◐ η ≫⋆ ρ ⬖ η
[]        ◧ η = []
[ χ , p ] ◧ η = [ χ ◧ η , con η p ]


-- (_∼◾≈_)
infixl 4 _∼⦙≫_
_∼⦙≫_ : ∀ {A Γ} → {M M′ : Γ ⊢ A} {a : Γ ⊩ A}
                → M ∼ M′ → M′ ≫ a
                → M ≫ a
_∼⦙≫_ {⎵}     p q = p ⦙∼ q
_∼⦙≫_ {A ⊃ B} p f = λ η q → ren∼ η p ∙∼ refl∼ ∼⦙≫ f η q


-- (∈≈)
get≫ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                 → σ ≫⋆ ρ → (i : Ξ ∋ A)
                 → getₛ σ i ≫ getᵥ ρ i
get≫ [ χ , p ] zero    = p
get≫ [ χ , p ] (suc i) = get≫ χ i

-- (Tm≈)
eval≫ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                  → σ ≫⋆ ρ → (M : Ξ ⊢ A)
                  → sub σ M ≫ eval ρ M
eval≫ {σ = σ} {ρ} χ (` i)   = get≫ χ i
eval≫ {σ = σ} {ρ} χ (ƛ M)   = λ η {N} {a} q →
                                cast βred∼ (ren (liftₑ η) (sub (liftₛ σ) M)) N via
                                  (((ƛ (ren (liftₑ η) (sub (liftₛ σ) M)) ∙ N) ∼_)
                                   & ( sub◑ [ idₛ , N ] (liftₑ η) (sub (liftₛ σ) M) ⁻¹
                                     ⦙ sub● (liftₑ η ◑ [ idₛ , N ]) (liftₛ σ) M ⁻¹
                                     ⦙ (λ σ′ → sub [ σ′ , N ] M)
                                       & ( comp●◑ [ η ◑ idₛ , N ] (wkₑ idₑ) σ
                                         ⦙ (σ ●_) & id₁◑ (η ◑ idₛ)
                                         ⦙ comp●◑ idₛ η σ ⁻¹
                                         ⦙ id₂● (σ ◐ η)
                                         )
                                     ))
                                ∼⦙≫
                                eval≫ [ χ ◧ η , q ] M
eval≫ {σ = σ} {ρ} χ (M ∙ N) rewrite idren (sub σ M) ⁻¹
                            = eval≫ χ M idₑ (eval≫ χ N)

mutual
  -- (q≈)
  reify≫ : ∀ {A Γ} → {M : Γ ⊢ A} {a : Γ ⊩ A}
                   → (p : M ≫ a)
                   → M ∼ embⁿᶠ (reify a)
  reify≫ {⎵}     {M = M} p = p
  reify≫ {A ⊃ B} {M = M} f = ηexp∼ M ⦙∼ ƛ∼ (reify≫ (f (wkₑ idₑ) (reflect≫ (` zero))))

  -- (u≈)
  reflect≫ : ∀ {A Γ} → (M : Γ ⊢ⁿᵉ A)
                     → embⁿᵉ M ≫ reflect M
  reflect≫ {⎵}     M = refl∼
  reflect≫ {A ⊃ B} M η {N} {a} rewrite natembⁿᵉ η M ⁻¹
                     = λ p → refl∼ ∙∼ reify≫ p ∼⦙≫ reflect≫ (renⁿᵉ η M ∙ reify a)


-- (uᶜ≈)
id₌ : ∀ {Γ} → idₛ {Γ} ≫⋆ idᵥ
id₌ {[]}        = []
id₌ {[ Γ , A ]} = [ id₌ ◧ wkₑ idₑ , reflect≫ (` zero) ]


complete : ∀ {Γ A} → (M : Γ ⊢ A)
                   → M ∼ embⁿᶠ (nf M)
complete M = cast reify≫ (eval≫ id₌ M) via
               ((_∼ embⁿᶠ (reify (eval idᵥ M))) & idsub M)
