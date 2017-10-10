module STLC.Kovacs.Completeness where

open import STLC.Kovacs.Normalisation public
open import STLC.Kovacs.Convertibility public


--------------------------------------------------------------------------------


-- (_≈_)
infix 3 _≫_
_≫_ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A → Set

_≫_ {⎵}      {Γ} M N = M ∼ embⁿᶠ N

_≫_ {A ⇒ B} {Γ} M f = ∀ {Γ′} → (η : Γ′ ⊇ Γ) {N : Γ′ ⊢ A} {a : Γ′ ⊩ A}
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
acc≫ {⎵}      {M = M} {N} η p = coe ((λ N′ → ren η M ∼ N′) & (natembⁿᶠ η N ⁻¹))
                                    (ren∼ η p)

acc≫ {A ⇒ B} {M = M} {f} η g η′ rewrite ren○ η′ η M ⁻¹
                              = g (η ○ η′)

-- (≈ᶜₑ)
_⬖≫_ : ∀ {Γ Γ′ Ξ} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                  → (χ : σ ≫⋆ ρ) (η : Γ′ ⊇ Γ)
                  → σ ◐ η ≫⋆ ρ ⬖ η
∅       ⬖≫ η = ∅
(χ , p) ⬖≫ η = χ ⬖≫ η , acc≫ η p


-- (_∼◾≈_)
coe≫ : ∀ {A Γ} → {M₁ M₂ : Γ ⊢ A} {a : Γ ⊩ A}
               → M₁ ∼ M₂ → M₁ ≫ a
               → M₂ ≫ a
coe≫ {⎵}      p q = p ⁻¹ ⦙ q
coe≫ {A ⇒ B} p f = λ η q →
                      coe≫ (ren∼ η p ∙∼ refl∼)
                           (f η q)


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
  coe≫ (coe (((ƛ (ren (liftₑ η) (sub (liftₛ σ) M)) ∙ N) ∼_)
             & ( sub◑ (idₛ , N) (liftₑ η) (sub (liftₛ σ) M) ⁻¹
               ⦙ sub● (liftₑ η ◑ (idₛ , N)) (liftₛ σ) M ⁻¹
               ⦙ (λ σ′ → sub (σ′ , N) M)
                 & ( comp●◑ (η ◑ idₛ , N) (wkₑ idₑ) σ
                   ⦙ (σ ●_) & lid◑ (η ◑ idₛ)
                   ⦙ comp●◑ idₛ η σ ⁻¹
                   ⦙ rid● (σ ◐ η)
                   )
               ))
            (red⇒ (ren (liftₑ η) (sub (liftₛ σ) M)) N) ⁻¹)
       (eval≫ (χ ⬖≫ η , q) M)

eval≫ {σ = σ} χ (M ∙ N)
  rewrite idren (sub σ M) ⁻¹
  = eval≫ χ M idₑ (eval≫ χ N)


mutual
  -- (q≈)
  reify≫ : ∀ {A Γ} → {M : Γ ⊢ A} {a : Γ ⊩ A}
                   → (p : M ≫ a)
                   → M ∼ embⁿᶠ (reify a)
  reify≫ {⎵}      {M = M} p = p
  reify≫ {A ⇒ B} {M = M} f = exp⇒ M
                            ⦙ ƛ∼ (reify≫ (f (wkₑ idₑ) (reflect≫ 0)))

  -- (u≈)
  reflect≫ : ∀ {A Γ} → (M : Γ ⊢ⁿᵉ A)
                     → embⁿᵉ M ≫ reflect M
  reflect≫ {⎵}      M = refl∼
  reflect≫ {A ⇒ B} M η {N} {a} p rewrite natembⁿᵉ η M ⁻¹
                      = coe≫ (refl∼ ∙∼ reify≫ p ⁻¹)
                             (reflect≫ (renⁿᵉ η M ∙ reify a))


-- (uᶜ≈)
id≫⋆ : ∀ {Γ} → idₛ {Γ} ≫⋆ idᵥ
id≫⋆ {∅}     = ∅
id≫⋆ {Γ , A} = id≫⋆ ⬖≫ wkₑ idₑ , reflect≫ 0


complete : ∀ {Γ A} → (M : Γ ⊢ A)
                   → M ∼ embⁿᶠ (nf M)
complete M = coe ((_∼ embⁿᶠ (reify (eval idᵥ M))) & idsub M)
                 (reify≫ (eval≫ id≫⋆ M))


--------------------------------------------------------------------------------
