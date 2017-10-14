module STLCP.Kovacs.Completeness where

open import STLCP.Kovacs.Normalisation public
open import STLCP.Kovacs.Convertibility public


--------------------------------------------------------------------------------


-- (_≈_)
infix 3 _≫_
_≫_ : ∀ {A Γ} → Γ ⊢ A → Γ ⊩ A → Set

_≫_ {⎵}      {Γ} M N = M ∼ embⁿᶠ N

_≫_ {A ⇒ B} {Γ} M f = ∀ {Γ′} → (η : Γ′ ⊇ Γ) {N : Γ′ ⊢ A} {a : Γ′ ⊩ A}
                                 (p : N ≫ a)
                              → ren η M ∙ N ≫ f η a

_≫_ {A ⩕ B}  {Γ} M s = π₁ M ≫ proj₁ s × π₂ M ≫ proj₂ s

_≫_ {⫪}     {Γ} M s = ⊤


-- (_≈ᶜ_)
infix 3 _≫⋆_
data _≫⋆_ : ∀ {Γ Ξ} → Γ ⊢⋆ Ξ → Γ ⊩⋆ Ξ → Set
  where
    ∅   : ∀ {Γ} → ∅ {Γ = Γ} ≫⋆ ∅

    _,_ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ} {M : Γ ⊢ A} {a : Γ ⊩ A}
                    → (χ : σ ≫⋆ ρ) (p : M ≫ a)
                    → σ , M ≫⋆ ρ , a


--------------------------------------------------------------------------------


-- (_∼◾≈_)
coe≫ : ∀ {A Γ} → {M₁ M₂ : Γ ⊢ A} {a : Γ ⊩ A}
               → M₁ ∼ M₂ → M₁ ≫ a
               → M₂ ≫ a
coe≫ {⎵}      p q = p ⁻¹ ⦙ q
coe≫ {A ⇒ B} p f = λ η q →
                      coe≫ (ren∼ η p ∙∼ refl∼)
                           (f η q)
coe≫ {A ⩕ B}  p q = coe≫ (π₁∼ p) (proj₁ q) , coe≫ (π₂∼ p) (proj₂ q)
coe≫ {⫪}     p q = tt


--------------------------------------------------------------------------------


-- (≈ₑ)
acc≫ : ∀ {A Γ Γ′} → (η : Γ′ ⊇ Γ)
                  → {M : Γ ⊢ A} {a : Γ ⊩ A}
                  → M ≫ a
                  → ren η M ≫ acc η a
acc≫ {⎵}      η {M} {N} p = coe ((λ N′ → ren η M ∼ N′) & (natembⁿᶠ η N ⁻¹))
                                (ren∼ η p)
acc≫ {A ⇒ B} η {M} {f} g η′
                          rewrite ren○ η′ η M ⁻¹
                          = g (η ○ η′)
acc≫ {A ⩕ B}  η {M} {s} q = acc≫ η (proj₁ q) , acc≫ η (proj₂ q)
acc≫ {⫪}     η {M} {s} q = tt


-- (≈ᶜₑ)
-- NOTE: _⬖≫_ = ∂acc≫⋆
_⬖≫_ : ∀ {Γ Γ′ Ξ} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                  → (χ : σ ≫⋆ ρ) (η : Γ′ ⊇ Γ)
                  → σ ◐ η ≫⋆ ρ ⬖ η
∅       ⬖≫ η = ∅
(χ , p) ⬖≫ η = χ ⬖≫ η , acc≫ η p


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

eval≫ χ (` i)
  = get≫ χ i

eval≫ {σ = σ} χ (ƛ M) η {N} q
  = coe≫ (coe (((ƛ (ren (liftₑ η) (sub (liftₛ σ) M)) ∙ N) ∼_)
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

eval≫ {σ = σ} χ (M , N)
  = coe≫ (red⩕₁ (sub σ M) (sub σ N) ⁻¹) (eval≫ χ M)
  , coe≫ (red⩕₂ (sub σ M) (sub σ N) ⁻¹∼) (eval≫ χ N)

eval≫ {σ = σ} χ (π₁ M)
  = proj₁ (eval≫ χ M)

eval≫ {σ = σ} χ (π₂ M)
  = proj₂ (eval≫ χ M)

eval≫ {σ = σ} χ τ
  = tt


--------------------------------------------------------------------------------


mutual
  -- (q≈)
  reify≫ : ∀ {A Γ} → {M : Γ ⊢ A} {a : Γ ⊩ A}
                   → (p : M ≫ a)
                   → M ∼ embⁿᶠ (reify a)
  reify≫ {⎵}      {M = M} p = p
  reify≫ {A ⇒ B} {M = M} f = exp⇒ M
                            ⦙ ƛ∼ (reify≫ (f (wkₑ idₑ) (reflect≫ 0)))
  reify≫ {A ⩕ B}  {M = M} s = exp⩕ M
                            ⦙ reify≫ (proj₁ s) ,∼ reify≫ (proj₂ s)
  reify≫ {⫪}     {M = M} s = exp⫪ M

  -- (u≈)
  reflect≫ : ∀ {A Γ} → (M : Γ ⊢ⁿᵉ A)
                     → embⁿᵉ M ≫ reflect M
  reflect≫ {⎵}      M = refl∼
  reflect≫ {A ⇒ B} M η {N} {a} p
                      rewrite natembⁿᵉ η M ⁻¹
                      = coe≫ (refl∼ ∙∼ reify≫ p ⁻¹)
                             (reflect≫ (renⁿᵉ η M ∙ reify a))
  reflect≫ {A ⩕ B}  M = reflect≫ (π₁ M) , reflect≫ (π₂ M)
  reflect≫ {⫪}     M = tt


-- (uᶜ≈)
id≫⋆ : ∀ {Γ} → idₛ {Γ} ≫⋆ idᵥ
id≫⋆ {∅}     = ∅
id≫⋆ {Γ , A} = id≫⋆ ⬖≫ wkₑ idₑ , reflect≫ 0


complete : ∀ {Γ A} → (M : Γ ⊢ A)
                   → M ∼ embⁿᶠ (nf M)
complete M = coe ((_∼ embⁿᶠ (reify (eval idᵥ M))) & idsub M)
                 (reify≫ (eval≫ id≫⋆ M))


--------------------------------------------------------------------------------
