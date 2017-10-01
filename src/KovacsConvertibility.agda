module KovacsConvertibility where

open import KovacsSubstitution public


-- Convertibility (_~_ ; ~refl ; _~⁻¹ ; lam ; app ; β ; η)
infix  3 _≅_
infix  6 _⁻¹≅
infixl 4 _⦙≅_
data _≅_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
  where
    refl≅ : ∀ {Γ A} → {M : Γ ⊢ A}
                    → M ≅ M

    _⁻¹≅  : ∀ {Γ A} → {M M′ : Γ ⊢ A}
                    → (p : M ≅ M′)
                    → M′ ≅ M

    _⦙≅_  : ∀ {Γ A} → {M M′ M″ : Γ ⊢ A}
                    → (p : M ≅ M′) (q : M′ ≅ M″)
                    → M ≅ M″

    ƛ≅    : ∀ {Γ A B} → {M M′ : [ Γ , A ] ⊢ B}
                      → (p : M ≅ M′)
                      → ƛ M ≅ ƛ M′

    _∙≅_  : ∀ {Γ A B} → {M M′ : Γ ⊢ A ⊃ B} {N N′ : Γ ⊢ A}
                      → (p : M ≅ M′) (q : N ≅ N′)
                      → M ∙ N ≅ M′ ∙ N′

    βred≅ : ∀ {Γ A B} → (M : [ Γ , A ] ⊢ B) (N : Γ ⊢ A)
                      → (ƛ M) ∙ N ≅ sub [ idₛ , N ] M

    ηexp≅ : ∀ {Γ A B} → (M : Γ ⊢ A ⊃ B)
                      → M ≅ ƛ (wk M ∙ ` zero)


--------------------------------------------------------------------------------


-- (~ₑ)
ren≅ : ∀ {Γ Γ′ A} → {M M′ : Γ ⊢ A}
                  → (η : Γ′ ⊇ Γ) → M ≅ M′
                  → ren η M ≅ ren η M′
ren≅ η refl≅       = refl≅
ren≅ η (p ⁻¹≅)     = ren≅ η p ⁻¹≅
ren≅ η (p ⦙≅ q)    = ren≅ η p ⦙≅ ren≅ η q
ren≅ η (ƛ≅ p)      = ƛ≅ (ren≅ (liftₑ η) p)
ren≅ η (p ∙≅ q)    = ren≅ η p ∙≅ ren≅ η q
ren≅ η (βred≅ M N) = cast βred≅ (ren (liftₑ η) M) (ren η N) via
                       (((ƛ (ren (liftₑ η) M) ∙ ren η N) ≅_)
                        & ( sub◑ [ idₛ , ren η N ] (liftₑ η) M ⁻¹
                          ⦙ (λ σ → sub [ σ , ren η N ] M) & (id₂◑ η ⦙ id₁◐ η ⁻¹)
                          ⦙ sub◐ η [ idₛ , N ] M
                          ))
ren≅ η (ηexp≅ M)   = cast ηexp≅ (ren η M) via
                       ((λ M′ → ren η M ≅ ƛ (M′ ∙ ` zero))
                        & ( ren○ (wkₑ idₑ) η M ⁻¹
                          ⦙ (λ η′ → ren (wkₑ η′) M) & (id₂○ η ⦙ id₁○ η ⁻¹)
                          ⦙ ren○ (liftₑ η) (wkₑ idₑ) M
                          ))
