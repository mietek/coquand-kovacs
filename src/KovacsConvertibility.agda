module KovacsConvertibility where

open import KovacsSubstitution public


--------------------------------------------------------------------------------


-- Convertibility (_~_ ; ~refl ; _~⁻¹ ; lam ; app ; β ; η)
infix 3 _∼_
data _∼_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
  where
    refl∼ : ∀ {Γ A} → {M : Γ ⊢ A}
                    → M ∼ M

    _⁻¹∼  : ∀ {Γ A} → {M₁ M₂ : Γ ⊢ A}
                    → (p : M₁ ∼ M₂)
                    → M₂ ∼ M₁

    _⦙∼_  : ∀ {Γ A} → {M₁ M₂ M₃ : Γ ⊢ A}
                    → (p : M₁ ∼ M₂) (q : M₂ ∼ M₃)
                    → M₁ ∼ M₃

    ƛ∼    : ∀ {Γ A B} → {M₁ M₂ : Γ , A ⊢ B}
                      → (p : M₁ ∼ M₂)
                      → ƛ M₁ ∼ ƛ M₂

    _∙∼_  : ∀ {Γ A B} → {M₁ M₂ : Γ ⊢ A ⊃ B} {N₁ N₂ : Γ ⊢ A}
                      → (p : M₁ ∼ M₂) (q : N₁ ∼ N₂)
                      → M₁ ∙ N₁ ∼ M₂ ∙ N₂

    βred∼ : ∀ {Γ A B} → (M : Γ , A ⊢ B) (N : Γ ⊢ A)
                      → (ƛ M) ∙ N ∼ sub (idₛ , N) M

    ηexp∼ : ∀ {Γ A B} → (M : Γ ⊢ A ⊃ B)
                      → M ∼ ƛ (wk M ∙ ` zero)

instance
  per∼ : ∀ {Γ A} → PER (Γ ⊢ A) _∼_
  per∼ =
    record
      { _⁻¹ = _⁻¹∼
      ; _⦙_ = _⦙∼_
      }


--------------------------------------------------------------------------------


-- (~ₑ)
ren∼ : ∀ {Γ Γ′ A} → {M₁ M₂ : Γ ⊢ A}
                  → (η : Γ′ ⊇ Γ) → M₁ ∼ M₂
                  → ren η M₁ ∼ ren η M₂
ren∼ η refl∼       = refl∼
ren∼ η (p ⁻¹∼)     = ren∼ η p ⁻¹
ren∼ η (p ⦙∼ q)    = ren∼ η p ⦙ ren∼ η q
ren∼ η (ƛ∼ p)      = ƛ∼ (ren∼ (liftₑ η) p)
ren∼ η (p ∙∼ q)    = ren∼ η p ∙∼ ren∼ η q
ren∼ η (βred∼ M N) = coe (((ƛ (ren (liftₑ η) M) ∙ ren η N) ∼_)
                          & ( sub◑ (idₛ , ren η N) (liftₑ η) M ⁻¹
                            ⦙ (λ σ → sub (σ , ren η N) M) & ( rid◑ η
                                                             ⦙ lid◐ η ⁻¹
                                                             )
                            ⦙ sub◐ η (idₛ , N) M
                            ))
                         (βred∼ (ren (liftₑ η) M) (ren η N))
ren∼ η (ηexp∼ M)   = coe ((λ M′ → ren η M ∼ ƛ (M′ ∙ ` zero))
                          & ( ren○ (wkₑ idₑ) η M ⁻¹
                            ⦙ (λ η′ → ren (wkₑ η′) M) & ( rid○ η
                                                         ⦙ lid○ η ⁻¹
                                                         )
                            ⦙ ren○ (liftₑ η) (wkₑ idₑ) M
                            ))
                         (ηexp∼ (ren η M))


--------------------------------------------------------------------------------
