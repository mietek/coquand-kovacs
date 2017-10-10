module STLC.Kovacs.Convertibility where

open import STLC.Kovacs.Substitution public


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

    _∙∼_  : ∀ {Γ A B} → {M₁ M₂ : Γ ⊢ A ⇒ B} {N₁ N₂ : Γ ⊢ A}
                      → (p : M₁ ∼ M₂) (q : N₁ ∼ N₂)
                      → M₁ ∙ N₁ ∼ M₂ ∙ N₂

    red⇒ : ∀ {Γ A B} → (M : Γ , A ⊢ B) (N : Γ ⊢ A)
                      → (ƛ M) ∙ N ∼ cut N M

    exp⇒ : ∀ {Γ A B} → (M : Γ ⊢ A ⇒ B)
                      → M ∼ ƛ (wk M ∙ 0)


instance
  per∼ : ∀ {Γ A} → PER (Γ ⊢ A) _∼_
  per∼ =
    record
      { _⁻¹ = _⁻¹∼
      ; _⦙_ = _⦙∼_
      }


--------------------------------------------------------------------------------


renwk : ∀ {Γ Γ′ A B} → (η : Γ′ ⊇ Γ) (M : Γ ⊢ A)
                     → (wk {B} ∘ ren η) M ≡
                        (ren (liftₑ η) ∘ wk) M
renwk η M = ren○ (wkₑ idₑ) η M ⁻¹
          ⦙ (λ η′ → ren (wkₑ η′) M) & ( rid○ η
                                       ⦙ lid○ η ⁻¹
                                       )
          ⦙ ren○ (liftₑ η) (wkₑ idₑ) M

rencut : ∀ {Γ Γ′ A B} → (η : Γ′ ⊇ Γ) (M : Γ ⊢ A) (N : Γ , A ⊢ B)
                      → (cut (ren η M) ∘ ren (liftₑ η)) N ≡
                         (ren η ∘ cut M) N
rencut η M N = sub◑ (idₛ , ren η M) (liftₑ η) N ⁻¹
             ⦙ (λ σ → sub (σ , ren η M) N) & ( rid◑ η
                                              ⦙ lid◐ η ⁻¹
                                              )
             ⦙ sub◐ η (idₛ , M) N


-- (~ₑ)
ren∼ : ∀ {Γ Γ′ A} → {M₁ M₂ : Γ ⊢ A}
                  → (η : Γ′ ⊇ Γ) → M₁ ∼ M₂
                  → ren η M₁ ∼ ren η M₂
ren∼ η refl∼       = refl∼
ren∼ η (p ⁻¹∼)     = ren∼ η p ⁻¹
ren∼ η (p ⦙∼ q)    = ren∼ η p ⦙ ren∼ η q
ren∼ η (ƛ∼ p)      = ƛ∼ (ren∼ (liftₑ η) p)
ren∼ η (p ∙∼ q)    = ren∼ η p ∙∼ ren∼ η q
ren∼ η (red⇒ M N) = coe (((ƛ (ren (liftₑ η) M) ∙ ren η N) ∼_)
                          & rencut η N M)
                         (red⇒ (ren (liftₑ η) M) (ren η N))
ren∼ η (exp⇒ M)   = coe ((λ M′ → ren η M ∼ ƛ (M′ ∙ 0))
                          & renwk η M)
                         (exp⇒ (ren η M))


--------------------------------------------------------------------------------
