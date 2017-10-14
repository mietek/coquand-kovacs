module STLCE.Kovacs.Convertibility where

open import STLCE.Kovacs.Substitution public


--------------------------------------------------------------------------------


-- Convertibility (_~_ ; ~refl ; _~⁻¹ ; lam ; app ; β ; η)
infix 3 _∼_
data _∼_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
  where
    refl∼    : ∀ {Γ A} → {M : Γ ⊢ A}
                       → M ∼ M

    _⁻¹∼     : ∀ {Γ A} → {M₁ M₂ : Γ ⊢ A}
                       → (p : M₁ ∼ M₂)
                       → M₂ ∼ M₁

    _⦙∼_     : ∀ {Γ A} → {M₁ M₂ M₃ : Γ ⊢ A}
                       → (p : M₁ ∼ M₂) (q : M₂ ∼ M₃)
                       → M₁ ∼ M₃


    ƛ∼       : ∀ {Γ A B} → {M₁ M₂ : Γ , A ⊢ B}
                         → (p : M₁ ∼ M₂)
                         → ƛ M₁ ∼ ƛ M₂

    _∙∼_     : ∀ {Γ A B} → {M₁ M₂ : Γ ⊢ A ⇒ B} {N₁ N₂ : Γ ⊢ A}
                         → (p : M₁ ∼ M₂) (q : N₁ ∼ N₂)
                         → M₁ ∙ N₁ ∼ M₂ ∙ N₂

    _,∼_     : ∀ {Γ A B} → {M₁ M₂ : Γ ⊢ A} {N₁ N₂ : Γ ⊢ B}
                         → (p : M₁ ∼ M₂) (q : N₁ ∼ N₂)
                         → M₁ , N₁ ∼ M₂ , N₂

    π₁∼      : ∀ {Γ A B} → {M₁ M₂ : Γ ⊢ A ⩕ B}
                         → (p : M₁ ∼ M₂)
                         → π₁ M₁ ∼ π₁ M₂

    π₂∼      : ∀ {Γ A B} → {M₁ M₂ : Γ ⊢ A ⩕ B}
                         → (p : M₁ ∼ M₂)
                         → π₂ M₁ ∼ π₂ M₂

    φ∼       : ∀ {Γ C} → {M₁ M₂ : Γ ⊢ ⫫}
                       → (p : M₁ ∼ M₂)
                       → φ {C = C} M₁ ∼ φ M₂

    ι₁∼      : ∀ {Γ A B} → {M₁ M₂ : Γ ⊢ A}
                         → (p : M₁ ∼ M₂)
                         → ι₁ {B = B} M₁ ∼ ι₁ M₂

    ι₂∼      : ∀ {Γ A B} → {M₁ M₂ : Γ ⊢ B}
                         → (p : M₁ ∼ M₂)
                         → ι₂ {A = A} M₁ ∼ ι₂ M₂

    _⁇∼_∥∼_  : ∀ {Γ A B C} → {M₁ M₂ : Γ ⊢ A ⩖ B}
                              {N₁₁ N₁₂ : Γ , A ⊢ C} {N₂₁ N₂₂ : Γ , B ⊢ C}
                           → (p : M₁ ∼ M₂) (q₁ : N₁₁ ∼ N₁₂) (q₂ : N₂₁ ∼ N₂₂)
                           → M₁ ⁇ N₁₁ ∥ N₂₁ ∼ M₂ ⁇ N₁₂ ∥ N₂₂


    red⇒    : ∀ {Γ A B} → (M : Γ , A ⊢ B) (N : Γ ⊢ A)
                         → (ƛ M) ∙ N ∼ cut N M

    red⩕₁    : ∀ {Γ A B} → (M : Γ ⊢ A) (N : Γ ⊢ B)
                         → π₁ (M , N) ∼ M

    red⩕₂    : ∀ {Γ A B} → (M : Γ ⊢ A) (N : Γ ⊢ B)
                         → π₂ (M , N) ∼ N

    red⩖₁    : ∀ {Γ A B C} → (M : Γ ⊢ A) (N₁ : Γ , A ⊢ C) (N₂ : Γ , B ⊢ C)
                           → ι₁ M ⁇ N₁ ∥ N₂ ∼ cut M N₁

    red⩖₂    : ∀ {Γ A B C} → (M : Γ ⊢ B) (N₁ : Γ , A ⊢ C) (N₂ : Γ , B ⊢ C)
                           → ι₂ M ⁇ N₁ ∥ N₂ ∼ cut M N₂


    exp⇒    : ∀ {Γ A B} → (M : Γ ⊢ A ⇒ B)
                         → M ∼ ƛ (wk M ∙ 0)

    exp⩕     : ∀ {Γ A B} → (M : Γ ⊢ A ⩕ B)
                         → M ∼ π₁ M , π₂ M

    exp⫪    : ∀ {Γ} → (M : Γ ⊢ ⫪)
                     → M ∼ τ

    exp⩖     : ∀ {Γ A B} → (M : Γ ⊢ A ⩖ B)
                         → M ∼ M ⁇ ι₁ 0 ∥ ι₂ 0


    comm⫫∙  : ∀ {Γ A B} → (M : Γ ⊢ ⫫) (N : Γ ⊢ A)
                         → _∙_ {A = A} {B} (φ M) N ∼ φ M

    comm⫫π₁ : ∀ {Γ A B} → (M : Γ ⊢ ⫫)
                         → π₁ {A = A} {B} (φ M) ∼ φ M

    comm⫫π₂ : ∀ {Γ A B} → (M : Γ ⊢ ⫫)
                         → π₂ {A = A} {B} (φ M) ∼ φ M

    comm⫫φ  : ∀ {Γ C} → (M : Γ ⊢ ⫫)
                       → φ {C = C} (φ M) ∼ φ M

    comm⫫⁇∥ : ∀ {Γ A B C} → (M : Γ ⊢ ⫫) (N₁ : Γ , A ⊢ C) (N₂ : Γ , B ⊢ C)
                           → φ M ⁇ N₁ ∥ N₂ ∼ φ M


    comm⩖∙   : ∀ {Γ A B C D} → (M : Γ ⊢ A ⩖ B)
                                (N₁ : Γ , A ⊢ C ⇒ D)
                                (N₂ : Γ , B ⊢ C ⇒ D)
                                (O : Γ ⊢ C)
                             → (M ⁇ N₁ ∥ N₂) ∙ O ∼
                                M ⁇ (N₁ ∙ wk O) ∥ (N₂ ∙ wk O)

    comm⩖π₁  : ∀ {Γ A B C D} → (M : Γ ⊢ A ⩖ B)
                                (N₁ : Γ , A ⊢ C ⩕ D)
                                (N₂ : Γ , B ⊢ C ⩕ D)
                             → π₁ (M ⁇ N₁ ∥ N₂) ∼
                                M ⁇ (π₁ N₁) ∥ (π₁ N₂)

    comm⩖π₂  : ∀ {Γ A B C D} → (M : Γ ⊢ A ⩖ B)
                                (N₁ : Γ , A ⊢ C ⩕ D)
                                (N₂ : Γ , B ⊢ C ⩕ D)
                             → π₂ (M ⁇ N₁ ∥ N₂) ∼
                                M ⁇ (π₂ N₁) ∥ (π₂ N₂)

    comm⩖φ   : ∀ {Γ A B C} → (M : Γ ⊢ A ⩖ B)
                              (N₁ : Γ , A ⊢ ⫫)
                              (N₂ : Γ , B ⊢ ⫫)
                           → φ {C = C} (M ⁇ N₁ ∥ N₂) ∼
                              M ⁇ (φ N₁) ∥ (φ N₂)

    comm⩖⁇∥  : ∀ {Γ A B C D E} → (M : Γ ⊢ A ⩖ B)
                                  (N₁ : Γ , A ⊢ C ⩖ D)
                                  (N₂ : Γ , B ⊢ C ⩖ D)
                                  (O₁ : Γ , C ⊢ E)
                                  (O₂ : Γ , D ⊢ E)
                               → (M ⁇ N₁ ∥ N₂) ⁇ O₁ ∥ O₂ ∼
                                  M ⁇ (N₁ ⁇ liftwk O₁ ∥ liftwk O₂)
                                    ∥ (N₂ ⁇ liftwk O₁ ∥ liftwk O₂)


≡→∼ : ∀ {Γ A} → {M₁ M₂ : Γ ⊢ A}
               → M₁ ≡ M₂
               → M₁ ∼ M₂
≡→∼ refl = refl∼

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

renliftwk : ∀ {Γ Γ′ A B C} → (η : Γ′ ⊇ Γ) (M : Γ , A ⊢ B)
                           → (liftwk {C} ∘ ren (liftₑ η)) M ≡
                              (ren (liftₑ (liftₑ η)) ∘ liftwk) M
renliftwk η M = ren○ (liftₑ (wkₑ idₑ)) (liftₑ η) M ⁻¹
              ⦙ (λ η′ → ren (liftₑ (wkₑ η′)) M) & ( rid○ η
                                                   ⦙ lid○ η ⁻¹
                                                   )
              ⦙ ren○ (liftₑ (liftₑ η)) (liftₑ (wkₑ idₑ)) M

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

ren∼ η refl∼                   = refl∼
ren∼ η (p ⁻¹∼)                 = ren∼ η p ⁻¹
ren∼ η (p ⦙∼ q)                = ren∼ η p ⦙ ren∼ η q
ren∼ η (ƛ∼ p)                  = ƛ∼ (ren∼ (liftₑ η) p)
ren∼ η (p ∙∼ q)                = ren∼ η p ∙∼ ren∼ η q
ren∼ η (p ,∼ q)                = ren∼ η p ,∼ ren∼ η q
ren∼ η (π₁∼ p)                 = π₁∼ (ren∼ η p)
ren∼ η (π₂∼ p)                 = π₂∼ (ren∼ η p)
ren∼ η (φ∼ p)                  = φ∼ (ren∼ η p)
ren∼ η (ι₁∼ p)                 = ι₁∼ (ren∼ η p)
ren∼ η (ι₂∼ p)                 = ι₂∼ (ren∼ η p)
ren∼ η (p ⁇∼ q₁ ∥∼ q₂)         = ren∼ η p ⁇∼ ren∼ (liftₑ η) q₁
                                          ∥∼ ren∼ (liftₑ η) q₂

ren∼ η (red⇒ M N)
  = coe (((ƛ (ren (liftₑ η) M) ∙ ren η N) ∼_)
         & rencut η N M)
        (red⇒ (ren (liftₑ η) M) (ren η N))

ren∼ η (red⩕₁ M N)             = red⩕₁ (ren η M) (ren η N)
ren∼ η (red⩕₂ M N)             = red⩕₂ (ren η M) (ren η N)

ren∼ η (red⩖₁ M N₁ N₂)
  = coe (((ι₁ (ren η M) ⁇ ren (liftₑ η) N₁
                        ∥ ren (liftₑ η) N₂) ∼_)
         & rencut η M N₁)
        (red⩖₁ (ren η M)
               (ren (liftₑ η) N₁)
               (ren (liftₑ η) N₂))

ren∼ η (red⩖₂ M N₁ N₂)
  = coe (((ι₂ (ren η M) ⁇ ren (liftₑ η) N₁
                        ∥ ren (liftₑ η) N₂) ∼_)
         & rencut η M N₂)
        (red⩖₂ (ren η M)
               (ren (liftₑ η) N₁)
               (ren (liftₑ η) N₂))

ren∼ η (exp⇒ M)
  = coe ((λ M′ → ren η M ∼ ƛ (M′ ∙ 0))
         & renwk η M)
        (exp⇒ (ren η M))

ren∼ η (exp⩕ M)                = exp⩕ (ren η M)
ren∼ η (exp⫪ M)               = exp⫪ (ren η M)
ren∼ η (exp⩖ M)                = exp⩖ (ren η M)
ren∼ η (comm⫫∙ M N)           = comm⫫∙ (ren η M) (ren η N)
ren∼ η (comm⫫π₁ M)            = comm⫫π₁ (ren η M)
ren∼ η (comm⫫π₂ M)            = comm⫫π₂ (ren η M)
ren∼ η (comm⫫φ M)             = comm⫫φ (ren η M)
ren∼ η (comm⫫⁇∥ M N₁ N₂)      = comm⫫⁇∥ (ren η M)
                                          (ren (liftₑ η) N₁)
                                          (ren (liftₑ η) N₂)

ren∼ η (comm⩖∙ M N₁ N₂ O)
  = coe ((((ren η M ⁇ ren (liftₑ η) N₁
                    ∥ ren (liftₑ η) N₂) ∙ ren η O ) ∼_)
         & ((λ N₁′ N₂′ → ren η M ⁇ N₁′ ∥ N₂′)
            & ((λ O′ → ren (liftₑ η) N₁ ∙ O′)
               & renwk η O)
            ⊗ ((λ O′ → ren (liftₑ η) N₂ ∙ O′)
               & renwk η O)))
        (comm⩖∙ (ren η M)
                (ren (liftₑ η) N₁)
                (ren (liftₑ η) N₂)
                (ren η O))

ren∼ η (comm⩖π₁ M N₁ N₂)       = comm⩖π₁ (ren η M)
                                         (ren (liftₑ η) N₁)
                                         (ren (liftₑ η) N₂)
ren∼ η (comm⩖π₂ M N₁ N₂)       = comm⩖π₂ (ren η M)
                                         (ren (liftₑ η) N₁)
                                         (ren (liftₑ η) N₂)
ren∼ η (comm⩖φ M N₁ N₂)        = comm⩖φ (ren η M)
                                        (ren (liftₑ η) N₁)
                                        (ren (liftₑ η) N₂)

ren∼ η (comm⩖⁇∥ M N₁ N₂ O₁ O₂)
  = coe ((((ren η M ⁇ ren (liftₑ η) N₁
                    ∥ ren (liftₑ η) N₂) ⁇ ren (liftₑ η) O₁
                                        ∥ ren (liftₑ η) O₂) ∼_)
         & ((λ N₁′ N₂′ → ren η M ⁇ N₁′ ∥ N₂′)
            & ((λ O₁′ O₂′ → ren (liftₑ η) N₁ ⁇ O₁′ ∥ O₂′)
               & renliftwk η O₁ ⊗ renliftwk η O₂)
            ⊗ ((λ O₁′ O₂′ → ren (liftₑ η) N₂ ⁇ O₁′ ∥ O₂′)
               & renliftwk η O₁ ⊗ renliftwk η O₂)))
        (comm⩖⁇∥ (ren η M)
                 (ren (liftₑ η) N₁)
                 (ren (liftₑ η) N₂)
                 (ren (liftₑ η) O₁)
                 (ren (liftₑ η) O₂))


--------------------------------------------------------------------------------
