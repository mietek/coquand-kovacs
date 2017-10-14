module STLC.Coquand.Convertibility where

open import STLC.Coquand.Substitution public


--------------------------------------------------------------------------------


-- Convertibility
infix  3 _∼_
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

    red⇒ : ∀ {Γ Ξ A B} → (σ : Γ ⊢⋆ Ξ) (M : Ξ , A ⊢ B) (N : Γ ⊢ A)
                        → sub σ (ƛ M) ∙ N ∼ sub (σ , N) M

    exp⇒ : ∀ {Γ A B} → (M : Γ ⊢ A ⇒ B)
                      → M ∼ ƛ (wk M ∙ 0)


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


renred⇒ : ∀ {Γ Γ′ Ξ A B} → {η : Γ′ ∋⋆ Γ}
                          → (σ : Γ ⊢⋆ Ξ) (M : Ξ , A ⊢ B) (N : Γ ⊢ A)
                          → ren η (sub σ (ƛ M) ∙ N) ∼ ren η (sub (σ , N) M)
renred⇒ {η = η} σ M N = ƛ∼ (≡→∼ (sublift◑ η σ M ⁻¹)) ∙∼ refl∼
                       ⦙ red⇒ (η ◑ σ) M (ren η N)
                       ⦙ ≡→∼ ( (λ σ′ → sub σ′ M)
                                & ((⌊ η ⌋ ● σ ,_) & ⌊sub⌋ η N ⁻¹)
                              ⦙ sub◑ η (σ , N) M
                              )

renexp⇒` : ∀ {Γ Γ′ A B} → {η : Γ′ ∋⋆ Γ}
                         → (i : Γ ∋ A ⇒ B)
                         → ren η (` i) ∼ ren η (ƛ (wk (` i) ∙ 0))
renexp⇒` {η = η} i = exp⇒ (` (getᵣ η i))
                    ⦙ ƛ∼ (≡→∼ (` & ( get○ (wkᵣ idᵣ) η i ⁻¹
                                    ⦙ (λ η′ → getᵣ η′ i)
                                      & ( wklid○ η
                                        ⦙ liftwkrid○ η ⁻¹
                                        )
                                    ⦙ get○ (liftᵣ η) (wkᵣ idᵣ) i
                                    )) ∙∼ refl∼)

renexp⇒ƛ : ∀ {Γ Γ′ A B} → {η : Γ′ ∋⋆ Γ}
                         → (M : Γ , A ⊢ B)
                         → ren η (ƛ M) ∼ ren η (ƛ (wk (ƛ M) ∙ 0))
renexp⇒ƛ {η = η} M = exp⇒ (ƛ (ren (liftᵣ η) M))
                    ⦙ ƛ∼ (ƛ∼ (≡→∼ ( renlift○ (wkᵣ idᵣ) η M ⁻¹
                                   ⦙ (λ η′ → ren η′ M)
                                     & (liftᵣ & ( wklid○ η
                                                ⦙ wkrid○ η ⁻¹
                                                ⦙ zap○ (wkᵣ η) idᵣ 0 ⁻¹
                                                ))
                                   ⦙ renlift○ (liftᵣ η) (wkᵣ idᵣ) M
                                   )) ∙∼ refl∼)

renexp⇒∙ : ∀ {Γ Γ′ A B C} → {η : Γ′ ∋⋆ Γ}
                           → (M : Γ ⊢ A ⇒ B ⇒ C) (N : Γ ⊢ A)
                           → ren η (M ∙ N) ∼ ren η (ƛ (wk (M ∙ N) ∙ 0))
renexp⇒∙ {η = η} M N = exp⇒ (ren η M ∙ ren η N)
                      ⦙ ƛ∼ ((≡→∼ ( ren○ (wkᵣ idᵣ) η M ⁻¹
                                  ⦙ (λ η′ → ren η′ M)
                                    & ( wklid○ η
                                      ⦙ wkrid○ η ⁻¹
                                      ⦙ wk○ η idᵣ ⁻¹
                                      )
                                  ⦙ renliftwk○ η idᵣ M
                                  )
                             ∙∼
                             ≡→∼ ( ren○ (wkᵣ idᵣ) η N ⁻¹
                                  ⦙ (λ η′ → ren η′ N)
                                    & ( wklid○ η
                                      ⦙ wkrid○ η ⁻¹
                                      ⦙ wk○ η idᵣ ⁻¹
                                      )
                                  ⦙ renliftwk○ η idᵣ N
                                  )) ∙∼ refl∼)


ren∼ : ∀ {Γ Γ′ A} → {η : Γ′ ∋⋆ Γ} {M₁ M₂ : Γ ⊢ A}
                  → M₁ ∼ M₂
                  → ren η M₁ ∼ ren η M₂
ren∼ refl∼           = refl∼
ren∼ (p ⁻¹∼)         = ren∼ p ⁻¹
ren∼ (p ⦙∼ q)        = ren∼ p ⦙ ren∼ q
ren∼ (ƛ∼ p)          = ƛ∼ (ren∼ p)
ren∼ (p ∙∼ q)        = ren∼ p ∙∼ ren∼ q
ren∼ (red⇒ σ M N)   = renred⇒ σ M N
ren∼ (exp⇒ (` i))   = renexp⇒` i
ren∼ (exp⇒ (ƛ M))   = renexp⇒ƛ M
ren∼ (exp⇒ (M ∙ N)) = renexp⇒∙ M N


--------------------------------------------------------------------------------


subred⇒ : ∀ {Γ Ξ Φ A B} → {σ₁ : Γ ⊢⋆ Ξ}
                         → (σ₂ : Ξ ⊢⋆ Φ) (M : Φ , A ⊢ B) (N : Ξ ⊢ A)
                         → sub σ₁ (sub σ₂ (ƛ M) ∙ N) ∼ sub σ₁ (sub (σ₂ , N) M)
subred⇒ {σ₁ = σ₁} σ₂ M N = ƛ∼ (≡→∼ (sublift● σ₁ σ₂ M ⁻¹)) ∙∼ refl∼
                          ⦙ red⇒ (σ₁ ● σ₂) M (sub σ₁ N)
                          ⦙ ≡→∼ (sub● σ₁ (σ₂ , N) M)

subexp⇒` : ∀ {Γ Ξ A B} → {σ : Γ ⊢⋆ Ξ}
                        → (i : Ξ ∋ A ⇒ B)
                        → sub σ (` i) ∼ sub σ (ƛ (wk (` i) ∙ 0))
subexp⇒` {σ = σ} i = exp⇒ (getₛ σ i)
                    ⦙ ƛ∼ (≡→∼ ( natgetₛ σ i ⁻¹
                               ⦙ (λ σ′ → getₛ σ′ i) & liftwkrid◐ σ ⁻¹
                               ⦙ get◐ (liftₛ σ) (wkᵣ idᵣ) i
                               ) ∙∼ refl∼)

subexp⇒ƛ : ∀ {Γ Ξ A B} → {σ : Γ ⊢⋆ Ξ}
                        → (M : Ξ , A ⊢ B)
                        → sub σ (ƛ M) ∼ sub σ (ƛ (wk (ƛ M) ∙ 0))
subexp⇒ƛ {σ = σ} M = ƛ∼ ( ≡→∼ ( (λ σ′ → sub σ′ M)
                                  & ((_, 0)
                                     & ( rid◐ (wkₛ σ) ⁻¹
                                       ⦙ zap◐ (wkₛ σ) idᵣ 0 ⁻¹
                                       ⦙ zap◐ (liftₛ σ) (wkᵣ idᵣ) 0 ⁻¹
                                       ))
                                ⦙ sub◐ (liftₛ σ , 0) (liftᵣ (wkᵣ idᵣ)) M
                                )
                         ⦙ red⇒ (liftₛ σ) (ren (liftᵣ (wkᵣ idᵣ)) M) 0 ⁻¹
                         )

subexp⇒∙ : ∀ {Γ Ξ A B C} → {σ : Γ ⊢⋆ Ξ}
                          → (M : Ξ ⊢ A ⇒ B ⇒ C) (N : Ξ ⊢ A)
                          → sub σ (M ∙ N) ∼ sub σ (ƛ (wk (M ∙ N) ∙ 0))
subexp⇒∙ {σ = σ} M N = exp⇒ (sub σ M ∙ sub σ N)
                      ⦙ ƛ∼ ((≡→∼ ( sub◑ (wkᵣ idᵣ) σ M ⁻¹
                                  ⦙ (λ σ′ → sub σ′ M)
                                    & ( wklid◑ σ
                                      ⦙ wkrid◐ σ ⁻¹
                                      ⦙ wk◐ σ idᵣ ⁻¹
                                      )
                                  ⦙ subliftwk◐ σ idᵣ M
                                  )
                             ∙∼
                             ≡→∼ ( sub◑ (wkᵣ idᵣ) σ N ⁻¹
                                  ⦙ (λ σ′ → sub σ′ N)
                                    & ( wklid◑ σ
                                      ⦙ wkrid◐ σ ⁻¹
                                      ⦙ wk◐ σ idᵣ ⁻¹
                                      )
                                  ⦙ subliftwk◐ σ idᵣ N
                                  )) ∙∼ refl∼)


sub∼ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {M₁ M₂ : Ξ ⊢ A}
                 → M₁ ∼ M₂
                 → sub σ M₁ ∼ sub σ M₂
sub∼ refl∼           = refl∼
sub∼ (p ⁻¹∼)         = sub∼ p ⁻¹
sub∼ (p ⦙∼ q)        = sub∼ p ⦙ sub∼ q
sub∼ (ƛ∼ p)          = ƛ∼ (sub∼ p)
sub∼ (p ∙∼ q)        = sub∼ p ∙∼ sub∼ q
sub∼ (red⇒ σ M N)   = subred⇒ σ M N
sub∼ (exp⇒ (` i))   = subexp⇒` i
sub∼ (exp⇒ (ƛ M))   = subexp⇒ƛ M
sub∼ (exp⇒ (M ∙ N)) = subexp⇒∙ M N



--------------------------------------------------------------------------------


-- Convertibility of substitutions
infix 3 _∼⋆_
data _∼⋆_ : ∀ {Γ Ξ} → Γ ⊢⋆ Ξ → Γ ⊢⋆ Ξ → Set
  where
    ∅   : ∀ {Γ} → ∅ {Γ} ∼⋆ ∅

    _,_ : ∀ {Γ Ξ A} → {σ₁ σ₂ : Γ ⊢⋆ Ξ} {M₁ M₂ : Γ ⊢ A}
                    → (χ : σ₁ ∼⋆ σ₂) (p : M₁ ∼ M₂)
                    → σ₁ , M₁ ∼⋆ σ₂ , M₂


refl∼⋆ : ∀ {Γ Ξ} → {σ : Γ ⊢⋆ Ξ}
                 → σ ∼⋆ σ
refl∼⋆ {σ = ∅}     = ∅
refl∼⋆ {σ = σ , M} = refl∼⋆ , refl∼

_⁻¹∼⋆ : ∀ {Γ Ξ} → {σ₁ σ₂ : Γ ⊢⋆ Ξ}
                → σ₁ ∼⋆ σ₂
                → σ₂ ∼⋆ σ₁
∅       ⁻¹∼⋆ = ∅
(χ , p) ⁻¹∼⋆ = χ ⁻¹∼⋆ , p ⁻¹

_⦙∼⋆_ : ∀ {Γ Ξ} → {σ₁ σ₂ σ₃ : Γ ⊢⋆ Ξ}
                → σ₁ ∼⋆ σ₂ → σ₂ ∼⋆ σ₃
                → σ₁ ∼⋆ σ₃
∅        ⦙∼⋆ ∅        = ∅
(χ₁ , p) ⦙∼⋆ (χ₂ , q) = (χ₁ ⦙∼⋆ χ₂) , (p ⦙ q)


≡→∼⋆ : ∀ {Γ Ξ} → {σ₁ σ₂ : Γ ⊢⋆ Ξ}
                → σ₁ ≡ σ₂
                → σ₁ ∼⋆ σ₂
≡→∼⋆ refl = refl∼⋆

instance
  per∼⋆ : ∀ {Γ Ξ} → PER (Γ ⊢⋆ Ξ) _∼⋆_
  per∼⋆ =
    record
      { _⁻¹ = _⁻¹∼⋆
      ; _⦙_ = _⦙∼⋆_
      }


wk∼⋆ : ∀ {A Γ Ξ} → {σ₁ σ₂ : Γ ⊢⋆ Ξ}
                 → σ₁ ∼⋆ σ₂
                 → wkₛ {A} σ₁ ∼⋆ wkₛ σ₂
wk∼⋆ ∅       = ∅
wk∼⋆ (χ , p) = wk∼⋆ χ , ren∼ p

lift∼⋆ : ∀ {A Γ Ξ} → {σ₁ σ₂ : Γ ⊢⋆ Ξ}
                   → σ₁ ∼⋆ σ₂
                   → liftₛ {A} σ₁ ∼⋆ liftₛ σ₂
lift∼⋆ ∅       = ∅ , refl∼
lift∼⋆ (χ , p) = wk∼⋆ χ , ren∼ p , refl∼


-- NOTE: Needs getₛ σ₁ i ∼ getₛ σ₂ i
-- ◐∼⋆ : ∀ {Γ Ξ Ξ′} → {σ₁ σ₂ : Γ ⊢⋆ Ξ′} {η : Ξ′ ∋⋆ Ξ}
--                  → σ₁ ∼⋆ σ₂ → σ₁ ◐ η ∼⋆ σ₂ ◐ η
-- ◐∼⋆ {η = ∅}        χ = ∅
-- ◐∼⋆ {η = [ η , i ]} χ = [ ◐∼⋆ χ , {!!} ]

◑∼⋆ : ∀ {Γ Γ′ Ξ} → {η : Γ′ ∋⋆ Γ} {σ₁ σ₂ : Γ ⊢⋆ Ξ}
                 → σ₁ ∼⋆ σ₂
                 → η ◑ σ₁ ∼⋆ η ◑ σ₂
◑∼⋆ ∅       = ∅
◑∼⋆ (χ , p) = ◑∼⋆ χ , sub∼ p

-- NOTE: Needs a more general sub∼
-- ●∼⋆ : ∀ {Γ Ξ Φ} → {σ₁ σ₂ : Γ ⊢⋆ Ξ} {τ₁ τ₂ : Ξ ⊢⋆ Φ}
--                 → σ₁ ∼⋆ σ₂ → τ₁ ∼⋆ τ₂
--                 → σ₁ ● τ₁ ∼⋆ σ₂ ● τ₂
-- ●∼⋆ χ₁ ∅         = ∅
-- ●∼⋆ χ₁ [ χ₂ , p ] = [ ●∼⋆ χ₁ χ₂ , {!!} ]


--------------------------------------------------------------------------------
