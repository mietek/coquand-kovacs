module CoquandConvertibility where

open import CoquandSubstitution public


-- Convertibility
infix  3 _∼_
infix  6 _⁻¹∼
infixl 4 _⦙∼_
data _∼_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set
  where
    refl∼ : ∀ {Γ A} → {M : Γ ⊢ A}
                    → M ∼ M

    _⁻¹∼  : ∀ {Γ A} → {M M′ : Γ ⊢ A}
                    → (p : M ∼ M′)
                    → M′ ∼ M

    _⦙∼_  : ∀ {Γ A} → {M M′ M″ : Γ ⊢ A}
                    → (p : M ∼ M′) (q : M′ ∼ M″)
                    → M ∼ M″

    ƛ∼    : ∀ {Γ A B} → {M M′ : [ Γ , A ] ⊢ B}
                      → (p : M ∼ M′)
                      → ƛ M ∼ ƛ M′

    _∙∼_  : ∀ {Γ A B} → {M M′ : Γ ⊢ A ⊃ B} {N N′ : Γ ⊢ A}
                      → (p : M ∼ M′) (q : N ∼ N′)
                      → M ∙ N ∼ M′ ∙ N′

    βred∼ : ∀ {Γ Ξ A B} → (σ : Γ ⊢⋆ Ξ) (M : [ Ξ , A ] ⊢ B) (N : Γ ⊢ A)
                        → sub σ (ƛ M) ∙ N ∼ sub [ σ , N ] M

    ηexp∼ : ∀ {Γ A B} → (M : Γ ⊢ A ⊃ B)
                      → M ∼ ƛ (wk M ∙ ` zero)


≡→∼ : ∀ {Γ A} → {M M′ : Γ ⊢ A} → M ≡ M′ → M ∼ M′
≡→∼ refl = refl∼


--------------------------------------------------------------------------------


renβred∼ : ∀ {Γ Γ′ Ξ A B} → {η : Γ′ ∋⋆ Γ}
                          → (σ : Γ ⊢⋆ Ξ) (M : [ Ξ , A ] ⊢ B) (N : Γ ⊢ A)
                          → ren η (sub σ (ƛ M) ∙ N) ∼ ren η (sub [ σ , N ] M)
renβred∼ {η = η} σ M N =  ƛ∼ (≡→∼ (sublift◑ η σ M ⁻¹)) ∙∼ refl∼
                       ⦙∼ βred∼ (η ◑ σ) M (ren η N)
                       ⦙∼ ≡→∼ ( (λ σ′ → sub σ′ M)
                                 & ([ ⌊ η ⌋ ● σ ,_] & ⌊sub⌋ η N ⁻¹)
                               ⦙ sub◑ η [ σ , N ] M
                               )

renηexp`∼ : ∀ {Γ Γ′ A B} → {η : Γ′ ∋⋆ Γ}
                         → (i : Γ ∋ A ⊃ B)
                         → ren η (` i) ∼ ren η (ƛ (wk (` i) ∙ ` zero))
renηexp`∼ {η = η} i =  ηexp∼ (` (getᵣ η i))
                    ⦙∼ ƛ∼ (≡→∼ (` & ( get○ (wkᵣ idᵣ) η i ⁻¹
                                     ⦙ (λ η′ → getᵣ η′ i)
                                       & ( wkid₁○ η
                                         ⦙ liftwkid₂○ η ⁻¹
                                         )
                                     ⦙ get○ (liftᵣ η) (wkᵣ idᵣ) i
                                     )) ∙∼ refl∼)

renηexpƛ∼ : ∀ {Γ Γ′ A B} → {η : Γ′ ∋⋆ Γ}
                         → (M : [ Γ , A ] ⊢ B)
                         → ren η (ƛ M) ∼ ren η (ƛ (wk (ƛ M) ∙ ` zero))
renηexpƛ∼ {η = η} M =  ηexp∼ (ƛ (ren (liftᵣ η) M))
                    ⦙∼ ƛ∼ (ƛ∼ (≡→∼ ( renlift○ (wkᵣ idᵣ) η M ⁻¹
                                    ⦙ (λ η′ → ren η′ M)
                                      & (liftᵣ & ( wkid₁○ η
                                                 ⦙ wkid₂○ η ⁻¹
                                                 ⦙ zap○ (wkᵣ η) idᵣ zero ⁻¹
                                                 ))
                                    ⦙ renlift○ (liftᵣ η) (wkᵣ idᵣ) M
                                    )) ∙∼ refl∼)

renηexp∙∼ : ∀ {Γ Γ′ A B C} → {η : Γ′ ∋⋆ Γ}
                           → (M : Γ ⊢ A ⊃ B ⊃ C) (N : Γ ⊢ A)
                           → ren η (M ∙ N) ∼ ren η (ƛ (wk (M ∙ N) ∙ ` zero))
renηexp∙∼ {η = η} M N =  ηexp∼ (ren η M ∙ ren η N)
                      ⦙∼ ƛ∼ ((≡→∼ ( ren○ (wkᵣ idᵣ) η M ⁻¹
                                   ⦙ (λ η′ → ren η′ M)
                                     & ( wkid₁○ η
                                       ⦙ wkid₂○ η ⁻¹
                                       ⦙ wk○ η idᵣ ⁻¹
                                       )
                                   ⦙ renliftwk○ η idᵣ M
                                   )
                              ∙∼
                              ≡→∼ ( ren○ (wkᵣ idᵣ) η N ⁻¹
                                   ⦙ (λ η′ → ren η′ N)
                                     & ( wkid₁○ η
                                       ⦙ wkid₂○ η ⁻¹
                                       ⦙ wk○ η idᵣ ⁻¹
                                       )
                                   ⦙ renliftwk○ η idᵣ N
                                   )) ∙∼ refl∼)


ren∼ : ∀ {Γ Γ′ A} → {η : Γ′ ∋⋆ Γ} {M M′ : Γ ⊢ A}
                  → M ∼ M′
                  → ren η M ∼ ren η M′
ren∼ refl∼           = refl∼
ren∼ (p ⁻¹∼)         = ren∼ p ⁻¹∼
ren∼ (p ⦙∼ q)        = ren∼ p ⦙∼ ren∼ q
ren∼ (ƛ∼ p)          = ƛ∼ (ren∼ p)
ren∼ (p ∙∼ q)        = ren∼ p ∙∼ ren∼ q
ren∼ (βred∼ σ M N)   = renβred∼ σ M N
ren∼ (ηexp∼ (` i))   = renηexp`∼ i
ren∼ (ηexp∼ (ƛ M))   = renηexpƛ∼ M
ren∼ (ηexp∼ (M ∙ N)) = renηexp∙∼ M N


--------------------------------------------------------------------------------


subβred∼ : ∀ {Γ Ξ Φ A B} → {σ₁ : Γ ⊢⋆ Ξ}
                         → (σ₂ : Ξ ⊢⋆ Φ) (M : [ Φ , A ] ⊢ B) (N : Ξ ⊢ A)
                         → sub σ₁ (sub σ₂ (ƛ M) ∙ N) ∼ sub σ₁ (sub [ σ₂ , N ] M)
subβred∼ {σ₁ = σ₁} σ₂ M N =  ƛ∼ (≡→∼ (sublift● σ₁ σ₂ M ⁻¹)) ∙∼ refl∼
                          ⦙∼ βred∼ (σ₁ ● σ₂) M (sub σ₁ N)
                          ⦙∼ ≡→∼ (sub● σ₁ [ σ₂ , N ] M)

subηexp`∼ : ∀ {Γ Ξ A B} → {σ : Γ ⊢⋆ Ξ}
                        → (i : Ξ ∋ A ⊃ B)
                        → sub σ (` i) ∼ sub σ (ƛ (wk (` i) ∙ ` zero))
subηexp`∼ {σ = σ} i =  ηexp∼ (getₛ σ i)
                    ⦙∼ ƛ∼ (≡→∼ ( natgetₛ σ i ⁻¹
                                ⦙ (λ σ′ → getₛ σ′ i) & liftwkid₂◐ σ ⁻¹
                                ⦙ get◐ (liftₛ σ) (wkᵣ idᵣ) i
                                ) ∙∼ refl∼)

subηexpƛ∼ : ∀ {Γ Ξ A B} → {σ : Γ ⊢⋆ Ξ}
                        → (M : [ Ξ , A ] ⊢ B)
                        → sub σ (ƛ M) ∼ sub σ (ƛ (wk (ƛ M) ∙ ` zero))
subηexpƛ∼ {σ = σ} M = ƛ∼ (  ≡→∼ ( (λ σ′ → sub σ′ M)
                                   & ([_, ` zero ]
                                      & ( id₂◐ (wkₛ σ) ⁻¹
                                        ⦙ zap◐ (wkₛ σ) idᵣ (` zero) ⁻¹
                                        ⦙ zap◐ (liftₛ σ) (wkᵣ idᵣ) (` zero) ⁻¹
                                        ))
                                 ⦙ sub◐ [ liftₛ σ , ` zero ] (liftᵣ (wkᵣ idᵣ)) M
                                 )
                         ⦙∼ βred∼ (liftₛ σ) (ren (liftᵣ (wkᵣ idᵣ)) M) (` zero) ⁻¹∼
                         )

subηexp∙∼ : ∀ {Γ Ξ A B C} → {σ : Γ ⊢⋆ Ξ}
                          → (M : Ξ ⊢ A ⊃ B ⊃ C) (N : Ξ ⊢ A)
                          → sub σ (M ∙ N) ∼ sub σ (ƛ (wk (M ∙ N) ∙ ` zero))
subηexp∙∼ {σ = σ} M N =  ηexp∼ (sub σ M ∙ sub σ N)
                      ⦙∼ ƛ∼ ((≡→∼ ( sub◑ (wkᵣ idᵣ) σ M ⁻¹
                                   ⦙ (λ σ′ → sub σ′ M)
                                     & ( wkid₁◑ σ
                                       ⦙ wkid₂◐ σ ⁻¹
                                       ⦙ wk◐ σ idᵣ ⁻¹
                                       )
                                   ⦙ subliftwk◐ σ idᵣ M
                                   )
                              ∙∼
                              ≡→∼ ( sub◑ (wkᵣ idᵣ) σ N ⁻¹
                                   ⦙ (λ σ′ → sub σ′ N)
                                     & ( wkid₁◑ σ
                                       ⦙ wkid₂◐ σ ⁻¹
                                       ⦙ wk◐ σ idᵣ ⁻¹
                                       )
                                   ⦙ subliftwk◐ σ idᵣ N
                                   )) ∙∼ refl∼)


sub∼ : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {M M′ : Ξ ⊢ A}
                 → M ∼ M′
                 → sub σ M ∼ sub σ M′
sub∼ refl∼           = refl∼
sub∼ (p ⁻¹∼)         = sub∼ p ⁻¹∼
sub∼ (p ⦙∼ q)        = sub∼ p ⦙∼ sub∼ q
sub∼ (ƛ∼ p)          = ƛ∼ (sub∼ p)
sub∼ (p ∙∼ q)        = sub∼ p ∙∼ sub∼ q
sub∼ (βred∼ σ M N)   = subβred∼ σ M N
sub∼ (ηexp∼ (` i))   = subηexp`∼ i
sub∼ (ηexp∼ (ƛ M))   = subηexpƛ∼ M
sub∼ (ηexp∼ (M ∙ N)) = subηexp∙∼ M N



--------------------------------------------------------------------------------


-- Convertibility of substitutions
infix 3 _∼⋆_
data _∼⋆_ : ∀ {Γ Ξ} → Γ ⊢⋆ Ξ → Γ ⊢⋆ Ξ → Set
  where
    [] : ∀ {Γ} → ([] {Γ}) ∼⋆ []

    [_,_] : ∀ {Γ Ξ A} → {σ σ′ : Γ ⊢⋆ Ξ} {M M′ : Γ ⊢ A}
                      → (ψ : σ ∼⋆ σ′) (p : M ∼ M′)
                      → [ σ , M ] ∼⋆ [ σ′ , M′ ]


refl∼⋆ : ∀ {Γ Ξ} → {σ : Γ ⊢⋆ Ξ}
                 → σ ∼⋆ σ
refl∼⋆ {σ = []}        = []
refl∼⋆ {σ = [ σ , M ]} = [ refl∼⋆ , refl∼ ]

infix  6 _⁻¹∼⋆
_⁻¹∼⋆ : ∀ {Γ Ξ} → {σ σ′ : Γ ⊢⋆ Ξ}
                → σ ∼⋆ σ′
                → σ′ ∼⋆ σ
[] ⁻¹∼⋆        = []
[ ψ , p ] ⁻¹∼⋆ = [ ψ ⁻¹∼⋆ , p ⁻¹∼ ]

infixl 4 _⦙∼⋆_
_⦙∼⋆_ : ∀ {Γ Ξ} → {σ σ′ σ″ : Γ ⊢⋆ Ξ}
                → σ ∼⋆ σ′ → σ′ ∼⋆ σ″
                → σ ∼⋆ σ″
[]         ⦙∼⋆ []         = []
[ ψ₁ , p ] ⦙∼⋆ [ ψ₂ , q ] = [ ψ₁ ⦙∼⋆ ψ₂ , p ⦙∼ q ]


≡→∼⋆ : ∀ {Γ Ξ} → {σ σ′ : Γ ⊢⋆ Ξ}
                → σ ≡ σ′
                → σ ∼⋆ σ′
≡→∼⋆ refl = refl∼⋆


wk∼⋆ : ∀ {A Γ Ξ} → {σ σ′ : Γ ⊢⋆ Ξ}
                 → σ ∼⋆ σ′
                 → wkₛ {A} σ ∼⋆ wkₛ σ′
wk∼⋆ []        = []
wk∼⋆ [ ψ , p ] = [ wk∼⋆ ψ , ren∼ p ]

lift∼⋆ : ∀ {A Γ Ξ} → {σ σ′ : Γ ⊢⋆ Ξ}
                   → σ ∼⋆ σ′
                   → liftₛ {A} σ ∼⋆ liftₛ σ′
lift∼⋆ []        = [ [] , refl∼ ]
lift∼⋆ [ ψ , p ] = [ [ wk∼⋆ ψ , ren∼ p ] , refl∼ ]


-- NOTE: Needs getₛ σ i ∼ getₛ σ′ i
-- ◐∼⋆ : ∀ {Γ Ξ Ξ′} → {σ σ′ : Γ ⊢⋆ Ξ′} {η : Ξ′ ∋⋆ Ξ}
--                  → σ ∼⋆ σ′
--                  → σ ◐ η ∼⋆ σ′ ◐ η
-- ◐∼⋆ {η = []}        ψ = []
-- ◐∼⋆ {η = [ η , i ]} ψ = [ ◐∼⋆ ψ , {!!} ]

◑∼⋆ : ∀ {Γ Γ′ Ξ} → {η : Γ′ ∋⋆ Γ} {σ σ′ : Γ ⊢⋆ Ξ}
                 → σ ∼⋆ σ′
                 → η ◑ σ ∼⋆ η ◑ σ′
◑∼⋆ []        = []
◑∼⋆ [ ψ , p ] = [ ◑∼⋆ ψ , sub∼ p ]

-- NOTE: Needs a more general sub∼
-- ●∼⋆ : ∀ {Γ Ξ Φ} → {σ₁ σ₁′ : Γ ⊢⋆ Ξ} {σ₂ σ₂′ : Ξ ⊢⋆ Φ}
--                 → σ₁ ∼⋆ σ₁′ → σ₂ ∼⋆ σ₂′
--                 → σ₁ ● σ₂ ∼⋆ σ₁′ ● σ₂′
-- ●∼⋆ ψ₁ []         = []
-- ●∼⋆ ψ₁ [ ψ₂ , p ] = [ ●∼⋆ ψ₁ ψ₂ , {!!} ]
