module CoquandSubstitution where

open import CoquandRenaming public
open import Category


--------------------------------------------------------------------------------


-- Substitutions
infix 3 _⊢⋆_
data _⊢⋆_ : 𝒞 → 𝒞 → Set
  where
    ∅   : ∀ {Γ} → Γ ⊢⋆ ∅

    _,_ : ∀ {Γ Ξ A} → (σ : Γ ⊢⋆ Ξ) (M : Γ ⊢ A)
                    → Γ ⊢⋆ Ξ , A


putₛ : ∀ {Ξ Γ} → (∀ {A} → Ξ ⊢ A → Γ ⊢ A) → Γ ⊢⋆ Ξ
putₛ {∅}     f = ∅
putₛ {Γ , A} f = putₛ (λ M → f (wk M)) , f (` zero)

getₛ : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ∋ A → Γ ⊢ A
getₛ (σ , M) zero    = M
getₛ (σ , M) (suc i) = getₛ σ i

wkₛ : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ → Γ , A ⊢⋆ Ξ
wkₛ ∅       = ∅
wkₛ (σ , M) = wkₛ σ , wk M

liftₛ : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ → Γ , A ⊢⋆ Ξ , A
liftₛ σ = wkₛ σ , ` zero

idₛ : ∀ {Γ} → Γ ⊢⋆ Γ
idₛ {∅}     = ∅
idₛ {Γ , A} = liftₛ idₛ

sub : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ⊢ A → Γ ⊢ A
sub σ (` i)   = getₛ σ i
sub σ (ƛ M)   = ƛ (sub (liftₛ σ) M)
sub σ (M ∙ N) = sub σ M ∙ sub σ N

cut : ∀ {Γ A B} → Γ ⊢ A → Γ , A ⊢ B → Γ ⊢ B
cut M N = sub (idₛ , M) N

-- NOTE: _●_ = sub⋆
_●_ : ∀ {Γ Ξ Φ} → Γ ⊢⋆ Ξ → Ξ ⊢⋆ Φ → Γ ⊢⋆ Φ
σ₁ ● ∅        = ∅
σ₁ ● (σ₂ , M) = σ₁ ● σ₂ , sub σ₁ M


--------------------------------------------------------------------------------


-- (wkgetₛ)
natgetₛ : ∀ {Γ Ξ A B} → (σ : Γ ⊢⋆ Ξ) (i : Ξ ∋ A)
                      → getₛ (wkₛ {B} σ) i ≡ (wk ∘ getₛ σ) i
natgetₛ (σ , M) zero    = refl
natgetₛ (σ , M) (suc i) = natgetₛ σ i

idgetₛ : ∀ {Γ A} → (i : Γ ∋ A)
                 → getₛ idₛ i ≡ ` i
idgetₛ zero    = refl
idgetₛ (suc i) = natgetₛ idₛ i
               ⦙ wk & idgetₛ i
               ⦙ ` & ( natgetᵣ idᵣ i
                     ⦙ suc & idgetᵣ i
                     )

idsub : ∀ {Γ A} → (M : Γ ⊢ A)
                → sub idₛ M ≡ M
idsub (` i)   = idgetₛ i
idsub (ƛ M)   = ƛ & idsub M
idsub (M ∙ N) = _∙_ & idsub M
                    ⊗ idsub N


--------------------------------------------------------------------------------


⌊_⌋ : ∀ {Γ Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢⋆ Γ
⌊ ∅ ⌋     = ∅
⌊ η , i ⌋ = ⌊ η ⌋ , ` i

-- NOTE: _◐_ = getₛ⋆
_◐_ : ∀ {Γ Ξ Ξ′} → Γ ⊢⋆ Ξ′ → Ξ′ ∋⋆ Ξ → Γ ⊢⋆ Ξ
σ ◐ η = σ ● ⌊ η ⌋

-- NOTE: _◑_ = ren⋆
_◑_ : ∀ {Γ Γ′ Ξ} → Γ′ ∋⋆ Γ → Γ ⊢⋆ Ξ → Γ′ ⊢⋆ Ξ
η ◑ σ = ⌊ η ⌋ ● σ


⌊get⌋ : ∀ {Γ Γ′ A} → (η : Γ′ ∋⋆ Γ) (i : Γ ∋ A)
                   → getₛ ⌊ η ⌋ i ≡ ` (getᵣ η i)
⌊get⌋ (η , j) zero    = refl
⌊get⌋ (η , j) (suc i) = ⌊get⌋ η i

⌊wk⌋ : ∀ {Γ Γ′ A} → (η : Γ′ ∋⋆ Γ)
                  → wkₛ {A} ⌊ η ⌋ ≡ ⌊ wkᵣ η ⌋
⌊wk⌋ ∅       = refl
⌊wk⌋ (η , i) = (wkₛ ⌊ η ⌋ ,_) & (` & natgetᵣ idᵣ i)
             ⦙ _,_ & ⌊wk⌋ η
                   ⊗ ` ∘ suc & idgetᵣ i

⌊lift⌋ : ∀ {Γ Γ′ A} → (η : Γ′ ∋⋆ Γ)
                    → liftₛ {A} ⌊ η ⌋ ≡ ⌊ liftᵣ η ⌋
⌊lift⌋ η = (_, ` zero) & ⌊wk⌋ η

⌊id⌋ : ∀ {Γ} → idₛ {Γ} ≡ ⌊ idᵣ ⌋
⌊id⌋ {∅}     = refl
⌊id⌋ {Γ , A} = (_, ` zero) & ( wkₛ & ⌊id⌋
                             ⦙ ⌊wk⌋ idᵣ
                             )

⌊sub⌋ : ∀ {Γ Γ′ A} → (η : Γ′ ∋⋆ Γ) (M : Γ ⊢ A)
                   → sub ⌊ η ⌋ M ≡ ren η M
⌊sub⌋ η (` i)   = ⌊get⌋ η i
⌊sub⌋ η (ƛ M)   = ƛ & ( (λ σ → sub σ M) & ⌊lift⌋ η
                      ⦙ ⌊sub⌋ (liftᵣ η) M
                      )
⌊sub⌋ η (M ∙ N) = _∙_ & ⌊sub⌋ η M
                      ⊗ ⌊sub⌋ η N

⌊○⌋ : ∀ {Γ Γ′ Γ″} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ)
                  → ⌊ η₁ ○ η₂ ⌋ ≡ ⌊ η₁ ⌋ ● ⌊ η₂ ⌋
⌊○⌋ η₁ ∅        = refl
⌊○⌋ η₁ (η₂ , i) = _,_ & ⌊○⌋ η₁ η₂
                      ⊗ (⌊get⌋ η₁ i ⁻¹)


--------------------------------------------------------------------------------


zap◐ : ∀ {Γ Ξ Ξ′ A} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (M : Γ ⊢ A)
                    → (σ , M) ◐ wkᵣ η ≡ σ ◐ η
zap◐ σ ∅       M = refl
zap◐ σ (η , i) M = (_, getₛ σ i) & zap◐ σ η M

rid◐ : ∀ {Γ Ξ} → (σ : Γ ⊢⋆ Ξ)
               → σ ◐ idᵣ ≡ σ
rid◐ ∅       = refl
rid◐ (σ , M) = (_, M) & ( zap◐ σ idᵣ M
                        ⦙ rid◐ σ
                        )


--------------------------------------------------------------------------------


get◐ : ∀ {Γ Ξ Ξ′ A} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (i : Ξ ∋ A)
                    → getₛ (σ ◐ η) i ≡ (getₛ σ ∘ getᵣ η) i
get◐ σ (η , j) zero    = refl
get◐ σ (η , j) (suc i) = get◐ σ η i

wk◐ : ∀ {Γ Ξ Ξ′ A} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ)
                   → wkₛ {A} (σ ◐ η) ≡ wkₛ σ ◐ η
wk◐ σ ∅       = refl
wk◐ σ (η , i) = _,_ & wk◐ σ η
                    ⊗ (natgetₛ σ i ⁻¹)

lift◐ : ∀ {Γ Ξ Ξ′ A} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ)
                     → liftₛ {A} (σ ◐ η) ≡ liftₛ σ ◐ liftᵣ η
lift◐ σ η = (_, ` zero) & ( wk◐ σ η
                        ⦙ zap◐ (wkₛ σ) η (` zero) ⁻¹
                        )

wkrid◐ : ∀ {Γ Ξ A} → (σ : Γ ⊢⋆ Ξ)
                   → wkₛ {A} σ ◐ idᵣ ≡ wkₛ σ
wkrid◐ σ = wk◐ σ idᵣ ⁻¹
         ⦙ wkₛ & rid◐ σ

liftwkrid◐ : ∀ {Γ Ξ A} → (σ : Γ ⊢⋆ Ξ)
                       → liftₛ {A} σ ◐ wkᵣ idᵣ ≡ wkₛ σ
liftwkrid◐ σ = zap◐ (wkₛ σ) idᵣ (` zero)
             ⦙ wkrid◐ σ

mutual
  sub◐ : ∀ {Γ Ξ Ξ′ A} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (M : Ξ ⊢ A)
                      → sub (σ ◐ η) M ≡ (sub σ ∘ ren η) M
  sub◐ σ η (` i)   = get◐ σ η i
  sub◐ σ η (ƛ M)   = ƛ & sublift◐ σ η M
  sub◐ σ η (M ∙ N) = _∙_ & sub◐ σ η M
                         ⊗ sub◐ σ η N

  sublift◐ : ∀ {Γ Ξ Ξ′ A B} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (M : Ξ , B ⊢ A)
                            → sub (liftₛ {B} (σ ◐ η)) M ≡
                               (sub (liftₛ σ) ∘ ren (liftᵣ η)) M
  sublift◐ σ η M = (λ σ′ → sub σ′ M) & lift◐ σ η
                 ⦙ sub◐ (liftₛ σ) (liftᵣ η) M

subwk◐ : ∀ {Γ Ξ Ξ′ A B} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (M : Ξ ⊢ A)
                        → sub (wkₛ {B} (σ ◐ η)) M ≡
                           (sub (wkₛ σ) ∘ ren η) M
subwk◐ σ η M = (λ σ′ → sub σ′ M) & wk◐ σ η
             ⦙ sub◐ (wkₛ σ) η M

subliftwk◐ : ∀ {Γ Ξ Ξ′ A B} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (M : Ξ ⊢ A)
                            → sub (wkₛ {B} (σ ◐ η)) M ≡
                               (sub (liftₛ σ) ∘ ren (wkᵣ η)) M
subliftwk◐ σ η M = (λ σ′ → sub σ′ M) & ( wk◐ σ η
                                        ⦙ zap◐ (wkₛ σ) η (` zero) ⁻¹
                                        )
                 ⦙ sub◐ (liftₛ σ) (wkᵣ η) M


--------------------------------------------------------------------------------


zap◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ) (i : Γ′ ∋ A)
                    → (η , i) ◑ wkₛ σ ≡ η ◑ σ
zap◑ η ∅       i = refl
zap◑ η (σ , j) i = _,_ & zap◑ η σ i
                       ⊗ ( sub◐ (⌊ η ⌋ , ` i) (wkᵣ idᵣ) j ⁻¹
                         ⦙ (λ σ′ → sub σ′ j)
                           & ( zap◐ ⌊ η ⌋ idᵣ (` i)
                             ⦙ rid◐ ⌊ η ⌋
                             )
                         )

lid◑ : ∀ {Γ Ξ} → (σ : Γ ⊢⋆ Ξ)
               → idᵣ ◑ σ ≡ σ
lid◑ ∅       = refl
lid◑ (σ , M) = _,_ & lid◑ σ
                   ⊗ ( (λ σ′ → sub σ′ M) & ⌊id⌋ ⁻¹
                     ⦙ idsub M
                     )


--------------------------------------------------------------------------------


zap● : ∀ {Γ Ξ Φ A} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (M : Γ ⊢ A)
                   → (σ₁ , M) ● wkₛ σ₂ ≡ σ₁ ● σ₂
zap● σ₁ ∅        M = refl
zap● σ₁ (σ₂ , N) M = _,_ & zap● σ₁ σ₂ M
                         ⊗ ( sub◐ (σ₁ , M) (wkᵣ idᵣ) N ⁻¹
                           ⦙ (λ σ′ → sub σ′ N)
                             & ( zap◐ σ₁ idᵣ M
                               ⦙ rid◐ σ₁
                               )
                           )

lid● : ∀ {Γ Ξ} → (σ : Γ ⊢⋆ Ξ)
               → idₛ ● σ ≡ σ
lid● ∅       = refl
lid● (σ , M) = _,_ & lid● σ
                   ⊗ idsub M

rid● : ∀ {Γ Ξ} → (σ : Γ ⊢⋆ Ξ)
               → σ ● idₛ ≡ σ
rid● σ = (σ ●_) & ⌊id⌋ ⦙ rid◐ σ


--------------------------------------------------------------------------------


get◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ) (i : Ξ ∋ A)
                    → getₛ (η ◑ σ) i ≡ (ren η ∘ getₛ σ) i
get◑ η (σ , M) zero    = ⌊sub⌋ η M
get◑ η (σ , M) (suc i) = get◑ η σ i

wk◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ)
                   → wkₛ {A} (η ◑ σ) ≡ wkᵣ η ◑ σ
wk◑ η ∅       = refl
wk◑ η (σ , M) = _,_ & wk◑ η σ
                    ⊗ ( ren (wkᵣ idᵣ) & ⌊sub⌋ η M
                      ⦙ ren○ (wkᵣ idᵣ) η M ⁻¹
                      ⦙ (λ η′ → ren η′ M) & wklid○ η
                      ⦙ ⌊sub⌋ (wkᵣ η) M ⁻¹
                      )

lift◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ)
                     → liftₛ {A} (η ◑ σ) ≡ liftᵣ η ◑ liftₛ σ
lift◑ η σ = (_, ` zero) & ( wk◑ η σ
                          ⦙ zap● ⌊ wkᵣ η ⌋ σ (` zero) ⁻¹
                          )

wklid◑ : ∀ {Γ Ξ A} → (σ : Γ ⊢⋆ Ξ)
                   → wkᵣ {A} idᵣ ◑ σ ≡ wkₛ σ
wklid◑ σ = wk◑ idᵣ σ ⁻¹
         ⦙ wkₛ & lid◑ σ

liftwklid◑ : ∀ {Γ Ξ A} → (σ : Γ ⊢⋆ Ξ)
                       → (liftᵣ {A} idᵣ ◑ wkₛ σ) ≡ wkₛ σ
liftwklid◑ σ = zap◑ (wkᵣ idᵣ) σ zero
             ⦙ wklid◑ σ

mutual
  sub◑ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ) (M : Ξ ⊢ A)
                      → sub (η ◑ σ) M ≡ (ren η ∘ sub σ) M
  sub◑ η σ (` i)   = get◑ η σ i
  sub◑ η σ (ƛ M)   = ƛ & sublift◑ η σ M
  sub◑ η σ (M ∙ N) = _∙_ & sub◑ η σ M
                         ⊗ sub◑ η σ N

  sublift◑ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ) (M : Ξ , B ⊢ A)
                            → sub (liftₛ {B} (η ◑ σ)) M ≡
                               (ren (liftᵣ η) ∘ sub (liftₛ σ)) M
  sublift◑ η σ M = (λ σ′ → sub σ′ M) & lift◑ η σ
                 ⦙ sub◑ (liftᵣ η) (liftₛ σ) M

subwk◑ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ) (M : Ξ ⊢ A)
                        → sub (wkₛ {B} (η ◑ σ)) M ≡
                           (ren (wkᵣ η) ∘ sub σ) M
subwk◑ η σ M = (λ σ′ → sub σ′ M) & wk◑ η σ
             ⦙ sub◑ (wkᵣ η) σ M
subliftwk◑ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ) (M : Ξ ⊢ A)
                            → sub (wkₛ {B} (η ◑ σ)) M ≡
                               (ren (liftᵣ η) ∘ sub (wkₛ σ)) M
subliftwk◑ η σ M = (λ σ′ → sub σ′ M) & ( wk◑ η σ
                                        ⦙ zap◑ (wkᵣ η) σ zero ⁻¹
                                        )
                 ⦙ sub◑ (liftᵣ η) (wkₛ σ) M


--------------------------------------------------------------------------------


get● : ∀ {Γ Ξ Φ A} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (i : Φ ∋ A)
                   → getₛ (σ₁ ● σ₂) i ≡ (sub σ₁ ∘ getₛ σ₂) i
get● σ₁ (σ₂ , M) zero    = refl
get● σ₁ (σ₂ , M) (suc i) = get● σ₁ σ₂ i

wk● : ∀ {Γ Ξ Φ A} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ)
                  → wkₛ {A} (σ₁ ● σ₂) ≡ wkₛ σ₁ ● σ₂
wk● σ₁ ∅        = refl
wk● σ₁ (σ₂ , M) = _,_ & wk● σ₁ σ₂
                      ⊗ ( sub◑ (wkᵣ idᵣ) σ₁ M ⁻¹
                        ⦙ (λ σ′ → sub σ′ M) & wklid◑ σ₁
                        )

lift● : ∀ {Γ Ξ Φ A} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ)
                    → liftₛ {A} (σ₁ ● σ₂) ≡ liftₛ σ₁ ● liftₛ σ₂
lift● σ₁ σ₂ = (_, ` zero) & ( wk● σ₁ σ₂
                            ⦙ zap● (wkₛ σ₁) σ₂ (` zero) ⁻¹
                            )

wklid● : ∀ {Γ Ξ A} → (σ : Γ ⊢⋆ Ξ)
                   → wkₛ {A} idₛ ● σ ≡ wkₛ σ
wklid● σ = wk● idₛ σ ⁻¹
         ⦙ wkₛ & lid● σ

wkrid● : ∀ {Γ Ξ A} → (σ : Γ ⊢⋆ Ξ)
                   → wkₛ {A} σ ● idₛ ≡ wkₛ σ
wkrid● σ = wk● σ idₛ ⁻¹
         ⦙ wkₛ & rid● σ

liftwkrid● : ∀ {Γ Ξ A} → (σ : Γ ⊢⋆ Ξ)
                       → liftₛ {A} σ ● wkₛ idₛ ≡ wkₛ σ
liftwkrid● σ = zap● (wkₛ σ) idₛ (` zero)
             ⦙ wkrid● σ

mutual
  sub● : ∀ {Γ Ξ Φ A} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (M : Φ ⊢ A)
                     → sub (σ₁ ● σ₂) M ≡ (sub σ₁ ∘ sub σ₂) M
  sub● σ₁ σ₂ (` i)   = get● σ₁ σ₂ i
  sub● σ₁ σ₂ (ƛ M)   = ƛ & sublift● σ₁ σ₂ M
  sub● σ₁ σ₂ (M ∙ N) = _∙_ & sub● σ₁ σ₂ M
                           ⊗ sub● σ₁ σ₂ N

  sublift● : ∀ {Γ Ξ Φ A B} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (M : Φ , B ⊢ A)
                           → sub (liftₛ {B} (σ₁ ● σ₂)) M ≡
                              (sub (liftₛ σ₁) ∘ sub (liftₛ σ₂)) M
  sublift● σ₁ σ₂ M = (λ σ′ → sub σ′ M) & lift● σ₁ σ₂
                   ⦙ sub● (liftₛ σ₁) (liftₛ σ₂) M

subwk● : ∀ {Γ Ξ Φ A B} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (M : Φ ⊢ A)
                       → sub (wkₛ {B} (σ₁ ● σ₂)) M ≡
                          (sub (wkₛ σ₁) ∘ sub σ₂) M
subwk● σ₁ σ₂ M = (λ σ′ → sub σ′ M) & wk● σ₁ σ₂
               ⦙ sub● (wkₛ σ₁) σ₂ M

subliftwk● : ∀ {Γ Ξ Φ A B} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (M : Φ ⊢ A)
                           → sub (wkₛ {B} (σ₁ ● σ₂)) M ≡
                              (sub (liftₛ σ₁) ∘ sub (wkₛ σ₂)) M
subliftwk● σ₁ σ₂ M = (λ σ′ → sub σ′ M) & ( wk● σ₁ σ₂
                                          ⦙ zap● (wkₛ σ₁) σ₂ (` zero) ⁻¹
                                          )
                   ⦙ sub● (liftₛ σ₁) (wkₛ σ₂) M


--------------------------------------------------------------------------------


comp◐○ : ∀ {Γ Ξ Ξ′ Ξ″} → (σ : Γ ⊢⋆ Ξ″) (η₁ : Ξ″ ∋⋆ Ξ′) (η₂ : Ξ′ ∋⋆ Ξ)
                       → σ ◐ (η₁ ○ η₂) ≡ (σ ◐ η₁) ◐ η₂
comp◐○ σ η₁ ∅        = refl
comp◐○ σ η₁ (η₂ , i) = _,_ & comp◐○ σ η₁ η₂
                           ⊗ (get◐ σ η₁ i ⁻¹)


comp◑○ : ∀ {Γ Γ′ Γ″ Ξ} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ)
                       → η₁ ◑ (η₂ ◑ σ) ≡ (η₁ ○ η₂) ◑ σ
comp◑○ η₁ η₂ ∅       = refl
comp◑○ η₁ η₂ (σ , M) = _,_ & comp◑○ η₁ η₂ σ
                           ⊗ ( sub● ⌊ η₁ ⌋ ⌊ η₂ ⌋ M ⁻¹
                             ⦙ (λ σ′ → sub σ′ M)
                               & ⌊○⌋ η₁ η₂ ⁻¹
                             )

comp◑◐ : ∀ {Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ∋⋆ Γ) (σ : Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ∋⋆ Ξ)
                       → η₁ ◑ (σ ◐ η₂) ≡ (η₁ ◑ σ) ◐ η₂
comp◑◐ η₁ σ ∅        = refl
comp◑◐ η₁ σ (η₂ , i) = _,_ & comp◑◐ η₁ σ η₂
                           ⊗ ( ⌊sub⌋ η₁ (getₛ σ i)
                             ⦙ get◑ η₁ σ i ⁻¹
                             )

comp◑● : ∀ {Γ Γ′ Ξ Φ} → (η : Γ′ ∋⋆ Γ) (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ)
                      → η ◑ (σ₁ ● σ₂) ≡ (η ◑ σ₁) ● σ₂
comp◑● η σ₁ ∅        = refl
comp◑● η σ₁ (σ₂ , M) = _,_ & comp◑● η σ₁ σ₂
                           ⊗ (sub● ⌊ η ⌋ σ₁ M ⁻¹)


comp●◐ : ∀ {Γ Ξ Φ Φ′} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ′) (η : Φ′ ∋⋆ Φ)
                      → σ₁ ● (σ₂ ◐ η) ≡ (σ₁ ● σ₂) ◐ η
comp●◐ σ₁ σ₂ ∅       = refl
comp●◐ σ₁ σ₂ (η , i) = _,_ & comp●◐ σ₁ σ₂ η
                           ⊗ (get● σ₁ σ₂ i ⁻¹)

comp●◑ : ∀ {Γ Ξ Ξ′ Φ} → (σ₁ : Γ ⊢⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ)
                      → σ₁ ● (η ◑ σ₂) ≡ (σ₁ ◐ η) ● σ₂
comp●◑ σ₁ η ∅        = refl
comp●◑ σ₁ η (σ₂ , M) = _,_ & comp●◑ σ₁ η σ₂
                           ⊗ (sub● σ₁ ⌊ η ⌋ M ⁻¹)


--------------------------------------------------------------------------------


assoc● : ∀ {Γ Ξ Φ Ψ} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (σ₃ : Φ ⊢⋆ Ψ)
                     → σ₁ ● (σ₂ ● σ₃) ≡ (σ₁ ● σ₂) ● σ₃
assoc● σ₁ σ₂ ∅        = refl
assoc● σ₁ σ₂ (σ₃ , M) = _,_ & assoc● σ₁ σ₂ σ₃
                            ⊗ (sub● σ₁ σ₂ M ⁻¹)


--------------------------------------------------------------------------------


𝗦𝗧𝗟𝗖 : Category 𝒞 _⊢⋆_
𝗦𝗧𝗟𝗖 =
  record
    { idₓ    = idₛ
    ; _⋄_    = flip _●_
    ; lid⋄   = rid●
    ; rid⋄   = lid●
    ; assoc⋄ = assoc●
    }


subPsh : 𝒯 → Presheaf₀ 𝗦𝗧𝗟𝗖
subPsh A =
  record
    { Fₓ   = _⊢ A
    ; Fₘ   = sub
    ; idFₘ = fext! idsub
    ; Fₘ⋄  = λ σ₁ σ₂ → fext! (sub● σ₂ σ₁)
    }


--------------------------------------------------------------------------------
