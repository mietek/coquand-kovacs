module STLC.Coquand.Renaming where

open import STLC.Syntax public
open import Category


--------------------------------------------------------------------------------


-- Renamings
infix 4 _∋⋆_
data _∋⋆_ : 𝒞 → 𝒞 → Set
  where
    ∅   : ∀ {Γ} → Γ ∋⋆ ∅

    _,_ : ∀ {Γ Γ′ A} → (η : Γ′ ∋⋆ Γ) (i : Γ′ ∋ A)
                     → Γ′ ∋⋆ Γ , A


putᵣ : ∀ {Γ Γ′} → (∀ {A} → Γ ∋ A → Γ′ ∋ A) → Γ′ ∋⋆ Γ
putᵣ {∅}     f = ∅
putᵣ {Γ , A} f = putᵣ (λ i → f (suc i)) , f 0

getᵣ : ∀ {Γ Γ′ A} → Γ′ ∋⋆ Γ → Γ ∋ A → Γ′ ∋ A
getᵣ (η , i) zero    = i
getᵣ (η , i) (suc j) = getᵣ η j

wkᵣ : ∀ {A Γ Γ′} → Γ′ ∋⋆ Γ → Γ′ , A ∋⋆ Γ
wkᵣ ∅       = ∅
wkᵣ (η , i) = wkᵣ η , suc i

liftᵣ : ∀ {A Γ Γ′} → Γ′ ∋⋆ Γ → Γ′ , A ∋⋆ Γ , A
liftᵣ η = wkᵣ η , 0

idᵣ : ∀ {Γ} → Γ ∋⋆ Γ
idᵣ {∅}     = ∅
idᵣ {Γ , A} = liftᵣ idᵣ

ren : ∀ {Γ Γ′ A} → Γ′ ∋⋆ Γ → Γ ⊢ A → Γ′ ⊢ A
ren η (` i)   = ` (getᵣ η i)
ren η (ƛ M)   = ƛ (ren (liftᵣ η) M)
ren η (M ∙ N) = ren η M ∙ ren η N

wk : ∀ {B Γ A} → Γ ⊢ A → Γ , B ⊢ A
wk M = ren (wkᵣ idᵣ) M

-- NOTE: _○_ = getᵣ⋆
_○_ : ∀ {Γ Γ′ Γ″} → Γ″ ∋⋆ Γ′ → Γ′ ∋⋆ Γ → Γ″ ∋⋆ Γ
η₁ ○ ∅        = ∅
η₁ ○ (η₂ , i) = η₁ ○ η₂ , getᵣ η₁ i


--------------------------------------------------------------------------------


-- (wkgetᵣ)
natgetᵣ : ∀ {Γ Γ′ A B} → (η : Γ′ ∋⋆ Γ) (i : Γ ∋ A)
                       → getᵣ (wkᵣ {B} η) i ≡ (suc ∘ getᵣ η) i
natgetᵣ (η , j) zero    = refl
natgetᵣ (η , j) (suc i) = natgetᵣ η i

idgetᵣ : ∀ {Γ A} → (i : Γ ∋ A)
                 → getᵣ idᵣ i ≡ i
idgetᵣ zero    = refl
idgetᵣ (suc i) = natgetᵣ idᵣ i
               ⦙ suc & idgetᵣ i

idren : ∀ {Γ A} → (M : Γ ⊢ A)
                → ren idᵣ M ≡ M
idren (` i)   = ` & idgetᵣ i
idren (ƛ M)   = ƛ & idren M
idren (M ∙ N) = _∙_ & idren M
                    ⊗ idren N


--------------------------------------------------------------------------------


zap○ : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ) (i : Γ″ ∋ A)
                     → (η₁ , i) ○ wkᵣ η₂ ≡ η₁ ○ η₂
zap○ η₁ ∅        i = refl
zap○ η₁ (η₂ , j) i = (_, getᵣ η₁ j) & zap○ η₁ η₂ i

lid○ : ∀ {Γ Γ′} → (η : Γ′ ∋⋆ Γ)
                → idᵣ ○ η ≡ η
lid○ ∅       = refl
lid○ (η , i) = _,_ & lid○ η
                   ⊗ idgetᵣ i

rid○ : ∀ {Γ Γ′} → (η : Γ′ ∋⋆ Γ)
                → η ○ idᵣ ≡ η
rid○ {∅}     ∅       = refl
rid○ {Γ , A} (η , i) = (_, i) & ( zap○ η idᵣ i
                                ⦙ rid○ η
                                )


--------------------------------------------------------------------------------


get○ : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ) (i : Γ ∋ A)
                     → getᵣ (η₁ ○ η₂) i ≡ (getᵣ η₁ ∘ getᵣ η₂) i
get○ η₁ (η₂ , j) zero    = refl
get○ η₁ (η₂ , j) (suc i) = get○ η₁ η₂ i

wk○ : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ)
                    → wkᵣ {A} (η₁ ○ η₂) ≡ wkᵣ η₁ ○ η₂
wk○ η₁ ∅        = refl
wk○ η₁ (η₂ , i) = _,_ & wk○ η₁ η₂
                      ⊗ (natgetᵣ η₁ i ⁻¹)

lift○ : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ)
                      → liftᵣ {A} (η₁ ○ η₂) ≡ liftᵣ η₁ ○ liftᵣ η₂
lift○ η₁ η₂ = (_, 0) & ( wk○ η₁ η₂
                          ⦙ (zap○ (wkᵣ η₁) η₂ 0 ⁻¹)
                          )

wklid○ : ∀ {Γ Γ′ A} → (η : Γ′ ∋⋆ Γ)
                    → wkᵣ {A} idᵣ ○ η ≡ wkᵣ η
wklid○ η = wk○ idᵣ η ⁻¹
         ⦙ wkᵣ & lid○ η

wkrid○ : ∀ {Γ Γ′ A} → (η : Γ′ ∋⋆ Γ)
                    → wkᵣ {A} η ○ idᵣ ≡ wkᵣ η
wkrid○ η = wk○ η idᵣ ⁻¹
         ⦙ wkᵣ & rid○ η

liftwkrid○ : ∀ {Γ Γ′ A} → (η : Γ′ ∋⋆ Γ)
                        → liftᵣ {A} η ○ wkᵣ idᵣ ≡ wkᵣ η
liftwkrid○ η = zap○ (wkᵣ η) idᵣ 0 ⦙ wkrid○ η

mutual
  ren○ : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ) (M : Γ ⊢ A)
                       → ren (η₁ ○ η₂) M ≡ (ren η₁ ∘ ren η₂) M
  ren○ η₁ η₂ (` i)   = ` & get○ η₁ η₂ i
  ren○ η₁ η₂ (ƛ M)   = ƛ & renlift○ η₁ η₂ M
  ren○ η₁ η₂ (M ∙ N) = _∙_ & ren○ η₁ η₂ M
                           ⊗ ren○ η₁ η₂ N

  renlift○ : ∀ {Γ Γ′ Γ″ A B} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ) (M : Γ , B ⊢ A)
                             → ren (liftᵣ {B} (η₁ ○ η₂)) M ≡
                                (ren (liftᵣ η₁) ∘ ren (liftᵣ η₂)) M
  renlift○ η₁ η₂ M = (λ η′ → ren η′ M) & lift○ η₁ η₂
                   ⦙ ren○ (liftᵣ η₁) (liftᵣ η₂) M

renwk○ : ∀ {Γ Γ′ Γ″ A B} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ) (M : Γ ⊢ A)
                         → ren (wkᵣ {B} (η₁ ○ η₂)) M ≡
                            (ren (wkᵣ η₁) ∘ ren η₂) M
renwk○ η₁ η₂ M = (λ η′ → ren η′ M) & wk○ η₁ η₂
               ⦙ ren○ (wkᵣ η₁) η₂ M

renliftwk○ : ∀ {Γ Γ′ Γ″ A B} → (η₁ : Γ″ ∋⋆ Γ′) (η₂ : Γ′ ∋⋆ Γ) (M : Γ ⊢ A)
                             → ren (wkᵣ {B} (η₁ ○ η₂)) M ≡
                                (ren (liftᵣ η₁) ∘ ren (wkᵣ η₂)) M
renliftwk○ η₁ η₂ M = (λ η′ → ren η′ M) & ( wk○ η₁ η₂
                                          ⦙ zap○ (wkᵣ η₁) η₂ 0 ⁻¹
                                          )
                   ⦙ ren○ (liftᵣ η₁) (wkᵣ η₂) M


--------------------------------------------------------------------------------


assoc○ : ∀ {Γ Γ′ Γ″ Γ‴} → (η₁ : Γ‴ ∋⋆ Γ″) (η₂ : Γ″ ∋⋆ Γ′) (η₃ : Γ′ ∋⋆ Γ)
                        → η₁ ○ (η₂ ○ η₃) ≡ (η₁ ○ η₂) ○ η₃
assoc○ η₁ η₂ ∅        = refl
assoc○ η₁ η₂ (η₃ , i) = _,_ & assoc○ η₁ η₂ η₃
                            ⊗ (get○ η₁ η₂ i ⁻¹)


--------------------------------------------------------------------------------


𝗥𝗲𝗻 : Category 𝒞 _∋⋆_
𝗥𝗲𝗻 =
  record
    { idₓ    = idᵣ
    ; _⋄_    = flip _○_
    ; lid⋄   = rid○
    ; rid⋄   = lid○
    ; assoc⋄ = assoc○
    }


getᵣPsh : 𝒯 → Presheaf₀ 𝗥𝗲𝗻
getᵣPsh A =
  record
    { Fₓ  = _∋ A
    ; F   = getᵣ
    ; idF = fext! idgetᵣ
    ; F⋄  = λ η₂ η₁ → fext! (get○ η₁ η₂)
    }

renPsh : 𝒯 → Presheaf₀ 𝗥𝗲𝗻
renPsh A =
  record
    { Fₓ  = _⊢ A
    ; F   = ren
    ; idF = fext! idren
    ; F⋄  = λ η₂ η₁ → fext! (ren○ η₁ η₂)
    }


--------------------------------------------------------------------------------
