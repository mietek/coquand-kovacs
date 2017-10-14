module STLCP.Kovacs.Embedding where

open import STLCP.Syntax public
open import Category


--------------------------------------------------------------------------------


-- Embeddings (OPE ; ∙ ; drop ; keep)
infix 4 _⊇_
data _⊇_ : 𝒞 → 𝒞 → Set
  where
    done  : ∅ ⊇ ∅

    wkₑ   : ∀ {Γ Γ′ A} → (η : Γ′ ⊇ Γ)
                       → Γ′ , A ⊇ Γ

    liftₑ : ∀ {Γ Γ′ A} → (η : Γ′ ⊇ Γ)
                       → Γ′ , A ⊇ Γ , A


idₑ : ∀ {Γ} → Γ ⊇ Γ
idₑ {∅}     = done
idₑ {Γ , A} = liftₑ idₑ

-- (_∘ₑ_)
_○_ : ∀ {Γ Γ′ Γ″} → Γ′ ⊇ Γ → Γ″ ⊇ Γ′ → Γ″ ⊇ Γ
η₂       ○ done     = η₂
η₂       ○ wkₑ η₁   = wkₑ (η₂ ○ η₁)
wkₑ η₂   ○ liftₑ η₁ = wkₑ (η₂ ○ η₁)
liftₑ η₂ ○ liftₑ η₁ = liftₑ (η₂ ○ η₁)

-- (idlₑ)
lid○ : ∀ {Γ Γ′} → (η : Γ′ ⊇ Γ)
                → idₑ ○ η ≡ η
lid○ done      = refl
lid○ (wkₑ η)   = wkₑ & lid○ η
lid○ (liftₑ η) = liftₑ & lid○ η

-- (idrₑ)
rid○ : ∀ {Γ Γ′} → (η : Γ′ ⊇ Γ)
                → η ○ idₑ ≡ η
rid○ done      = refl
rid○ (wkₑ η)   = wkₑ & rid○ η
rid○ (liftₑ η) = liftₑ & rid○ η

-- (assₑ)
assoc○ : ∀ {Γ Γ′ Γ″ Γ‴} → (η₁ : Γ‴ ⊇ Γ″) (η₂ : Γ″ ⊇ Γ′) (η₃ : Γ′ ⊇ Γ)
                        → (η₃ ○ η₂) ○ η₁ ≡ η₃ ○ (η₂ ○ η₁)
assoc○ done       η₂         η₃         = refl
assoc○ (wkₑ η₁)   η₂         η₃         = wkₑ & assoc○ η₁ η₂ η₃
assoc○ (liftₑ η₁) (wkₑ η₂)   η₃         = wkₑ & assoc○ η₁ η₂ η₃
assoc○ (liftₑ η₁) (liftₑ η₂) (wkₑ η₃)   = wkₑ & assoc○ η₁ η₂ η₃
assoc○ (liftₑ η₁) (liftₑ η₂) (liftₑ η₃) = liftₑ & assoc○ η₁ η₂ η₃


--------------------------------------------------------------------------------


-- (∈ₑ)
getₑ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ∋ A → Γ′ ∋ A
getₑ done      i       = i
getₑ (wkₑ η)   i       = suc (getₑ η i)
getₑ (liftₑ η) zero    = zero
getₑ (liftₑ η) (suc i) = suc (getₑ η i)

-- (∈-idₑ)
idgetₑ : ∀ {Γ A} → (i : Γ ∋ A)
                 → getₑ idₑ i ≡ i
idgetₑ zero    = refl
idgetₑ (suc i) = suc & idgetₑ i

-- (∈-∘ₑ)
get○ : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ″ ⊇ Γ′) (η₂ : Γ′ ⊇ Γ) (i : Γ ∋ A)
                     → getₑ (η₂ ○ η₁) i ≡ (getₑ η₁ ∘ getₑ η₂) i
get○ done       done       ()
get○ (wkₑ η₁)   η₂         i       = suc & get○ η₁ η₂ i
get○ (liftₑ η₁) (wkₑ η₂)   i       = suc & get○ η₁ η₂ i
get○ (liftₑ η₁) (liftₑ η₂) zero    = refl
get○ (liftₑ η₁) (liftₑ η₂) (suc i) = suc & get○ η₁ η₂ i


--------------------------------------------------------------------------------


-- (Tmₑ)
ren : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ A → Γ′ ⊢ A
ren η (` i)   = ` (getₑ η i)
ren η (ƛ M)   = ƛ (ren (liftₑ η) M)
ren η (M ∙ N) = ren η M ∙ ren η N
ren η (M , N) = ren η M , ren η N
ren η (π₁ M)  = π₁ (ren η M)
ren η (π₂ M)  = π₂ (ren η M)
ren η τ       = τ

wk : ∀ {B Γ A} → Γ ⊢ A → Γ , B ⊢ A
wk M = ren (wkₑ idₑ) M

-- (Tm-idₑ)
idren : ∀ {Γ A} → (M : Γ ⊢ A)
                → ren idₑ M ≡ M
idren (` i)   = ` & idgetₑ i
idren (ƛ M)   = ƛ & idren M
idren (M ∙ N) = _∙_ & idren M
                    ⊗ idren N
idren (M , N) = _,_ & idren M
                    ⊗ idren N
idren (π₁ M)  = π₁ & idren M
idren (π₂ M)  = π₂ & idren M
idren τ       = refl

-- (Tm-∘ₑ)
ren○ : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ″ ⊇ Γ′) (η₂ : Γ′ ⊇ Γ) (M : Γ ⊢ A)
                     → ren (η₂ ○ η₁) M ≡ (ren η₁ ∘ ren η₂) M
ren○ η₁ η₂ (` i)   = ` & get○ η₁ η₂ i
ren○ η₁ η₂ (ƛ M)   = ƛ & ren○ (liftₑ η₁) (liftₑ η₂) M
ren○ η₁ η₂ (M ∙ N) = _∙_ & ren○ η₁ η₂ M
                         ⊗ ren○ η₁ η₂ N
ren○ η₁ η₂ (M , N) = _,_ & ren○ η₁ η₂ M
                         ⊗ ren○ η₁ η₂ N
ren○ η₁ η₂ (π₁ M)  = π₁ & ren○ η₁ η₂ M
ren○ η₁ η₂ (π₂ M)  = π₂ & ren○ η₁ η₂ M
ren○ η₁ η₂ τ       = refl


--------------------------------------------------------------------------------


𝗢𝗣𝗘 : Category 𝒞 _⊇_
𝗢𝗣𝗘 =
  record
    { idₓ    = idₑ
    ; _⋄_    = _○_
    ; lid⋄   = lid○
    ; rid⋄   = rid○
    ; assoc⋄ = assoc○
    }


getₑPsh : 𝒯 → Presheaf₀ 𝗢𝗣𝗘
getₑPsh A =
  record
    { Fₓ  = _∋ A
    ; F   = getₑ
    ; idF = fext! idgetₑ
    ; F⋄  = λ η₁ η₂ → fext! (get○ η₂ η₁)
    }

renPsh : 𝒯 → Presheaf₀ 𝗢𝗣𝗘
renPsh A =
  record
    { Fₓ  = _⊢ A
    ; F   = ren
    ; idF = fext! idren
    ; F⋄  = λ η₁ η₂ → fext! (ren○ η₂ η₁)
    }


--------------------------------------------------------------------------------
