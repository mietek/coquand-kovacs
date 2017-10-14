module STLC1.Kovacs.NormalForm where

open import STLC1.Kovacs.Embedding public
open import Category


--------------------------------------------------------------------------------


mutual
  -- (Nfₑ)
  renⁿᶠ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ⁿᶠ A → Γ′ ⊢ⁿᶠ A
  renⁿᶠ η (ƛ M)   = ƛ (renⁿᶠ (liftₑ η) M)
  renⁿᶠ η (M , N) = renⁿᶠ η M , renⁿᶠ η N
  renⁿᶠ η τ       = τ
  renⁿᶠ η (ne M)  = ne (renⁿᵉ η M)

  -- (Neₑ)
  renⁿᵉ : ∀ {Γ Γ′ A} → Γ′ ⊇ Γ → Γ ⊢ⁿᵉ A → Γ′ ⊢ⁿᵉ A
  renⁿᵉ η (` i)   = ` (getₑ η i)
  renⁿᵉ η (M ∙ N) = renⁿᵉ η M ∙ renⁿᶠ η N
  renⁿᵉ η (π₁ M)  = π₁ (renⁿᵉ η M)
  renⁿᵉ η (π₂ M)  = π₂ (renⁿᵉ η M)


mutual
  -- (Nf-idₑ)
  idrenⁿᶠ : ∀ {Γ A} → (M : Γ ⊢ⁿᶠ A)
                    → renⁿᶠ idₑ M ≡ M
  idrenⁿᶠ (ƛ M)   = ƛ & idrenⁿᶠ M
  idrenⁿᶠ (M , N) = _,_ & idrenⁿᶠ M ⊗ idrenⁿᶠ N
  idrenⁿᶠ τ       = refl
  idrenⁿᶠ (ne M)  = ne & idrenⁿᵉ M

  -- (Ne-idₑ)
  idrenⁿᵉ : ∀ {Γ A} → (M : Γ ⊢ⁿᵉ A)
                    → renⁿᵉ idₑ M ≡ M
  idrenⁿᵉ (` i)   = ` & idgetₑ i
  idrenⁿᵉ (M ∙ N) = _∙_ & idrenⁿᵉ M
                        ⊗ idrenⁿᶠ N
  idrenⁿᵉ (π₁ M)  = π₁ & idrenⁿᵉ M
  idrenⁿᵉ (π₂ M)  = π₂ & idrenⁿᵉ M


mutual
  -- (Nf-∘ₑ)
  renⁿᶠ○ : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ″ ⊇ Γ′) (η₂ : Γ′ ⊇ Γ) (M : Γ ⊢ⁿᶠ A)
                         → renⁿᶠ (η₂ ○ η₁) M ≡ (renⁿᶠ η₁ ∘ renⁿᶠ η₂) M
  renⁿᶠ○ η₁ η₂ (ƛ M)   = ƛ & renⁿᶠ○ (liftₑ η₁) (liftₑ η₂) M
  renⁿᶠ○ η₁ η₂ (M , N) = _,_ & renⁿᶠ○ η₁ η₂ M
                             ⊗ renⁿᶠ○ η₁ η₂ N
  renⁿᶠ○ η₁ η₂ τ       = refl
  renⁿᶠ○ η₁ η₂ (ne M)  = ne & renⁿᵉ○ η₁ η₂ M

  -- (Ne-∘ₑ)
  renⁿᵉ○ : ∀ {Γ Γ′ Γ″ A} → (η₁ : Γ″ ⊇ Γ′) (η₂ : Γ′ ⊇ Γ) (M : Γ ⊢ⁿᵉ A)
                         → renⁿᵉ (η₂ ○ η₁) M ≡ (renⁿᵉ η₁ ∘ renⁿᵉ η₂) M
  renⁿᵉ○ η₁ η₂ (` i)   = ` & get○ η₁ η₂ i
  renⁿᵉ○ η₁ η₂ (M ∙ N) = _∙_ & renⁿᵉ○ η₁ η₂ M
                             ⊗ renⁿᶠ○ η₁ η₂ N
  renⁿᵉ○ η₁ η₂ (π₁ M)  = π₁ & renⁿᵉ○ η₁ η₂ M
  renⁿᵉ○ η₁ η₂ (π₂ M)  = π₂ & renⁿᵉ○ η₁ η₂ M


--------------------------------------------------------------------------------


mutual
  -- (⌜_⌝Nf)
  embⁿᶠ : ∀ {Γ A} → Γ ⊢ⁿᶠ A → Γ ⊢ A
  embⁿᶠ (ƛ M)   = ƛ (embⁿᶠ M)
  embⁿᶠ (M , N) = embⁿᶠ M , embⁿᶠ N
  embⁿᶠ τ       = τ
  embⁿᶠ (ne M)  = embⁿᵉ M

  -- (⌜_⌝Ne)
  embⁿᵉ : ∀ {Γ A} → Γ ⊢ⁿᵉ A → Γ ⊢ A
  embⁿᵉ (` i)   = ` i
  embⁿᵉ (M ∙ N) = embⁿᵉ M ∙ embⁿᶠ N
  embⁿᵉ (π₁ M)  = π₁ (embⁿᵉ M)
  embⁿᵉ (π₂ M)  = π₂ (embⁿᵉ M)


mutual
  -- (⌜⌝Nf-nat)
  natembⁿᶠ : ∀ {A Γ Γ′} → (η : Γ′ ⊇ Γ) (M : Γ ⊢ⁿᶠ A)
                        → (embⁿᶠ ∘ renⁿᶠ η) M ≡ (ren η ∘ embⁿᶠ) M
  natembⁿᶠ η (ƛ M)   = ƛ & natembⁿᶠ (liftₑ η) M
  natembⁿᶠ η (M , N) = _,_ & natembⁿᶠ η M
                           ⊗ natembⁿᶠ η N
  natembⁿᶠ η τ       = refl
  natembⁿᶠ η (ne M)  = natembⁿᵉ η M

  -- (⌜⌝Ne-nat)
  natembⁿᵉ : ∀ {A Γ Γ′} → (η : Γ′ ⊇ Γ) (M : Γ ⊢ⁿᵉ A)
                        → (embⁿᵉ ∘ renⁿᵉ η) M ≡ (ren η ∘ embⁿᵉ) M
  natembⁿᵉ η (` i)   = refl
  natembⁿᵉ η (M ∙ N) = _∙_ & natembⁿᵉ η M
                           ⊗ natembⁿᶠ η N
  natembⁿᵉ η (π₁ M)  = π₁ & natembⁿᵉ η M
  natembⁿᵉ η (π₂ M)  = π₂ & natembⁿᵉ η M


--------------------------------------------------------------------------------


renⁿᶠPsh : 𝒯 → Presheaf₀ 𝗢𝗣𝗘
renⁿᶠPsh A =
  record
    { Fₓ  = _⊢ⁿᶠ A
    ; F   = renⁿᶠ
    ; idF = fext! idrenⁿᶠ
    ; F⋄  = λ η₁ η₂ → fext! (renⁿᶠ○ η₂ η₁)
    }

renⁿᵉPsh : 𝒯 → Presheaf₀ 𝗢𝗣𝗘
renⁿᵉPsh A =
  record
    { Fₓ  = _⊢ⁿᵉ A
    ; F   = renⁿᵉ
    ; idF = fext! idrenⁿᵉ
    ; F⋄  = λ η₁ η₂ → fext! (renⁿᵉ○ η₂ η₁)
    }


embⁿᶠNT : ∀ {A} → NaturalTransformation (renⁿᶠPsh A) (renPsh A)
embⁿᶠNT =
  record
    { N    = embⁿᶠ
    ; natN = λ η → fext! (λ M → natembⁿᶠ η M)
    }

embⁿᵉNT : ∀ {A} → NaturalTransformation (renⁿᵉPsh A) (renPsh A)
embⁿᵉNT =
  record
    { N    = embⁿᵉ
    ; natN = λ η → fext! (λ M → natembⁿᵉ η M)
    }


--------------------------------------------------------------------------------
