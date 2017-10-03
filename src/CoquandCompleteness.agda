{-# OPTIONS --no-positivity-check #-}

module CoquandCompleteness where

open import CoquandNormalisation public
open import CoquandConvertibility public


data CV : ∀ {Γ A} → Γ ⊢ A → Γ ⊩ A → Set
  where
    cv⎵ : ∀ {Γ} → {M : Γ ⊢ ⎵} {f : Γ ⊩ ⎵}
                → (h : ∀ {Γ′} → (η : Γ′ ∋⋆ Γ)
                               → sub ⌊ η ⌋ M ∼ ⟦g⟧⟨ η ⟩ f)
                → CV M f

    cv⊃ : ∀ {Γ A B} → {M : Γ ⊢ A ⊃ B} {f : Γ ⊩ A ⊃ B}
                    → (h : ∀ {Γ′ N a} → (η : Γ′ ∋⋆ Γ) → CV N a
                                       → CV (sub ⌊ η ⌋ M ∙ N) (f ◎⟨ η ⟩ a))
                    → CV M f


data CV⋆ : ∀ {Γ Ξ} → Γ ⊢⋆ Ξ → Γ ⊩⋆ Ξ → Set
  where
    []    : ∀ {Γ} → {σ : Γ ⊢⋆ []}
                  → CV⋆ σ []

    [_,_] : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ [ Ξ , A ]} {ρ : Γ ⊩⋆ Ξ} {a : Γ ⊩ A}
                      → (κ : CV⋆ (σ ◐ wkᵣ {A} idᵣ) ρ) (k : CV (sub σ (` zero)) a)
                      → CV⋆ σ [ ρ , a ]


--------------------------------------------------------------------------------


postulate
  congCV : ∀ {Γ A} → {M₁ M₂ : Γ ⊢ A} {a : Γ ⊩ A}
                   → M₁ ∼ M₂ → CV M₁ a
                   → CV M₂ a

-- (cong↑⟨_⟩CV)
postulate
  accCV : ∀ {Γ Γ′ A} → {M : Γ ⊢ A} {a : Γ ⊩ A}
                     → (η : Γ′ ∋⋆ Γ) → CV M a
                     → CV (sub ⌊ η ⌋ M) (acc η a)

-- (conglookupCV)
postulate
  getCV : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                    → (i : Ξ ∋ A) → CV⋆ σ ρ
                    → CV (sub σ (` i)) (getᵥ ρ i)

-- (cong↑⟨_⟩CV⋆)
postulate
  accCV⋆ : ∀ {Γ Γ′ Ξ} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                      → (η : Γ′ ∋⋆ Γ) → CV⋆ σ ρ
                      → CV⋆ (η ◑ σ) (η ⬗ ρ)

-- (cong↓⟨_⟩CV⋆)
postulate
  getCV⋆ : ∀ {Γ Ξ Ξ′} → {σ : Γ ⊢⋆ Ξ′} {ρ : Γ ⊩⋆ Ξ′}
                      → (η : Ξ′ ∋⋆ Ξ) → CV⋆ σ ρ
                      → CV⋆ (σ ◐ η) (ρ ⬖ η)


--------------------------------------------------------------------------------


-- Lemma 8.
postulate
  ⟦_⟧CV : ∀ {Γ Ξ A} → {σ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                    → (M : Ξ ⊢ A) → CV⋆ σ ρ
                    → CV (sub σ M) (⟦ M ⟧ ρ)

postulate
  ⟦_⟧CV⋆ : ∀ {Γ Ξ Φ} → {σ₁ : Γ ⊢⋆ Ξ} {ρ : Γ ⊩⋆ Ξ}
                     → (σ₂ : Ξ ⊢⋆ Φ) → CV⋆ σ₁ ρ
                     → CV⋆ (σ₁ ● σ₂) (⟦ σ₂ ⟧⋆ ρ)


--------------------------------------------------------------------------------


-- Lemma 9.
mutual
  postulate
    lem₉ : ∀ {Γ A} → {M : Γ ⊢ A} {a : Γ ⊩ A}
                   → CV M a
                   → M ∼ reify a

  postulate
    aux₄₆₈ : ∀ {A Γ} → {M : Γ ⊢ A} {f : ∀ {Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢ A}
                     → (∀ {Γ′} → (η : Γ′ ∋⋆ Γ) → sub ⌊ η ⌋ M ∼ f η)
                     → CV M (⟪ f ⟫)

postulate
  ⌊_⌋ᶜᵛ : ∀ {Γ Γ′} → (η : Γ′ ∋⋆ Γ)
                   → CV⋆ ⌊ η ⌋ ⌊ η ⌋ᵥ

idᶜᵛ : ∀ {Γ} → CV⋆ ⌊ idᵣ ⌋ (idᵥ {Γ})
idᶜᵛ = ⌊ idᵣ ⌋ᶜᵛ

postulate
  aux₄₆₉ : ∀ {Γ A} → (M : Γ ⊢ A)
                   → sub ⌊ idᵣ ⌋ M ∼ nf M


--------------------------------------------------------------------------------


-- Theorem 2.
postulate
  thm₂ : ∀ {Γ A} → (M : Γ ⊢ A)
                 → M ∼ nf M

-- Theorem 3.
thm₃ : ∀ {Γ A} → (M₁ M₂ : Γ ⊢ A) → Eq (⟦ M₁ ⟧ idᵥ) (⟦ M₂ ⟧ idᵥ)
               → M₁ ∼ M₂
thm₃ M₁ M₂ e =  thm₂ M₁
             ⦙∼ ≡→∼ (cor₁ M₁ M₂ e)
             ⦙∼ thm₂ M₂ ⁻¹∼
