module Syntax where

open import Prelude public


-- Types (Ty ; ι ; _⇒_)
infixr 7 _⊃_
data 𝒯 : Set
  where
    ⎵   : 𝒯

    _⊃_ : (A B : 𝒯) → 𝒯


-- Contexts (Con ; ∙ ; _,_)
data 𝒞 : Set
  where
    []    : 𝒞

    [_,_] : (Γ : 𝒞) (A : 𝒯) → 𝒞


-- Variables (_∈_ ; vz ; vs)
infix 4 _∋_
data _∋_ : 𝒞 → 𝒯 → Set
  where
    zero : ∀ {Γ A} → [ Γ , A ] ∋ A

    suc  : ∀ {Γ A B} → (i : Γ ∋ A)
                     → [ Γ , B ] ∋ A


-- Terms (Tm ; var ; lam ; app)
infix 3 _⊢_
data _⊢_ : 𝒞 → 𝒯 → Set
  where
    `   : ∀ {Γ A} → (i : Γ ∋ A)
                  → Γ ⊢ A

    ƛ   : ∀ {Γ A B} → (M : [ Γ , A ] ⊢ B)
                    → Γ ⊢ A ⊃ B

    _∙_ : ∀ {Γ A B} → (M : Γ ⊢ A ⊃ B) (N : Γ ⊢ A)
                    → Γ ⊢ B
