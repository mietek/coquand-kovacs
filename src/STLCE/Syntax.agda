module STLCE.Syntax where

open import Prelude public


--------------------------------------------------------------------------------


-- Types
infix  9 _⩕_
infix  8 _⩖_
infixr 7 _⇒_
data 𝒯 : Set
  where
    ⎵    : 𝒯

    _⇒_ : (A B : 𝒯) → 𝒯

    _⩕_  : (A B : 𝒯) → 𝒯

    ⫪   : 𝒯

    ⫫   : 𝒯

    _⩖_  : (A B : 𝒯) → 𝒯


--------------------------------------------------------------------------------


-- Contexts
data 𝒞 : Set
  where
    ∅   : 𝒞

    _,_ : (Γ : 𝒞) (A : 𝒯) → 𝒞


length : 𝒞 → Nat
length ∅       = zero
length (Γ , x) = suc (length Γ)

lookup : (Γ : 𝒞) (i : Nat) {{_ : True (length Γ >? i)}} → 𝒯
lookup ∅       i       {{()}}
lookup (Γ , A) zero    {{yes}} = A
lookup (Γ , B) (suc i) {{p}}   = lookup Γ i


-- Variables
infix 4 _∋_
data _∋_ : 𝒞 → 𝒯 → Set
  where
    zero : ∀ {Γ A} → Γ , A ∋ A

    suc  : ∀ {Γ A B} → (i : Γ ∋ A)
                     → Γ , B ∋ A


Nat→∋ : ∀ {Γ} → (i : Nat) {{_ : True (length Γ >? i)}}
               → Γ ∋ lookup Γ i
Nat→∋ {Γ = ∅}     i       {{()}}
Nat→∋ {Γ = Γ , A} zero    {{yes}} = zero
Nat→∋ {Γ = Γ , B} (suc i) {{p}}   = suc (Nat→∋ i)

instance
  num∋ : ∀ {Γ A} → Number (Γ ∋ A)
  num∋ {Γ} {A} =
    record
      { Constraint = λ i → Σ (True (length Γ >? i))
                              (λ p → lookup Γ i {{p}} ≡ A)
      ; fromNat    = λ { i {{p , refl}} → Nat→∋ i }
      }


--------------------------------------------------------------------------------


-- Terms
infix 3 _⊢_
data _⊢_ : 𝒞 → 𝒯 → Set
  where
    `     : ∀ {Γ A} → (i : Γ ∋ A)
                    → Γ ⊢ A

    ƛ     : ∀ {Γ A B} → (M : Γ , A ⊢ B)
                      → Γ ⊢ A ⇒ B

    _∙_   : ∀ {Γ A B} → (M : Γ ⊢ A ⇒ B) (N : Γ ⊢ A)
                      → Γ ⊢ B

    _,_   : ∀ {Γ A B} → (M : Γ ⊢ A) (N : Γ ⊢ B)
                      → Γ ⊢ A ⩕ B

    π₁    : ∀ {Γ A B} → (M : Γ ⊢ A ⩕ B)
                      → Γ ⊢ A

    π₂    : ∀ {Γ A B} → (M : Γ ⊢ A ⩕ B)
                      → Γ ⊢ B

    τ     : ∀ {Γ} → Γ ⊢ ⫪

    φ     : ∀ {Γ C} → (M : Γ ⊢ ⫫)
                    → Γ ⊢ C

    ι₁    : ∀ {Γ A B} → (M : Γ ⊢ A)
                      → Γ ⊢ A ⩖ B

    ι₂    : ∀ {Γ A B} → (M : Γ ⊢ B)
                      → Γ ⊢ A ⩖ B

    _⁇_∥_ : ∀ {Γ A B C} → (M : Γ ⊢ A ⩖ B) (N₁ : Γ , A ⊢ C) (N₂ : Γ , B ⊢ C)
                        → Γ ⊢ C


instance
  num⊢ : ∀ {Γ A} → Number (Γ ⊢ A)
  num⊢ {Γ} {A} =
    record
      { Constraint = λ i → Σ (True (length Γ >? i))
                              (λ p → lookup Γ i {{p}} ≡ A)
      ; fromNat    = λ { i {{p , refl}} → ` (Nat→∋ i) }
      }


--------------------------------------------------------------------------------


-- Normal forms
mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : 𝒞 → 𝒯 → Set where
    ƛ     : ∀ {Γ A B} → (M : Γ , A ⊢ⁿᶠ B)
                      → Γ ⊢ⁿᶠ A ⇒ B

    _,_   : ∀ {Γ A B} → (M : Γ ⊢ⁿᶠ A) (N : Γ ⊢ⁿᶠ B)
                      → Γ ⊢ⁿᶠ A ⩕ B

    τ     : ∀ {Γ} → Γ ⊢ⁿᶠ ⫪

    ι₁    : ∀ {Γ A B} → (M : Γ ⊢ⁿᶠ A)
                      → Γ ⊢ⁿᶠ A ⩖ B

    ι₂    : ∀ {Γ A B} → (M : Γ ⊢ⁿᶠ B)
                      → Γ ⊢ⁿᶠ A ⩖ B

    ne    : ∀ {Γ A} → (M : Γ ⊢ⁿᵉ A)
                    → Γ ⊢ⁿᶠ A

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : 𝒞 → 𝒯 → Set where
    `     : ∀ {Γ A} → (i : Γ ∋ A)
                    → Γ ⊢ⁿᵉ A

    _∙_   : ∀ {Γ A B} → (M : Γ ⊢ⁿᵉ A ⇒ B) (N : Γ ⊢ⁿᶠ A)
                      → Γ ⊢ⁿᵉ B

    π₁    : ∀ {Γ A B} → (M : Γ ⊢ⁿᵉ A ⩕ B)
                      → Γ ⊢ⁿᵉ A

    π₂    : ∀ {Γ A B} → (M : Γ ⊢ⁿᵉ A ⩕ B)
                      → Γ ⊢ⁿᵉ B

    φ     : ∀ {Γ C} → (M : Γ ⊢ⁿᵉ ⫫)
                    → Γ ⊢ⁿᵉ C

    _⁇_∥_ : ∀ {Γ A B C} → (M : Γ ⊢ⁿᵉ A ⩖ B)
                           (N₁ : Γ , A ⊢ⁿᶠ C)
                           (N₂ : Γ , B ⊢ⁿᶠ C)
                        → Γ ⊢ⁿᵉ C


instance
  num⊢ⁿᵉ : ∀ {Γ A} → Number (Γ ⊢ⁿᵉ A)
  num⊢ⁿᵉ {Γ} {A} =
    record
      { Constraint = λ i → Σ (True (length Γ >? i))
                              (λ p → lookup Γ i {{p}} ≡ A)
      ; fromNat    = λ { i {{p , refl}} → ` (Nat→∋ i) }
      }


--------------------------------------------------------------------------------
