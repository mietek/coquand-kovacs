module STLC.Syntax where

open import Prelude public


--------------------------------------------------------------------------------


-- Types (Ty ; ι ; _⇒_)
infixr 7 _⇒_
data 𝒯 : Set
  where
    ⎵    : 𝒯

    _⇒_ : (A B : 𝒯) → 𝒯


-- Contexts (Con ; ∙ ; _,_)
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


-- Variables (_∈_ ; vz ; vs)
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


-- Terms (Tm ; var ; lam ; app)
infix 3 _⊢_
data _⊢_ : 𝒞 → 𝒯 → Set
  where
    `   : ∀ {Γ A} → (i : Γ ∋ A)
                  → Γ ⊢ A

    ƛ   : ∀ {Γ A B} → (M : Γ , A ⊢ B)
                    → Γ ⊢ A ⇒ B

    _∙_ : ∀ {Γ A B} → (M : Γ ⊢ A ⇒ B) (N : Γ ⊢ A)
                    → Γ ⊢ B


instance
  num⊢ : ∀ {Γ A} → Number (Γ ⊢ A)
  num⊢ {Γ} {A} =
    record
      { Constraint = λ i → Σ (True (length Γ >? i))
                              (λ p → lookup Γ i {{p}} ≡ A)
      ; fromNat    = λ { i {{p , refl}} → ` (Nat→∋ i) }
      }


--------------------------------------------------------------------------------


-- Normal forms (Nf ; lam ; ne ; Ne ; var ; app)
mutual
  infix 3 _⊢ⁿᶠ_
  data _⊢ⁿᶠ_ : 𝒞 → 𝒯 → Set where
    ƛ   : ∀ {Γ A B} → (M : Γ , A ⊢ⁿᶠ B)
                    → Γ ⊢ⁿᶠ A ⇒ B

    ne  : ∀ {Γ} → (M : Γ ⊢ⁿᵉ ⎵)
                → Γ ⊢ⁿᶠ ⎵

  infix 3 _⊢ⁿᵉ_
  data _⊢ⁿᵉ_ : 𝒞 → 𝒯 → Set where
    `   : ∀ {Γ A} → (i : Γ ∋ A)
                  → Γ ⊢ⁿᵉ A

    _∙_ : ∀ {Γ A B} → (M : Γ ⊢ⁿᵉ A ⇒ B) (N : Γ ⊢ⁿᶠ A)
                    → Γ ⊢ⁿᵉ B


instance
  num⊢ⁿᵉ : ∀ {Γ A} → Number (Γ ⊢ⁿᵉ A)
  num⊢ⁿᵉ {Γ} {A} =
    record
      { Constraint = λ i → Σ (True (length Γ >? i))
                              (λ p → lookup Γ i {{p}} ≡ A)
      ; fromNat    = λ { i {{p , refl}} → ` (Nat→∋ i) }
      }


--------------------------------------------------------------------------------
