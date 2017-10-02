{-# OPTIONS --no-positivity-check #-}

module CoquandNormalisation where

open import CoquandSubstitution public


record 𝔐 : Set₁ where
  field
    𝒲      : Set

    𝒢      : 𝒲 → Set

    _⊒_    : 𝒲 → 𝒲 → Set

    idₐ    : ∀ {w} → w ⊒ w

    _□_    : ∀ {w w′ w″} → w″ ⊒ w′ → w′ ⊒ w → w″ ⊒ w

    id₁□   : ∀ {w w′} → (ξ : w′ ⊒ w)
                      → idₐ □ ξ ≡ ξ

    id₂□   : ∀ {w w′} → (ξ : w′ ⊒ w)
                      → ξ □ idₐ ≡ ξ

    assoc□ : ∀ {w w′ w″ w‴} → (ξ₁ : w‴ ⊒ w″) (ξ₂ : w″ ⊒ w′) (ξ₃ : w′ ⊒ w)
                            → ξ₁ □ (ξ₂ □ ξ₃) ≡ (ξ₁ □ ξ₂) □ ξ₃


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  infix 3 _⊩_
  data _⊩_ : 𝒲 → 𝒯 → Set
    where
      ⟦G⟧ : ∀ {w} → (h : ∀ {w′} → (ξ : w′ ⊒ w)
                                 → 𝒢 w′)
                  → w ⊩ ⎵

      ⟦ƛ⟧ : ∀ {A B w} → (h : ∀ {w′} → (ξ : w′ ⊒ w) (a : w′ ⊩ A)
                                     → w′ ⊩ B)
                      → w ⊩ A ⊃ B

  ⟦g⟧⟨_⟩ : ∀ {w w′} → w′ ⊒ w → w ⊩ ⎵ → 𝒢 w′
  ⟦g⟧⟨ ξ ⟩ (⟦G⟧ f) = f ξ

  _◎⟨_⟩_ : ∀ {A B w w′} → w ⊩ A ⊃ B → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B
  (⟦ƛ⟧ f) ◎⟨ ξ ⟩ a = f ξ a

  -- ⟦putᵣ⟧ can’t be stated here
  -- ⟦getᵣ⟧ can’t be stated here
  -- ⟦wkᵣ⟧ can’t be stated here
  -- ⟦liftᵣ⟧ can’t be stated here
  -- idₐ = ⟦idᵣ⟧

  -- acc = ⟦ren⟧
  acc : ∀ {A w w′} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
  acc {⎵}     ξ f = ⟦G⟧ (λ ξ′   → ⟦g⟧⟨ ξ′ □ ξ ⟩ f)
  acc {A ⊃ B} ξ f = ⟦ƛ⟧ (λ ξ′ a → f ◎⟨ ξ′ □ ξ ⟩ a)

  -- ⟦wk⟧ can’t be stated here
  -- _□_ = _⟦○⟧_


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  mutual
    data Eq : ∀ {A w} → w ⊩ A → w ⊩ A → Set
      where
        eq⎵ : ∀ {w} → {f f′ : w ⊩ ⎵}
                    → (h : ∀ {w′} → (ξ : w′ ⊒ w)
                                   → ⟦g⟧⟨ ξ ⟩ f ≡ ⟦g⟧⟨ ξ ⟩ f′)
                    → Eq f f′

        eq⊃ : ∀ {A B w} → {f f′ : w ⊩ A ⊃ B}
                        → (h : ∀ {w′} → (ξ : w′ ⊒ w) {a : w′ ⊩ A} (u : Un a)
                                       → Eq (f ◎⟨ ξ ⟩ a) (f′ ◎⟨ ξ ⟩ a))
                        → Eq f f′

    data Un : ∀ {A w} → w ⊩ A → Set
      where
        un⎵ : ∀ {w} → {f : w ⊩ ⎵}
                    → Un f

        un⊃ : ∀ {A B w} → {f : w ⊩ A ⊃ B}
                        → (h₁ : ∀ {w′} → (ξ : w′ ⊒ w) {a : w′ ⊩ A} (u : Un a)
                                        → Un (f ◎⟨ ξ ⟩ a))
                        → (h₂ : ∀ {w′} → (ξ : w′ ⊒ w) {a a′ : w′ ⊩ A} (e : Eq a a′) (u₁ : Un a) (u₂ : Un a′)
                                        → Eq (f ◎⟨ ξ ⟩ a) (f ◎⟨ ξ ⟩ a′))
                        → (h₃ : ∀ {w′ w″} → (ξ₁ : w″ ⊒ w′) (ξ₂ : w′ ⊒ w) {a : w′ ⊩ A} (u : Un a)
                                           → Eq (acc ξ₁ (f ◎⟨ ξ₂ ⟩ a)) (f ◎⟨ ξ₁ □ ξ₂ ⟩ (acc ξ₁ a)))
                        → Un f

  reflEq : ∀ {A w} → {a : w ⊩ A}
                   → Un a
                   → Eq a a
  reflEq un⎵            = eq⎵ (λ ξ   → refl)
  reflEq (un⊃ h₁ h₂ h₃) = eq⊃ (λ ξ u → reflEq (h₁ ξ u))

  symEq : ∀ {A w} → {a a′ : w ⊩ A}
                  → Eq a a′
                  → Eq a′ a
  symEq {⎵}     (eq⎵ h) = eq⎵ (λ ξ   → sym (h ξ))
  symEq {A ⊃ B} (eq⊃ h) = eq⊃ (λ ξ u → symEq (h ξ u))

  transEq : ∀ {A w} → {a a′ a″ : w ⊩ A}
                    → Eq a a′ → Eq a′ a″
                    → Eq a a″
  transEq {⎵}     (eq⎵ h₁) (eq⎵ h₂) = eq⎵ (λ ξ   → trans (h₁ ξ) (h₂ ξ))
  transEq {A ⊃ B} (eq⊃ h₁) (eq⊃ h₂) = eq⊃ (λ ξ u → transEq (h₁ ξ u) (h₂ ξ u))


  ≡→Eq : ∀ {A w} → {a a′ : w ⊩ A} → a ≡ a′ → Un a → Eq a a′
  ≡→Eq refl u = reflEq u

  module Eq-Reasoning where
    infix 1 begin_
    begin_ : ∀ {A w} → {a a′ : w ⊩ A} → Eq a a′ → Eq a a′
    begin e = e

    infixr 2 _Eq⟨⟩_
    _Eq⟨⟩_ : ∀ {A w} → (a {a′} : w ⊩ A) → Eq a a′ → Eq a a′
    a Eq⟨⟩ e = e

    infixr 2 _Eq⟨_⟩_
    _Eq⟨_⟩_ : ∀ {A w} → (a {a′ a″} : w ⊩ A) → Eq a a′ → Eq a′ a″ → Eq a a″
    a Eq⟨ e₁ ⟩ e₂ = transEq e₁ e₂

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {A w} → (a {a′} : w ⊩ A) → Eq a a′ → Eq a a′
    a ≡⟨⟩ e = e

    infixr 2 _≡⟨_∣_⟩_
    _≡⟨_∣_⟩_ : ∀ {A w} → (a {a′ a″} : w ⊩ A) → a ≡ a′ → Un a → Eq a′ a″ → Eq a a″
    a ≡⟨ e₁ ∣ u ⟩ e₂ = transEq (≡→Eq e₁ u) e₂

    infix 3 _∎⟨_⟩
    _∎⟨_⟩ : ∀ {A w} → (a : w ⊩ A) → Un a → Eq a a
    a ∎⟨ u ⟩ = reflEq u


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  -- (cong◎⟨_⟩Eq)
  postulate
    cong◎Eq : ∀ {A B w w′} → {f f′ : w ⊩ A ⊃ B} {a a′ : w′ ⊩ A}
                           → (ξ : w′ ⊒ w) → Eq f f′ → Un f → Un f′ → Eq a a′ → Un a → Un a′
                           → Eq (f ◎⟨ ξ ⟩ a)
                                 (f′ ◎⟨ ξ ⟩ a′)

  cong◎Un : ∀ {A B w w′} → {f : w ⊩ A ⊃ B} {a : w′ ⊩ A}
                         → (ξ : w′ ⊒ w) → Un f → Un a
                         → Un (f ◎⟨ ξ ⟩ a)
  cong◎Un ξ (un⊃ h₁ h₂ h₃) u = h₁ ξ u

  -- (cong↑⟨_⟩Eq)
  postulate
    congaccEq : ∀ {A w w′} → {a a′ : w ⊩ A}
                           → (ξ : w′ ⊒ w) → Eq a a′
                           → Eq (acc ξ a) (acc ξ a′)

  -- (cong↑⟨_⟩𝒰)
  postulate
    congaccUn : ∀ {A w w′} → {a : w ⊩ A}
                           → (ξ : w′ ⊒ w) → Un a
                           → Un (acc ξ a)

  -- (aux₄₁₁)
  postulate
    id₁accEq : ∀ {A w} → {a : w ⊩ A}
                       → Un a
                       → Eq (acc idₐ a) a

  -- (aux₄₁₂)
  postulate
    acc□Eq : ∀ {A w w′ w″} → {a : w ⊩ A}
                           → (ξ₁ : w″ ⊒ w′) (ξ₂ : w′ ⊒ w) → Un a
                           → Eq (acc (ξ₁ □ ξ₂) a)
                                 ((acc ξ₁ ∘ acc ξ₂) a)

  -- (aux₄₁₃)
  postulate
    acc◎idEq : ∀ {A B w w′} → {f : w ⊩ A ⊃ B} {a : w′ ⊩ A}
                            → (ξ : w′ ⊒ w) → Un f → Un a
                            → Eq (acc ξ f ◎⟨ idₐ ⟩ a)
                                  (f ◎⟨ ξ ⟩ a)

  acc◎Eq : ∀ {A B w w′ w″} → {f : w ⊩ A ⊃ B} {a : w′ ⊩ A}
                           → (ξ₁ : w′ ⊒ w) (ξ₂ : w″ ⊒ w′) → Un f → Un a
                           → Eq (acc ξ₁ f ◎⟨ ξ₂ ⟩ acc ξ₂ a)
                                 (acc ξ₂ (f ◎⟨ ξ₁ ⟩ a))
  acc◎Eq ξ₁ ξ₂ (un⊃ h₁ h₂ h₃) u = symEq (h₃ ξ₂ ξ₁ u)


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  infix 3 _⊩⋆_
  data _⊩⋆_ : 𝒲 → 𝒞 → Set
    where
      []    : ∀ {w} →
                w ⊩⋆ []

      [_,_] : ∀ {Ξ A w} →
                (ρ : w ⊩⋆ Ξ) (a : w ⊩ A) →
                w ⊩⋆ [ Ξ , A ]

  -- ⟦putₛ⟧ can’t be stated here

  -- (⟦getₛ⟧ / lookup)
  getₑ : ∀ {Ξ A w} → w ⊩⋆ Ξ → Ξ ∋ A
                   → w ⊩ A
  getₑ [ ρ , a ] zero    = a
  getₑ [ ρ , a ] (suc i) = getₑ ρ i

  -- (⟦unwkₛ⟧)
  unwkₑ : ∀ {Ξ A w} → w ⊩⋆ [ Ξ , A ]
                    → w ⊩⋆ Ξ
  unwkₑ [ ρ , a ] = ρ

  -- ⟦wkₛ⟧ can’t be stated here
  -- ⟦liftₛ⟧ can’t be stated here
  -- ⟦idₛ⟧ can’t be stated here
  -- ⟦sub⟧ can’t be stated here
  -- ⟦cut⟧ can’t be stated here
  -- _■_ can’t be stated here


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  -- (⟦_◑_⟧ / ↑⟨_⟩⊩⋆)
  _◨_ : ∀ {Ξ w w′} → w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  ξ ◨ []        = []
  ξ ◨ [ ρ , a ] = [ ξ ◨ ρ , acc ξ a ]

  -- (⟦_◐_⟧ / ↓⟨_⟩⊩⋆)
  _◧_ : ∀ {Ξ Ξ′ w} → w ⊩⋆ Ξ′ → Ξ′ ∋⋆ Ξ → w ⊩⋆ Ξ
  ρ ◧ []        = []
  ρ ◧ [ η , i ] = [ ρ ◧ η , getₑ ρ i ]


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  zap◧ : ∀ {Ξ Ξ′ A w} → (ρ : w ⊩⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (a : w ⊩ A)
                      → [ ρ , a ] ◧ wkᵣ η ≡ ρ ◧ η
  zap◧ ρ []        a = refl
  zap◧ ρ [ η , i ] a = cong² [_,_] (zap◧ ρ η a) refl

  id₂◧ : ∀ {Ξ w} → (ρ : w ⊩⋆ Ξ)
                 → ρ ◧ idᵣ ≡ ρ
  id₂◧ []        = refl
  id₂◧ [ ρ , a ] = begin
    [ [ ρ , a ] ◧ wkᵣ idᵣ , a ] ≡⟨ cong² [_,_] (zap◧ ρ idᵣ a) refl ⟩
    [ ρ ◧ idᵣ , a ]             ≡⟨ cong² [_,_] (id₂◧ ρ) refl ⟩
    [ ρ , a ] ∎
    where open ≡-Reasoning


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  get◧ : ∀ {Ξ Ξ′ A w} → (ρ : w ⊩⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (i : Ξ ∋ A)
                      → getₑ (ρ ◧ η) i ≡ (getₑ ρ ∘ getᵣ η) i
  get◧ ρ [ η , j ] zero    = refl
  get◧ ρ [ η , j ] (suc i) = get◧ ρ η i

  comp◧○ : ∀ {Ξ Ξ′ Ξ″ w} → (ρ : w ⊩⋆ Ξ″) (η₁ : Ξ″ ∋⋆ Ξ′) (η₂ : Ξ′ ∋⋆ Ξ)
                         → ρ ◧ (η₁ ○ η₂) ≡ (ρ ◧ η₁) ◧ η₂
  comp◧○ σ η₁ []         = refl
  comp◧○ σ η₁ [ η₂ , z ] = cong² [_,_] (comp◧○ σ η₁ η₂) (sym (get◧ σ η₁ z))

  -- wk◧ can’t be stated here
  -- lift◧ can’t be stated here
  -- wkid₂◧ can’t be stated here
  -- liftwkid₂◧ can’t be stated here
  -- sub◧ can’t be stated here
  -- subwk◧ can’t be stated here
  -- sublift◧ can’t be stated here
  -- subliftwk◧ can’t be stated here


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  data Eq⋆ : ∀ {Ξ w} → w ⊩⋆ Ξ → w ⊩⋆ Ξ → Set
    where
      []    : ∀ {w} → Eq⋆ ([] {w}) []

      [_,_] : ∀ {Ξ A w} → {ρ ρ′ : w ⊩⋆ Ξ} {a a′ : w ⊩ A}
                        → (ε : Eq⋆ ρ ρ′) (e : Eq a a′)
                        → Eq⋆ [ ρ , a ] [ ρ′ , a′ ]

  data Un⋆ : ∀ {Ξ w} → w ⊩⋆ Ξ → Set
    where
      []    : ∀ {w} → Un⋆ ([] {w})

      [_,_] : ∀ {Ξ A w} → {ρ : w ⊩⋆ Ξ} {a : w ⊩ A}
                        → (υ : Un⋆ ρ) (u : Un a)
                        → Un⋆ [ ρ , a ]

  reflEq⋆ : ∀ {Ξ w} → {ρ : w ⊩⋆ Ξ}
                    → Un⋆ ρ
                    → Eq⋆ ρ ρ
  reflEq⋆ []        = []
  reflEq⋆ [ υ , u ] = [ reflEq⋆ υ , reflEq u ]

  symEq⋆ : ∀ {Ξ w} → {ρ ρ′ : w ⊩⋆ Ξ}
                   → Eq⋆ ρ ρ′
                   → Eq⋆ ρ′ ρ
  symEq⋆ []        = []
  symEq⋆ [ ε , e ] = [ symEq⋆ ε , symEq e ]

  transEq⋆ : ∀ {Ξ w} → {ρ ρ′ ρ″ : w ⊩⋆ Ξ}
                     → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ″
                     → Eq⋆ ρ ρ″
  transEq⋆ []          []          = []
  transEq⋆ [ ε₁ , e₁ ] [ ε₂ , e₂ ] = [ transEq⋆ ε₁ ε₂ , transEq e₁ e₂ ]

  ≡→Eq⋆ : ∀ {Ξ w} → {ρ ρ′ : w ⊩⋆ Ξ} → ρ ≡ ρ′ → Un⋆ ρ → Eq⋆ ρ ρ′
  ≡→Eq⋆ refl υ = reflEq⋆ υ

  module Eq⋆-Reasoning where
    infix 1 begin_
    begin_ : ∀ {Ξ w} → {ρ ρ′ : w ⊩⋆ Ξ} → Eq⋆ ρ ρ′ → Eq⋆ ρ ρ′
    begin ε = ε

    infixr 2 _Eq⋆⟨⟩_
    _Eq⋆⟨⟩_ : ∀ {Ξ w} → (ρ {ρ′} : w ⊩⋆ Ξ) → Eq⋆ ρ ρ′ → Eq⋆ ρ ρ′
    ρ Eq⋆⟨⟩ ε = ε

    infixr 2 _Eq⋆⟨_⟩_
    _Eq⋆⟨_⟩_ : ∀ {Ξ w} → (ρ {ρ′ ρ″} : w ⊩⋆ Ξ) → Eq⋆ ρ ρ′ → Eq⋆ ρ′ ρ″ → Eq⋆ ρ ρ″
    ρ Eq⋆⟨ ε₁ ⟩ ε₂ = transEq⋆ ε₁ ε₂

    infixr 2 _≡⟨⟩_
    _≡⟨⟩_ : ∀ {Ξ w} → (ρ {ρ′} : w ⊩⋆ Ξ) → Eq⋆ ρ ρ′ → Eq⋆ ρ ρ′
    ρ ≡⟨⟩ ε = ε

    infixr 2 _≡⟨_∣_⟩_
    _≡⟨_∣_⟩_ : ∀ {Ξ w} → (ρ {ρ′ ρ″} : w ⊩⋆ Ξ) → ρ ≡ ρ′ → Un⋆ ρ → Eq⋆ ρ′ ρ″ → Eq⋆ ρ ρ″
    ρ ≡⟨ ε₁ ∣ υ ⟩ ε₂ = transEq⋆ (≡→Eq⋆ ε₁ υ) ε₂

    infix 3 _∎⟨_⟩
    _∎⟨_⟩ : ∀ {Ξ w} → (ρ : w ⊩⋆ Ξ) → Un⋆ ρ → Eq⋆ ρ ρ
    ρ ∎⟨ υ ⟩ = reflEq⋆ υ


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  -- (conglookupEq)
  postulate
    conggetEq : ∀ {Ξ A w} → {ρ ρ′ : w ⊩⋆ Ξ}
                          → (i : Ξ ∋ A) → Eq⋆ ρ ρ′
                          → Eq (getₑ ρ i) (getₑ ρ′ i)

  -- (cong↑⟨_⟩Eq⋆)
  postulate
    cong◨Eq⋆ : ∀ {Ξ w w′} → {ρ ρ′ : w ⊩⋆ Ξ}
                          → (ξ : w′ ⊒ w) → Eq⋆ ρ ρ′
                          → Eq⋆ (ξ ◨ ρ) (ξ ◨ ρ′)

  -- (cong↓⟨_⟩Eq⋆)
  postulate
    cong◧Eq⋆ : ∀ {Ξ Ξ′ w} → {ρ ρ′ : w ⊩⋆ Ξ′}
                          → (η : Ξ′ ∋⋆ Ξ) → Eq⋆ ρ ρ′
                          → Eq⋆ (ρ ◧ η) (ρ′ ◧ η)

  -- (conglookup𝒰)
  postulate
    conggetUn : ∀ {Ξ A w} → {ρ : w ⊩⋆ Ξ}
                          → (i : Ξ ∋ A) → Un⋆ ρ
                          → Un (getₑ ρ i)

  -- (cong↑⟨_⟩𝒰⋆)
  postulate
    cong◨Un⋆ : ∀ {Ξ w w′} → {ρ : w ⊩⋆ Ξ}
                          → (ξ : w′ ⊒ w) → Un⋆ ρ
                          → Un⋆ (ξ ◨ ρ)

  -- (cong↓⟨_⟩𝒰⋆)
  postulate
    cong◧Un⋆ : ∀ {Ξ Ξ′ w} → {ρ : w ⊩⋆ Ξ′}
                          → (η : Ξ′ ∋⋆ Ξ) → Un⋆ ρ
                          → Un⋆ (ρ ◧ η)


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  -- (aux₄₂₁)
  postulate
    get◧Eq : ∀ {Ξ Ξ′ A w} → {ρ : w ⊩⋆ Ξ′}
                          → (η : Ξ′ ∋⋆ Ξ) (i : Ξ′ ∋ A) (j : Ξ ∋ A) → Un⋆ ρ
                          → Eq (getₑ (ρ ◧ η) j)
                                (getₑ ρ i)

  -- (conglookup↑⟨_⟩Eq)
  postulate
    get◨Eq : ∀ {Ξ A w w′} → {ρ : w ⊩⋆ Ξ}
                          → (ξ : w′ ⊒ w) (i : Ξ ∋ A) → Un⋆ ρ
                          → Eq (getₑ (ξ ◨ ρ) i)
                                (acc ξ (getₑ ρ i))

  -- (aux₄₂₃)
  postulate
    zap◧Eq⋆ : ∀ {Ξ Ξ′ A w} → {ρ : w ⊩⋆ Ξ′} {a : w ⊩ A}
                           → (η₁ : [ Ξ′ , A ] ∋⋆ Ξ) (η₂ : Ξ′ ∋⋆ Ξ) → Un⋆ ρ
                           → Eq⋆ ([ ρ , a ] ◧ η₁)
                                  (ρ ◧ η₂)

  -- (aux₄₂₄)
  postulate
    id₂◧Eq⋆ : ∀ {Ξ w} → {ρ : w ⊩⋆ Ξ}
                      → Un⋆ ρ
                      → Eq⋆ (ρ ◧ idᵣ) ρ

  -- (aux₄₂₅)
  postulate
    id₁◨Eq⋆ : ∀ {Ξ w} → {ρ : w ⊩⋆ Ξ}
                      → Un⋆ ρ
                      → Eq⋆ (idₐ ◨ ρ) ρ

  -- (aux₄₂₆)
  postulate
    comp◧○Eq⋆ : ∀ {Ξ Ξ′ Ξ″ w} → {ρ : w ⊩⋆ Ξ″}
                              → (η₁ : Ξ″ ∋⋆ Ξ′) (η₂ : Ξ′ ∋⋆ Ξ) → Un⋆ ρ
                              → Eq⋆ (ρ ◧ (η₁ ○ η₂))
                                     ((ρ ◧ η₁) ◧ η₂)

  -- (aux₄₂₇)
  postulate
    comp◨□Eq⋆ : ∀ {Ξ w w′ w″} → {ρ : w ⊩⋆ Ξ}
                              → (ξ₁ : w″ ⊒ w′) (ξ₂ : w′ ⊒ w) → Un⋆ ρ
                              → Eq⋆ (ξ₁ ◨ (ξ₂ ◨ ρ))
                                     ((ξ₁ □ ξ₂) ◨ ρ)

  -- (aux₄₂₈)
  postulate
    comp◨◧Eq⋆ : ∀ {Ξ Ξ′ w w′} → {ρ : w ⊩⋆ Ξ′}
                              → (ξ : w′ ⊒ w) (η : Ξ′ ∋⋆ Ξ) → Un⋆ ρ
                              → Eq⋆ (ξ ◨ (ρ ◧ η))
                                     ((ξ ◨ ρ) ◧ η)


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  ⟦_⟧ : ∀ {Ξ A w} → Ξ ⊢ A → w ⊩⋆ Ξ → w ⊩ A
  ⟦ ` i ⟧   ρ = getₑ ρ i
  ⟦ ƛ M ⟧   ρ = ⟦ƛ⟧ (λ ξ a → ⟦ M ⟧ [ ξ ◨ ρ , a ])
  ⟦ M ∙ N ⟧ ρ = ⟦ M ⟧ ρ ◎⟨ idₐ ⟩ ⟦ N ⟧ ρ

  ⟦_⟧⋆ : ∀ {Ξ Φ w} → Ξ ⊢⋆ Φ → w ⊩⋆ Ξ → w ⊩⋆ Φ
  ⟦ [] ⟧⋆        ρ = []
  ⟦ [ σ , M ] ⟧⋆ ρ = [ ⟦ σ ⟧⋆ ρ , ⟦ M ⟧ ρ ]


--------------------------------------------------------------------------------


instance
  canon : 𝔐
  canon = record
    { 𝒲      = 𝒞
    ; 𝒢      = _⊢ ⎵
    ; _⊒_    = _∋⋆_
    ; idₐ    = idᵣ
    ; _□_    = _○_
    ; id₁□   = id₁○
    ; id₂□   = id₂○
    ; assoc□ = assoc○
    }


--------------------------------------------------------------------------------


mutual
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {⎵}     f = ⟦g⟧⟨ idᵣ ⟩ f
  reify {A ⊃ B} f = ƛ (reify (f ◎⟨ wkᵣ idᵣ ⟩ ⟪` zero ⟫))

  ⟪_⟫ : ∀ {A Γ} → (∀ {Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢ A) → Γ ⊩ A
  ⟪_⟫ {⎵}     f = ⟦G⟧ (λ η   → f η)
  ⟪_⟫ {A ⊃ B} f = ⟦ƛ⟧ (λ η a → ⟪ (λ η′ → f (η′ ○ η) ∙ reify (acc η′ a)) ⟫)

  ⟪`_⟫ : ∀ {Γ A} → Γ ∋ A → Γ ⊩ A
  ⟪` i ⟫ = ⟪ (λ η → ren η (` i)) ⟫

postulate
  aux₄₄₁ : ∀ {A Γ} → (f f′ : ∀ {Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢ A)
                   → (∀ {Γ′} → (η : Γ′ ∋⋆ Γ) → f η ≡ f′ η)
                   → Eq (⟪ f ⟫) (⟪ f′ ⟫)

postulate
  aux₄₄₂ : ∀ {A Γ Γ′} → (η : Γ′ ∋⋆ Γ) (f : (∀ {Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢ A))
                      → Eq (acc η ⟪ f ⟫) (⟪ (λ η′ → f (η′ ○ η)) ⟫)


--------------------------------------------------------------------------------


-- Theorem 1.
mutual
  postulate
    thm₁ : ∀ {Γ A} → {a a′ : Γ ⊩ A}
                   → Eq a a′
                   → reify a ≡ reify a′

  postulate
    ⟪`_⟫ᵤ : ∀ {Γ A} → (i : Γ ∋ A)
                    → Un (⟪` i ⟫)

  postulate
    aux₄₄₃ : ∀ {A Γ} → (f : ∀ {Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢ A)
                     → Un (⟪ f ⟫)


--------------------------------------------------------------------------------


⌊_⌋ₑ : ∀ {Γ Γ′} → Γ′ ∋⋆ Γ
                → Γ′ ⊩⋆ Γ
⌊ [] ⌋ₑ        = []
⌊ [ η , i ] ⌋ₑ = [ ⌊ η ⌋ₑ , ⟪` i ⟫ ]

idₑ : ∀ {Γ} → Γ ⊩⋆ Γ
idₑ = ⌊ idᵣ ⌋ₑ


nf : ∀ {Γ A} → Γ ⊢ A
             → Γ ⊢ A
nf M = reify (⟦ M ⟧ idₑ)


-- Corollary 1.
postulate
  cor₁ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → Eq (⟦ M ⟧ idₑ) (⟦ M′ ⟧ idₑ)
                 → nf M ≡ nf M′
