{-# OPTIONS --no-positivity-check #-}

module STLC.Coquand.Normalisation where

open import STLC.Coquand.Substitution public


--------------------------------------------------------------------------------


record 𝔐 : Set₁ where
  field
    𝒲      : Set

    𝒢      : 𝒲 → Set

    _⊒_    : 𝒲 → 𝒲 → Set

    idₐ    : ∀ {w} → w ⊒ w

    _◇_    : ∀ {w w′ w″} → w″ ⊒ w′ → w′ ⊒ w → w″ ⊒ w

    lid◇   : ∀ {w w′} → (ξ : w′ ⊒ w)
                      → idₐ ◇ ξ ≡ ξ

    rid◇   : ∀ {w w′} → (ξ : w′ ⊒ w)
                      → ξ ◇ idₐ ≡ ξ

    assoc◇ : ∀ {w w′ w″ w‴} → (ξ₁ : w‴ ⊒ w″) (ξ₂ : w″ ⊒ w′) (ξ₃ : w′ ⊒ w)
                            → ξ₁ ◇ (ξ₂ ◇ ξ₃) ≡ (ξ₁ ◇ ξ₂) ◇ ξ₃


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
                      → w ⊩ A ⇒ B


  ⟦g⟧⟨_⟩ : ∀ {w w′} → w′ ⊒ w → w ⊩ ⎵ → 𝒢 w′
  ⟦g⟧⟨ ξ ⟩ (⟦G⟧ f) = f ξ

  _⟦∙⟧⟨_⟩_ : ∀ {A B w w′} → w ⊩ A ⇒ B → w′ ⊒ w → w′ ⊩ A → w′ ⊩ B
  (⟦ƛ⟧ f) ⟦∙⟧⟨ ξ ⟩ a = f ξ a

  -- ⟦putᵣ⟧ can’t be stated here
  -- ⟦getᵣ⟧ can’t be stated here
  -- ⟦wkᵣ⟧ can’t be stated here
  -- ⟦liftᵣ⟧ can’t be stated here
  -- idₐ = ⟦idᵣ⟧

  -- acc = ⟦ren⟧
  acc : ∀ {A w w′} → w′ ⊒ w → w ⊩ A → w′ ⊩ A
  acc {⎵}      ξ f = ⟦G⟧ (λ ξ′   → ⟦g⟧⟨ ξ′ ◇ ξ ⟩ f)
  acc {A ⇒ B} ξ f = ⟦ƛ⟧ (λ ξ′ a → f ⟦∙⟧⟨ ξ′ ◇ ξ ⟩ a)

  -- ⟦wk⟧ can’t be stated here
  -- _◇_ = _⟦○⟧_


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪


  mutual
    data Eq : ∀ {A w} → w ⊩ A → w ⊩ A → Set
      where
        eq⎵ : ∀ {w} → {f₁ f₂ : w ⊩ ⎵}
                    → (h : ∀ {w′} → (ξ : w′ ⊒ w)
                                   → ⟦g⟧⟨ ξ ⟩ f₁ ≡ ⟦g⟧⟨ ξ ⟩ f₂)
                    → Eq f₁ f₂

        eq⊃ : ∀ {A B w} → {f₁ f₂ : w ⊩ A ⇒ B}
                        → (h : ∀ {w′} → (ξ : w′ ⊒ w) {a : w′ ⊩ A} (u : Un a)
                                       → Eq (f₁ ⟦∙⟧⟨ ξ ⟩ a) (f₂ ⟦∙⟧⟨ ξ ⟩ a))
                        → Eq f₁ f₂

    data Un : ∀ {A w} → w ⊩ A → Set
      where
        un⎵ : ∀ {w} → {f : w ⊩ ⎵}
                    → Un f

        un⊃ : ∀ {A B w} → {f : w ⊩ A ⇒ B}
                        → (h₁ : ∀ {w′} → (ξ : w′ ⊒ w)
                                           {a : w′ ⊩ A}
                                           (u : Un a)
                                        → Un (f ⟦∙⟧⟨ ξ ⟩ a))
                        → (h₂ : ∀ {w′} → (ξ : w′ ⊒ w)
                                           {a₁ a₂ : w′ ⊩ A}
                                           (p : Eq a₁ a₂)
                                           (u₁ : Un a₁)
                                           (u₂ : Un a₂)
                                        → Eq (f ⟦∙⟧⟨ ξ ⟩ a₁) (f ⟦∙⟧⟨ ξ ⟩ a₂))
                        → (h₃ : ∀ {w′ w″} → (ξ₁ : w″ ⊒ w′)
                                              (ξ₂ : w′ ⊒ w)
                                              {a : w′ ⊩ A}
                                              (u : Un a)
                                           → Eq (acc ξ₁ (f ⟦∙⟧⟨ ξ₂ ⟩ a))
                                                 (f ⟦∙⟧⟨ ξ₁ ◇ ξ₂ ⟩ (acc ξ₁ a)))
                        → Un f


  reflEq : ∀ {A w} → {a : w ⊩ A}
                   → Un a
                   → Eq a a
  reflEq un⎵            = eq⎵ (λ ξ → refl)
  reflEq (un⊃ h₁ h₂ h₃) = eq⊃ (λ ξ u → reflEq (h₁ ξ u))

  _⁻¹Eq : ∀ {A w} → {a₁ a₂ : w ⊩ A}
                  → Eq a₁ a₂
                  → Eq a₂ a₁
  _⁻¹Eq {⎵}      (eq⎵ h) = eq⎵ (λ ξ → h ξ ⁻¹)
  _⁻¹Eq {A ⇒ B} (eq⊃ h) = eq⊃ (λ ξ u → h ξ u ⁻¹Eq)

  _⦙Eq_ : ∀ {A w} → {a₁ a₂ a₃ : w ⊩ A}
                  → Eq a₁ a₂ → Eq a₂ a₃
                  → Eq a₁ a₃
  _⦙Eq_ {⎵}      (eq⎵ h₁) (eq⎵ h₂) = eq⎵ (λ ξ → h₁ ξ ⦙ h₂ ξ)
  _⦙Eq_ {A ⇒ B} (eq⊃ h₁) (eq⊃ h₂) = eq⊃ (λ ξ u → h₁ ξ u ⦙Eq h₂ ξ u)


  instance
    perEq : ∀ {A w} → PER (w ⊩ A) Eq
    perEq =
      record
        { _⁻¹ = _⁻¹Eq
        ; _⦙_ = _⦙Eq_
        }


  ≡→Eq : ∀ {A w} → {a₁ a₂ : w ⊩ A} → a₁ ≡ a₂ → Un a₁ → Eq a₁ a₂
  ≡→Eq refl u = reflEq u


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  -- (cong⟦∙⟧⟨_⟩Eq)
  postulate
    cong⟦∙⟧Eq : ∀ {A B w w′} → {f₁ f₂ : w ⊩ A ⇒ B} {a₁ a₂ : w′ ⊩ A}
                             → (ξ : w′ ⊒ w)
                             → Eq f₁ f₂ → Un f₁ → Un f₂
                             → Eq a₁ a₂ → Un a₁ → Un a₂
                             → Eq (f₁ ⟦∙⟧⟨ ξ ⟩ a₁)
                                   (f₂ ⟦∙⟧⟨ ξ ⟩ a₂)

  cong⟦∙⟧Un : ∀ {A B w w′} → {f : w ⊩ A ⇒ B} {a : w′ ⊩ A}
                           → (ξ : w′ ⊒ w) → Un f → Un a
                           → Un (f ⟦∙⟧⟨ ξ ⟩ a)
  cong⟦∙⟧Un ξ (un⊃ h₁ h₂ h₃) u = h₁ ξ u

  -- (cong↑⟨_⟩Eq)
  postulate
    congaccEq : ∀ {A w w′} → {a₁ a₂ : w ⊩ A}
                           → (ξ : w′ ⊒ w) → Eq a₁ a₂
                           → Eq (acc ξ a₁) (acc ξ a₂)

  -- (cong↑⟨_⟩𝒰)
  postulate
    congaccUn : ∀ {A w w′} → {a : w ⊩ A}
                           → (ξ : w′ ⊒ w) → Un a
                           → Un (acc ξ a)

  -- (aux₄₁₁)
  postulate
    lidaccEq : ∀ {A w} → {a : w ⊩ A}
                       → Un a
                       → Eq (acc idₐ a) a

  -- (aux₄₁₂)
  postulate
    acc◇Eq : ∀ {A w w′ w″} → {a : w ⊩ A}
                           → (ξ₁ : w″ ⊒ w′) (ξ₂ : w′ ⊒ w) → Un a
                           → Eq (acc (ξ₁ ◇ ξ₂) a)
                                 ((acc ξ₁ ∘ acc ξ₂) a)

  -- (aux₄₁₃)
  postulate
    acc⟦∙⟧idEq : ∀ {A B w w′} → {f : w ⊩ A ⇒ B} {a : w′ ⊩ A}
                              → (ξ : w′ ⊒ w) → Un f → Un a
                              → Eq (acc ξ f ⟦∙⟧⟨ idₐ ⟩ a)
                                    (f ⟦∙⟧⟨ ξ ⟩ a)

  acc⟦∙⟧Eq : ∀ {A B w w′ w″} → {f : w ⊩ A ⇒ B} {a : w′ ⊩ A}
                             → (ξ₁ : w′ ⊒ w) (ξ₂ : w″ ⊒ w′) → Un f → Un a
                             → Eq (acc ξ₁ f ⟦∙⟧⟨ ξ₂ ⟩ acc ξ₂ a)
                                   (acc ξ₂ (f ⟦∙⟧⟨ ξ₁ ⟩ a))
  acc⟦∙⟧Eq ξ₁ ξ₂ (un⊃ h₁ h₂ h₃) u = h₃ ξ₂ ξ₁ u ⁻¹


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪


  infix 3 _⊩⋆_
  data _⊩⋆_ : 𝒲 → 𝒞 → Set
    where
      ∅   : ∀ {w} → w ⊩⋆ ∅

      _,_ : ∀ {Ξ A w} → (ρ : w ⊩⋆ Ξ) (a : w ⊩ A) →
                         w ⊩⋆ Ξ , A


  -- ⟦putₛ⟧ can’t be stated here

  -- getᵥ = ⟦getₛ⟧ (lookup)
  getᵥ : ∀ {Ξ A w} → w ⊩⋆ Ξ → Ξ ∋ A → w ⊩ A
  getᵥ (ρ , a) zero    = a
  getᵥ (ρ , a) (suc i) = getᵥ ρ i

  -- unwkᵥ ≡ ⟦unwkₛ⟧
  unwkᵥ : ∀ {Ξ A w} → w ⊩⋆ Ξ , A → w ⊩⋆ Ξ
  unwkᵥ (ρ , a) = ρ

  -- ⟦wkₛ⟧ can’t be stated here
  -- ⟦liftₛ⟧ can’t be stated here
  -- ⟦idₛ⟧ can’t be stated here
  -- ⟦sub⟧ can’t be stated here
  -- ⟦cut⟧ can’t be stated here
  -- _◆_ can’t be stated here


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  -- (⟦_◑_⟧ / ↑⟨_⟩⊩⋆)
  _⬗_ : ∀ {Ξ w w′} → w′ ⊒ w → w ⊩⋆ Ξ → w′ ⊩⋆ Ξ
  ξ ⬗ ∅       = ∅
  ξ ⬗ (ρ , a) = ξ ⬗ ρ , acc ξ a

  -- (⟦_◐_⟧ / ↓⟨_⟩⊩⋆)
  _⬖_ : ∀ {Ξ Ξ′ w} → w ⊩⋆ Ξ′ → Ξ′ ∋⋆ Ξ → w ⊩⋆ Ξ
  ρ ⬖ ∅       = ∅
  ρ ⬖ (η , i) = ρ ⬖ η , getᵥ ρ i


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  zap⬖ : ∀ {Ξ Ξ′ A w} → (ρ : w ⊩⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (a : w ⊩ A)
                      → (ρ , a) ⬖ wkᵣ η ≡ ρ ⬖ η
  zap⬖ ρ ∅       a = refl
  zap⬖ ρ (η , i) a = (_, getᵥ ρ i) & zap⬖ ρ η a

  rid⬖ : ∀ {Ξ w} → (ρ : w ⊩⋆ Ξ)
                 → ρ ⬖ idᵣ ≡ ρ
  rid⬖ ∅       = refl
  rid⬖ (ρ , a) = (_, a) & ( zap⬖ ρ idᵣ a
                          ⦙ rid⬖ ρ
                          )


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  get⬖ : ∀ {Ξ Ξ′ A w} → (ρ : w ⊩⋆ Ξ′) (η : Ξ′ ∋⋆ Ξ) (i : Ξ ∋ A)
                      → getᵥ (ρ ⬖ η) i ≡ (getᵥ ρ ∘ getᵣ η) i
  get⬖ ρ (η , j) zero    = refl
  get⬖ ρ (η , j) (suc i) = get⬖ ρ η i

  comp⬖○ : ∀ {Ξ Ξ′ Ξ″ w} → (ρ : w ⊩⋆ Ξ″) (η₁ : Ξ″ ∋⋆ Ξ′) (η₂ : Ξ′ ∋⋆ Ξ)
                         → ρ ⬖ (η₁ ○ η₂) ≡ (ρ ⬖ η₁) ⬖ η₂
  comp⬖○ σ η₁ ∅        = refl
  comp⬖○ σ η₁ (η₂ , i) = _,_ & comp⬖○ σ η₁ η₂
                             ⊗ (get⬖ σ η₁ i ⁻¹)

  -- wk⬖ can’t be stated here
  -- lift⬖ can’t be stated here
  -- wkrid⬖ can’t be stated here
  -- liftwkrid⬖ can’t be stated here
  -- sub⬖ can’t be stated here
  -- subwk⬖ can’t be stated here
  -- sublift⬖ can’t be stated here
  -- subliftwk⬖ can’t be stated here


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪


  data Eq⋆ : ∀ {Ξ w} → w ⊩⋆ Ξ → w ⊩⋆ Ξ → Set
    where
      ∅   : ∀ {w} → Eq⋆ (∅ {w}) ∅

      _,_ : ∀ {Ξ A w} → {ρ₁ ρ₂ : w ⊩⋆ Ξ} {a₁ a₂ : w ⊩ A}
                      → (χ : Eq⋆ ρ₁ ρ₂) (p : Eq a₁ a₂)
                      → Eq⋆ (ρ₁ , a₁) (ρ₂ , a₂)

  data Un⋆ : ∀ {Ξ w} → w ⊩⋆ Ξ → Set
    where
      ∅   : ∀ {w} → Un⋆ (∅ {w})

      _,_ : ∀ {Ξ A w} → {ρ : w ⊩⋆ Ξ} {a : w ⊩ A}
                      → (υ : Un⋆ ρ) (u : Un a)
                      → Un⋆ (ρ , a)


  reflEq⋆ : ∀ {Ξ w} → {ρ : w ⊩⋆ Ξ}
                    → Un⋆ ρ
                    → Eq⋆ ρ ρ
  reflEq⋆ ∅       = ∅
  reflEq⋆ (υ , u) = reflEq⋆ υ , reflEq u

  _⁻¹Eq⋆ : ∀ {Ξ w} → {ρ₁ ρ₂ : w ⊩⋆ Ξ}
                   → Eq⋆ ρ₁ ρ₂
                   → Eq⋆ ρ₂ ρ₁
  ∅       ⁻¹Eq⋆ = ∅
  (χ , p) ⁻¹Eq⋆ = χ ⁻¹Eq⋆ , p ⁻¹Eq

  _⦙Eq⋆_ : ∀ {Ξ w} → {ρ₁ ρ₂ ρ₃ : w ⊩⋆ Ξ}
                   → Eq⋆ ρ₁ ρ₂ → Eq⋆ ρ₂ ρ₃
                   → Eq⋆ ρ₁ ρ₃
  ∅        ⦙Eq⋆ ∅        = ∅
  (χ₁ , p) ⦙Eq⋆ (χ₂ , q) = χ₁ ⦙Eq⋆ χ₂ , p ⦙Eq q


  instance
    perEq⋆ : ∀ {Ξ w} → PER (w ⊩⋆ Ξ) Eq⋆
    perEq⋆ =
      record
        { _⁻¹ = _⁻¹Eq⋆
        ; _⦙_ = _⦙Eq⋆_
        }


  ≡→Eq⋆ : ∀ {Ξ w} → {ρ₁ ρ₂ : w ⊩⋆ Ξ} → ρ₁ ≡ ρ₂ → Un⋆ ρ₁ → Eq⋆ ρ₁ ρ₂
  ≡→Eq⋆ refl υ = reflEq⋆ υ


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  -- (conglookupEq)
  postulate
    conggetEq : ∀ {Ξ A w} → {ρ₁ ρ₂ : w ⊩⋆ Ξ}
                          → (i : Ξ ∋ A) → Eq⋆ ρ₁ ρ₂
                          → Eq (getᵥ ρ₁ i) (getᵥ ρ₂ i)

  -- (cong↑⟨_⟩Eq⋆)
  postulate
    cong⬗Eq⋆ : ∀ {Ξ w w′} → {ρ₁ ρ₂ : w ⊩⋆ Ξ}
                          → (ξ : w′ ⊒ w) → Eq⋆ ρ₁ ρ₂
                          → Eq⋆ (ξ ⬗ ρ₁) (ξ ⬗ ρ₂)

  -- (cong↓⟨_⟩Eq⋆)
  postulate
    cong⬖Eq⋆ : ∀ {Ξ Ξ′ w} → {ρ₁ ρ₂ : w ⊩⋆ Ξ′}
                          → Eq⋆ ρ₁ ρ₂ → (η : Ξ′ ∋⋆ Ξ)
                          → Eq⋆ (ρ₁ ⬖ η) (ρ₂ ⬖ η)

  -- (conglookup𝒰)
  postulate
    conggetUn : ∀ {Ξ A w} → {ρ : w ⊩⋆ Ξ}
                          → (i : Ξ ∋ A) → Un⋆ ρ
                          → Un (getᵥ ρ i)

  -- (cong↑⟨_⟩𝒰⋆)
  postulate
    cong⬗Un⋆ : ∀ {Ξ w w′} → {ρ : w ⊩⋆ Ξ}
                          → (ξ : w′ ⊒ w) → Un⋆ ρ
                          → Un⋆ (ξ ⬗ ρ)

  -- (cong↓⟨_⟩𝒰⋆)
  postulate
    cong⬖Un⋆ : ∀ {Ξ Ξ′ w} → {ρ : w ⊩⋆ Ξ′}
                          → (η : Ξ′ ∋⋆ Ξ) → Un⋆ ρ
                          → Un⋆ (ρ ⬖ η)


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  -- (aux₄₂₁)
  postulate
    get⬖Eq : ∀ {Ξ Ξ′ A w} → {ρ : w ⊩⋆ Ξ′}
                          → (η : Ξ′ ∋⋆ Ξ) (i : Ξ′ ∋ A) (j : Ξ ∋ A) → Un⋆ ρ
                          → Eq (getᵥ (ρ ⬖ η) j)
                                (getᵥ ρ i)

  -- (conglookup↑⟨_⟩Eq)
  postulate
    get⬗Eq : ∀ {Ξ A w w′} → {ρ : w ⊩⋆ Ξ}
                          → (ξ : w′ ⊒ w) (i : Ξ ∋ A) → Un⋆ ρ
                          → Eq (getᵥ (ξ ⬗ ρ) i)
                                (acc ξ (getᵥ ρ i))

  -- (aux₄₂₃)
  postulate
    zap⬖Eq⋆ : ∀ {Ξ Ξ′ A w} → {ρ : w ⊩⋆ Ξ′} {a : w ⊩ A}
                           → (η₁ : Ξ′ , A ∋⋆ Ξ) (η₂ : Ξ′ ∋⋆ Ξ) → Un⋆ ρ
                           → Eq⋆ ((ρ , a) ⬖ η₁)
                                  (ρ ⬖ η₂)

  -- (aux₄₂₄)
  postulate
    rid⬖Eq⋆ : ∀ {Ξ w} → {ρ : w ⊩⋆ Ξ}
                      → Un⋆ ρ
                      → Eq⋆ (ρ ⬖ idᵣ) ρ

  -- (aux₄₂₅)
  postulate
    lid⬗Eq⋆ : ∀ {Ξ w} → {ρ : w ⊩⋆ Ξ}
                      → Un⋆ ρ
                      → Eq⋆ (idₐ ⬗ ρ) ρ

  -- (aux₄₂₆)
  postulate
    comp⬖○Eq⋆ : ∀ {Ξ Ξ′ Ξ″ w} → {ρ : w ⊩⋆ Ξ″}
                              → (η₁ : Ξ″ ∋⋆ Ξ′) (η₂ : Ξ′ ∋⋆ Ξ) → Un⋆ ρ
                              → Eq⋆ (ρ ⬖ (η₁ ○ η₂))
                                     ((ρ ⬖ η₁) ⬖ η₂)

  -- (aux₄₂₇)
  postulate
    comp⬗◇Eq⋆ : ∀ {Ξ w w′ w″} → {ρ : w ⊩⋆ Ξ}
                              → (ξ₁ : w″ ⊒ w′) (ξ₂ : w′ ⊒ w) → Un⋆ ρ
                              → Eq⋆ (ξ₁ ⬗ (ξ₂ ⬗ ρ))
                                     ((ξ₁ ◇ ξ₂) ⬗ ρ)

  -- (aux₄₂₈)
  postulate
    comp⬗⬖Eq⋆ : ∀ {Ξ Ξ′ w w′} → {ρ : w ⊩⋆ Ξ′}
                              → (ξ : w′ ⊒ w) (η : Ξ′ ∋⋆ Ξ) → Un⋆ ρ
                              → Eq⋆ (ξ ⬗ (ρ ⬖ η))
                                     ((ξ ⬗ ρ) ⬖ η)


--------------------------------------------------------------------------------


module _ {{𝔪 : 𝔐}} where
  open 𝔐 𝔪

  ⟦_⟧ : ∀ {Ξ A w} → Ξ ⊢ A → w ⊩⋆ Ξ → w ⊩ A
  ⟦ ` i ⟧   ρ = getᵥ ρ i
  ⟦ ƛ M ⟧   ρ = ⟦ƛ⟧ (λ ξ a → ⟦ M ⟧ (ξ ⬗ ρ , a))
  ⟦ M ∙ N ⟧ ρ = ⟦ M ⟧ ρ ⟦∙⟧⟨ idₐ ⟩ ⟦ N ⟧ ρ

  ⟦_⟧⋆ : ∀ {Ξ Φ w} → Ξ ⊢⋆ Φ → w ⊩⋆ Ξ → w ⊩⋆ Φ
  ⟦ ∅ ⟧⋆     ρ = ∅
  ⟦ σ , M ⟧⋆ ρ = ⟦ σ ⟧⋆ ρ , ⟦ M ⟧ ρ


--------------------------------------------------------------------------------


instance
  canon : 𝔐
  canon = record
    { 𝒲      = 𝒞
    ; 𝒢      = _⊢ ⎵
    ; _⊒_    = _∋⋆_
    ; idₐ    = idᵣ
    ; _◇_    = _○_
    ; lid◇   = lid○
    ; rid◇   = rid○
    ; assoc◇ = assoc○
    }


mutual
  reify : ∀ {A Γ} → Γ ⊩ A → Γ ⊢ A
  reify {⎵}      f = ⟦g⟧⟨ idᵣ ⟩ f
  reify {A ⇒ B} f = ƛ (reify (f ⟦∙⟧⟨ wkᵣ idᵣ ⟩ ⟪` zero ⟫))

  ⟪_⟫ : ∀ {A Γ} → (∀ {Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢ A) → Γ ⊩ A
  ⟪_⟫ {⎵}      f = ⟦G⟧ (λ η   → f η)
  ⟪_⟫ {A ⇒ B} f = ⟦ƛ⟧ (λ η a → ⟪ (λ η′ → f (η′ ○ η) ∙ reify (acc η′ a)) ⟫)

  ⟪`_⟫ : ∀ {Γ A} → Γ ∋ A → Γ ⊩ A
  ⟪` i ⟫ = ⟪ (λ η → ren η (` i)) ⟫

postulate
  aux₄₄₁ : ∀ {A Γ} → (f₁ f₂ : ∀ {Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢ A)
                   → (∀ {Γ′} → (η : Γ′ ∋⋆ Γ) → f₁ η ≡ f₂ η)
                   → Eq (⟪ f₁ ⟫) (⟪ f₂ ⟫)

postulate
  aux₄₄₂ : ∀ {A Γ Γ′} → (η : Γ′ ∋⋆ Γ) (f : (∀ {Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢ A))
                      → Eq (acc η ⟪ f ⟫) (⟪ (λ η′ → f (η′ ○ η)) ⟫)


--------------------------------------------------------------------------------


-- Theorem 1.
mutual
  postulate
    thm₁ : ∀ {Γ A} → {a₁ a₂ : Γ ⊩ A}
                   → Eq a₁ a₂
                   → reify a₁ ≡ reify a₂

  postulate
    ⟪`_⟫ᵤ : ∀ {Γ A} → (i : Γ ∋ A)
                    → Un (⟪` i ⟫)

  postulate
    aux₄₄₃ : ∀ {A Γ} → (f : ∀ {Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊢ A)
                     → Un (⟪ f ⟫)


--------------------------------------------------------------------------------


⌊_⌋ᵥ : ∀ {Γ Γ′} → Γ′ ∋⋆ Γ → Γ′ ⊩⋆ Γ
⌊ ∅ ⌋ᵥ     = ∅
⌊ η , i ⌋ᵥ = ⌊ η ⌋ᵥ , ⟪` i ⟫

idᵥ : ∀ {Γ} → Γ ⊩⋆ Γ
idᵥ = ⌊ idᵣ ⌋ᵥ


nf : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
nf M = reify (⟦ M ⟧ idᵥ)


-- Corollary 1.
postulate
  cor₁ : ∀ {Γ A} → (M₁ M₂ : Γ ⊢ A) → Eq (⟦ M₁ ⟧ idᵥ) (⟦ M₂ ⟧ idᵥ)
                 → nf M₁ ≡ nf M₂


--------------------------------------------------------------------------------
