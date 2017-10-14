module STLC.Kovacs.Substitution where

open import STLC.Kovacs.Embedding public
open import Category


--------------------------------------------------------------------------------


-- Substitutions (Sub ; ∙ ; _,_)
infix 3 _⊢⋆_
data _⊢⋆_ : 𝒞 → 𝒞 → Set
  where
    ∅   : ∀ {Γ} → Γ ⊢⋆ ∅

    _,_ : ∀ {Γ Ξ A} → (σ : Γ ⊢⋆ Ξ) (M : Γ ⊢ A)
                    → Γ ⊢⋆ Ξ , A


-- (_ₛ∘ₑ_)
-- NOTE: _◐_ = ren⋆
_◐_ : ∀ {Γ Γ′ Ξ} → Γ ⊢⋆ Ξ → Γ′ ⊇ Γ → Γ′ ⊢⋆ Ξ
∅       ◐ η = ∅
(σ , M) ◐ η = σ ◐ η , ren η M

-- (_ₑ∘ₛ_)
_◑_ : ∀ {Γ Ξ Ξ′} → Ξ′ ⊇ Ξ → Γ ⊢⋆ Ξ′ → Γ ⊢⋆ Ξ
done    ◑ σ       = σ
wkₑ η   ◑ (σ , M) = η ◑ σ
liftₑ η ◑ (σ , M) = η ◑ σ , M


--------------------------------------------------------------------------------


-- (dropₛ)
wkₛ : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ → Γ , A ⊢⋆ Ξ
wkₛ σ = σ ◐ wkₑ idₑ

-- (keepₛ)
liftₛ : ∀ {A Γ Ξ} → Γ ⊢⋆ Ξ → Γ , A ⊢⋆ Ξ , A
liftₛ σ = wkₛ σ , 0

-- (⌜_⌝ᵒᵖᵉ)
⌊_⌋ : ∀ {Γ Γ′} → Γ′ ⊇ Γ → Γ′ ⊢⋆ Γ
⌊ done ⌋    = ∅
⌊ wkₑ η ⌋   = wkₛ ⌊ η ⌋
⌊ liftₑ η ⌋ = liftₛ ⌊ η ⌋

-- (∈ₛ)
getₛ : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ∋ A → Γ ⊢ A
getₛ (σ , M) zero    = M
getₛ (σ , M) (suc i) = getₛ σ i

-- (Tmₛ)
sub : ∀ {Γ Ξ A} → Γ ⊢⋆ Ξ → Ξ ⊢ A → Γ ⊢ A
sub σ (𝓋 i)   = getₛ σ i
sub σ (ƛ M)   = ƛ (sub (liftₛ σ) M)
sub σ (M ∙ N) = sub σ M ∙ sub σ N

-- (idₛ)
idₛ : ∀ {Γ} → Γ ⊢⋆ Γ
idₛ {∅}     = ∅
idₛ {Γ , A} = liftₛ idₛ

cut : ∀ {Γ A B} → Γ ⊢ A → Γ , A ⊢ B → Γ ⊢ B
cut M N = sub (idₛ , M) N

-- (_∘ₛ_)
-- NOTE: _●_ = sub⋆
_●_ : ∀ {Γ Ξ Φ} → Ξ ⊢⋆ Φ → Γ ⊢⋆ Ξ → Γ ⊢⋆ Φ
∅        ● σ₁ = ∅
(σ₂ , M) ● σ₁ = σ₂ ● σ₁ , sub σ₁ M


--------------------------------------------------------------------------------


-- (assₛₑₑ)
comp◐○ : ∀ {Γ Γ′ Γ″ Ξ} → (η₁ : Γ″ ⊇ Γ′) (η₂ : Γ′ ⊇ Γ) (σ : Γ ⊢⋆ Ξ)
                       → (σ ◐ η₂) ◐ η₁ ≡ σ ◐ (η₂ ○ η₁)
comp◐○ η₁ η₂ ∅       = refl
comp◐○ η₁ η₂ (σ , M) = _,_ & comp◐○ η₁ η₂ σ
                           ⊗ (ren○ η₁ η₂ M ⁻¹)

-- (assₑₛₑ)
comp◑◐ : ∀ {Γ Γ′ Ξ Ξ′} → (η₁ : Γ′ ⊇ Γ) (σ : Γ ⊢⋆ Ξ′) (η₂ : Ξ′ ⊇ Ξ)
                       → (η₂ ◑ σ) ◐ η₁ ≡ η₂ ◑ (σ ◐ η₁)
comp◑◐ η₁ ∅       done       = refl
comp◑◐ η₁ (σ , M) (wkₑ η₂)   = comp◑◐ η₁ σ η₂
comp◑◐ η₁ (σ , M) (liftₑ η₂) = (_, ren η₁ M) & comp◑◐ η₁ σ η₂


--------------------------------------------------------------------------------


-- (idlₑₛ)
lid◑ : ∀ {Γ Ξ} → (σ : Γ ⊢⋆ Ξ)
               → idₑ ◑ σ ≡ σ
lid◑ ∅       = refl
lid◑ (σ , M) = (_, M) & lid◑ σ

-- (idlₛₑ)
lid◐ : ∀ {Γ Γ′} → (η : Γ′ ⊇ Γ)
                → idₛ ◐ η ≡ ⌊ η ⌋
lid◐ done      = refl
lid◐ (wkₑ η)   = ((idₛ ◐_) ∘ wkₑ) & rid○ η ⁻¹
               ⦙ comp◐○ (wkₑ idₑ) η idₛ ⁻¹
               ⦙ wkₛ & lid◐ η
lid◐ (liftₑ η) = (_, 0) & ( comp◐○ (liftₑ η) (wkₑ idₑ) idₛ
                          ⦙ ((idₛ ◐_) ∘ wkₑ) & ( lid○ η
                                               ⦙ rid○ η ⁻¹
                                               )
                          ⦙ comp◐○ (wkₑ idₑ) η idₛ ⁻¹
                          ⦙ (_◐ wkₑ idₑ) & lid◐ η
                          )

-- (idrₑₛ)
rid◑ : ∀ {Γ Γ′} → (η : Γ′ ⊇ Γ)
                → η ◑ idₛ ≡ ⌊ η ⌋
rid◑ done      = refl
rid◑ (wkₑ η)   = comp◑◐ (wkₑ idₑ) idₛ η ⁻¹
               ⦙ wkₛ & rid◑ η
rid◑ (liftₑ η) = (_, 0) & ( comp◑◐ (wkₑ idₑ) idₛ η ⁻¹
                          ⦙ (_◐ wkₑ idₑ) & rid◑ η
                          )


--------------------------------------------------------------------------------


-- (∈-ₑ∘ₛ)
get◑ : ∀ {Γ Ξ Ξ′ A} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (i : Ξ ∋ A)
                    → getₛ (η ◑ σ) i ≡ (getₛ σ ∘ getₑ η) i
get◑ σ       done      i       = refl
get◑ (σ , M) (wkₑ η)   i       = get◑ σ η i
get◑ (σ , M) (liftₑ η) zero    = refl
get◑ (σ , M) (liftₑ η) (suc i) = get◑ σ η i

-- (Tm-ₑ∘ₛ)
mutual
  sub◑ : ∀ {Γ Ξ Ξ′ A} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (M : Ξ ⊢ A)
                      → sub (η ◑ σ) M ≡ (sub σ ∘ ren η) M
  sub◑ σ η (𝓋 i)   = get◑ σ η i
  sub◑ σ η (ƛ M)   = ƛ & sublift◑ σ η M
  sub◑ σ η (M ∙ N) = _∙_ & sub◑ σ η M
                         ⊗ sub◑ σ η N

  sublift◑ : ∀ {Γ Ξ Ξ′ A B} → (σ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (M : Ξ , B ⊢ A)
                            → sub (liftₛ {B} (η ◑ σ)) M ≡
                               (sub (liftₛ σ) ∘ ren (liftₑ η)) M
  sublift◑ σ η M = (λ σ′ → sub (σ′ , 0) M)
                   & comp◑◐ (wkₑ idₑ) σ η
                 ⦙ sub◑ (liftₛ σ) (liftₑ η) M


--------------------------------------------------------------------------------


-- (∈-ₛ∘ₑ)
get◐ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (σ : Γ ⊢⋆ Ξ) (i : Ξ ∋ A)
                    → getₛ (σ ◐ η) i ≡ (ren η ∘ getₛ σ) i
get◐ η (σ , M) zero    = refl
get◐ η (σ , M) (suc i) = get◐ η σ i

-- (Tm-ₛ∘ₑ)
mutual
  sub◐ : ∀ {Γ Γ′ Ξ A} → (η : Γ′ ⊇ Γ) (σ : Γ ⊢⋆ Ξ) (M : Ξ ⊢ A)
                      → sub (σ ◐ η) M ≡ (ren η ∘ sub σ) M
  sub◐ η σ (𝓋 i)   = get◐ η σ i
  sub◐ η σ (ƛ M)   = ƛ & sublift◐ η σ M
  sub◐ η σ (M ∙ N) = _∙_ & sub◐ η σ M
                         ⊗ sub◐ η σ N

  sublift◐ : ∀ {Γ Γ′ Ξ A B} → (η : Γ′ ⊇ Γ) (σ : Γ ⊢⋆ Ξ) (M : Ξ , B ⊢ A)
                            → sub (liftₛ {B} (σ ◐ η)) M ≡
                               (ren (liftₑ η) ∘ sub (liftₛ σ)) M
  sublift◐ η σ M = (λ σ′ → sub (σ′ , 0) M)
                   & ( comp◐○ (wkₑ idₑ) η σ
                     ⦙ (σ ◐_) & (wkₑ & ( rid○ η
                                       ⦙ lid○ η ⁻¹
                                       ))
                     ⦙ comp◐○ (liftₑ η) (wkₑ idₑ) σ ⁻¹
                     )
                 ⦙ sub◐ (liftₑ η) (liftₛ σ) M


--------------------------------------------------------------------------------


-- (assₛₑₛ)
comp●◑ : ∀ {Γ Ξ Ξ′ Φ} → (σ₁ : Γ ⊢⋆ Ξ′) (η : Ξ′ ⊇ Ξ) (σ₂ : Ξ ⊢⋆ Φ)
                      → (σ₂ ◐ η) ● σ₁ ≡ σ₂ ● (η ◑ σ₁)
comp●◑ σ₁ η ∅        = refl
comp●◑ σ₁ η (σ₂ , M) = _,_ & comp●◑ σ₁ η σ₂
                           ⊗ (sub◑ σ₁ η M ⁻¹)

-- (assₛₛₑ)
comp●◐ : ∀ {Γ Γ′ Ξ Φ} → (η : Γ′ ⊇ Γ) (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ)
                      → (σ₂ ● σ₁) ◐ η ≡ σ₂ ● (σ₁ ◐ η)
comp●◐ η σ₁ ∅        = refl
comp●◐ η σ₁ (σ₂ , M) = _,_ & comp●◐ η σ₁ σ₂
                           ⊗ (sub◐ η σ₁ M ⁻¹)


--------------------------------------------------------------------------------


-- (∈-∘ₛ)
get● : ∀ {Γ Ξ Φ A} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (i : Φ ∋ A)
                   → getₛ (σ₂ ● σ₁) i ≡ (sub σ₁ ∘ getₛ σ₂) i
get● σ₁ (σ₂ , M) zero    = refl
get● σ₁ (σ₂ , M) (suc i) = get● σ₁ σ₂ i

-- (Tm-∘ₛ)
mutual
  sub● : ∀ {Γ Ξ Φ A} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (M : Φ ⊢ A)
                     → sub (σ₂ ● σ₁) M ≡ (sub σ₁ ∘ sub σ₂) M
  sub● σ₁ σ₂ (𝓋 i)   = get● σ₁ σ₂ i
  sub● σ₁ σ₂ (ƛ M)   = ƛ & sublift● σ₁ σ₂ M
  sub● σ₁ σ₂ (M ∙ N) = _∙_ & sub● σ₁ σ₂ M
                           ⊗ sub● σ₁ σ₂ N

  sublift● : ∀ {Γ Ξ Φ A B} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (M : Φ , B ⊢ A)
                           → sub (liftₛ {B} (σ₂ ● σ₁)) M ≡
                              (sub (liftₛ σ₁) ∘ sub (liftₛ σ₂)) M
  sublift● σ₁ σ₂ M = (λ σ′ → sub (σ′ , 0) M)
                     & ( comp●◐ (wkₑ idₑ) σ₁ σ₂
                       ⦙ (σ₂ ●_) & (lid◑ (wkₛ σ₁) ⁻¹)
                       ⦙ comp●◑ (liftₛ σ₁) (wkₑ idₑ) σ₂ ⁻¹
                       )
                   ⦙ sub● (liftₛ σ₁) (liftₛ σ₂) M


--------------------------------------------------------------------------------


-- (∈-idₛ)
idgetₛ : ∀ {Γ A} → (i : Γ ∋ A)
                 → getₛ idₛ i ≡ 𝓋 i
idgetₛ zero    = refl
idgetₛ (suc i) = get◐ (wkₑ idₑ) idₛ i
               ⦙ wk & idgetₛ i
               ⦙ 𝓋 ∘ suc & idgetₑ i

-- (Tm-idₛ)
idsub : ∀ {Γ A} → (M : Γ ⊢ A)
                → sub idₛ M ≡ M
idsub (𝓋 i)   = idgetₛ i
idsub (ƛ M)   = ƛ & idsub M
idsub (M ∙ N) = _∙_ & idsub M
                    ⊗ idsub N


--------------------------------------------------------------------------------


-- (idrₛ)
rid● : ∀ {Γ Ξ} → (σ : Γ ⊢⋆ Ξ)
               → σ ● idₛ ≡ σ
rid● ∅       = refl
rid● (σ , M) = _,_ & rid● σ
                   ⊗ idsub M

-- (idlₛ)
lid● : ∀ {Γ Ξ} → (σ : Γ ⊢⋆ Ξ)
               → idₛ ● σ ≡ σ
lid● ∅       = refl
lid● (σ , M) = (_, M) & ( comp●◑ (σ , M) (wkₑ idₑ) idₛ
                        ⦙ lid● (idₑ ◑ σ)
                        ⦙ lid◑ σ
                        )

-- (assₛ)
assoc● : ∀ {Γ Ξ Φ Ψ} → (σ₁ : Γ ⊢⋆ Ξ) (σ₂ : Ξ ⊢⋆ Φ) (σ₃ : Φ ⊢⋆ Ψ)
                     → (σ₃ ● σ₂) ● σ₁ ≡ σ₃ ● (σ₂ ● σ₁)
assoc● σ₁ σ₂ ∅        = refl
assoc● σ₁ σ₂ (σ₃ , M) = _,_ & assoc● σ₁ σ₂ σ₃
                            ⊗ (sub● σ₁ σ₂ M ⁻¹)


--------------------------------------------------------------------------------


𝗦𝗧𝗟𝗖 : Category 𝒞 _⊢⋆_
𝗦𝗧𝗟𝗖 =
  record
    { idₓ    = idₛ
    ; _⋄_    = _●_
    ; lid⋄   = lid●
    ; rid⋄   = rid●
    ; assoc⋄ = assoc●
    }


subPsh : 𝒯 → Presheaf₀ 𝗦𝗧𝗟𝗖
subPsh A =
  record
    { Fₓ  = _⊢ A
    ; F   = sub
    ; idF = fext! idsub
    ; F⋄  = λ σ₁ σ₂ → fext! (sub● σ₂ σ₁)
    }


--------------------------------------------------------------------------------
