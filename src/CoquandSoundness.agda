module CoquandSoundness where

open import CoquandCompleteness public


--------------------------------------------------------------------------------


-- Un⟦_⟧
postulate
  ⟦_⟧Un : ∀ {Γ Ξ A} → {ρ : Γ ⊩⋆ Ξ}
                    → (M : Ξ ⊢ A) → Un⋆ ρ
                    → Un (⟦ M ⟧ ρ)

-- 𝒰⋆⟦_⟧ₛ
postulate
  ⟦_⟧Un⋆ : ∀ {Γ Ξ Φ} → {ρ : Γ ⊩⋆ Ξ}
                     → (σ : Ξ ⊢⋆ Φ) → Un⋆ ρ
                     → Un⋆ (⟦ σ ⟧⋆ ρ)

postulate
  ⟦_⟧Eq : ∀ {Γ Ξ A} → {ρ₁ ρ₂ : Γ ⊩⋆ Ξ}
                    → (M : Ξ ⊢ A) → Eq⋆ ρ₁ ρ₂ → Un⋆ ρ₁ → Un⋆ ρ₂
                    → Eq (⟦ M ⟧ ρ₁) (⟦ M ⟧ ρ₂)

-- Eq⋆⟦_⟧ₛ
postulate
  ⟦_⟧Eq⋆ : ∀ {Γ Ξ Φ} → {ρ₁ ρ₂ : Γ ⊩⋆ Ξ}
                     → (σ : Ξ ⊢⋆ Φ) → Eq⋆ ρ₁ ρ₂ → Un⋆ ρ₁ → Un⋆ ρ₂
                     → Eq⋆ (⟦ σ ⟧⋆ ρ₁) (⟦ σ ⟧⋆ ρ₂)


--------------------------------------------------------------------------------


-- ⟦_⟧⬗Eq = symEq ∘ ↑⟨_⟩Eq⟦_⟧
⟦_⟧⬗Eq : ∀ {Γ Γ′ Ξ A} → {ρ : Γ ⊩⋆ Ξ}
                      → (M : Ξ ⊢ A) (η : Γ′ ∋⋆ Γ) → Un⋆ ρ
                      → Eq (⟦ M ⟧ (η ⬗ ρ))
                            (acc η (⟦ M ⟧ ρ))

⟦_⟧⬗Eq (` i)   η υ = get⬗Eq η i υ

⟦_⟧⬗Eq (ƛ M)   η υ = eq⊃ (λ η′ u →
                           ⟦ M ⟧Eq (comp⬗◇Eq⋆ η′ η υ , reflEq u)
                                   (cong⬗Un⋆ η′ (cong⬗Un⋆ η υ) , u)
                                   (cong⬗Un⋆ (η′ ○ η) υ , u))

⟦_⟧⬗Eq (M ∙ N) η υ =
    cong◎Eq idᵣ (⟦ M ⟧⬗Eq η υ) (⟦ M ⟧Un (cong⬗Un⋆ η υ)) (congaccUn η (⟦ M ⟧Un υ))
                (⟦ N ⟧⬗Eq η υ) (⟦ N ⟧Un (cong⬗Un⋆ η υ)) (congaccUn η (⟦ N ⟧Un υ))
  ⦙ acc◎idEq η (⟦ M ⟧Un υ) (congaccUn η (⟦ N ⟧Un υ))
  ⦙ (cong◎Eq η ((lidaccEq (⟦ M ⟧Un υ)) ⁻¹) (⟦ M ⟧Un υ) (congaccUn idᵣ (⟦ M ⟧Un υ))
               (reflEq (congaccUn η (⟦ N ⟧Un υ))) (congaccUn η (⟦ N ⟧Un υ)) (congaccUn η (⟦ N ⟧Un υ))
  ⦙ acc◎Eq idᵣ η (⟦ M ⟧Un υ) (⟦ N ⟧Un υ))


-- ⟦_⟧⬗Eq⋆ = symEq ∘ ↑⟨_⟩Eq⋆⟦_⟧ₛ
⟦_⟧⬗Eq⋆ : ∀ {Γ Γ′ Ξ Φ} → {ρ : Γ ⊩⋆ Ξ}
                       → (σ : Ξ ⊢⋆ Φ) (η : Γ′ ∋⋆ Γ) → Un⋆ ρ
                       → Eq⋆ (⟦ σ ⟧⋆ (η ⬗ ρ))
                              (η ⬗ ⟦ σ ⟧⋆ ρ)
⟦_⟧⬗Eq⋆ ∅       η υ = ∅
⟦_⟧⬗Eq⋆ (σ , M) η υ = ⟦ σ ⟧⬗Eq⋆ η υ , ⟦ M ⟧⬗Eq η υ


--------------------------------------------------------------------------------


-- TODO: Generalise to zap⬖
postulate
  aux₄₈₁ : ∀ {Γ Ξ A} → {ρ : Γ ⊩⋆ Ξ} {a : Γ ⊩ A}
                     → Un⋆ ρ
                     → Eq⋆ ((ρ , a) ⬖ wkᵣ idᵣ) ρ


-- TODO
-- Basic properties of _◇_
-- Advanced properties of _◇_
-- Basic properties of _⬗_
-- Basic properties of _◆_
-- Advanced properties of _⬗_
-- Advanced properties of _◆_


-- TODO: Fix the instance argument problem; abstract over models; rename η to ξ…


--------------------------------------------------------------------------------


renlift⟦_⟧Eq : ∀ {Γ Γ′ A B w w′} → {ρ : w ⊩⋆ Γ′} {a : w′ ⊩ A}
                                 → (M : Γ , A ⊢ B) (η₁ : Γ′ ∋⋆ Γ) (η₂ : w′ ∋⋆ w) → Un⋆ ρ → Un a
                                 → Eq (⟦ ren (liftᵣ {A} η₁) M ⟧ (η₂ ⬗ ρ , a))
                                       (⟦ M ⟧ (η₂ ⬗ (ρ ⬖ η₁) , a))

renlift⟦_⟧Eq (` zero) η₁ η₂ υ u = reflEq u

renlift⟦_⟧Eq {ρ = ρ} {a} (` (suc i)) η₁ η₂ υ u =
    ≡→Eq ((getᵥ (η₂ ⬗ ρ , a)) & natgetᵣ η₁ i)
          (conggetUn (getᵣ (wkᵣ η₁) i) (cong⬗Un⋆ η₂ υ , u))
  ⦙ get⬖Eq η₁ (getᵣ η₁ i) i (cong⬗Un⋆ η₂ υ) ⁻¹
  ⦙ conggetEq i (comp⬗⬖Eq⋆ η₂ η₁ υ ⁻¹)

renlift⟦_⟧Eq (ƛ M) η₁ η₂ υ u =
      eq⊃ (λ η′ u′ → renlift⟦ M ⟧Eq (liftᵣ η₁) η′ (cong⬗Un⋆ η₂ υ , u) u′
                    ⦙ ⟦ M ⟧Eq ( ( cong⬗Eq⋆ η′ (( comp⬗⬖Eq⋆ η₂ η₁ υ
                                               ⦙ zap⬖Eq⋆ (wkᵣ η₁) η₁ (cong⬗Un⋆ η₂ υ) ⁻¹
                                               ) ⁻¹)
                                , reflEq (congaccUn η′ u)
                                )
                              , reflEq u′
                              )
                              ((cong⬗Un⋆ η′ (cong⬖Un⋆ (wkᵣ η₁) (cong⬗Un⋆ η₂ υ , u)) , congaccUn η′ u) , u′)
                              ((cong⬗Un⋆ η′ (cong⬗Un⋆ η₂ (cong⬖Un⋆ η₁ υ)) , congaccUn η′ u) , u′))

renlift⟦_⟧Eq (M ∙ N) η₁ η₂ υ u =
  cong◎Eq idᵣ (renlift⟦ M ⟧Eq η₁ η₂ υ u) (⟦ ren (liftᵣ η₁) M ⟧Un (cong⬗Un⋆ η₂ υ , u)) (⟦ M ⟧Un (cong⬗Un⋆ η₂ (cong⬖Un⋆ η₁ υ) , u))
              (renlift⟦ N ⟧Eq η₁ η₂ υ u) (⟦ ren (liftᵣ η₁) N ⟧Un (cong⬗Un⋆ η₂ υ , u)) (⟦ N ⟧Un (cong⬗Un⋆ η₂ (cong⬖Un⋆ η₁ υ) , u))


--------------------------------------------------------------------------------


renwk⟦_⟧Eq : ∀ {Γ Γ′ A C w} → {ρ : w ⊩⋆ Γ′} {a : w ⊩ A}
                            → (M : Γ ⊢ C) (η : Γ′ ∋⋆ Γ) → Un⋆ ρ → Un a
                            → Eq (⟦ ren (wkᵣ {A} η) M ⟧ (ρ , a))
                                  (⟦ M ⟧ (ρ ⬖ η))

renwk⟦_⟧Eq (` i) η υ u =
    get⬖Eq (wkᵣ η) (getᵣ (wkᵣ η) i) i (υ , u) ⁻¹
  ⦙ conggetEq i (zap⬖Eq⋆ (wkᵣ η) η υ)

renwk⟦_⟧Eq (ƛ M) η υ u =
  eq⊃ (λ η′ u′ → renlift⟦ M ⟧Eq (wkᵣ η) η′ (υ , u) u′
                ⦙ ⟦ M ⟧Eq (cong⬗Eq⋆ η′ (zap⬖Eq⋆ (wkᵣ η) η υ) , reflEq u′)
                          (cong⬗Un⋆ η′ (cong⬖Un⋆ (wkᵣ η) (υ , u)) , u′)
                          (cong⬗Un⋆ η′ (cong⬖Un⋆ η υ) , u′))

renwk⟦_⟧Eq (M ∙ N) η υ u =
  cong◎Eq idᵣ (renwk⟦ M ⟧Eq η υ u) (⟦ ren (wkᵣ η) M ⟧Un (υ , u)) (⟦ M ⟧Un (cong⬖Un⋆ η υ))
              (renwk⟦ N ⟧Eq η υ u) (⟦ ren (wkᵣ η) N ⟧Un (υ , u)) (⟦ N ⟧Un (cong⬖Un⋆ η υ))


--------------------------------------------------------------------------------


wk⟦_⟧Eq : ∀ {Γ A C w} → {ρ : w ⊩⋆ Γ} {a : w ⊩ A}
                      → (M : Γ ⊢ C) → Un⋆ ρ → Un a
                      → Eq (⟦ wk {A} M ⟧ (ρ , a))
                            (⟦ M ⟧ ρ)
wk⟦_⟧Eq M υ u = renwk⟦ M ⟧Eq idᵣ υ u
              ⦙ ⟦ M ⟧Eq (rid⬖Eq⋆ υ) (cong⬖Un⋆ idᵣ υ) υ

wk⟦_⟧Eq⋆ : ∀ {Γ Ξ A w} → {ρ : w ⊩⋆ Γ} {a : w ⊩ A}
                       → (σ : Γ ⊢⋆ Ξ) → Un⋆ ρ → Un a
                       → Eq⋆ (⟦ wkₛ {A} σ ⟧⋆ (ρ , a))
                              (⟦ σ ⟧⋆ ρ)
wk⟦_⟧Eq⋆ ∅       υ u = ∅
wk⟦_⟧Eq⋆ (σ , M) υ u = wk⟦ σ ⟧Eq⋆ υ u , wk⟦ M ⟧Eq υ u


--------------------------------------------------------------------------------


get⟦_⟧Eq : ∀ {Γ Ξ A w} → {ρ : w ⊩⋆ Γ}
                       → (σ : Γ ⊢⋆ Ξ) (i : Ξ ∋ A) → Un⋆ ρ
                       → Eq (⟦ getₛ σ i ⟧ ρ)
                             (getᵥ (⟦ σ ⟧⋆ ρ) i)
get⟦_⟧Eq (σ , M) zero    υ = reflEq (⟦ M ⟧Un υ)
get⟦_⟧Eq (σ , M) (suc i) υ = get⟦ σ ⟧Eq i υ


--------------------------------------------------------------------------------


sublift⟦_⟧Eq : ∀ {Γ Ξ A B w} → {ρ : w ⊩⋆ Γ} {a : w ⊩ A}
                             → (M : Ξ , A ⊢ B) (σ : Γ ⊢⋆ Ξ) → Un⋆ ρ → Un a
                             → Eq (⟦ sub (liftₛ {A} σ) M ⟧ (ρ , a))
                                   (⟦ M ⟧ (⟦ σ ⟧⋆ ρ , a))

sublift⟦_⟧Eq (` zero) σ υ u = reflEq u

sublift⟦_⟧Eq {ρ = ρ} {a} (` (suc i)) σ υ u =
    ≡→Eq ((λ M′ → ⟦ M′ ⟧ (ρ , a)) & natgetₛ σ i)
          (⟦ getₛ (wkₛ σ) i ⟧Un (υ , u))
  ⦙ wk⟦ getₛ σ i ⟧Eq υ u
  ⦙ get⟦ σ ⟧Eq i υ

sublift⟦_⟧Eq (ƛ M) σ υ u =
  eq⊃ (λ η′ u′ → sublift⟦ M ⟧Eq (liftₛ σ) (cong⬗Un⋆ η′ υ , congaccUn η′ u) u′
                ⦙ ⟦ M ⟧Eq ((⟦ wkₛ σ ⟧⬗Eq⋆ η′ (υ , u) , reflEq (congaccUn η′ u)) , reflEq u′)
                          ((⟦ wkₛ σ ⟧Un⋆ (cong⬗Un⋆ η′ υ , congaccUn η′ u) , congaccUn η′ u) , u′)
                          ((cong⬗Un⋆ η′ (⟦ wkₛ σ ⟧Un⋆ (υ , u)) , congaccUn η′ u) , u′)
                ⦙ ⟦ M ⟧Eq ((cong⬗Eq⋆ η′ (wk⟦ σ ⟧Eq⋆ υ u) , reflEq (congaccUn η′ u)) , reflEq u′)
                          ((cong⬗Un⋆ η′ (⟦ wkₛ σ ⟧Un⋆ (υ , u)) , congaccUn η′ u) , u′)
                          ((cong⬗Un⋆ η′ (⟦ σ ⟧Un⋆ υ) , congaccUn η′ u) , u′))

sublift⟦_⟧Eq (M ∙ N) σ υ u =
  cong◎Eq idᵣ (sublift⟦ M ⟧Eq σ υ u) (⟦ sub (liftₛ σ) M ⟧Un (υ , u)) (⟦ M ⟧Un (⟦ σ ⟧Un⋆ υ , u))
              (sublift⟦ N ⟧Eq σ υ u) (⟦ sub (liftₛ σ) N ⟧Un (υ , u)) (⟦ N ⟧Un (⟦ σ ⟧Un⋆ υ , u))


--------------------------------------------------------------------------------


subliftwk⟦_⟧Eq : ∀ {Γ Ξ A A′ B w w′} → {ρ : w ⊩⋆ Γ} {a : w ⊩ A} {a′ : w′ ⊩ A′}
                                     → (M : Ξ , A′ ⊢ B) (σ : Γ ⊢⋆ Ξ) (η : w′ ∋⋆ w) → Un⋆ ρ → Un a → Un a′
                                     → Eq (⟦ sub (liftₛ (wkₛ σ)) M ⟧ (η ⬗ ρ , acc η a , a′))
                                           (⟦ sub (liftₛ σ) M ⟧ (η ⬗ ρ , a′))
subliftwk⟦_⟧Eq M σ η υ u u′ = sublift⟦ M ⟧Eq (wkₛ σ) (cong⬗Un⋆ η υ , congaccUn η u) u′
                            ⦙ ⟦ M ⟧Eq (wk⟦ σ ⟧Eq⋆ (cong⬗Un⋆ η υ) (congaccUn η u) , reflEq u′)
                                      (⟦ wkₛ σ ⟧Un⋆ (cong⬗Un⋆ η υ , congaccUn η u) , u′)
                                      (⟦ σ ⟧Un⋆ (cong⬗Un⋆ η υ) , u′)
                            ⦙ sublift⟦ M ⟧Eq σ (cong⬗Un⋆ η υ) u′ ⁻¹


--------------------------------------------------------------------------------


subwk⟦_⟧Eq : ∀ {Γ Ξ A C w} → {ρ : w ⊩⋆ Γ} {a : w ⊩ A}
                           → (M : Ξ ⊢ C) (σ : Γ ⊢⋆ Ξ) → Un⋆ ρ → Un a
                           → Eq (⟦ sub (wkₛ {A} σ) M ⟧ (ρ , a))
                                 (⟦ sub σ M ⟧ ρ)

subwk⟦_⟧Eq {ρ = ρ} {a} (` i) σ υ u =
    ≡→Eq ((λ M′ → ⟦ M′ ⟧ (ρ , a)) & (natgetₛ σ i))
          (⟦ getₛ (wkₛ σ) i ⟧Un (υ , u))
  ⦙ wk⟦ getₛ σ i ⟧Eq υ u

subwk⟦_⟧Eq (ƛ {A = A′} M) σ υ u =
  eq⊃ (λ η u′ → subliftwk⟦ M ⟧Eq σ η υ u u′)

subwk⟦_⟧Eq (M ∙ N) σ υ u =
  cong◎Eq idᵣ (subwk⟦ M ⟧Eq σ υ u) (⟦ sub (wkₛ σ) M ⟧Un (υ , u)) (⟦ sub σ M ⟧Un υ)
              (subwk⟦ N ⟧Eq σ υ u) (⟦ sub (wkₛ σ) N ⟧Un (υ , u)) (⟦ sub σ N ⟧Un υ)


--------------------------------------------------------------------------------


sub⟦_⟧Eq : ∀ {Γ Ξ A w} → {ρ : w ⊩⋆ Γ}
                       → (M : Ξ ⊢ A) (σ : Γ ⊢⋆ Ξ) → Un⋆ ρ
                       → Eq (⟦ sub σ M ⟧ ρ)
                             (⟦ M ⟧ (⟦ σ ⟧⋆ ρ))

sub⟦_⟧Eq (` i) σ υ = get⟦ σ ⟧Eq i υ

sub⟦_⟧Eq (ƛ M) σ υ =
  eq⊃ (λ η u → sublift⟦ M ⟧Eq σ (cong⬗Un⋆ η υ) u
              ⦙ ⟦ M ⟧Eq (⟦ σ ⟧⬗Eq⋆ η υ , reflEq u)
                        (⟦ σ ⟧Un⋆ (cong⬗Un⋆ η υ) , u)
                        (cong⬗Un⋆ η (⟦ σ ⟧Un⋆ υ) , u))

sub⟦_⟧Eq (M ∙ N) σ υ =
  cong◎Eq idᵣ (sub⟦ M ⟧Eq σ υ) (⟦ sub σ M ⟧Un υ) (⟦ M ⟧Un (⟦ σ ⟧Un⋆ υ))
              (sub⟦ N ⟧Eq σ υ) (⟦ sub σ N ⟧Un υ) (⟦ N ⟧Un (⟦ σ ⟧Un⋆ υ))


--------------------------------------------------------------------------------


-- TODO: Rename this
sublift⟦⟧Eq⁈ : ∀ {Γ Ξ A B w} → {ρ : w ⊩⋆ Γ}
                             → (σ : Γ ⊢⋆ Ξ) (M : Ξ , A ⊢ B) (N : Γ ⊢ A) → Un⋆ ρ
                             → Eq (⟦ sub (liftₛ {A} σ) M ⟧ (ρ , ⟦ N ⟧ ρ))
                                   (⟦ sub (σ , N) M ⟧ ρ)
sublift⟦⟧Eq⁈ {ρ = ρ} σ M N υ = sublift⟦ M ⟧Eq σ υ (⟦ N ⟧Un υ)
                             ⦙ sub⟦ M ⟧Eq (σ , N) υ ⁻¹


--------------------------------------------------------------------------------


-- TODO: Generalise theorem 4 over models

module _ where
  open 𝔐 canon

  mutual
    lemƛ : ∀ {Γ A B w} → {ρ : w ⊩⋆ Γ} {M M′ : Γ , A ⊢ B}
                       → M ∼ M′ → Un⋆ ρ
                       → Eq (⟦ ƛ M ⟧ ρ) (⟦ ƛ M′ ⟧ ρ)
    lemƛ p υ = eq⊃ (λ xs u → cong⟦ p ⟧Eq (cong⬗Un⋆ xs υ , u))

    lem∙ : ∀ {Γ A B w} → {ρ : w ⊩⋆ Γ} {M M′ : Γ ⊢ A ⊃ B} {N N′ : Γ ⊢ A}
                       → M ∼ M′ → N ∼ N′ → Un⋆ ρ
                       → Eq (⟦ M ∙ N ⟧ ρ) (⟦ M′ ∙ N′ ⟧ ρ)
    lem∙ {M = M} {M′} {N} {N′} p q υ = cong◎Eq idᵣ (cong⟦ p ⟧Eq υ) (⟦ M ⟧Un υ) (⟦ M′ ⟧Un υ)
                                                   (cong⟦ q ⟧Eq υ) (⟦ N ⟧Un υ) (⟦ N′ ⟧Un υ)

    lemβred : ∀ {Γ Ξ A B w} → {ρ : w ⊩⋆ Γ}
                            → (σ : Γ ⊢⋆ Ξ) (M : Ξ , A ⊢ B) (N : Γ ⊢ A) → Un⋆ ρ
                            → Eq (⟦ sub σ (ƛ M) ∙ N ⟧ ρ) (⟦ sub (σ , N) M ⟧ ρ)
    lemβred {ρ = ρ} σ M N υ =
        ⟦ sub (liftₛ σ) M ⟧Eq (lid⬗Eq⋆ υ , reflEq (⟦ N ⟧Un υ))
                              (cong⬗Un⋆ idᵣ υ , ⟦ N ⟧Un υ)
                              (υ , ⟦ N ⟧Un υ)
      ⦙ sublift⟦⟧Eq⁈ σ M N υ

    lemηexp : ∀ {Γ A B w} → {ρ : w ⊩⋆ Γ}
                          → (M : Γ ⊢ A ⊃ B) → Un⋆ ρ
                          → Eq (⟦ M ⟧ ρ) (⟦ ƛ (wk M ∙ ` zero) ⟧ ρ)
    lemηexp {ρ = ρ} M υ =
      eq⊃ (λ η {a} u → acc◎idEq η (⟦ M ⟧Un υ) u ⁻¹
                      ⦙ cong◎Eq idᵣ (⟦ M ⟧⬗Eq η υ ⁻¹) (congaccUn η (⟦ M ⟧Un υ)) (⟦ M ⟧Un (cong⬗Un⋆ η υ))
                                    (reflEq u) u u
                      ⦙ cong◎Eq idᵣ (wk⟦ M ⟧Eq (cong⬗Un⋆ η υ) u ⁻¹) (⟦ M ⟧Un (cong⬗Un⋆ η υ)) (⟦ wk M ⟧Un (cong⬗Un⋆ η υ , u))
                                    (reflEq u) u u)

    -- Theorem 4.
    cong⟦_⟧Eq : ∀ {Γ A w} → {M M′ : Γ ⊢ A} {ρ : w ⊩⋆ Γ}
                          → M ∼ M′ → Un⋆ ρ
                          → Eq (⟦ M ⟧ ρ) (⟦ M′ ⟧ ρ)
    cong⟦ refl∼ {M = M} ⟧Eq υ = reflEq (⟦ M ⟧Un υ)
    cong⟦ p ⁻¹∼ ⟧Eq         υ = cong⟦ p ⟧Eq υ ⁻¹
    cong⟦ p ⦙∼ q ⟧Eq        υ = cong⟦ p ⟧Eq υ ⦙ cong⟦ q ⟧Eq υ
    cong⟦ ƛ∼ p ⟧Eq          υ = lemƛ p υ
    cong⟦ p ∙∼ q ⟧Eq        υ = lem∙ p q υ
    cong⟦ βred∼ σ M N ⟧Eq   υ = lemβred σ M N υ
    cong⟦ ηexp∼ M ⟧Eq       υ = lemηexp M υ


--------------------------------------------------------------------------------


-- Theorem 5.
thm₅ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → nf M ≡ nf M′
               → M ∼ M′
thm₅ M M′ p = thm₂ M
            ⦙ ≡→∼ p
            ⦙ (thm₂ M′ ⁻¹)


--------------------------------------------------------------------------------


-- proj⟨_⟩𝒰⋆
⌊_⌋ᵤ : ∀ {Γ Γ′} → (η : Γ′ ∋⋆ Γ)
                → Un⋆ ⌊ η ⌋ᵥ
⌊ ∅ ⌋ᵤ     = ∅
⌊ η , i ⌋ᵤ = ⌊ η ⌋ᵤ , ⟪` i ⟫ᵤ

-- refl𝒰⋆
idᵤ : ∀ {Γ} → Un⋆ (idᵥ {Γ})
idᵤ = ⌊ idᵣ ⌋ᵤ

-- Theorem 6.
thm₆ : ∀ {Γ A} → (M M′ : Γ ⊢ A) → M ∼ M′
               → nf M ≡ nf M′
thm₆ M M′ p = cor₁ M M′ (cong⟦ p ⟧Eq idᵤ)


--------------------------------------------------------------------------------
