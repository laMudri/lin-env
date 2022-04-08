module Modal.CtxMonoid where

  open import Data.Product
  open import Function.Base using (_$_; id; _∘_)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Relation.Nary

  open import Algebra.Rel.Propositional

  ⋃ : ∀ {i j ℓ} {I : Set i} {J : Set j} → (I → J → Set ℓ) → (J → Set (i ⊔ ℓ))
  ⋃ P j = ∃ \ i → P i j

  module WithModalities (Mod : Set) where

    infixr 50 _⊸_

    data Ty : Set where
      ι : Ty
      _⊸_ : (mA : Mod × Ty) (B : Ty) → Ty

    private
      variable
        A B C : Ty
        m : Mod
        mA : Mod × Ty

    module WithStuff
      (CtxCM : RelCommutativeMonoid′)
      (open RelCommutativeMonoid′ CtxCM renaming (Carrier to Ctx))
      (_∋_ : Ctx → Ty → Set)
      (_-,_ : Ctx → Mod × Ty → Ctx)
      (mod : Mod → Ctx → Ctx → Set)
      (Env : (Ctx → Ty → Set) → (Ctx → Ctx → Set))
      (lookup : ∀ {V Γ Δ} → Env V Γ Δ → ∀[ Δ ∋_ ⇒ V Γ ])
      (bind : ∀ {V Γ Δ mA} → Env V Γ Δ → Env V (Γ -, mA) (Δ -, mA))
      (+-env : ∀ {V Γ Δₗ Δᵣ} →
        (∃ \ Δ → Env V Γ Δ × [ Δₗ ∙ Δᵣ ]∼ Δ) →
        (∃₂ \ Γₗ Γᵣ → [ Γₗ ∙ Γᵣ ]∼ Γ × Env V Γₗ Δₗ × Env V Γᵣ Δᵣ))
      (m-env : ∀ {V m Γ Δ′} →
        (∃ \ Δ → Env V Γ Δ × mod m Δ Δ′) →
        (∃ \ Γ′ → mod m Γ Γ′ × Env V Γ′ Δ′))
      where

      infix 40 _⊢_ [_]_⇒ᵉ_
      infixr 20 _·_

      OpenType = Ctx → Set

      _─OpenFam : Set → Set₁
      I ─OpenFam = Ctx → I → Set
      OpenFam = Ty ─OpenFam

      _·_ : Mod → OpenType → OpenType
      (m · T) Γ = ∃⟨ mod m Γ ∩ T ⟩

      data _⊢_ : OpenFam where
        var : ∀[ _∋ A ⇒ _⊢ A ]
        ⊸I : ∀[ _⊢ B ∘ _-, mA ⇒ _⊢ mA ⊸ B ]
        ⊸E : ∀[ (_⊢ (m , A) ⊸ B ✴ (m · _⊢ A)) ⇒ _⊢ B ]

      [_]_⇒ᵉ_ = Env

      private
        variable
          Γ Δ Θ : Ctx

      module _ {V} (tm : ∀[ V ⇒ _⊢_ ]) where

        trav : [ V ] Γ ⇒ᵉ Δ → Δ ⊢ A → Γ ⊢ A
        trav ρ (var v) = tm (lookup ρ v)
        trav ρ (⊸I M) = ⊸I (trav (bind ρ) M)
        trav ρ (⊸E (⟨ M , (_ , spm , N) ⟩✴ sp+)) =
          let _ , _ , sp+′ , ρM , ρᵣ = +-env (_ , ρ , sp+) in
          let _ , spm′ , ρN = m-env (_ , ρᵣ , spm) in
          ⊸E (⟨ trav ρM M , (_ , spm′ , trav ρN N) ⟩✴ sp+′)
