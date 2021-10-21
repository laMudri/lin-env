module List.MALL where

  open import Data.List using (List; []; _∷_)
  open import Data.List.Relation.Binary.Pointwise as Pw
  open import Data.List.Relation.Ternary.Interleaving.Propositional
    hiding (split)
  open import Data.Product
  open import Function.Base using (_∘_)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡
  open import Relation.Nary

  module _ where

    -- Interleaving algebra

    infix 20 []≈_ [_,_]≈_ _≈_

    private
      variable
        a : Level
        A : Set a
        ws xs ys zs : List A
        xss yss : List (List A)

    data []≈_ {A : Set a} : List A → Set a where
      [] : []≈ []

    [_,_]≈_ : (xs ys zs : List A) → Set _
    [ xs , ys ]≈ zs = Interleaving xs ys zs

    _≈_ : (xs ys : List A) → Set _
    _≈_ = Pointwise _≡_

    [[],-]≈- : ∃⟨ []≈_ ∩ [_, xs ]≈ ys ⟩ → xs ≈ ys
    [[],-]≈- (_ , [] , is) = lemma is
      where
      lemma : [ [] , xs ]≈ ys → xs ≈ ys
      lemma [] = []
      lemma (q ∷ʳ is) = q ∷ lemma is

    -≈[[],-] : xs ≈ ys → ∃⟨ []≈_ ∩ [_, xs ]≈ ys ⟩
    -≈[[],-] qs = _ , [] , right qs

    [-,[]]≈- : ∃⟨ [ xs ,_]≈ ys ∩ []≈_ ⟩ → xs ≈ ys
    [-,[]]≈- (_ , is , []) = lemma is
      where
      lemma : [ xs , [] ]≈ ys → xs ≈ ys
      lemma [] = []
      lemma (q ∷ˡ is) = q ∷ lemma is

    -≈[-,[]] : xs ≈ ys → ∃⟨ [ xs ,_]≈ ys ∩ []≈_ ⟩
    -≈[-,[]] qs = _ , left qs , []

    [[-,-],-]≈[-,[-,-]] :
      ∃⟨ [ ws , xs ]≈_ ∩ [_, ys ]≈ zs ⟩ → ∃⟨ [ ws ,_]≈ zs ∩ [ xs , ys ]≈_ ⟩
    [[-,-],-]≈[-,[-,-]] (_ , is , consʳ js) =
      let _ , is′ , js′ = [[-,-],-]≈[-,[-,-]] (_ , is , js) in
      _ , consʳ is′ , consʳ js′
    [[-,-],-]≈[-,[-,-]] (_ , [] , []) = _ , [] , []
    [[-,-],-]≈[-,[-,-]] (_ , consˡ is , consˡ js) =
      let _ , is′ , js′ = [[-,-],-]≈[-,[-,-]] (_ , is , js) in
      _ , consˡ is′ , js′
    [[-,-],-]≈[-,[-,-]] (_ , consʳ is , consˡ js) =
      let _ , is′ , js′ = [[-,-],-]≈[-,[-,-]] (_ , is , js) in
      _ , consʳ is′ , consˡ js′

    [-,[-,-]]≈[[-,-],-] :
      ∃⟨ [ ws ,_]≈ zs ∩ [ xs , ys ]≈_ ⟩ → ∃⟨ [ ws , xs ]≈_ ∩ [_, ys ]≈ zs ⟩
    [-,[-,-]]≈[[-,-],-] (_ , [] , []) = _ , [] , []
    [-,[-,-]]≈[[-,-],-] (_ , consˡ is , js) =
      let _ , is′ , js′ = [-,[-,-]]≈[[-,-],-] (_ , is , js) in
      _ , consˡ is′ , consˡ js′
    [-,[-,-]]≈[[-,-],-] (_ , consʳ is , consˡ js) =
      let _ , is′ , js′ = [-,[-,-]]≈[[-,-],-] (_ , is , js) in
      _ , consʳ is′ , consˡ js′
    [-,[-,-]]≈[[-,-],-] (_ , consʳ is , consʳ js) =
      let _ , is′ , js′ = [-,[-,-]]≈[[-,-],-] (_ , is , js) in
      _ , is′ , consʳ js′

    [-,-]≈-comm : [ xs , ys ]≈ zs → [ ys , xs ]≈ zs
    [-,-]≈-comm [] = []
    [-,-]≈-comm (x ∷ˡ is) = x ∷ʳ [-,-]≈-comm is
    [-,-]≈-comm (x ∷ʳ is) = x ∷ˡ [-,-]≈-comm is

    -- Variables

    infix 20 _∋_

    _∋_ : List A → A → Set _
    xs ∋ x = xs ≈ (x ∷ [])

    -- 2D

    infix 20 ⋃[_]≈_

    data ⋃[_]≈_ {A : Set a} : List (List A) → List A → Set a where
      [] : ⋃[ [] ]≈ []
      _∷_ : [ xs , ys ]≈ zs → ⋃[ xss ]≈ ys → ⋃[ xs ∷ xss ]≈ zs

  -- Types & terms

  infixr 70 _⊸_
  infix 20 _⊢_
  infix 7 _✴_

  data Ty : Set where
    ι : Ty
    _⊸_ : (A B : Ty) → Ty

  Ctx = List Ty

  private
    variable
      A B C : Ty
      Γ Δ Θ Γ0 Γ1 Δ0 Δ1 : List Ty

  OpenType = Ctx → Set

  _─OpenFam : Set → Set₁
  I ─OpenFam = Ctx → I → Set
  OpenFam = Ty ─OpenFam

  record _✴_ (T U : OpenType) (Γ : Ctx) : Set where
    constructor _✴⟨_,_⟩
    field
      {ΓT ΓU} : Ctx
      split : [ ΓT , ΓU ]≈ Γ
      T-prf : T ΓT
      U-prf : U ΓU

  data _⊢_ : OpenFam where
    var : ∀[ _∋ A ⇒ _⊢ A ]
    ⊸I : ∀[ _⊢ B ∘ (A ∷_) ⇒ _⊢ A ⊸ B ]
    ⊸E : ∀[ (_⊢ A ⊸ B ✴ _⊢ A) ⇒ _⊢ B ]

  -- Environments

  -- [_]_⇒ᵉ_ : Ty ─OpenFam → Ctx ─OpenFam
  record [_]_⇒ᵉ_ (𝓥 : OpenFam) (Γ Δ : Ctx) : Set where
    constructor env
    field
      {Γs} : List Ctx
      combine : ⋃[ Γs ]≈ Γ
      vals : Pointwise 𝓥 Γs Δ
  open [_]_⇒ᵉ_ public

  private
    variable
      𝓥 : OpenFam

  lookup : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ∋ A → 𝓥 Γ A
  lookup (env (is ∷ []) (v ∷ [])) (refl ∷ [])
    with refl ← Pointwise-≡⇒≡ ([-,[]]≈- (_ , is , [])) = v

  []ᵉ : []≈ Γ → [ 𝓥 ] Γ ⇒ᵉ []
  []ᵉ [] = env [] []

  consᵉ : [ Γ0 , Γ1 ]≈ Γ → 𝓥 Γ0 B → [ 𝓥 ] Γ1 ⇒ᵉ Δ → [ 𝓥 ] Γ ⇒ᵉ (B ∷ Δ)
  consᵉ is v (env us vs) = env (is ∷ us) (v ∷ vs)

  []ᵉ⁻¹ : [ 𝓥 ] Γ ⇒ᵉ [] → []≈ Γ
  []ᵉ⁻¹ (env [] []) = []

  consᵉ⁻¹ :
    [ 𝓥 ] Γ ⇒ᵉ (B ∷ Δ) → ∃₂ \ Γ0 Γ1 → [ Γ0 , Γ1 ]≈ Γ × 𝓥 Γ0 B × [ 𝓥 ] Γ1 ⇒ᵉ Δ
  consᵉ⁻¹ (env (is ∷ us) (v ∷ vs)) = _ , _ , is , v , env us vs

  ,-env : ∃⟨ [ 𝓥 ] Γ ⇒ᵉ_ ∩ [ Δ0 , Δ1 ]≈_ ⟩ →
    (∃₂ \ Γ0 Γ1 → [ Γ0 , Γ1 ]≈ Γ × [ 𝓥 ] Γ0 ⇒ᵉ Δ0 × [ 𝓥 ] Γ1 ⇒ᵉ Δ1)
  ,-env (_ , ρ , []) with [] ← []ᵉ⁻¹ ρ = _ , _ , [] , ρ , ρ
  ,-env (_ , vρ , consˡ js) =
    let _ , _ , v,ρ , v , ρ = consᵉ⁻¹ vρ in
    let _ , _ , ρ0,ρ1 , ρ0 , ρ1 = ,-env (_ , ρ , js) in
    let _ , v,ρ0 , ,ρ1 = [-,[-,-]]≈[[-,-],-] (_ , v,ρ , ρ0,ρ1) in
    _ , _ , ,ρ1 , consᵉ v,ρ0 v ρ0 , ρ1
  ,-env (_ , vρ , consʳ js) =
    let _ , _ , v,ρ , v , ρ = consᵉ⁻¹ vρ in
    let _ , _ , ρ0,ρ1 , ρ0 , ρ1 = ,-env (_ , ρ , js) in
    let _ , v,ρ1 , ,ρ0 = [-,[-,-]]≈[[-,-],-] (_ , v,ρ , [-,-]≈-comm ρ0,ρ1) in
    _ , _ , [-,-]≈-comm ,ρ0 , ρ0 , consᵉ v,ρ1 v ρ1

  record Kit (𝓥 : OpenFam) : Set where
    field
      vr : ∀[ _∋_ {A = Ty} ⇒ 𝓥 ]
      tm : ∀[ 𝓥 ⇒ _⊢_ ]

    extend : [ 𝓥 ] Γ ⇒ᵉ Δ → [ 𝓥 ] (A ∷ Γ) ⇒ᵉ (A ∷ Δ)
    extend ρ = consᵉ (consˡ (right (Pw.refl ≡.refl))) (vr (≡.refl ∷ [])) ρ

    trav : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ⊢ A → Γ ⊢ A
    trav ρ (var v) = tm (lookup ρ v)
    trav ρ (⊸I M) = ⊸I (trav (extend ρ) M)
    trav ρ (⊸E (sp ✴⟨ M , N ⟩)) =
      let _ , _ , sp′ , ρM , ρN = ,-env (_ , ρ , sp) in
      ⊸E (sp′ ✴⟨ trav ρM M , trav ρN N ⟩)
