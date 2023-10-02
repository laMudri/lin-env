module List.MALL where

  open import Data.List using (List; []; _∷_)
  open import Data.List.Relation.Binary.Pointwise as Pw
  open import Data.List.Relation.Ternary.Interleaving.Propositional
    hiding (split)
  open import Data.Product
  open import Function.Base using (id; _∘_; _$_)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡
  open import Relation.Nary

  infix 20 [_]_⊨_
  [_]_⊨_ = id

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
  infix 20 _⊢_ _⊨_
  infix 7 _✴_
  infixr 6 _─✴_

  data Ty : Set where
    ι : Ty
    _⊸_ : (A B : Ty) → Ty

  Ctx = List Ty

  private
    variable
      A B C : Ty
      Γ Δ Θ Γ0 Γ1 Δ0 Δ1 : List Ty

  OpenType : ∀ ℓ → Set (suc ℓ)
  OpenType ℓ = Ctx → Set ℓ

  _─OpenFam_ : ∀ {i} → Set i → ∀ ℓ → Set (i ⊔ suc ℓ)
  I ─OpenFam ℓ = Ctx → I → Set ℓ
  OpenFam = Ty ─OpenFam_

  record _✴_ {ℓ} (T U : OpenType ℓ) (Γ : Ctx) : Set ℓ where
    constructor _✴⟨_,_⟩
    field
      {ΓT ΓU} : Ctx
      split : [ ΓT , ΓU ]≈ Γ
      T-prf : T ΓT
      U-prf : U ΓU

  record _─✴_ {ℓ} (T U : OpenType ℓ) (Γ : Ctx) : Set ℓ where
    constructor lam✴
    field app✴ : ∀ {ΓT ΓU} → [ ΓT , Γ ]≈ ΓU → T ΓT → U ΓU
  open _─✴_ public

  eval✴ : ∀ {ℓ} {T U : OpenType ℓ} → ∀[ (T ─✴ U) ✴ T ⇒ U ]
  eval✴ (sp ✴⟨ f , t ⟩) = f .app✴ ([-,-]≈-comm sp) t
    -- The need for commutativity here stems from using cons-lists for contexts
    -- in conjunction with functions which take arguments to their right.

  data _⊢_ : OpenFam 0ℓ where
    var : ∀[ _∋ A ⇒ _⊢ A ]
    ⊸I : ∀[ _⊢ B ∘ (A ∷_) ⇒ _⊢ A ⊸ B ]
    ⊸E : ∀[ (_⊢ A ⊸ B ✴ _⊢ A) ⇒ _⊢ B ]

  -- Environments

  -- [_]_⇒ᵉ_ : Ty ─OpenFam → Ctx ─OpenFam
  record [_]_⇒ᵉ_ {ℓ} (𝓥 : OpenFam ℓ) (Γ Δ : Ctx) : Set ℓ where
    constructor env
    field
      {Γs} : List Ctx
      combine : ⋃[ Γs ]≈ Γ
      vals : Pointwise 𝓥 Γs Δ
  open [_]_⇒ᵉ_ public

  private
    variable
      𝓥 : OpenFam 0ℓ

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

  idᵉ : (∀ A → 𝓥 (A ∷ []) A) → [ 𝓥 ] Γ ⇒ᵉ Γ
  idᵉ {Γ = []} v = []ᵉ []
  idᵉ {Γ = x ∷ Γ} v = consᵉ (consˡ (right (Pw.refl ≡.refl))) (v _) (idᵉ v)

  record Kit (𝓥 : OpenFam 0ℓ) : Set where
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

  record Sem (𝓥 𝓒 : OpenFam 0ℓ) : Set where
    field
      ⟦var⟧ : ∀[ 𝓥 ⇒ 𝓒 ]
      ⟦⊸I⟧ : ∀ {A B} → ∀[ ([ 𝓥 ]_⊨ A ─✴ [ 𝓒 ]_⊨ B) ⇒ [ 𝓒 ]_⊨ A ⊸ B ]
      ⟦⊸E⟧ : ∀ {A B} → ∀[ [ 𝓒 ]_⊨ A ⊸ B ✴ [ 𝓒 ]_⊨ A ⇒ [ 𝓒 ]_⊨ B ]

    sem : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ⊢ A → 𝓒 Γ A
    sem ρ (var v) = ⟦var⟧ (lookup ρ v)
    sem ρ (⊸I M) = ⟦⊸I⟧ (lam✴ λ sp v → sem (consᵉ sp v ρ) M)
    sem ρ (⊸E (sp ✴⟨ M , N ⟩)) =
      let _ , _ , sp′ , ρM , ρN = ,-env (_ , ρ , sp) in
      ⟦⊸E⟧ (sp′ ✴⟨ sem ρM M , sem ρN N ⟩)

  data _NE⊢_ : OpenFam 0ℓ
  data _NF⊢_ : OpenFam 0ℓ

  data _NE⊢_ where
    var : ∀[ _∋ A ⇒ _NE⊢ A ]
    ⊸E : ∀[ (_NE⊢ A ⊸ B ✴ _NF⊢ A) ⇒ _NE⊢ B ]

  data _NF⊢_ where
    emb : ∀[ _NE⊢_ ⇒ _NF⊢_ ]
    ⊸I : ∀[ _NF⊢ B ∘ (A ∷_) ⇒ _NF⊢ A ⊸ B ]

  _⊨_ : OpenFam 0ℓ
  Γ ⊨ ι = Γ NF⊢ ι
  Γ ⊨ A ⊸ B = (_⊨ A ─✴ _⊨ B) Γ

  module _ where
    open Sem

    evalSem : Sem _⊨_ _⊨_
    evalSem .⟦var⟧ = id
    evalSem .⟦⊸I⟧ = id
    evalSem .⟦⊸E⟧ = eval✴

    eval = sem evalSem

  reify : ∀ A → ∀[ _⊨ A ⇒ _NF⊢ A ]
  reflect : ∀ A → ∀[ _NE⊢ A ⇒ _⊨ A ]

  reify ι v = v
  reify (A ⊸ B) v = ⊸I $ reify B $
    v .app✴ (consˡ (right (Pw.refl ≡.refl))) (reflect A (var (≡.refl ∷ [])))

  reflect ι M = emb M
  reflect (A ⊸ B) M .app✴ sp v =
    reflect B (⊸E ([-,-]≈-comm sp ✴⟨ M , reify A v ⟩))

  nbe : ∀[ _⊢_ ⇒ _NF⊢_ ]
  nbe M = reify _ (eval (idᵉ (λ A → reflect A (var (≡.refl ∷ [])))) M)
