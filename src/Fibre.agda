module Fibre where

  open import Data.Product as ×
  open import Data.Sum as ⊎
  open import Function.Base using (_$_; _$′_; id; _∘_; _∘′_)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; subst)
  open import Relation.Nary
  open import Relation.Unary using (_⊆_)

  module _ where

    private
      variable
        a ℓ : Level
        A : Set a

    infixl 50 _-,_ _-u_ _-l_ _-u* _-lˡ _-lʳ _-refl
    infix 40 _∼0 _∼+ _≈_ _∋_
    infixr 7 _✴_
    infixr 6 _─✴_

    data Tsil (A : Set a) : Set a where
      [] : Tsil A
      _-,_ : Tsil A → A → Tsil A

    data Mode : Set where
      unr lin : Mode

    _─Ctx : Set a → Set a
    A ─Ctx = Tsil (Mode × A)

    pattern _-u_ Γ x = Γ -, (unr , x)
    pattern _-l_ Γ x = Γ -, (lin , x)

    private
      variable
        Γ Δ Θ Λ : A ─Ctx
        x y z : A
        xs ys zs : Tsil A
        m : Mode

    data _∼0 {A : Set a} : A ─Ctx → Set a where
      [] : [] ∼0
      _-u* : Γ ∼0 → Γ -u x ∼0

    data _∼+ {A : Set a} : A ─Ctx → Set a where
      [] : [] ∼+
      _-u*  : Γ ∼+ → Γ -u x ∼+
      _-lˡ : Γ ∼+ → Γ -l x ∼+
      _-lʳ : Γ ∼+ → Γ -l x ∼+

    ∼+-summands : {Γ : A ─Ctx} → Γ ∼+ → A ─Ctx × A ─Ctx
    ∼+-summands [] = [] , []
    ∼+-summands (_-u* {x = x} sp) = ×.map (_-u x) (_-u x) (∼+-summands sp)
    ∼+-summands (_-lˡ {x = x} sp) = ×.map (_-l x) id (∼+-summands sp)
    ∼+-summands (_-lʳ {x = x} sp) = ×.map id (_-l x) (∼+-summands sp)

    ∼+-ll ∼+-rr : {Γ : A ─Ctx} → Γ ∼+ → A ─Ctx
    ∼+-ll = proj₁ ∘ ∼+-summands
    ∼+-rr = proj₂ ∘ ∼+-summands

    data _≈_ {A : Set a} : (xs ys : Tsil A) → Set a where
      [] : [] ≈ []
      _-,_ : (ps : xs ≈ ys) (p : x ≡ y) → xs -, x ≈ ys -, y

    pattern _-refl ps = ps -, ≡.refl

    ≈⇒≡ : xs ≈ ys → xs ≡ ys
    ≈⇒≡ [] = ≡.refl
    ≈⇒≡ (ps -, p) = ≡.cong₂ _-,_ (≈⇒≡ ps) p

    refl-≈ : xs ≈ xs
    refl-≈ {xs = []} = []
    refl-≈ {xs = xs -, x} = refl-≈ -refl

    sym-≈ : xs ≈ ys → ys ≈ xs
    sym-≈ [] = []
    sym-≈ (qs -, q) = sym-≈ qs -, ≡.sym q

    identityˡ→ : (sp+ : Γ ∼+) (sp0 : ∼+-ll sp+ ∼0) → ∼+-rr sp+ ≈ Γ
    identityˡ→ [] zs = []
    identityˡ→ (as -u*) (zs -u*) = identityˡ→ as zs -refl
    identityˡ→ (as -lʳ) zs = identityˡ→ as zs -refl

    identityˡ← : Σ[ sp+ ∈ Γ ∼+ ] ∼+-ll sp+ ∼0 × ∼+-rr sp+ ≈ Γ
    identityˡ← {Γ = []} = [] , [] , []
    identityˡ← {Γ = Γ -u _} =
      ×.map _-u* (×.map _-u* _-refl) (identityˡ← {Γ = Γ})
    identityˡ← {Γ = Γ -l _} =
      ×.map _-lʳ (×.map id _-refl) (identityˡ← {Γ = Γ})

    identityʳ→ : (sp+ : Γ ∼+) (sp0 : ∼+-rr sp+ ∼0) → ∼+-ll sp+ ≈ Γ
    identityʳ→ [] zs = []
    identityʳ→ (as -u*) (zs -u*) = identityʳ→ as zs -refl
    identityʳ→ (as -lˡ) zs = identityʳ→ as zs -refl

    identityʳ← : Σ[ sp+ ∈ Γ ∼+ ] ∼+-rr sp+ ∼0 × ∼+-ll sp+ ≈ Γ
    identityʳ← {Γ = []} = [] , [] , []
    identityʳ← {Γ = Γ -u _} =
      ×.map _-u* (×.map _-u* _-refl) (identityʳ← {Γ = Γ})
    identityʳ← {Γ = Γ -l _} =
      ×.map _-lˡ (×.map id _-refl) (identityʳ← {Γ = Γ})

    assoc→ : (sp : Γ ∼+) (spl : ∼+-ll sp ∼+) →
      Σ[ sp′ ∈ Γ ∼+ ] Σ[ spr ∈ ∼+-rr sp′ ∼+ ]
        ∼+-ll spl ≈ ∼+-ll sp′ × ∼+-rr spl ≈ ∼+-ll spr × ∼+-rr sp ≈ ∼+-rr spr
    assoc→ [] [] = [] , [] , [] , [] , []
    assoc→ (sp -u*) (spl -u*) =
      ×.map _-u* (×.map _-u* (×.map _-refl (×.map _-refl _-refl)))
      $ assoc→ sp spl
    assoc→ (sp -lˡ) (spl -lˡ) =
      ×.map _-lˡ (×.map id (×.map _-refl (×.map id id))) $ assoc→ sp spl
    assoc→ (sp -lˡ) (spl -lʳ) =
      ×.map _-lʳ (×.map _-lˡ (×.map id (×.map _-refl id))) $ assoc→ sp spl
    assoc→ (sp -lʳ) spl =
      ×.map _-lʳ (×.map _-lʳ (×.map id (×.map id _-refl))) $ assoc→ sp spl

    assoc← : (sp : Γ ∼+) (spr : ∼+-rr sp ∼+) →
      Σ[ sp′ ∈ Γ ∼+ ] Σ[ spl ∈ ∼+-ll sp′ ∼+ ]
        ∼+-ll sp ≈ ∼+-ll spl × ∼+-ll spr ≈ ∼+-rr spl × ∼+-rr spr ≈ ∼+-rr sp′
    assoc← [] [] = [] , [] , [] , [] , []
    assoc← (sp -u*) (spr -u*) =
      ×.map _-u* (×.map _-u* (×.map _-refl (×.map _-refl _-refl)))
      $ assoc← sp spr
    assoc← (sp -lˡ) spr =
      ×.map _-lˡ (×.map _-lˡ (×.map _-refl (×.map id id))) $ assoc← sp spr
    assoc← (sp -lʳ) (spr -lˡ) =
      ×.map _-lˡ (×.map _-lʳ (×.map id (×.map _-refl id))) $ assoc← sp spr
    assoc← (sp -lʳ) (spr -lʳ) =
      ×.map _-lʳ (×.map id (×.map id (×.map id _-refl))) $ assoc← sp spr

    comm : (sp : Γ ∼+) →
      Σ[ sp′ ∈ Γ ∼+ ] ∼+-rr sp ≈ ∼+-ll sp′ × ∼+-ll sp ≈ ∼+-rr sp′
    comm [] = [] , [] , []
    comm (sp -u*) = ×.map _-u* (×.map _-refl _-refl) $ comm sp
    comm (sp -lˡ) = ×.map _-lʳ (×.map id _-refl) $ comm sp
    comm (sp -lʳ) = ×.map _-lˡ (×.map _-refl id) $ comm sp

    0-dup : (sp0 : Γ ∼0) → Σ[ sp+ ∈ Γ ∼+ ] Γ ≈ ∼+-ll sp+ × Γ ≈ ∼+-rr sp+
    0-dup [] = [] , [] , []
    0-dup (zs -u*) = ×.map _-u* (×.map _-refl _-refl) $ 0-dup zs

    data _∋_ {A : Set a} : A ─Ctx → A → Set a where
      here : Γ ∼0 → Γ -, (m , x) ∋ x
      there : Γ ∋ x → Γ -u y ∋ x

    _─OpenType : Set a → Set (a ⊔ suc 0ℓ)
    A ─OpenType = A ─Ctx → Set

    record ℑ {A : Set a} (Γ : A ─Ctx) : Set a where
      constructor _✴⟨⟩
      field
        split : Γ ∼0

    record _✴_ {A : Set a} (T U : A ─OpenType) (Γ : A ─Ctx) : Set a where
      constructor _✴⟨_,_⟩
      field
        split : Γ ∼+
        T-prf : T (∼+-ll split)
        U-prf : U (∼+-rr split)

    record _─✴_ {A : Set a} (T U : A ─OpenType) (Γ : A ─Ctx) : Set a where
      constructor lam✴
      field app✴ : ∀ {Δ} (sp : Δ ∼+) → Γ ≈ ∼+-ll sp → T (∼+-rr sp) → U Δ
    open _─✴_ public

    record □ {A : Set a} (T : A ─OpenType) (Γ : A ─Ctx) : Set a where
      constructor _□⟨_⟩
      field
        clear : Γ ∼0
        T-prf : T Γ

    private
      variable
        S S′ T T′ U U′ V : A ─OpenType

    ✴-map : ∀[ T ⇒ T′ ] × ∀[ U ⇒ U′ ] → ∀[ (T ✴ U) ⇒ (T′ ✴ U′) ]
    ✴-map (f , g) (sp ✴⟨ x , y ⟩) = sp ✴⟨ f x , g y ⟩

    ✴-identityˡ→ : ∀[ ℑ ✴ T ⇒ T ]
    ✴-identityˡ→ {T = T} (as ✴⟨ zs ✴⟨⟩ , x ⟩)
      = subst T (≈⇒≡ (identityˡ→ as zs)) x

    ✴-identityˡ← : ∀[ T ⇒ ℑ ✴ T ]
    ✴-identityˡ← {T = T} x =
      let sp+ , sp0 , qs = identityˡ← in
      sp+ ✴⟨ sp0 ✴⟨⟩ , subst T (≡.sym (≈⇒≡ qs)) x ⟩

    ✴-identityʳ→ : ∀[ T ✴ ℑ ⇒ T ]
    ✴-identityʳ→ {T = T} (as ✴⟨ x , zs ✴⟨⟩ ⟩)
      = subst T (≈⇒≡ (identityʳ→ as zs)) x

    ✴-identityʳ← : ∀[ T ⇒ T ✴ ℑ ]
    ✴-identityʳ← {T = T} x =
      let sp+ , sp0 , qs = identityʳ← in
      sp+ ✴⟨ subst T (≡.sym (≈⇒≡ qs)) x , sp0 ✴⟨⟩ ⟩

    ✴-identity²→ : ∀[ ℑ ✴ ℑ ⇒ ℑ {A = A} ]
    ✴-identity²→ = ✴-identityˡ→
    ✴-identity²← : ∀[ ℑ {A = A} ⇒ ℑ ✴ ℑ ]
    ✴-identity²← = ✴-identityˡ←

    ✴-assoc→ : ∀[ ((T ✴ U) ✴ V) ⇒ (T ✴ (U ✴ V)) ]
    ✴-assoc→ {T = T} {U} {V} (xy+z ✴⟨ x+y ✴⟨ x , y ⟩ , z ⟩) =
      let x+yz , y+z , xq , yq , zq = assoc→ xy+z x+y in
      x+yz ✴⟨ subst T (≈⇒≡ xq) x ,
        y+z ✴⟨ subst U (≈⇒≡ yq) y , subst V (≈⇒≡ zq) z ⟩ ⟩

    ✴-assoc← : ∀[ (T ✴ (U ✴ V)) ⇒ ((T ✴ U) ✴ V) ]
    ✴-assoc← {T = T} {U} {V} (x+yz ✴⟨ x , y+z ✴⟨ y , z ⟩ ⟩) =
      let xy+z , x+y , xq , yq , zq = assoc← x+yz y+z in
      xy+z ✴⟨ x+y ✴⟨ subst T (≈⇒≡ xq) x , subst U (≈⇒≡ yq) y ⟩ ,
        subst V (≈⇒≡ zq) z ⟩

    ✴-comm : ∀[ (T ✴ U) ⇒ (U ✴ T) ]
    ✴-comm {T = T} {U} (sp ✴⟨ x , y ⟩) =
      let sp′ , xq , yq = comm sp in
      sp′ ✴⟨ subst U (≈⇒≡ xq) y , subst T (≈⇒≡ yq) x ⟩

    ✴-inter : ∀[ ((T ✴ T′) ✴ (U ✴ U′)) ⇒ ((T ✴ U) ✴ (T′ ✴ U′)) ]
    ✴-inter =
      ✴-assoc← ∘
      ✴-map (id , ✴-assoc→ ∘ ✴-map (✴-comm , id) ∘ ✴-assoc←)
      ∘ ✴-assoc→

    ∪-distribˡ-✴→ : (S ∪ T) ✴ U ⊆ (S ✴ U) ∪ (T ✴ U)
    ∪-distribˡ-✴→ (sp ✴⟨ inj₁ s , u ⟩) = inj₁ (sp ✴⟨ s , u ⟩)
    ∪-distribˡ-✴→ (sp ✴⟨ inj₂ t , u ⟩) = inj₂ (sp ✴⟨ t , u ⟩)

    f✴ : (S ✴ T ⊆ U) → (S ⊆ T ─✴ U)
    f✴ {S = S} h x .app✴ sp q y = h (sp ✴⟨ subst S (≈⇒≡ q) x , y ⟩)

    g✴ : (S ⊆ T ─✴ U) → (S ✴ T ⊆ U)
    g✴ h (sp ✴⟨ x , y ⟩) = h x .app✴ sp refl-≈ y

    eval✴ : (S ─✴ T) ✴ S ⊆ T
    eval✴ = g✴ id

    □-map : S ⊆ T → □ S ⊆ □ T
    □-map f (zs □⟨ x ⟩) = zs □⟨ f x ⟩

    □-del : ∀[ □ T ⇒ ℑ ]
    □-del (zs □⟨ _ ⟩) = zs ✴⟨⟩

    □-dup : ∀[ □ T ⇒ (□ T ✴ □ T) ]
    □-dup {T = T} b@(zs □⟨ x ⟩) =
      let as , ps , qs = 0-dup zs in
      as ✴⟨ subst (□ T) (≈⇒≡ ps) b , subst (□ T) (≈⇒≡ qs) b ⟩

  infixr 70 _⊸_
  infix 20 _⊢_ [_]_⊨_ _⊨_ [_]_n⊢_ _ne⊢_ _nf⊢_

  [_]_⊨_ = id

  data Ty : Set where
    ι : Ty
    _⊸_ : (A B : Ty) → Ty
    ! : (A : Ty) → Ty

  Ctx : Set
  Ctx = Ty ─Ctx

  OpenType = Ty ─OpenType

  _─OpenFam : Set → Set₁
  I ─OpenFam = Ctx → I → Set
  OpenFam = Ty ─OpenFam

  private
    variable
      A B C : Ty
      Γ Δ Θ : Ctx
      𝓥 : OpenFam
      m : Mode

  data _⊢_ : OpenFam where
    var : ∀[ _∋ A ⇒ _⊢ A ]
    ⊸I : ∀[ _⊢ B ∘ _-l A ⇒ _⊢ A ⊸ B ]
    ⊸E : ∀[ (_⊢ A ⊸ B ✴ _⊢ A) ⇒ _⊢ B ]
    !I : ∀[ □ (_⊢ A) ⇒ _⊢ ! A ]
    !E : ∀[ (_⊢ ! A ✴ (_⊢ C ∘ _-u A)) ⇒ _⊢ C ]

  data [_]_⇒ᵉ_ (𝓥 : Ty ─OpenFam) : Ctx ─OpenFam where
    [] : ∀[ ℑ ⇒ [ 𝓥 ]_⇒ᵉ [] ]
    snoc-l : ∀[ ([ 𝓥 ]_⇒ᵉ Δ ✴ [ 𝓥 ]_⊨ A) ⇒ [ 𝓥 ]_⇒ᵉ Δ -l A ]
    snoc-u : ∀[ ([ 𝓥 ]_⇒ᵉ Δ ✴ □ ([ 𝓥 ]_⊨ A)) ⇒ [ 𝓥 ]_⇒ᵉ Δ -u A ]

  _⇒ʳ_ : Ctx ─OpenFam
  _⇒ʳ_ = [ _∋_ ]_⇒ᵉ_

  Renameable : OpenType → Set
  Renameable T = ∀ {Γ Δ} → Γ ⇒ʳ Δ → T Δ → T Γ

  module _ {𝓥 : OpenFam} where

    0-env : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ∼0 → ℑ Γ
    0-env ([] spΓ) [] = spΓ
    0-env (snoc-u x) (spΔ -u*) =
      ✴-identity²→ ∘ ✴-map ((λ ρ → 0-env ρ spΔ) , □-del) $ x

    +-env : [ 𝓥 ] Γ ⇒ᵉ Δ → (sp : Δ ∼+) → ([ 𝓥 ]_⇒ᵉ ∼+-ll sp ✴ [ 𝓥 ]_⇒ᵉ ∼+-rr sp) Γ
    +-env ([] spΓ) [] = ✴-map ([] , []) (✴-identity²← spΓ)
    +-env (snoc-u x) (spΔ -u*) =
      ✴-map (snoc-u , snoc-u) ∘ ✴-inter ∘
      ✴-map ((λ ρ → +-env ρ spΔ) , □-dup)
      $ x
    +-env (snoc-l x) (spΔ -lˡ) =
      ✴-map (snoc-l , id) ∘ (✴-assoc← ∘ ✴-map (id , ✴-comm) ∘ ✴-assoc→) ∘
      ✴-map ((λ ρ → +-env ρ spΔ) , id)
      $ x
    +-env (snoc-l x) (spΔ -lʳ) =
      ✴-map (id , snoc-l) ∘ ✴-assoc→ ∘
      ✴-map ((λ ρ → +-env ρ spΔ) , id)
      $ x

    lookup : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ∋ A → 𝓥 Γ A
    lookup (snoc-l (as ✴⟨ ρ , v ⟩)) (here zs)
      rewrite ≈⇒≡ (identityˡ→ as (0-env ρ zs .ℑ.split)) = v
    lookup (snoc-u (as ✴⟨ ρ , _ □⟨ v ⟩ ⟩)) (here zs)
      rewrite ≈⇒≡ (identityˡ→ as (0-env ρ zs .ℑ.split)) = v
    lookup (snoc-u (as ✴⟨ ρ , zs □⟨ _ ⟩ ⟩)) (there x)
      rewrite ≈⇒≡ (identityʳ→ as zs) = lookup ρ x

  ren^□ : ∀ {T} → Renameable T → Renameable (□ T)
  ren^□ ren ρ (sp □⟨ x ⟩) = 0-env ρ sp .ℑ.split □⟨ ren ρ x ⟩

  infix 50 _++_

  data CtxExt : Set where
    [] : CtxExt
    _,-_ : Ty → CtxExt → CtxExt

  _++_ : Ctx → CtxExt → Ctx
  Γ ++ [] = Γ
  Γ ++ (A ,- Ξ) = (Γ -u A) ++ Ξ

  ++∼0 : ∀ Ξ → Γ ∼0 → (Γ ++ Ξ) ∼0
  ++∼0 [] sp = sp
  ++∼0 (A ,- Ξ) sp = ++∼0 Ξ (sp -u*)

  ++∼+ : ∀ Ξ → Γ ∼+ → (Γ ++ Ξ) ∼+
  ++∼+ [] sp = sp
  ++∼+ (A ,- Ξ) sp = ++∼+ Ξ (sp -u*)

  ++∼+-ll : ∀ Ξ (sp : Γ ∼+) → ∼+-ll (++∼+ Ξ sp) ≈ ∼+-ll sp ++ Ξ
  ++∼+-ll [] sp = refl-≈
  ++∼+-ll (A ,- Ξ) sp = ++∼+-ll Ξ (sp -u*)

  ++∼+-rr : ∀ Ξ (sp : Γ ∼+) → ∼+-rr (++∼+ Ξ sp) ≈ ∼+-rr sp ++ Ξ
  ++∼+-rr [] sp = refl-≈
  ++∼+-rr (A ,- Ξ) sp = ++∼+-rr Ξ (sp -u*)

  ++-there : ∀ Ξ → Γ ∋ A → Γ ++ Ξ ∋ A
  ++-there [] i = i
  ++-there (A ,- Ξ) i = ++-there Ξ (there i)

  id+extᵉ : (∀ {Γ A} → Γ ∋ A → 𝓥 Γ A) → ∀ {Γ} Ξ → [ 𝓥 ] Γ ++ Ξ ⇒ᵉ Γ
  id+extᵉ pure {[]} Ξ = [] $′ ++∼0 Ξ [] ✴⟨⟩
  id+extᵉ pure {Γ -l A} Ξ = snoc-l $′
    let sp+ , sp0 , qs = identityʳ← in
    ++∼+ Ξ (sp+ -lʳ)
      ✴⟨ subst ([ _ ]_⇒ᵉ _)
        (≡.sym (≡.trans (≈⇒≡ (++∼+-ll Ξ (sp+ -lʳ))) (≡.cong (_++ Ξ) (≈⇒≡ qs))))
        (id+extᵉ pure Ξ)
      , pure (subst (_∋ A) (≡.sym (≈⇒≡ (++∼+-rr Ξ (sp+ -lʳ))))
          (++-there Ξ (here sp0))) ⟩
  id+extᵉ pure {Γ -u A} Ξ = snoc-u $′
    let sp+ , sp0 , qs = identityʳ← in
    ++∼+ Ξ (sp+ -u*)
      ✴⟨ subst ([ _ ]_⇒ᵉ _)
        (≡.sym (≡.trans (≈⇒≡ (++∼+-ll Ξ (sp+ -u*)))
          (≡.cong (_++ (A ,- Ξ)) (≈⇒≡ qs))))
        (id+extᵉ pure (A ,- Ξ))
      , subst _∼0 (≡.sym (≈⇒≡ (++∼+-rr Ξ (sp+ -u*)))) (++∼0 Ξ (sp0 -u*))
        □⟨ pure (subst (_∋ A) (≡.sym (≈⇒≡ (++∼+-rr Ξ (sp+ -u*))))
            (++-there Ξ (here sp0))) ⟩ ⟩

  idᵉ : (∀ {Γ A} → Γ ∋ A → 𝓥 Γ A) → ∀ {Γ} → [ 𝓥 ] Γ ⇒ᵉ Γ
  idᵉ pure = id+extᵉ pure []

  compᵉ : ∀ {𝓤 𝓥 𝓦} → (∀ {Γ Δ} → [ 𝓤 ] Γ ⇒ᵉ Δ → 𝓥 Δ ⊆ 𝓦 Γ) →
    ∀ {Γ Δ Θ} → [ 𝓤 ] Γ ⇒ᵉ Δ → [ 𝓥 ] Δ ⇒ᵉ Θ → [ 𝓦 ] Γ ⇒ᵉ Θ
  compᵉ bind ρ ([] (sp ✴⟨⟩)) = [] $ 0-env ρ sp
  compᵉ bind ρ (snoc-l (sp ✴⟨ σ , v ⟩)) = snoc-l $
    ✴-map ((λ ρ′ → compᵉ bind ρ′ σ) , (λ ρ′ → bind ρ′ v)) $ +-env ρ sp
  compᵉ bind ρ (snoc-u (sp+ ✴⟨ σ , sp0 □⟨ v ⟩ ⟩)) = snoc-u $
    ✴-map ((λ ρ′ → compᵉ bind ρ′ σ) ,
      (λ ρ′ → 0-env ρ′ sp0 .ℑ.split □⟨ bind ρ′ v ⟩))
    $ +-env ρ sp+

  idʳ : Γ ⇒ʳ Γ
  idʳ = idᵉ id

  _>>ʳ_ : Γ ⇒ʳ Δ → Δ ⇒ʳ Θ → Γ ⇒ʳ Θ
  ρ >>ʳ σ = compᵉ (λ τ → lookup τ) ρ σ

  thereʳ : Γ ⇒ʳ Δ → Γ -u A ⇒ʳ Δ
  thereʳ ([] (sp ✴⟨⟩)) = [] $′ sp -u* ✴⟨⟩
  thereʳ (snoc-l (sp ✴⟨ ρ , v ⟩)) = snoc-l $′ sp -u* ✴⟨ thereʳ ρ , there v ⟩
  thereʳ (snoc-u (sp ✴⟨ ρ , cl □⟨ v ⟩ ⟩)) =
    snoc-u $′ sp -u* ✴⟨ thereʳ ρ , cl -u* □⟨ there v ⟩ ⟩

  liftᵉl : (∀ {Γ A} → Γ ∋ A → 𝓥 Γ A) → [ 𝓥 ] Γ ⇒ᵉ Δ → [ 𝓥 ] Γ -l A ⇒ᵉ Δ -l A
  liftᵉl pure ρ = snoc-l $′
    let sp+ , sp0 , qs = identityʳ← in
    sp+ -lʳ ✴⟨ subst ([ _ ]_⇒ᵉ _) (≡.sym (≈⇒≡ qs)) ρ , pure (here sp0) ⟩

  liftᵉu : (∀ {A} → Renameable ([ 𝓥 ]_⊨ A)) → (∀ {Γ A} → Γ ∋ A → 𝓥 Γ A) →
    [ 𝓥 ] Γ ⇒ᵉ Δ → [ 𝓥 ] Γ -u A ⇒ᵉ Δ -u A
  liftᵉu {Γ = Γ} ren^𝓥 pure ρ = snoc-u $′
    let sp+ , sp0 , qs = identityʳ← in
    sp+ -u*
      ✴⟨ compᵉ (λ σ → ren^𝓥 σ) (thereʳ (subst (∼+-ll sp+ ⇒ʳ_) (≈⇒≡ qs) idʳ)) ρ
      , sp0 -u* □⟨ pure (here sp0) ⟩ ⟩

  □ʳ : OpenType → OpenType
  □ʳ T Γ = ∀ {Δ} → Δ ⇒ʳ Γ → T Δ

  record Sem (𝓥 𝓒 : OpenFam) : Set where
    field
      ren^𝓥 : ∀ {Γ Δ A} → Γ ⇒ʳ Δ → 𝓥 Δ A → 𝓥 Γ A
      ⟦var⟧ : ∀[ 𝓥 ⇒ 𝓒 ]
      ⟦⊸I⟧ : ∀ {A B} → □ʳ ([ 𝓥 ]_⊨ A ─✴ [ 𝓒 ]_⊨ B) ⊆ [ 𝓒 ]_⊨ A ⊸ B
      ⟦⊸E⟧ : ∀ {A B} → [ 𝓒 ]_⊨ A ⊸ B ✴ [ 𝓒 ]_⊨ A ⊆ [ 𝓒 ]_⊨ B
      ⟦!I⟧ : ∀ {A} → □ ([ 𝓒 ]_⊨ A) ⊆ [ 𝓒 ]_⊨ ! A
      ⟦!E⟧ : ∀ {A C} → [ 𝓒 ]_⊨ ! A ✴ □ʳ (□ ([ 𝓥 ]_⊨ A) ─✴ [ 𝓒 ]_⊨ C) ⊆ [ 𝓒 ]_⊨ C

    sem : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ⊢ A → 𝓒 Γ A
    sem ρ (var v) = ⟦var⟧ $ lookup ρ v
    sem ρ (⊸I M) = ⟦⊸I⟧ $ λ σ → lam✴ λ sp q v →
      sem
        (snoc-l (sp ✴⟨ compᵉ (λ σ → ren^𝓥 σ) (subst (_⇒ʳ _) (≈⇒≡ q) σ) ρ , v ⟩))
        M
    sem ρ (⊸E (sp ✴⟨ M , N ⟩)) = ⟦⊸E⟧ $
      ✴-map ((λ σ → sem σ M) , (λ τ → sem τ N)) $ +-env ρ sp
    sem ρ (!I (sp □⟨ M ⟩)) = ⟦!I⟧ $ 0-env ρ sp .ℑ.split □⟨ sem ρ M ⟩
    sem ρ (!E (sp ✴⟨ M , N ⟩)) = ⟦!E⟧ $
      ✴-map ((λ σ → sem σ M) ,
        (λ τ {_} υ → lam✴ λ sp′ q v →
          sem
            (snoc-u
              (sp′ ✴⟨ compᵉ (λ σ → ren^𝓥 σ) (subst (_⇒ʳ _) (≈⇒≡ q) υ) τ , v ⟩))
            N))
      $ +-env ρ sp

  data Noη : Ty → Set where
    ι-noη : Noη ι
    !-noη : Noη (! A)

  data NE/NF : Set where ne nf : NE/NF

  data [_]_n⊢_ : NE/NF → OpenFam
  _ne⊢_ _nf⊢_ : OpenFam
  _ne⊢_ = [ ne ]_n⊢_
  _nf⊢_ = [ nf ]_n⊢_

  data [_]_n⊢_ where
    var : _∋ A ⊆ _ne⊢ A
    ⊸E : _ne⊢ A ⊸ B ✴ _nf⊢ A ⊆ _ne⊢ B
    !E : _ne⊢ ! A ✴ _nf⊢ C ∘ _-u A ⊆ _ne⊢ C

    ⊸I : _nf⊢ B ∘ _-l A ⊆ _nf⊢ A ⊸ B
    !I : □ (_nf⊢ A) ⊆ _nf⊢ ! A
    emb : Noη A → _ne⊢ A ⊆ _nf⊢ A

  ren^n⊢ : ∀ {n} → Γ ⇒ʳ Δ → [ n ] Δ n⊢ A → [ n ] Γ n⊢ A
  ren^n⊢ ρ (var i) = var $′ lookup ρ i
  ren^n⊢ ρ (⊸E (sp ✴⟨ M , N ⟩)) = ⊸E $′
    ✴-map ((λ σ → ren^n⊢ σ M) , (λ τ → ren^n⊢ τ N))
    $ +-env ρ sp
  ren^n⊢ ρ (!E (sp ✴⟨ M , N ⟩)) = !E $′
    ✴-map ((λ σ → ren^n⊢ σ M) , (λ τ → ren^n⊢ (liftᵉu lookup id τ) N))
    $ +-env ρ sp
  ren^n⊢ ρ (⊸I M) = ⊸I $′ ren^n⊢ (liftᵉl id ρ) M
  ren^n⊢ ρ (!I (sp □⟨ M ⟩)) = !I $′ 0-env ρ sp .ℑ.split □⟨ ren^n⊢ ρ M ⟩
  ren^n⊢ ρ (emb e M) = emb e $′ ren^n⊢ ρ M

  _⊨_ : OpenFam
  Γ ⊨ ι = Γ ne⊢ ι
  Γ ⊨ A ⊸ B = □ʳ (_⊨ A ─✴ _⊨ B) Γ
  Γ ⊨ ! A = □ (_⊨ A) Γ ⊎ Γ ne⊢ ! A

  ren^⊨ : Γ ⇒ʳ Δ → Δ ⊨ A → Γ ⊨ A
  ren^⊨ {A = ι} ρ m = ren^n⊢ ρ m
  ren^⊨ {A = A ⊸ B} ρ m = λ σ → m (σ >>ʳ ρ)
  ren^⊨ {A = ! A} ρ m = ⊎.map (ren^□ ren^⊨ ρ) (ren^n⊢ ρ) m

  reify : ∀ A → _⊨ A ⊆ _nf⊢ A
  reflect : ∀ A → _ne⊢ A ⊆ _⊨ A

  reify ι m = emb ι-noη m
  reify (A ⊸ B) m = ⊸I $′
    let sp+ , sp0 , qs = identityʳ← in
    reify B (m idʳ .app✴ (sp+ -lʳ) (sym-≈ qs) (reflect A (var (here sp0))))
  reify (! A) (inj₁ m) = !I $′ □-map (reify A) m
  reify (! A) (inj₂ M) = emb !-noη M

  reflect ι M = M
  reflect (A ⊸ B) M ρ .app✴ sp qs n =
    reflect B (⊸E (sp ✴⟨ subst (_ne⊢ _) (≈⇒≡ qs) (ren^n⊢ ρ M) , reify A n ⟩))
  reflect (! A) M = inj₂ M

  module _ where
    open Sem

    Eval : Sem _⊨_ _⊨_
    Eval .ren^𝓥 = ren^⊨
    Eval .⟦var⟧ = id
    Eval .⟦⊸I⟧ = id
    Eval .⟦⊸E⟧ = eval✴ ∘ ✴-map ((λ f → f idʳ) , id)
    Eval .⟦!I⟧ = inj₁
    Eval .⟦!E⟧ =
      [ eval✴ ∘ ✴-map ((λ f → f idʳ) , id) ∘ ✴-comm
      , reflect _ ∘ !E ∘′ ✴-map (id , reify _ ∘ (λ f →
          let sp+ , sp0 , qs = identityʳ← in
          f (thereʳ idʳ) .app✴ (sp+ -u*) (sym-≈ qs -refl)
            (sp0 -u* □⟨ reflect _ (var (here sp0)) ⟩)))
      ]′ ∘ ∪-distribˡ-✴→

    eval : [ _⊨_ ] Γ ⇒ᵉ Δ → Δ ⊢ A → Γ ⊨ A
    eval = sem Eval
