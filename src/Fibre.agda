module Fibre where

  open import Data.Product as ×
  open import Data.Sum as ⊎
  open import Function.Base using (_$_; _$′_; id; _∘_; _∘′_)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
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

    record Castable {a t} {A : Set a} (T : Tsil A → Set t) : Set (a ⊔ t) where
      field
        cast : ∀ {xs ys} → xs ≈ ys → T ys → T xs
    open Castable {{...}} public

    CastableF : ∀ {a b t} {A : Set a} {B : Set b} (T : Tsil A → B → Set t) →
      Set (a ⊔ b ⊔ t)
    CastableF T = ∀ {x} → Castable (λ Γ → T Γ x)

    instance
      Castable-∪ : ∀ {t u} {T : Tsil A → Set t} {U : Tsil A → Set u} →
        {{Castable T}} → {{Castable U}} → Castable (T ∪ U)
      Castable-∪ .cast ps (inj₁ x) = inj₁ (cast ps x)
      Castable-∪ .cast ps (inj₂ y) = inj₂ (cast ps y)

      Castable-∼0 : Castable (_∼0 {a} {A})
      Castable-∼0 .cast [] [] = []
      Castable-∼0 .cast (ps -refl) (zs -u*) = cast ps zs -u*

      Castable-∼+ : Castable (_∼+ {a} {A})
      Castable-∼+ .cast [] [] = []
      Castable-∼+ .cast (ps -refl) (as -u*) = cast ps as -u*
      Castable-∼+ .cast (ps -refl) (as -lˡ) = cast ps as -lˡ
      Castable-∼+ .cast (ps -refl) (as -lʳ) = cast ps as -lʳ

    ∼+-ll-cast : ∀ {Γ Δ : A ─Ctx} (qs : Γ ≈ Δ) (as : Δ ∼+) →
      ∼+-ll (cast qs as) ≈ ∼+-ll as
    ∼+-ll-cast [] [] = []
    ∼+-ll-cast (qs -refl) (as -u*) = ∼+-ll-cast qs as -refl
    ∼+-ll-cast (qs -refl) (as -lˡ) = ∼+-ll-cast qs as -refl
    ∼+-ll-cast (qs -refl) (as -lʳ) = ∼+-ll-cast qs as

    ∼+-rr-cast : ∀ {Γ Δ : A ─Ctx} (qs : Γ ≈ Δ) (as : Δ ∼+) →
      ∼+-rr (cast qs as) ≈ ∼+-rr as
    ∼+-rr-cast [] [] = []
    ∼+-rr-cast (qs -refl) (as -u*) = ∼+-rr-cast qs as -refl
    ∼+-rr-cast (qs -refl) (as -lˡ) = ∼+-rr-cast qs as
    ∼+-rr-cast (qs -refl) (as -lʳ) = ∼+-rr-cast qs as -refl

    -- ≈⇒≡ : xs ≈ ys → xs ≡ ys
    -- ≈⇒≡ [] = ≡.refl
    -- ≈⇒≡ (ps -, p) = ≡.cong₂ _-,_ (≈⇒≡ ps) p

    refl-≈ : xs ≈ xs
    refl-≈ {xs = []} = []
    refl-≈ {xs = xs -, x} = refl-≈ -refl

    trans-≈ : xs ≈ ys → ys ≈ zs → xs ≈ zs
    trans-≈ [] [] = []
    trans-≈ (ps -, p) (qs -, q) = trans-≈ ps qs -, ≡.trans p q

    sym-≈ : xs ≈ ys → ys ≈ xs
    sym-≈ [] = []
    sym-≈ (qs -, q) = sym-≈ qs -, ≡.sym q

    identityˡ→ : (sp+ : Γ ∼+) (sp0 : ∼+-ll sp+ ∼0) → Γ ≈ ∼+-rr sp+
    identityˡ→ [] zs = []
    identityˡ→ (as -u*) (zs -u*) = identityˡ→ as zs -refl
    identityˡ→ (as -lʳ) zs = identityˡ→ as zs -refl

    identityˡ← : Σ[ sp+ ∈ Γ ∼+ ] ∼+-ll sp+ ∼0 × ∼+-rr sp+ ≈ Γ
    identityˡ← {Γ = []} = [] , [] , []
    identityˡ← {Γ = Γ -u _} =
      ×.map _-u* (×.map _-u* _-refl) (identityˡ← {Γ = Γ})
    identityˡ← {Γ = Γ -l _} =
      ×.map _-lʳ (×.map id _-refl) (identityˡ← {Γ = Γ})

    identityʳ→ : (sp+ : Γ ∼+) (sp0 : ∼+-rr sp+ ∼0) → Γ ≈ ∼+-ll sp+
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
        ∼+-ll sp′ ≈ ∼+-ll spl × ∼+-ll spr ≈ ∼+-rr spl × ∼+-rr spr ≈ ∼+-rr sp
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
        ∼+-ll spl ≈ ∼+-ll sp × ∼+-rr spl ≈ ∼+-ll spr × ∼+-rr sp′ ≈ ∼+-rr spr
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
      Σ[ sp′ ∈ Γ ∼+ ] ∼+-ll sp′ ≈ ∼+-rr sp × ∼+-rr sp′ ≈ ∼+-ll sp
    comm [] = [] , [] , []
    comm (sp -u*) = ×.map _-u* (×.map _-refl _-refl) $ comm sp
    comm (sp -lˡ) = ×.map _-lʳ (×.map id _-refl) $ comm sp
    comm (sp -lʳ) = ×.map _-lˡ (×.map _-refl id) $ comm sp

    0-dup : (sp0 : Γ ∼0) → Σ[ sp+ ∈ Γ ∼+ ] ∼+-ll sp+ ≈ Γ × ∼+-rr sp+ ≈ Γ
    0-dup [] = [] , [] , []
    0-dup (zs -u*) = ×.map _-u* (×.map _-refl _-refl) $ 0-dup zs

    data _∋_ {A : Set a} : A ─Ctx → A → Set a where
      here : (zs : Γ ∼0) → Γ -, (m , x) ∋ x
      there : Γ ∋ x → Γ -u y ∋ x

    instance
      Castable-∋ : {A : Set a} → CastableF (_∋_ {A = A})
      Castable-∋ .cast (qs -refl) (here zs) = here (cast qs zs)
      Castable-∋ .cast (qs -refl) (there i) = there (cast qs i)

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
      field app✴ : ∀ {Δ} (sp : Δ ∼+) → ∼+-ll sp ≈ Γ → T (∼+-rr sp) → U Δ
    open _─✴_ public

    record □ {A : Set a} (T : A ─OpenType) (Γ : A ─Ctx) : Set a where
      constructor _□⟨_⟩
      field
        clear : Γ ∼0
        T-prf : T Γ

    private
      variable
        S S′ T T′ U U′ V : A ─OpenType

    instance
      Castable-ℑ : Castable (ℑ {a} {A})
      Castable-ℑ .cast qs (zs ✴⟨⟩) = cast qs zs ✴⟨⟩

      Castable-✴ : {{Castable T}} → {{Castable U}} → Castable (T ✴ U)
      Castable-✴ .cast qs (as ✴⟨ x , y ⟩) =
        cast qs as ✴⟨ cast (∼+-ll-cast qs as) x , cast (∼+-rr-cast qs as) y ⟩

      Castable-─✴ : {{Castable T}} → {{Castable U}} → Castable (T ─✴ U)
      Castable-─✴ .cast ps f .app✴ sp qs x = f .app✴ sp (trans-≈ qs ps) x

      Castable-□ : {{Castable T}} → Castable (□ T)
      Castable-□ .cast qs (zs □⟨ x ⟩) = cast qs zs □⟨ cast qs x ⟩

    ✴-map : ∀[ T ⇒ T′ ] × ∀[ U ⇒ U′ ] → ∀[ (T ✴ U) ⇒ (T′ ✴ U′) ]
    ✴-map (f , g) (sp ✴⟨ x , y ⟩) = sp ✴⟨ f x , g y ⟩

    ✴-identityˡ→ : {{Castable T}} → ℑ ✴ T ⊆ T
    ✴-identityˡ→ (as ✴⟨ zs ✴⟨⟩ , x ⟩) = cast (identityˡ→ as zs) x

    ✴-identityˡ← : {{Castable T}} → T ⊆ ℑ ✴ T
    ✴-identityˡ← x =
      let sp+ , sp0 , qs = identityˡ← in
      sp+ ✴⟨ sp0 ✴⟨⟩ , cast qs x ⟩

    ✴-identityʳ→ : {{Castable T}} → T ✴ ℑ ⊆ T
    ✴-identityʳ→ (as ✴⟨ x , zs ✴⟨⟩ ⟩) = cast (identityʳ→ as zs) x

    ✴-identityʳ← : {{Castable T}} → T ⊆ T ✴ ℑ
    ✴-identityʳ← x =
      let sp+ , sp0 , qs = identityʳ← in
      sp+ ✴⟨ cast qs x , sp0 ✴⟨⟩ ⟩

    ✴-identity²→ : ∀[ ℑ ✴ ℑ ⇒ ℑ {A = A} ]
    ✴-identity²→ = ✴-identityˡ→
    ✴-identity²← : ∀[ ℑ {A = A} ⇒ ℑ ✴ ℑ ]
    ✴-identity²← = ✴-identityˡ←

    ✴-assoc→ : {{Castable T}} → {{Castable U}} → {{Castable V}} →
      (T ✴ U) ✴ V ⊆ T ✴ (U ✴ V)
    ✴-assoc→ (xy+z ✴⟨ x+y ✴⟨ x , y ⟩ , z ⟩) =
      let x+yz , y+z , xq , yq , zq = assoc→ xy+z x+y in
      x+yz ✴⟨ cast xq x , y+z ✴⟨ cast yq y , cast zq z ⟩ ⟩

    ✴-assoc← : {{Castable T}} → {{Castable U}} → {{Castable V}} →
      T ✴ (U ✴ V) ⊆ (T ✴ U) ✴ V
    ✴-assoc← (x+yz ✴⟨ x , y+z ✴⟨ y , z ⟩ ⟩) =
      let xy+z , x+y , xq , yq , zq = assoc← x+yz y+z in
      xy+z ✴⟨ x+y ✴⟨ cast xq x , cast yq y ⟩ , cast zq z ⟩

    ✴-comm : {{Castable T}} → {{Castable U}} → T ✴ U ⊆ U ✴ T
    ✴-comm {T = T} {U} (sp ✴⟨ x , y ⟩) =
      let sp′ , xq , yq = comm sp in
      sp′ ✴⟨ cast xq y , cast yq x ⟩

    ✴-inter :
      {{Castable T}} → {{Castable T′}} → {{Castable U}} → {{Castable U′}} →
      ∀[ ((T ✴ T′) ✴ (U ✴ U′)) ⇒ ((T ✴ U) ✴ (T′ ✴ U′)) ]
    ✴-inter =
      ✴-assoc← ∘
      ✴-map (id , ✴-assoc→ ∘ ✴-map (✴-comm , id) ∘ ✴-assoc←)
      ∘ ✴-assoc→

    ∪-distribˡ-✴→ : (S ∪ T) ✴ U ⊆ (S ✴ U) ∪ (T ✴ U)
    ∪-distribˡ-✴→ (sp ✴⟨ inj₁ s , u ⟩) = inj₁ (sp ✴⟨ s , u ⟩)
    ∪-distribˡ-✴→ (sp ✴⟨ inj₂ t , u ⟩) = inj₂ (sp ✴⟨ t , u ⟩)

    f✴ : {{Castable S}} → (S ✴ T ⊆ U) → (S ⊆ T ─✴ U)
    f✴ {S = S} h x .app✴ sp q y = h (sp ✴⟨ cast q x , y ⟩)

    g✴ : (S ⊆ T ─✴ U) → (S ✴ T ⊆ U)
    g✴ h (sp ✴⟨ x , y ⟩) = h x .app✴ sp refl-≈ y

    eval✴ : (S ─✴ T) ✴ S ⊆ T
    eval✴ = g✴ id

    □-map : S ⊆ T → □ S ⊆ □ T
    □-map f (zs □⟨ x ⟩) = zs □⟨ f x ⟩

    □-del : ∀[ □ T ⇒ ℑ ]
    □-del (zs □⟨ _ ⟩) = zs ✴⟨⟩

    □-dup : {{Castable T}} → ∀[ □ T ⇒ (□ T ✴ □ T) ]
    □-dup {T = T} b@(zs □⟨ x ⟩) =
      let as , ps , qs = 0-dup zs in
      as ✴⟨ cast ps b , cast qs b ⟩

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

  instance
    Castable-⇒ᵉˡ : {{CastableF 𝓥}} → Castable ([ 𝓥 ]_⇒ᵉ Δ)
    Castable-⇒ᵉˡ .cast qs ([] x) = [] (cast qs x)
    Castable-⇒ᵉˡ .cast qs (snoc-l x) = snoc-l (cast qs x)
    Castable-⇒ᵉˡ .cast qs (snoc-u x) = snoc-u (cast qs x)

    Castable-⇒ᵉʳ : Castable ([ 𝓥 ] Γ ⇒ᵉ_)
    Castable-⇒ᵉʳ .cast [] ([] x) = [] x
    Castable-⇒ᵉʳ .cast (qs -refl) (snoc-l (as ✴⟨ ρ , v ⟩)) =
      snoc-l (as ✴⟨ cast qs ρ , v ⟩)
    Castable-⇒ᵉʳ .cast (qs -refl) (snoc-u (as ✴⟨ ρ , bv ⟩)) =
      snoc-u (as ✴⟨ cast qs ρ , bv ⟩)

  _⇒ʳ_ : Ctx ─OpenFam
  _⇒ʳ_ = [ _∋_ ]_⇒ᵉ_

  record Renameable (T : OpenType) : Set where
    field ren : ∀ {Γ Δ} → Γ ⇒ʳ Δ → T Δ → T Γ
  open Renameable {{...}} public

  RenameableF : ∀ {I} (T : I ─OpenFam) → Set
  RenameableF T = ∀ {x} → Renameable (λ Γ → T Γ x)

  module _ {𝓥 : OpenFam} where

    0-env : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ∼0 → ℑ Γ
    0-env ([] spΓ) [] = spΓ
    0-env (snoc-u x) (spΔ -u*) =
      ✴-identity²→ ∘ ✴-map ((λ ρ → 0-env ρ spΔ) , □-del) $ x

    +-env : {{∀ {A} → Castable ([ 𝓥 ]_⊨ A)}} →
      [ 𝓥 ] Γ ⇒ᵉ Δ → (sp : Δ ∼+) → ([ 𝓥 ]_⇒ᵉ ∼+-ll sp ✴ [ 𝓥 ]_⇒ᵉ ∼+-rr sp) Γ
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

    lookup : {{CastableF 𝓥}} → [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ∋ A → 𝓥 Γ A
    lookup (snoc-l (as ✴⟨ ρ , v ⟩)) (here zs) =
      cast (identityˡ→ as (0-env ρ zs .ℑ.split)) v
    lookup (snoc-u (as ✴⟨ ρ , _ □⟨ v ⟩ ⟩)) (here zs) =
      cast (identityˡ→ as (0-env ρ zs .ℑ.split)) v
    lookup (snoc-u (as ✴⟨ ρ , zs □⟨ _ ⟩ ⟩)) (there x) =
      cast (identityʳ→ as zs) (lookup ρ x)

  instance
    ren^∋ : RenameableF _∋_
    ren^∋ .ren = lookup

    ren^□ : ∀ {T} → {{Renameable T}} → Renameable (□ T)
    ren^□ .ren ρ (sp □⟨ x ⟩) = 0-env ρ sp .ℑ.split □⟨ ren ρ x ⟩

  infix 50 _++_

  data CtxExt : Set where
    [] : CtxExt
    _,-_ : (A : Ty) → CtxExt → CtxExt

  _++_ : Ctx → CtxExt → Ctx
  Γ ++ [] = Γ
  Γ ++ (A ,- Ξ) = (Γ -u A) ++ Ξ

  ++-cong : ∀ {Γ Δ} Ξ → Γ ≈ Δ → Γ ++ Ξ ≈ Δ ++ Ξ
  ++-cong [] ps = ps
  ++-cong (A ,- Ξ) ps = ++-cong Ξ (ps -refl)

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

  id+extᵉ : {{CastableF 𝓥}} →
    (∀ {Γ A} → Γ ∋ A → 𝓥 Γ A) → ∀ {Γ} Ξ → [ 𝓥 ] Γ ++ Ξ ⇒ᵉ Γ
  id+extᵉ pure {[]} Ξ = [] $′ ++∼0 Ξ [] ✴⟨⟩
  id+extᵉ pure {Γ -l A} Ξ = snoc-l $′
    let sp+ , sp0 , qs = identityʳ← in
    ++∼+ Ξ (sp+ -lʳ)
      ✴⟨ cast
        (trans-≈ (++∼+-ll Ξ (sp+ -lʳ)) (++-cong Ξ qs))
        (id+extᵉ pure Ξ)
      , pure (cast (++∼+-rr Ξ (sp+ -lʳ)) (++-there Ξ (here sp0))) ⟩
  id+extᵉ pure {Γ -u A} Ξ = snoc-u $′
    let sp+ , sp0 , qs = identityʳ← in
    ++∼+ Ξ (sp+ -u*)
      ✴⟨ cast
        (trans-≈ (++∼+-ll Ξ (sp+ -u*)) (++-cong (A ,- Ξ) qs))
        (id+extᵉ pure (A ,- Ξ))
      , cast (++∼+-rr Ξ (sp+ -u*)) (++∼0 Ξ (sp0 -u*))
        □⟨ pure (cast (++∼+-rr Ξ (sp+ -u*)) (++-there Ξ (here sp0))) ⟩ ⟩

  idᵉ : {{CastableF 𝓥}} → (∀ {Γ A} → Γ ∋ A → 𝓥 Γ A) → ∀ {Γ} → [ 𝓥 ] Γ ⇒ᵉ Γ
  idᵉ pure = id+extᵉ pure []

  compᵉ : ∀ {𝓤 𝓥 𝓦} → {{CastableF 𝓤}} → (∀ {Γ Δ} → [ 𝓤 ] Γ ⇒ᵉ Δ → 𝓥 Δ ⊆ 𝓦 Γ) →
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

  liftᵉl : {{CastableF 𝓥}} → (∀ {Γ A} → Γ ∋ A → 𝓥 Γ A) →
    [ 𝓥 ] Γ ⇒ᵉ Δ → [ 𝓥 ] Γ -l A ⇒ᵉ Δ -l A
  liftᵉl pure ρ = snoc-l $′
    let sp+ , sp0 , qs = identityʳ← in
    sp+ -lʳ ✴⟨ cast qs ρ , pure (here sp0) ⟩

  liftᵉu : {{CastableF 𝓥}} → {{RenameableF 𝓥}} → (∀ {Γ A} → Γ ∋ A → 𝓥 Γ A) →
    [ 𝓥 ] Γ ⇒ᵉ Δ → [ 𝓥 ] Γ -u A ⇒ᵉ Δ -u A
  liftᵉu {Γ = Γ} pure ρ = snoc-u $′
    let sp+ , sp0 , qs = identityʳ← in
    sp+ -u*
      ✴⟨ compᵉ (λ σ → ren σ) (thereʳ (cast (sym-≈ qs) idʳ)) ρ
      , sp0 -u* □⟨ pure (here sp0) ⟩ ⟩

  □ʳ : OpenType → OpenType
  □ʳ T Γ = ∀ {Δ} → Δ ⇒ʳ Γ → T Δ

  instance
    Castable-□ʳ : ∀ {T} → Castable (□ʳ T)
    Castable-□ʳ .cast qs b ρ = b (cast (sym-≈ qs) ρ)

  record Sem (𝓥 𝓒 : OpenFam) : Set where
    field
      {{cast^𝓥}} : CastableF 𝓥
      {{ren^𝓥}} : ∀ {A} → Renameable ([ 𝓥 ]_⊨ A)
      ⟦var⟧ : ∀[ 𝓥 ⇒ 𝓒 ]
      ⟦⊸I⟧ : ∀ {A B} → □ʳ ([ 𝓥 ]_⊨ A ─✴ [ 𝓒 ]_⊨ B) ⊆ [ 𝓒 ]_⊨ A ⊸ B
      ⟦⊸E⟧ : ∀ {A B} → [ 𝓒 ]_⊨ A ⊸ B ✴ [ 𝓒 ]_⊨ A ⊆ [ 𝓒 ]_⊨ B
      ⟦!I⟧ : ∀ {A} → □ ([ 𝓒 ]_⊨ A) ⊆ [ 𝓒 ]_⊨ ! A
      ⟦!E⟧ : ∀ {A C} → [ 𝓒 ]_⊨ ! A ✴ □ʳ (□ ([ 𝓥 ]_⊨ A) ─✴ [ 𝓒 ]_⊨ C) ⊆ [ 𝓒 ]_⊨ C

    sem : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ⊢ A → 𝓒 Γ A
    sem ρ (var v) = ⟦var⟧ $ lookup ρ v
    sem ρ (⊸I M) = ⟦⊸I⟧ $ λ σ → lam✴ λ sp q v →
      sem
        (snoc-l (sp ✴⟨ compᵉ (λ σ → ren σ) (cast q σ) ρ , v ⟩))
        M
    sem ρ (⊸E (sp ✴⟨ M , N ⟩)) = ⟦⊸E⟧ $
      ✴-map ((λ σ → sem σ M) , (λ τ → sem τ N)) $ +-env ρ sp
    sem ρ (!I (sp □⟨ M ⟩)) = ⟦!I⟧ $ 0-env ρ sp .ℑ.split □⟨ sem ρ M ⟩
    sem ρ (!E (sp ✴⟨ M , N ⟩)) = ⟦!E⟧ $
      ✴-map ((λ σ → sem σ M) ,
        (λ τ {_} υ → lam✴ λ sp′ q v →
          sem
            (snoc-u
              (sp′ ✴⟨ compᵉ (λ σ → ren σ) (cast q υ) τ , v ⟩))
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

  instance
    Castable-n⊢ : ∀ {n A} → Castable ([ n ]_n⊢ A)
    Castable-n⊢ .cast qs (var i) = var $′ cast qs i
    Castable-n⊢ .cast qs (⊸E (sp ✴⟨ M , N ⟩)) = ⊸E $′
      cast qs sp ✴⟨ cast (∼+-ll-cast qs sp) M , cast (∼+-rr-cast qs sp) N ⟩
    Castable-n⊢ .cast qs (!E (sp ✴⟨ M , N ⟩)) = !E $′
      cast qs sp
        ✴⟨ cast (∼+-ll-cast qs sp) M , cast (∼+-rr-cast qs sp -refl) N ⟩
    Castable-n⊢ .cast qs (⊸I M) = ⊸I $′ cast (qs -refl) M
    Castable-n⊢ .cast qs (!I (cl □⟨ M ⟩)) = !I $′ cast qs cl □⟨ cast qs M ⟩
    Castable-n⊢ .cast qs (emb e M) = emb e $′ cast qs M

    ren^n⊢ : ∀ {n A} → Renameable ([ n ]_n⊢ A)
    ren^n⊢ .ren ρ (var i) = var $′ lookup ρ i
    ren^n⊢ .ren ρ (⊸E (sp ✴⟨ M , N ⟩)) = ⊸E $′
      ✴-map ((λ σ → ren σ M) , (λ τ → ren τ N))
      $ +-env ρ sp
    ren^n⊢ .ren ρ (!E (sp ✴⟨ M , N ⟩)) = !E $′
      ✴-map ((λ σ → ren σ M) , (λ τ → ren (liftᵉu id τ) N))
      $ +-env ρ sp
    ren^n⊢ .ren ρ (⊸I M) = ⊸I $′ ren (liftᵉl id ρ) M
    ren^n⊢ .ren ρ (!I (sp □⟨ M ⟩)) = !I $′ 0-env ρ sp .ℑ.split □⟨ ren ρ M ⟩
    ren^n⊢ .ren ρ (emb e M) = emb e $′ ren ρ M

  _⊨_ : OpenFam
  Γ ⊨ ι = Γ ne⊢ ι
  Γ ⊨ A ⊸ B = □ʳ (_⊨ A ─✴ _⊨ B) Γ
  Γ ⊨ ! A = □ (_⊨ A) Γ ⊎ Γ ne⊢ ! A

  instance
    Castable-⊨ : CastableF _⊨_
    Castable-⊨ {ι} .cast qs m = cast {{Castable-n⊢}} qs m
    Castable-⊨ {A ⊸ B} .cast qs m = cast {{Castable-□ʳ}} qs m
    Castable-⊨ { ! A} .cast qs m = cast {{Castable-∪}} qs m

    ren^⊨ : RenameableF _⊨_
    ren^⊨ {ι} .ren ρ m = ren^n⊢ .ren ρ m
    ren^⊨ {A ⊸ B} .ren ρ m = λ σ → m (σ >>ʳ ρ)
    ren^⊨ { ! A} .ren ρ m = ⊎.map (ren ρ) (ren ρ) m

  reify : ∀ A → _⊨ A ⊆ _nf⊢ A
  reflect : ∀ A → _ne⊢ A ⊆ _⊨ A

  reify ι m = emb ι-noη m
  reify (A ⊸ B) m = ⊸I $′
    let sp+ , sp0 , qs = identityʳ← in
    reify B (m idʳ .app✴ (sp+ -lʳ) qs (reflect A (var (here sp0))))
  reify (! A) (inj₁ m) = !I $′ □-map (reify A) m
  reify (! A) (inj₂ M) = emb !-noη M

  reflect ι M = M
  reflect (A ⊸ B) M ρ .app✴ sp qs n =
    reflect B (⊸E (sp ✴⟨ cast qs (ren ρ M) , reify A n ⟩))
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
          f (thereʳ idʳ) .app✴ (sp+ -u*) (qs -refl)
            (sp0 -u* □⟨ reflect _ (var (here sp0)) ⟩)))
      ]′ ∘ ∪-distribˡ-✴→

    eval : [ _⊨_ ] Γ ⇒ᵉ Δ → Δ ⊢ A → Γ ⊨ A
    eval = sem Eval
  {-
  -}
