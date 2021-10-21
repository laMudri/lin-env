module Modal.DILL where

  open import Data.Product
  open import Function.Base using (_$_; id; _∘_)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Relation.Nary

  module _ where

    private
      variable
        a ℓ : Level
        A : Set a

    infixl 50 _-,_ _-u_ _-l_ _-u* _-lˡ _-lʳ _-refl
    infix 40 _∼0 _∼[_+_] _≈_ _∋_
    infixr 7 _✴_

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

    data _∼[_+_] {A : Set a} : (Γ Δ Θ : A ─Ctx) → Set a where
      [] : [] ∼[ [] + [] ]
      _-u*  : Γ ∼[ Δ + Θ ] → Γ -u x ∼[ Δ -u x + Θ -u x ]
      _-lˡ : Γ ∼[ Δ + Θ ] → Γ -l x ∼[ Δ -l x + Θ      ]
      _-lʳ : Γ ∼[ Δ + Θ ] → Γ -l x ∼[ Δ      + Θ -l x ]

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

    identityˡ→ : ∃⟨ Γ ∼[_+ Δ ] ∩ _∼0 ⟩ → Γ ≈ Δ
    identityˡ→ (_ , [] , zs) = []
    identityˡ→ (_ , as -u* , zs -u*) = identityˡ→ (_ , as , zs) -refl
    identityˡ→ (_ , as -lʳ , zs) = identityˡ→ (_ , as , zs) -refl

    identityˡ← : Γ ≈ Δ → ∃⟨ Γ ∼[_+ Δ ] ∩ _∼0 ⟩
    identityˡ← [] = _ , [] , []
    identityˡ← (_-,_ {x = unr , _} ps ≡.refl) =
      let _ , as , zs = identityˡ← ps in
      _ , as -u* , zs -u*
    identityˡ← (_-,_ {x = lin , _} ps ≡.refl) =
      let _ , as , zs = identityˡ← ps in
      _ , as -lʳ , zs

    identityʳ→ : ∃⟨ Γ ∼[ Δ +_] ∩ _∼0 ⟩ → Γ ≈ Δ
    identityʳ→ (_ , [] , zs) = []
    identityʳ→ (_ , as -u* , zs -u*) = identityʳ→ (_ , as , zs) -refl
    identityʳ→ (_ , as -lˡ , zs) = identityʳ→ (_ , as , zs) -refl

    identityʳ← : Γ ≈ Δ → ∃⟨ Γ ∼[ Δ +_] ∩ _∼0 ⟩
    identityʳ← [] = _ , [] , []
    identityʳ← (_-,_ {x = unr , _} ps ≡.refl) =
      let _ , as , zs = identityʳ← ps in
      _ , as -u* , zs -u*
    identityʳ← (_-,_ {x = lin , _} ps ≡.refl) =
      let _ , as , zs = identityʳ← ps in
      _ , as -lˡ , zs

    0-dup : Γ ∼0 → Γ ∼[ Γ + Γ ]
    0-dup [] = []
    0-dup (zs -u*) = 0-dup zs -u*

    assoc→ : ∃⟨ Γ ∼[_+ Λ ] ∩ _∼[ Δ + Θ ] ⟩ → ∃⟨ Γ ∼[ Δ +_] ∩ _∼[ Θ + Λ ] ⟩
    assoc→ (_ , [] , []) = _ , [] , []
    assoc→ (_ , as -u* , bs -u*) =
      let _ , as′ , bs′ = assoc→ (_ , as , bs) in
      _ , as′ -u* , bs′ -u*
    assoc→ (_ , as -lˡ , bs -lˡ) =
      let _ , as′ , bs′ = assoc→ (_ , as , bs) in
      _ , as′ -lˡ , bs′
    assoc→ (_ , as -lˡ , bs -lʳ) =
      let _ , as′ , bs′ = assoc→ (_ , as , bs) in
      _ , as′ -lʳ , bs′ -lˡ
    assoc→ (_ , as -lʳ , bs) =
      let _ , as′ , bs′ = assoc→ (_ , as , bs) in
      _ , as′ -lʳ , bs′ -lʳ

    assoc← : ∃⟨ Γ ∼[ Δ +_] ∩ _∼[ Θ + Λ ] ⟩ → ∃⟨ Γ ∼[_+ Λ ] ∩ _∼[ Δ + Θ ] ⟩
    assoc← (_ , [] , []) = _ , [] , []
    assoc← (_ , as -u* , bs -u*) =
      let _ , as′ , bs′ = assoc← (_ , as , bs) in
      _ , as′ -u* , bs′ -u*
    assoc← (_ , as -lˡ , bs) =
      let _ , as′ , bs′ = assoc← (_ , as , bs) in
      _ , as′ -lˡ , bs′ -lˡ
    assoc← (_ , as -lʳ , bs -lˡ) =
      let _ , as′ , bs′ = assoc← (_ , as , bs) in
      _ , as′ -lˡ , bs′ -lʳ
    assoc← (_ , as -lʳ , bs -lʳ) =
      let _ , as′ , bs′ = assoc← (_ , as , bs) in
      _ , as′ -lʳ , bs′

    comm : Γ ∼[ Δ + Θ ] → Γ ∼[ Θ + Δ ]
    comm [] = []
    comm (as -u*) = comm as -u*
    comm (as -lˡ) = comm as -lʳ
    comm (as -lʳ) = comm as -lˡ

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
        {ΓT ΓU} : A ─Ctx
        split : Γ ∼[ ΓT + ΓU ]
        T-prf : T ΓT
        U-prf : U ΓU

    record □ {A : Set a} (T : A ─OpenType) (Γ : A ─Ctx) : Set a where
      constructor _□⟨_⟩
      field
        clear : Γ ∼0
        T-prf : T Γ

    private
      variable
        T T′ U U′ V : A ─OpenType

    ✴-map : ∀[ T ⇒ T′ ] × ∀[ U ⇒ U′ ] → ∀[ (T ✴ U) ⇒ (T′ ✴ U′) ]
    ✴-map (f , g) (sp ✴⟨ x , y ⟩) = sp ✴⟨ f x , g y ⟩

    ✴-identityˡ→ : ∀[ ℑ ✴ T ⇒ T ]
    ✴-identityˡ→ (as ✴⟨ zs ✴⟨⟩ , x ⟩)
      with ≡.refl ← ≈⇒≡ (identityˡ→ (_ , as , zs)) = x

    ✴-identityˡ← : ∀[ T ⇒ ℑ ✴ T ]
    ✴-identityˡ← x =
      let _ , as , zs = identityˡ← refl-≈ in as ✴⟨ zs ✴⟨⟩ , x ⟩

    ✴-identityʳ→ : ∀[ T ✴ ℑ ⇒ T ]
    ✴-identityʳ→ (as ✴⟨ x , zs ✴⟨⟩ ⟩)
      with ≡.refl ← ≈⇒≡ (identityʳ→ (_ , as , zs)) = x

    ✴-identityʳ← : ∀[ T ⇒ T ✴ ℑ ]
    ✴-identityʳ← x =
      let _ , as , zs = identityʳ← refl-≈ in as ✴⟨ x , zs ✴⟨⟩ ⟩

    ✴-identity²→ : ∀[ ℑ ✴ ℑ ⇒ ℑ {A = A} ]
    ✴-identity²→ = ✴-identityˡ→
    ✴-identity²← : ∀[ ℑ {A = A} ⇒ ℑ ✴ ℑ ]
    ✴-identity²← = ✴-identityˡ←

    ✴-assoc→ : ∀[ ((T ✴ U) ✴ V) ⇒ (T ✴ (U ✴ V)) ]
    ✴-assoc→ (xy+z ✴⟨ x+y ✴⟨ x , y ⟩ , z ⟩) =
      let _ , x+yz , y+z = assoc→ (_ , xy+z , x+y) in
      x+yz ✴⟨ x , y+z ✴⟨ y , z ⟩ ⟩

    ✴-assoc← : ∀[ (T ✴ (U ✴ V)) ⇒ ((T ✴ U) ✴ V) ]
    ✴-assoc← (x+yz ✴⟨ x , y+z ✴⟨ y , z ⟩ ⟩) =
      let _ , xy+z , x+y = assoc← (_ , x+yz , y+z) in
      xy+z ✴⟨ x+y ✴⟨ x , y ⟩ , z ⟩

    ✴-comm : ∀[ (T ✴ U) ⇒ (U ✴ T) ]
    ✴-comm (sp ✴⟨ x , y ⟩) = comm sp ✴⟨ y , x ⟩

    ✴-inter : ∀[ ((T ✴ T′) ✴ (U ✴ U′)) ⇒ ((T ✴ U) ✴ (T′ ✴ U′)) ]
    ✴-inter =
      ✴-assoc← ∘
      ✴-map (id , ✴-assoc→ ∘ ✴-map (✴-comm , id) ∘ ✴-assoc←)
      ∘ ✴-assoc→
    -- ✴-inter (wx+yz ✴⟨ w+x ✴⟨ w , x ⟩ , y+z ✴⟨ y , z ⟩ ⟩) =
    --   let _ , w+xyz , x+yz = assoc→ (_ , wx+yz , w+x) in
    --   let _ , xy+z , x+y = assoc← (_ , x+yz , y+z) in
    --   let y+x = comm x+y in
    --   let _ , y+xz , x+z = assoc→ (_ , xy+z , y+x) in
    --   let _ , wy+xz , w+y = assoc← (_ , w+xyz , y+xz) in
    --   wy+xz ✴⟨ w+y ✴⟨ w , y ⟩ , x+z ✴⟨ x , z ⟩ ⟩

    □-del : ∀[ □ T ⇒ ℑ ]
    □-del (zs □⟨ _ ⟩) = zs ✴⟨⟩

    □-dup : ∀[ □ T ⇒ (□ T ✴ □ T) ]
    □-dup b@(zs □⟨ x ⟩) = 0-dup zs ✴⟨ b , b ⟩

  infixr 70 _⊸_
  infix 20 _⊢_ [_]_⊨_

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
      Γ Δ Δ0 Δ1 : Ctx
      𝓥 : OpenFam
      m : Mode

  data _⊢_ : OpenFam where
    var : ∀[ _∋ A ⇒ _⊢ A ]
    ⊸I : ∀[ _⊢ B ∘ _-l A ⇒ _⊢ A ⊸ B ]
    ⊸E : ∀[ (_⊢ A ⊸ B ✴ _⊢ A) ⇒ _⊢ B ]
    !I : ∀[ □ (_⊢ A) ⇒ _⊢ ! A ]
    !E : ∀[ (_⊢ ! A ✴ (_⊢ C ∘ _-u A)) ⇒ _⊢ C ]

  data [_]_⇒ᵉ_ (𝓥 : OpenFam) : (Γ Δ : Ctx) → Set where
    [] : ∀[ ℑ ⇒ [ 𝓥 ]_⇒ᵉ [] ]
    cons-l : ∀[ ([ 𝓥 ]_⇒ᵉ Δ ✴ [ 𝓥 ]_⊨ A) ⇒ [ 𝓥 ]_⇒ᵉ Δ -l A ]
    cons-u : ∀[ ([ 𝓥 ]_⇒ᵉ Δ ✴ □ ([ 𝓥 ]_⊨ A)) ⇒ [ 𝓥 ]_⇒ᵉ Δ -u A ]

  module _ {𝓥 : OpenFam} where

    0-env : ∃⟨ [ 𝓥 ] Γ ⇒ᵉ_ ∩ _∼0 ⟩ → ℑ Γ
    0-env (_ , ρ , spΔ) = go ρ spΔ
      where
      go : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ∼0 → ℑ Γ
      go ([] spΓ) [] = spΓ
      go (cons-u x) (spΔ -u*) =
        ✴-identity²→ ∘ ✴-map ((λ ρ → go ρ spΔ) , □-del) $ x
    -- 0-env (_ , [] spΓ , []) = spΓ
    -- 0-env (_ , cons-u (as ✴⟨ ρ , zs □⟨ _ ⟩ ⟩) , spΔ -u*) =
    --   ✴-identity²→ (as ✴⟨ 0-env (_ , ρ , spΔ) , zs ✴⟨⟩ ⟩)

    +-env : ∃⟨ [ 𝓥 ] Γ ⇒ᵉ_ ∩ _∼[ Δ0 + Δ1 ] ⟩ → ([ 𝓥 ]_⇒ᵉ Δ0 ✴ [ 𝓥 ]_⇒ᵉ Δ1) Γ
    +-env (_ , [] spΓ , []) = ✴-map ([] , []) (✴-identity²← spΓ)
    +-env (_ , cons-u x , spΔ -u*) =
      ✴-map (cons-u , cons-u) ∘ ✴-inter ∘
      ✴-map ((λ ρ → +-env (_ , ρ , spΔ)) , □-dup)
      $ x
    +-env (_ , cons-l x , spΔ -lˡ) =
      ✴-map (cons-l , id) ∘ (✴-assoc← ∘ ✴-map (id , ✴-comm) ∘ ✴-assoc→) ∘
      ✴-map ((λ ρ → +-env (_ , ρ , spΔ)) , id)
      $ x
    +-env (_ , cons-l x , spΔ -lʳ) =
      ✴-map (id , cons-l) ∘ ✴-assoc→ ∘
      ✴-map ((λ ρ → +-env (_ , ρ , spΔ)) , id)
      $ x

    lookup : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ∋ A → 𝓥 Γ A
    lookup (cons-l (as ✴⟨ ρ , v ⟩)) (here zs)
      with ≡.refl ← ≈⇒≡ (identityˡ→ (_ , as , 0-env (_ , ρ , zs) .ℑ.split)) = v
    lookup (cons-u (as ✴⟨ ρ , _ □⟨ v ⟩ ⟩)) (here zs)
      with ≡.refl ← ≈⇒≡ (identityˡ→ (_ , as , 0-env (_ , ρ , zs) .ℑ.split)) = v
    lookup (cons-u (as ✴⟨ ρ , zs □⟨ _ ⟩ ⟩)) (there x)
      with ≡.refl ← ≈⇒≡ (identityʳ→ (_ , as , zs)) = lookup ρ x

  record Kit (𝓥 : OpenFam) : Set where
    field
      wk : ∀[ [ 𝓥 ] Γ ⊨_ ⇒ [ 𝓥 ] Γ -u A ⊨_ ]
      vr : ∀[ _∋_ {A = Ty} ⇒ 𝓥 ]
      tm : ∀[ 𝓥 ⇒ _⊢_ ]

    wkᵉ : ∀[ [ 𝓥 ] Γ ⇒ᵉ_ ⇒ [ 𝓥 ] Γ -u A ⇒ᵉ_ ]
    wkᵉ ([] (zs ✴⟨⟩)) = [] ((zs -u*) ✴⟨⟩)
    wkᵉ (cons-l (as ✴⟨ ρ , v ⟩)) = cons-l ((as -u*) ✴⟨ wkᵉ ρ , wk v ⟩)
    wkᵉ (cons-u (as ✴⟨ ρ , zs □⟨ v ⟩ ⟩)) =
      cons-u ((as -u*) ✴⟨ wkᵉ ρ , zs -u* □⟨ wk v ⟩ ⟩)

    bind : [ 𝓥 ] Γ ⇒ᵉ Δ → [ 𝓥 ] Γ -, (m , A) ⇒ᵉ Δ -, (m , A)
    bind {m = unr} ρ =
      let _ , as , zs = identityʳ← refl-≈ in
      cons-u ((as -u*) ✴⟨ wkᵉ ρ , (zs -u*) □⟨ vr (here zs) ⟩ ⟩)
    bind {m = lin} ρ =
      let _ , as , zs = identityʳ← refl-≈ in
      cons-l ((as -lʳ) ✴⟨ ρ , vr (here zs) ⟩)

    trav : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ⊢ A → Γ ⊢ A
    trav ρ (var x) = tm (lookup ρ x)
    trav ρ (⊸I M) = ⊸I (trav (bind ρ) M)
    trav ρ (⊸E (sp ✴⟨ M , N ⟩)) =
      ⊸E ∘ ✴-map ((λ ρ → trav ρ M) , (λ ρ → trav ρ N)) $ +-env (_ , ρ , sp)
    trav ρ (!I (zs □⟨ M ⟩)) = !I (0-env (_ , ρ , zs) .ℑ.split □⟨ trav ρ M ⟩)
    trav ρ (!E (sp ✴⟨ M , N ⟩)) =
      !E ∘ ✴-map ((λ ρ → trav ρ M) , (λ ρ → trav (bind ρ) N))
      $ +-env (_ , ρ , sp)
