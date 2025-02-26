module Modal.LnL where

  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product as ×
  open import Data.Sum as ⊎
  open import Data.Wrap
  open import Function.Base using (_$_; _$′_; id; _∘_; _∘′_; λ-; _$-; case_of_)
  open import Level
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
  open import Relation.Nary
  open import Relation.Unary using (_⊆_)

  module _ where

    private
      variable
        a ℓ : Level

    infix 80 _⊗l_ _×i_
    infixr 70 _⊸l_ _→i_
    infixl 50 _-,_ _-i_ _-l_ _-i* _-lˡ _-lʳ _-refl
    infix 40 _∼0 _∼[_+_] _∼_ _≈_
    infix 7 _✴_
    infixr 5 _─✴_

    data Tsil (A : Set a) : Set a where
      [] : Tsil A
      _-,_ : Tsil A → A → Tsil A

    data Mode : Set where
      lin int : Mode

    data Ty : Mode → Set where
      ιl : Ty lin
      ιi : Ty int
      _⊗l_ _⊸l_ : (A B : Ty lin) → Ty lin
      _×i_ _→i_ : (X Y : Ty int) → Ty int
      Fl : (X : Ty int) → Ty lin
      Gi : (A : Ty lin) → Ty int

    LCtx : Set
    LCtx = Tsil (∃ Ty)

    ICtx : Set
    ICtx = Tsil (Ty int)

    Ctx : Mode → Set
    Ctx lin = LCtx
    Ctx int = ICtx

    pattern _-i_ Γ x = Γ -, (int , x)
    pattern _-l_ Γ x = Γ -, (lin , x)

    private
      variable
        Γ Γl Γm Γr Δ : LCtx
        Θ Λ : ICtx
        m n : Mode
        A B C : Ty lin
        X Y Z : Ty int
        S T U : Ty m
        xs ys : Tsil _

    data _∼0 : LCtx → Set where
      [] : [] ∼0
      _-i* : Γ ∼0 → Γ -i X ∼0

    data _∼[_+_] : (Γ Γl Γr : LCtx) → Set where
      [] : [] ∼[ [] + [] ]
      _-i* : Γ ∼[ Γl + Γr ] → Γ -i X ∼[ Γl -i X + Γr -i X ]
      _-lˡ : Γ ∼[ Γl + Γr ] → Γ -l A ∼[ Γl -l A + Γr      ]
      _-lʳ : Γ ∼[ Γl + Γr ] → Γ -l A ∼[ Γl      + Γr -l A ]

    data _∼_ : LCtx → ICtx → Set where
      [] : [] ∼ []
      _-i* : Γ ∼ Θ → Γ -i X ∼ Θ -, X

    data _≈_ {A : Set a} : (xs ys : Tsil A) → Set a where
      [] : [] ≈ []
      _-,_ : ∀ {xs ys x y} (ps : xs ≈ ys) (p : x ≡ y) → xs -, x ≈ ys -, y

    pattern _-refl ps = ps -, ≡.refl

    ≈⇒≡ : xs ≈ ys → xs ≡ ys
    ≈⇒≡ [] = ≡.refl
    ≈⇒≡ (ps -, p) = ≡.cong₂ _-,_ (≈⇒≡ ps) p

    refl-≈ : xs ≈ xs
    refl-≈ {xs = []} = []
    refl-≈ {xs = xs -, x} = refl-≈ -refl

    identityˡ→ : ∃⟨ Γ ∼[_+ Δ ] ∩ _∼0 ⟩ → Γ ≈ Δ
    identityˡ→ (_ , [] , zs) = []
    identityˡ→ (_ , as -i* , zs -i*) = identityˡ→ (_ , as , zs) -refl
    identityˡ→ (_ , as -lʳ , zs) = identityˡ→ (_ , as , zs) -refl

    identityˡ← : Γ ≈ Δ → ∃⟨ Γ ∼[_+ Δ ] ∩ _∼0 ⟩
    identityˡ← [] = _ , [] , []
    identityˡ← (_-,_ {x = int , _} ps ≡.refl) =
      let _ , as , zs = identityˡ← ps in
      _ , as -i* , zs -i*
    identityˡ← (_-,_ {x = lin , _} ps ≡.refl) =
      let _ , as , zs = identityˡ← ps in
      _ , as -lʳ , zs

    identityʳ→ : ∃⟨ Γ ∼[ Δ +_] ∩ _∼0 ⟩ → Γ ≈ Δ
    identityʳ→ (_ , [] , zs) = []
    identityʳ→ (_ , as -i* , zs -i*) = identityʳ→ (_ , as , zs) -refl
    identityʳ→ (_ , as -lˡ , zs) = identityʳ→ (_ , as , zs) -refl

    identityʳ← : Γ ≈ Δ → ∃⟨ Γ ∼[ Δ +_] ∩ _∼0 ⟩
    identityʳ← [] = _ , [] , []
    identityʳ← (_-,_ {x = int , _} ps ≡.refl) =
      let _ , as , zs = identityʳ← ps in
      _ , as -i* , zs -i*
    identityʳ← (_-,_ {x = lin , _} ps ≡.refl) =
      let _ , as , zs = identityʳ← ps in
      _ , as -lˡ , zs

    identity²→ : Γ ∼[ Γl + Γr ] → Γl ∼0 → Γr ∼0 → Γ ≈ Γl × Γ ≈ Γr
    identity²→ sp+ sp0l sp0r =
      identityʳ→ (_ , sp+ , sp0r) , identityˡ→ (_ , sp+ , sp0l)

    0-dup : Γ ∼0 → Γ ∼[ Γ + Γ ]
    0-dup [] = []
    0-dup (zs -i*) = 0-dup zs -i*

    assoc→ : ∃⟨ Γ ∼[_+ Γr ] ∩ _∼[ Γl + Γm ] ⟩ → ∃⟨ Γ ∼[ Γl +_] ∩ _∼[ Γm + Γr ] ⟩
    assoc→ (_ , [] , []) = _ , [] , []
    assoc→ (_ , as -i* , bs -i*) =
      let _ , as′ , bs′ = assoc→ (_ , as , bs) in
      _ , as′ -i* , bs′ -i*
    assoc→ (_ , as -lˡ , bs -lˡ) =
      let _ , as′ , bs′ = assoc→ (_ , as , bs) in
      _ , as′ -lˡ , bs′
    assoc→ (_ , as -lˡ , bs -lʳ) =
      let _ , as′ , bs′ = assoc→ (_ , as , bs) in
      _ , as′ -lʳ , bs′ -lˡ
    assoc→ (_ , as -lʳ , bs) =
      let _ , as′ , bs′ = assoc→ (_ , as , bs) in
      _ , as′ -lʳ , bs′ -lʳ

    assoc← : ∃⟨ Γ ∼[ Γl +_] ∩ _∼[ Γm + Γr ] ⟩ → ∃⟨ Γ ∼[_+ Γr ] ∩ _∼[ Γl + Γm ] ⟩
    assoc← (_ , [] , []) = _ , [] , []
    assoc← (_ , as -i* , bs -i*) =
      let _ , as′ , bs′ = assoc← (_ , as , bs) in
      _ , as′ -i* , bs′ -i*
    assoc← (_ , as -lˡ , bs) =
      let _ , as′ , bs′ = assoc← (_ , as , bs) in
      _ , as′ -lˡ , bs′ -lˡ
    assoc← (_ , as -lʳ , bs -lˡ) =
      let _ , as′ , bs′ = assoc← (_ , as , bs) in
      _ , as′ -lˡ , bs′ -lʳ
    assoc← (_ , as -lʳ , bs -lʳ) =
      let _ , as′ , bs′ = assoc← (_ , as , bs) in
      _ , as′ -lʳ , bs′

    comm : Γ ∼[ Γl + Γr ] → Γ ∼[ Γr + Γl ]
    comm [] = []
    comm (as -i*) = comm as -i*
    comm (as -lˡ) = comm as -lʳ
    comm (as -lʳ) = comm as -lˡ

    ∼→0 : Γ ∼ Θ → Γ ∼0
    ∼→0 [] = []
    ∼→0 (sp -i*) = ∼→0 sp -i*

    0→ICtx : Γ ∼0 → ICtx
    0→ICtx [] = []
    0→ICtx {Γ = Γ -i X} (sp -i*) = 0→ICtx sp -, X

    0→∼ : (sp : Γ ∼0) → Γ ∼ 0→ICtx sp
    0→∼ [] = []
    0→∼ (sp -i*) = 0→∼ sp -i*

    ∼-total← : ∀ Θ → ∃⟨ _∼ Θ ⟩
    ∼-total← [] = _ , []
    ∼-total← (Θ -, X) = _ , ∼-total← Θ .proj₂ -i*

    ∼-func← : Γ ∼ Θ → Δ ∼ Θ → Γ ≈ Δ
    ∼-func← [] [] = []
    ∼-func← (relΓ -i*) (relΔ -i*) = ∼-func← relΓ relΔ -refl

    ∼-func→ : Γ ∼ Θ → Γ ∼ Λ → Θ ≈ Λ
    ∼-func→ [] [] = []
    ∼-func→ (relΘ -i*) (relΛ -i*) = ∼-func→ relΘ relΛ -refl

    record ℑ (Γ : LCtx) : Set where
      constructor _✴⟨⟩
      field
        split : Γ ∼0

    record _✴_ (T U : LCtx → Set) (Γ : LCtx) : Set where
      constructor _✴⟨_,_⟩
      field
        {ΓT ΓU} : LCtx
        split : Γ ∼[ ΓT + ΓU ]
        T-prf : T ΓT
        U-prf : U ΓU

    record _─✴_ (T U : LCtx → Set) (Γ : LCtx) : Set where
      constructor lam✴
      field app✴ : ∀ {ΓT ΓU} → ΓU ∼[ Γ + ΓT ] → T ΓT → U ΓU
    open _─✴_ public

    record F (T : ICtx → Set) (Γ : LCtx) : Set where
      constructor _F⟨_⟩
      field
        {ΘT} : ICtx
        split : Γ ∼ ΘT
        T-prf : T ΘT

    record G (T : LCtx → Set) (Θ : ICtx) : Set where
      constructor _G⟨_⟩
      field
        {ΓT} : LCtx
        split : ΓT ∼ Θ
        T-prf : T ΓT

    F? : ∀ {m} → (Ctx m → Set) → (LCtx → Set)
    F? {lin} T Γ = T Γ
    F? {int} T Γ = F T Γ

    map-✴ : {T U T′ U′ : LCtx → Set} → T ⊆ T′ → U ⊆ U′ → T ✴ U ⊆ T′ ✴ U′
    map-✴ f g (sp ✴⟨ t , u ⟩) = sp ✴⟨ f t , g u ⟩

    ✴-identityˡ→ : ∀ {T} → ℑ ✴ T ⊆ T
    ✴-identityˡ→ {T} (sp+ ✴⟨ sp0 ✴⟨⟩ , t ⟩) =
      let q = identityˡ→ (_ , sp+ , sp0) in
      ≡.subst T (≡.sym (≈⇒≡ q)) t

    ✴-identityˡ← : ∀ {T} → T ⊆ ℑ ✴ T
    ✴-identityˡ← t =
      let _ , sp+ , sp0 = identityˡ← refl-≈ in
      sp+ ✴⟨ sp0 ✴⟨⟩ , t ⟩

    ✴-identityʳ→ : ∀ {T} → T ✴ ℑ ⊆ T
    ✴-identityʳ→ {T} (sp+ ✴⟨ t , sp0 ✴⟨⟩ ⟩) =
      let q = identityʳ→ (_ , sp+ , sp0) in
      ≡.subst T (≡.sym (≈⇒≡ q)) t

    ✴-identityʳ← : ∀ {T} → T ⊆ T ✴ ℑ
    ✴-identityʳ← t =
      let _ , sp+ , sp0 = identityʳ← refl-≈ in
      sp+ ✴⟨ t , sp0 ✴⟨⟩ ⟩

    ✴-identity²→ : ℑ ✴ ℑ ⊆ ℑ
    ✴-identity²→ = ✴-identityˡ→

    ✴-identity²← : ℑ ⊆ ℑ ✴ ℑ
    ✴-identity²← = ✴-identityˡ←

    ✴-assoc→ : ∀ {S T U} → (S ✴ T) ✴ U ⊆ S ✴ (T ✴ U)
    ✴-assoc→ (spl ✴⟨ spr ✴⟨ s , t ⟩ , u ⟩) =
      let _ , spl′ , spr′ = assoc→ (_ , spl , spr) in
      spl′ ✴⟨ s , spr′ ✴⟨ t , u ⟩ ⟩

    ✴-assoc← : ∀ {S T U} → S ✴ (T ✴ U) ⊆ (S ✴ T) ✴ U
    ✴-assoc← (spl ✴⟨ s , spr ✴⟨ t , u ⟩ ⟩) =
      let _ , spl′ , spr′ = assoc← (_ , spl , spr) in
      spl′ ✴⟨ spr′ ✴⟨ s , t ⟩ , u ⟩

    ✴-comm : ∀ {T U} → T ✴ U ⊆ U ✴ T
    ✴-comm (sp ✴⟨ t , u ⟩) = comm sp ✴⟨ u , t ⟩

    ✴-exch : ∀ {S T U V} → (S ✴ T) ✴ (U ✴ V) ⊆ (S ✴ U) ✴ (T ✴ V)
    ✴-exch =
      ✴-assoc→ ∘ map-✴ (✴-assoc← ∘ map-✴ id ✴-comm ∘ ✴-assoc→) id ∘ ✴-assoc←

    eval✴ : ∀ {T U} → (T ─✴ U) ✴ T ⊆ U
    eval✴ (sp ✴⟨ f , t ⟩) = f .app✴ sp t

    uncurry✴ : ∀ {S T U} → (S ─✴ T ─✴ U) ⊆ (S ✴ T ─✴ U)
    uncurry✴ f .app✴ spr (spl ✴⟨ s , t ⟩) =
      let _ , spr′ , spl′ = assoc← (_ , spr , spl) in
      f .app✴ spl′ s .app✴ spr′ t

    map-F : ∀ {T U} → T ⊆ U → F T ⊆ F U
    map-F f (rel F⟨ t ⟩) = rel F⟨ f t ⟩

    F-del : ∀ {T} → F T ⊆ ℑ
    F-del (rel F⟨ t ⟩) = ∼→0 rel ✴⟨⟩

    F-dup : ∀ {T} → F T ⊆ F T ✴ F T
    F-dup (rel F⟨ t ⟩) = 0-dup (∼→0 rel) ✴⟨ rel F⟨ t ⟩ , rel F⟨ t ⟩ ⟩

    zip-F′ : ∀ {T U} → F T ∩ F U ⊆ F (T ∩ U)
    zip-F′ {T} {U} ((rt F⟨ t ⟩) , (ru F⟨ u ⟩)) =
      let q = ∼-func→ rt ru in
      ru F⟨ ≡.subst T (≈⇒≡ q) t , u ⟩

    zip-F : ∀ {T U} → F T ✴ F U ⊆ F (T ∩ U)
    zip-F {T} {U} (sp ✴⟨ rt F⟨ t ⟩ , ru F⟨ u ⟩ ⟩) =
      let p , q = identity²→ sp (∼→0 rt) (∼→0 ru) in
      zip-F′ ( ≡.subst (_∼ _) (≡.sym (≈⇒≡ p)) rt F⟨ t ⟩
             , ≡.subst (_∼ _) (≡.sym (≈⇒≡ q)) ru F⟨ u ⟩)

    map-G : ∀ {T U} → T ⊆ U → G T ⊆ G U
    map-G f (rel G⟨ t ⟩) = rel G⟨ f t ⟩

    zip-G : ∀ {T U} → G T ∩ G U ⊆ G (T ∩ U)
    zip-G {T} {U} (rt G⟨ t ⟩ , ru G⟨ u ⟩) =
      let q = ∼-func← rt ru in
      ru G⟨ ≡.subst T (≈⇒≡ q) t , u ⟩

    ∩⇒✴-under-G : ∀ {T U} → G (T ∩ U) ⊆ G (T ✴ U)
    ∩⇒✴-under-G (rel G⟨ t , u ⟩) = rel G⟨ 0-dup (∼→0 rel) ✴⟨ t , u ⟩ ⟩

    FG-η : ∀ {T} → F (G T) ⊆ T
    FG-η {T} (relf F⟨ relg G⟨ t ⟩ ⟩) = ≡.subst T (≈⇒≡ (∼-func← relg relf)) t

    infix 40 _∋_ _∋l_ _∋i_

    data _∋l_ : LCtx → Ty lin → Set where
      here : Γ ∼0 → Γ -, (lin , S) ∋l S
      there : Γ ∋l S → Γ -i X ∋l S

    data _∋i_ : ICtx → Ty int → Set where
      here : Θ -, X ∋i X
      there : Θ ∋i X → Θ -, Y ∋i X

    _∋_ : Ctx m → Ty m → Set
    _∋_ {lin} Γ A = Γ ∋l A
    _∋_ {int} Θ X = Θ ∋i X

  private
    variable
      Γ Γl Γm Γr Δ : LCtx
      Θ Λ : ICtx
      m n : Mode
      A B C : Ty lin
      X Y Z : Ty int
      S T U : Ty m
      𝓥 : ∀ {m} → Ctx m → Ty m → Set

  infix 20 _⊢_ [_]_⊨_ _⊨_ [_]_n⊢_ _ne⊢_ _nf⊢_

  [_]_⊨_ = id

  i[_]_⇒ᵉ_ : (ICtx → Ty int → Set) → (ICtx → ICtx → Set)
  i[_]_⇒ᵉ_ = Wrap λ 𝓥 Θ Λ → ∀ {X} → Λ ∋i X → 𝓥 Θ X

  []iᵉ : {𝓥 : ICtx → Ty int → Set} → i[ 𝓥 ] Θ ⇒ᵉ []
  []iᵉ .get ()

  _-,ᵉ_ : {𝓥 : ICtx → Ty int → Set} →
    i[ 𝓥 ] Θ ⇒ᵉ Λ → [ 𝓥 ] Θ ⊨ X → i[ 𝓥 ] Θ ⇒ᵉ Λ -, X
  (e -,ᵉ v) .get here = v
  (e -,ᵉ v) .get (there i) = e .get i

  last-iᵉ : ∀ {𝓥} → i[ 𝓥 ] Θ ⇒ᵉ (Λ -, X) → 𝓥 Θ X
  last-iᵉ ρ = ρ .get here

  init-iᵉ : ∀ {𝓥} → i[ 𝓥 ] Θ ⇒ᵉ (Λ -, X) → i[ 𝓥 ] Θ ⇒ᵉ Λ
  init-iᵉ ρ .get i = ρ .get (there i)

  map-iᵉ : {𝓥 𝓦 : ICtx → Ty int → Set} →
    ∀[ 𝓥 ⇒ 𝓦 ] → (i[ 𝓥 ] Θ ⇒ᵉ Λ → i[ 𝓦 ] Θ ⇒ᵉ Λ)
  map-iᵉ f e .get i = f (e .get i)

  postren-iᵉ : ∀ {𝓥 : ICtx → Ty int → Set} {Θ Λ Λ′} →
    i[ 𝓥 ] Θ ⇒ᵉ Λ → i[ _∋i_ ] Λ ⇒ᵉ Λ′ → i[ 𝓥 ] Θ ⇒ᵉ Λ′
  postren-iᵉ e f .get i = e .get (f .get i)

  data l[_]_⇒ᵉ_ (𝓥 : ∀ {m} → Ctx m → Ty m → Set) : (Γ Δ : LCtx) → Set where
    [] : ℑ ⊆ l[ 𝓥 ]_⇒ᵉ []
    snoc : ∀ m {S : Ty m} →
      l[ 𝓥 ]_⇒ᵉ Δ ✴ F? ([ 𝓥 ]_⊨ S) ⊆ l[ 𝓥 ]_⇒ᵉ Δ -, (m , S)
    -- snoc-l : l[ 𝓥 ]_⇒ᵉ Δ ✴ [ 𝓥 ]_⊨ A ⊆ l[ 𝓥 ]_⇒ᵉ Δ -l A
    -- snoc-i : l[ 𝓥 ]_⇒ᵉ Δ ✴ F ([ 𝓥 ]_⊨ X) ⊆ l[ 𝓥 ]_⇒ᵉ Δ -i X

  pattern snoc-l x = snoc lin x
  pattern snoc-i x = snoc int x

  []⁻¹ : l[ 𝓥 ]_⇒ᵉ [] ⊆ ℑ
  []⁻¹ ([] i) = i

  snoc-l⁻¹ : l[ 𝓥 ]_⇒ᵉ Δ -l A ⊆ l[ 𝓥 ]_⇒ᵉ Δ ✴ [ 𝓥 ]_⊨ A
  snoc-l⁻¹ (snoc-l x) = x

  iter-lᵉ : ∀ (_⇒_ : LCtx → LCtx → Set) →
    (ℑ ⊆ _⇒ []) →
    (∀ {Δ A} → _⇒ Δ ✴ [ 𝓥 ]_⊨ A ⊆ _⇒ Δ -l A) →
    (∀ {Δ X} → _⇒ Δ ✴ F ([ 𝓥 ]_⊨ X) ⊆ _⇒ Δ -i X) →
    ∀ {Γ Δ} → l[ 𝓥 ] Γ ⇒ᵉ Δ → Γ ⇒ Δ
  iter-lᵉ T n cl ci ([] x) = n x
  iter-lᵉ T n cl ci (snoc-l x) = cl (map-✴ (iter-lᵉ T n cl ci) id x)
  iter-lᵉ T n cl ci (snoc-i x) = ci (map-✴ (iter-lᵉ T n cl ci) id x)

  [_]_⇒ᵉ_ : (∀ {n} → Ctx n → Ty n → Set) → (∀ {m} → Ctx m → Ctx m → Set)
  [_]_⇒ᵉ_ 𝓥 {lin} Γ Δ = l[ 𝓥 ] Γ ⇒ᵉ Δ
  [_]_⇒ᵉ_ 𝓥 {int} Θ Λ = i[ 𝓥 ] Θ ⇒ᵉ Λ

  _⇒ʳ_ : ∀ {m} → Ctx m → Ctx m → Set
  _⇒ʳ_ = [ _∋_ ]_⇒ᵉ_

  _i⇒ʳ_ = i[ _∋i_ ]_⇒ᵉ_
  _l⇒ʳ_ = _⇒ʳ_ {lin}

  Ren : ∀ m → (Ctx m → Set) → Set
  Ren m T = ∀ {Γ Δ} → Γ ⇒ʳ Δ → T Δ → T Γ

  env-ℑ : ∀ {Γ} → (∃ \ Δ → l[ 𝓥 ] Γ ⇒ᵉ Δ × Δ ∼0) → ℑ Γ
  env-ℑ {𝓥 = 𝓥} (_ , ρ , sp) =
    iter-lᵉ (λ Γ Δ → Δ ∼0 → ℑ Γ)
      (λ { i [] → i })
      (λ rv ())
      (λ { rv (sp -i*) → ✴-identityʳ→ ∘′ map-✴ (λ f → f sp) F-del $′ rv })
      ρ sp

  env-✴ : ∀ {Γ Δl Δr} →
    (∃ \ Δ → l[ 𝓥 ] Γ ⇒ᵉ Δ × Δ ∼[ Δl + Δr ]) → (l[ 𝓥 ]_⇒ᵉ Δl ✴ l[ 𝓥 ]_⇒ᵉ Δr) Γ
  env-✴ {𝓥 = 𝓥} (_ , ρ , sp) =
    iter-lᵉ (λ Γ Δ → ∀ {Δl Δr} → Δ ∼[ Δl + Δr ] → (l[ 𝓥 ]_⇒ᵉ Δl ✴ l[ 𝓥 ]_⇒ᵉ Δr) Γ)
      (λ { i [] → map-✴ [] [] (✴-identity²← i) })
      (λ { rv (sp -lˡ) →
           let reassoc = ✴-assoc← ∘ map-✴ id ✴-comm ∘ ✴-assoc→ in
           map-✴ snoc-l id ∘ reassoc ∘ map-✴ (λ f → f sp) id $ rv
         ; rv (sp -lʳ) → map-✴ id snoc-l ∘ ✴-assoc→ ∘ map-✴ (λ f → f sp) id $ rv
         })
      (λ { rv (sp -i*) →
        map-✴ snoc-i snoc-i ∘ ✴-exch ∘ map-✴ (λ f → f sp) F-dup $ rv })
      ρ sp

  env-F : ∀ {Γ Λ} → (∃ \ Δ → l[ 𝓥 ] Γ ⇒ᵉ Δ × Δ ∼ Λ) → F (i[ 𝓥 ]_⇒ᵉ Λ) Γ
  env-F {𝓥 = 𝓥} (_ , ρ , rel) =
    iter-lᵉ (λ Γ Δ → ∀ {Λ} → Δ ∼ Λ → F (i[ 𝓥 ]_⇒ᵉ Λ) Γ)
      (λ { (sp ✴⟨⟩) [] → 0→∼ sp F⟨ []iᵉ ⟩ })
      (λ rv ())
      (λ { rv (sp -i*) →
        map-F (λ (ρ , v) → _-,ᵉ_ {𝓥 = 𝓥} ρ v) ∘ zip-F ∘ map-✴ (λ f → f sp) id
          $ rv })
      ρ rel

  env-G : ∀ {Θ Δ} → (∃ \ Λ → i[ 𝓥 ] Θ ⇒ᵉ Λ × Δ ∼ Λ) → G (l[ 𝓥 ]_⇒ᵉ Δ) Θ
  env-G (_ , ρ , []) =
    let rel = ∼-total← _ .proj₂ in
    rel G⟨ [] (∼→0 rel ✴⟨⟩) ⟩
  env-G {𝓥 = 𝓥} (_ , ρ , rel -i*) =
    let r@(rel′ G⟨ σ ⟩) = env-G {𝓥 = 𝓥} (_ , init-iᵉ ρ , rel) in
    rel′ G⟨ snoc-i (0-dup (∼→0 rel′) ✴⟨ σ , rel′ F⟨ last-iᵉ ρ ⟩ ⟩) ⟩

  ren^✴ : ∀ {T U} → Ren lin T → Ren lin U → Ren lin (T ✴ U)
  ren^✴ rt ru ρ (sp ✴⟨ t , u ⟩) =
    map-✴ (λ σ → rt σ t) (λ τ → ru τ u) $ env-✴ (_ , ρ , sp)

  ren^F : ∀ {T} → Ren int T → Ren lin (F T)
  ren^F r ρ (rel F⟨ t ⟩) = map-F (λ σ → r σ t) $ env-F (_ , ρ , rel)

  ren^G : ∀ {T} → Ren lin T → Ren int (G T)
  ren^G r ρ (rel G⟨ t ⟩) = map-G (λ σ → r σ t) $ env-G (_ , ρ , rel)

  lookup-i : ∀ {𝓥 : ICtx → Ty int → Set} →
    i[ 𝓥 ] Θ ⇒ᵉ Λ → _∋_ {int} Λ X → 𝓥 Θ X
  lookup-i ρ i = ρ .get i

  lookup-l : ∀ {𝓥 : ∀ {m} → Ctx m → Ty m → Set} →
    l[ 𝓥 ] Γ ⇒ᵉ Δ → Δ ∋l A → 𝓥 Γ A
  lookup-l (snoc-l ρv) (here sp) =
    ✴-identityˡ→ ∘ map-✴ (λ ρ → env-ℑ (_ , ρ , sp)) id $ ρv
  lookup-l (snoc-i ρf) (there i) =
    ✴-identityʳ→ ∘ map-✴ (λ ρ → lookup-l ρ i) F-del $ ρf

  lookup : ∀ {𝓥 : ∀ {m} → Ctx m → Ty m → Set} {Γ Δ : Ctx m} →
    [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ∋ S → 𝓥 Γ S
  lookup {lin} ρ i = lookup-l ρ i
  lookup {int} ρ i = lookup-i ρ i

  ren^∋ : {S : Ty m} → Ren m (_∋ S)
  ren^∋ = lookup

  id-iᵉ : ∀ {𝓥 Θ} → Θ ∋i_ ⊆ 𝓥 Θ → i[ 𝓥 ] Θ ⇒ᵉ Θ
  id-iᵉ pure .get i = pure i

  comp-iᵉ : ∀ {𝓤 𝓥 𝓦} → (∀ {Θ Λ} → i[ 𝓤 ] Θ ⇒ᵉ Λ → 𝓥 Λ ⊆ 𝓦 Θ) →
    ∀ {Θ Λ Ξ} → i[ 𝓤 ] Θ ⇒ᵉ Λ → i[ 𝓥 ] Λ ⇒ᵉ Ξ → i[ 𝓦 ] Θ ⇒ᵉ Ξ
  comp-iᵉ bind ρ σ .get i = bind ρ (σ .get i)

  comp-lᵉ : ∀ {𝓤 𝓥 𝓦 : ∀ {m} → Ctx m → Ty m → Set} →
    (∀ {m} {Γ Δ : Ctx m} → [ 𝓤 ] Γ ⇒ᵉ Δ → 𝓥 {m} Δ ⊆ 𝓦 {m} Γ) →
    ∀ {Ω Γ Δ} → l[ 𝓤 ] Ω ⇒ᵉ Γ → l[ 𝓥 ] Γ ⇒ᵉ Δ → l[ 𝓦 ] Ω ⇒ᵉ Δ
  comp-lᵉ bind {Δ = []} ρ ([] (sp ✴⟨⟩)) = [] $ env-ℑ (_ , ρ , sp)
  comp-lᵉ bind {Δ = Δ -l A} ρ (snoc-l (sp ✴⟨ σ , v ⟩)) =
    snoc-l ∘ map-✴ (λ ρ′ → comp-lᵉ bind ρ′ σ) (λ ρ′ → bind ρ′ v)
    $ env-✴ (_ , ρ , sp)
  comp-lᵉ bind {Δ = Δ -i X} ρ (snoc-i (sp ✴⟨ σ , rel F⟨ v ⟩ ⟩)) =
    snoc-i ∘
    map-✴
      (λ ρ′ → comp-lᵉ bind ρ′ σ)
      (λ ρ′ → map-F (λ ρ″ → bind ρ″ v) $ env-F (_ , ρ′ , rel))
    $ env-✴ (_ , ρ , sp)

  infixr 5 _,-_
  infix 5 _++l_ _++i_

  data CtxExt : Set where
    [] : CtxExt
    _,-_ : Ty int → CtxExt → CtxExt

  _++l_ : Ctx lin → CtxExt → Ctx lin
  Γ ++l [] = Γ
  Γ ++l (X ,- Ξ) = (Γ -i X) ++l Ξ

  _++i_ : Ctx int → CtxExt → Ctx int
  Θ ++i [] = Θ
  Θ ++i (X ,- Ξ) = (Θ -, X) ++i Ξ

  ++l∼++i : ∀ {Γ Θ} Ξ → Γ ∼ Θ → (Γ ++l Ξ) ∼ (Θ ++i Ξ)
  ++l∼++i [] sp = sp
  ++l∼++i (X ,- Ξ) sp = ++l∼++i Ξ (sp -i*)

  ++l∼0 : ∀ {Γ} Ξ → Γ ∼0 → (Γ ++l Ξ) ∼0
  ++l∼0 [] sp = sp
  ++l∼0 (X ,- Ξ) sp = ++l∼0 Ξ (sp -i*)

  ++l∼+ : ∀ {Γ Γl Γr} Ξ → Γ ∼[ Γl + Γr ] → (Γ ++l Ξ) ∼[ (Γl ++l Ξ) + (Γr ++l Ξ) ]
  ++l∼+ [] sp = sp
  ++l∼+ (X ,- Ξ) sp = ++l∼+ Ξ (sp -i*)

  ++l-there : ∀ {Γ A} Ξ → Γ ∋l A → (Γ ++l Ξ) ∋l A
  ++l-there [] i = i
  ++l-there (X ,- Ξ) i = ++l-there Ξ (there i)

  ++i-there : ∀ {Θ X} Ξ → Θ ∋i X → (Θ ++i Ξ) ∋i X
  ++i-there [] i = i
  ++i-there (X ,- Ξ) i = ++i-there Ξ (there i)

  id+ext-lᵉ : (∀ {m Γ} → Γ ∋_ ⊆ 𝓥 {m} Γ) → ∀ {Γ} Ξ → l[ 𝓥 ] Γ ++l Ξ ⇒ᵉ Γ
  id+ext-lᵉ pure {[]} Ξ = [] (++l∼0 Ξ [] ✴⟨⟩)
  id+ext-lᵉ pure {Γ -l A} Ξ =
    let _ , sp+ , sp0 = identityʳ← refl-≈ in
    snoc-l (++l∼+ Ξ (sp+ -lʳ) ✴⟨ id+ext-lᵉ pure Ξ , pure (++l-there Ξ (here sp0)) ⟩)
  id+ext-lᵉ pure {Γ -i X} Ξ =
    let _ , sp+ , sp0 = identityʳ← {Γ = Γ} refl-≈ in
    let sp0′ = ++l∼++i (X ,- Ξ) (0→∼ sp0) in
    snoc-i $ ++l∼+ Ξ (sp+ -i*)
      ✴⟨ id+ext-lᵉ pure (X ,- Ξ)
      , sp0′ F⟨ pure (++i-there Ξ here) ⟩
      ⟩

  id-lᵉ : (∀ {m Γ} → Γ ∋_ ⊆ 𝓥 {m} Γ) → ∀ {Γ} → l[ 𝓥 ] Γ ⇒ᵉ Γ
  id-lᵉ pure = id+ext-lᵉ pure []

  id-lʳ : Γ l⇒ʳ Γ
  id-lʳ = id-lᵉ id

  there-lʳ : Γ l⇒ʳ Δ → Γ -i X l⇒ʳ Δ
  there-lʳ {X = X} ρ =
    iter-lᵉ (λ Γ Δ → Γ -i X l⇒ʳ Δ)
      (λ { (sp ✴⟨⟩) → [] (sp -i* ✴⟨⟩) })
      (λ { (sp ✴⟨ ρ , v ⟩) → snoc-l (sp -i* ✴⟨ ρ , there v ⟩) })
      (λ { (sp ✴⟨ ρ , rel F⟨ v ⟩ ⟩) →
        snoc-i (sp -i* ✴⟨ ρ , rel -i* F⟨ there v ⟩ ⟩) })
      ρ

  there-iʳ : Θ i⇒ʳ Λ → Θ -, X i⇒ʳ Λ
  there-iʳ ρ .get i = there (ρ .get i)

  data _⊢_ : ∀ {m} → Ctx m → Ty m → Set where
    var : ∀ {m} {S : Ty m} → _∋ S ⊆ _⊢ S

    ⊗I : _⊢ A ✴ _⊢ B ⊆ _⊢ A ⊗l B
    ⊗E : _⊢ A ⊗l B ✴ (_⊢ C ∘ _-l B ∘ _-l A) ⊆ _⊢ C
    ⊸I : (_⊢ B ∘ _-l A) ⊆ _⊢ A ⊸l B
    ⊸E : _⊢ A ⊸l B ✴ _⊢ A ⊆ _⊢ B

    ×I : _⊢ X ∩ _⊢ Y ⊆ _⊢ X ×i Y
    ×El : _⊢ X ×i Y ⊆ _⊢ X
    ×Er : _⊢ X ×i Y ⊆ _⊢ Y
    →I : (_⊢ Y ∘ _-, X) ⊆ _⊢ X →i Y
    →E : _⊢ X →i Y ∩ _⊢ X ⊆ _⊢ Y

    FI : F (_⊢ X) ⊆ _⊢ Fl X
    FE : _⊢ Fl X ✴ (_⊢ A ∘ _-i X) ⊆ _⊢ A
    GI : G (_⊢ A) ⊆ _⊢ Gi A
    GE : F (_⊢ Gi A) ⊆ _⊢ A

  data Noη : ∀ {m} → Ty m → Set where
    ιl-noη : Noη ιl
    ιi-noη : Noη ιi
    ⊗-noη : Noη (A ⊗l B)
    F-noη : Noη (Fl X)

  data NE/NF : Set where ne nf : NE/NF

  data [_]_n⊢_ : NE/NF → ∀ {m} → Ctx m → Ty m → Set
  _ne⊢_ _nf⊢_ : ∀ {m} → Ctx m → Ty m → Set
  _ne⊢_ = [ ne ]_n⊢_
  _nf⊢_ = [ nf ]_n⊢_

  data [_]_n⊢_ where
    var : ∀ {m} {S : Ty m} → _∋ S ⊆ _ne⊢ S
    ⊗E : _ne⊢ A ⊗l B ✴ (_nf⊢ C ∘ _-l B ∘ _-l A) ⊆ _ne⊢ C
    ⊸E : _ne⊢ A ⊸l B ✴ _nf⊢ A ⊆ _ne⊢ B
    ×El : _ne⊢ X ×i Y ⊆ _ne⊢ X
    ×Er : _ne⊢ X ×i Y ⊆ _ne⊢ Y
    →E : _ne⊢ X →i Y ∩ _nf⊢ X ⊆ _ne⊢ Y
    FE : _ne⊢ Fl X ✴ (_nf⊢ A ∘ _-i X) ⊆ _ne⊢ A
    GE : F (_ne⊢ Gi A) ⊆ _ne⊢ A

    ⊗I : _nf⊢ A ✴ _nf⊢ B ⊆ _nf⊢ A ⊗l B
    ⊸I : (_nf⊢ B ∘ _-l A) ⊆ _nf⊢ A ⊸l B
    ×I : _nf⊢ X ∩ _nf⊢ Y ⊆ _nf⊢ X ×i Y
    →I : (_nf⊢ Y ∘ _-, X) ⊆ _nf⊢ X →i Y
    FI : F (_nf⊢ X) ⊆ _nf⊢ Fl X
    GI : G (_nf⊢ A) ⊆ _nf⊢ Gi A
    emb : Noη S → _ne⊢ S ⊆ _nf⊢ S

  □l : (LCtx → Set) → (LCtx → Set)
  □l T Γ = ∀ {Δ} → Δ l⇒ʳ Γ → T Δ

  □i : (ICtx → Set) → (ICtx → Set)
  □i T Θ = ∀ {Λ} → Λ i⇒ʳ Θ → T Λ

  □ : (Ctx m → Set) → (Ctx m → Set)
  □ {m = lin} = □l
  □ {m = int} = □i

  extend-lᵉ : ∀ {_⊨_ : ∀ {m} → Ctx m → Ty m → Set} → (∀ {m S} → Ren m (_⊨ S)) →
    l[ _⊨_ ]_⇒ᵉ Δ ⊆ □l (F? (_⊨ S) ─✴ l[ _⊨_ ]_⇒ᵉ Δ -, (m , S))
  extend-lᵉ ren ρ σ .app✴ sp s =
    snoc _ (sp ✴⟨ comp-lᵉ (λ τ → ren τ) σ ρ , s ⟩)

  lift-lᵉl : ∀[ _∋l_ ⇒ 𝓥 {lin} ] → l[ 𝓥 ] Γ ⇒ᵉ Δ → l[ 𝓥 ] Γ -l A ⇒ᵉ Δ -l A
  lift-lᵉl pure ρ =
    let _ , sp+ , sp0 = identityʳ← refl-≈ in
    snoc-l (sp+ -lʳ ✴⟨ ρ , pure (here sp0) ⟩)

  lift-lᵉi : (∀ {m S} → Ren m ([ 𝓥 ]_⊨ S)) → ∀[ _∋i_ ⇒ 𝓥 {int} ] →
    l[ 𝓥 ] Γ ⇒ᵉ Δ → l[ 𝓥 ] Γ -i X ⇒ᵉ Δ -i X
  lift-lᵉi ren pure ρ =
    let _ , sp+ , sp0 = identityʳ← refl-≈ in
    snoc-i $ sp+ -i*
      ✴⟨ comp-lᵉ (λ σ → ren σ) (there-lʳ id-lʳ) ρ
      , 0→∼ sp0 -i* F⟨ pure here ⟩ ⟩

  lift-iᵉ : ∀ {𝓥} → (∀ {X} → Ren int ([ 𝓥 ]_⊨ X)) → ∀[ _∋i_ ⇒ 𝓥 ] →
    i[ 𝓥 ] Θ ⇒ᵉ Λ → i[ 𝓥 ] Θ -, X ⇒ᵉ Λ -, X
  lift-iᵉ ren pure ρ .get here = pure here
  lift-iᵉ ren pure ρ .get (there i) = ren [ there ] (ρ .get i)

  -- Can't use ren^✴ &c because of termination checking.
  ren^n⊢ : ∀ {m n Γ Δ} {S : Ty m} → Γ ⇒ʳ Δ → [ n ] Δ n⊢ S → [ n ] Γ n⊢ S
  ren^n⊢ ρ (var v) = var (lookup ρ v)
  ren^n⊢ ρ (⊗E (sp ✴⟨ M , N ⟩)) = ⊗E ∘
    map-✴ (λ σ → ren^n⊢ σ M) (λ τ → ren^n⊢ (lift-lᵉl id (lift-lᵉl id τ)) N)
    $ env-✴ (_ , ρ , sp)
  ren^n⊢ ρ (⊸E (sp ✴⟨ M , N ⟩)) = ⊸E ∘
    map-✴ (λ σ → ren^n⊢ σ M) (λ τ → ren^n⊢ τ N)
    $ env-✴ (_ , ρ , sp)
  ren^n⊢ ρ (×El M) = ×El (ren^n⊢ ρ M)
  ren^n⊢ ρ (×Er M) = ×Er (ren^n⊢ ρ M)
  ren^n⊢ ρ (→E (M , N)) = →E (ren^n⊢ ρ M , ren^n⊢ ρ N)
  ren^n⊢ ρ (FE (sp ✴⟨ M , N ⟩)) = FE ∘
    map-✴ (λ σ → ren^n⊢ σ M) (λ τ → ren^n⊢ (lift-lᵉi ren^∋ id τ) N)
    $ env-✴ (_ , ρ , sp)
  ren^n⊢ ρ (GE (rel F⟨ M ⟩)) =
    GE ∘ map-F (λ σ → ren^n⊢ σ M) $ env-F (_ , ρ , rel)
  ren^n⊢ ρ (⊗I (sp ✴⟨ M , N ⟩)) =
    ⊗I ∘ map-✴ (λ σ → ren^n⊢ σ M) (λ τ → ren^n⊢ τ N) $ env-✴ (_ , ρ , sp)
  ren^n⊢ ρ (⊸I M) = ⊸I (ren^n⊢ (lift-lᵉl id ρ) M)
  ren^n⊢ ρ (×I (M , N)) = ×I (ren^n⊢ ρ M , ren^n⊢ ρ N)
  ren^n⊢ ρ (→I M) = →I (ren^n⊢ (lift-iᵉ ren^∋ id ρ) M)
  ren^n⊢ ρ (FI (rel F⟨ M ⟩)) =
    FI ∘ map-F (λ σ → ren^n⊢ σ M) $ env-F (_ , ρ , rel)
  ren^n⊢ ρ (GI (rel G⟨ M ⟩)) =
    GI ∘ map-G (λ σ → ren^n⊢ σ M) $ env-G (_ , ρ , rel)
  ren^n⊢ ρ (emb no M) = emb no (ren^n⊢ ρ M)

  _⊨_ : ∀ {m} → Ctx m → Ty m → Set
  Γ ⊨ ιl = Γ ne⊢ ιl
  Θ ⊨ ιi = Θ ne⊢ ιi
  Γ ⊨ A ⊗l B = (_⊨ A ✴ _⊨ B) Γ ⊎ Γ ne⊢ A ⊗l B
  Γ ⊨ A ⊸l B = □l (_⊨ A ─✴ _⊨ B) Γ
  Θ ⊨ X ×i Y = (_⊨ X ∩ _⊨ Y) Θ
  Θ ⊨ X →i Y = □i (_⊨ X ⇒ _⊨ Y) Θ
  Γ ⊨ Fl X = F (_⊨ X) Γ ⊎ Γ ne⊢ Fl X
  Θ ⊨ Gi A = G (_⊨ A) Θ

  ren^⊨ : ∀ {Γ Δ : Ctx m} S → Γ ⇒ʳ Δ → Δ ⊨ S → Γ ⊨ S
  ren^⊨ ιl ρ M = ren^n⊢ ρ M
  ren^⊨ ιi ρ M = ren^n⊢ ρ M
  ren^⊨ (A ⊗l B) ρ mn = ⊎.map (ren^✴ (ren^⊨ A) (ren^⊨ B) ρ) (ren^n⊢ ρ) mn
  ren^⊨ (A ⊸l B) ρ m σ .app✴ sp n = m (comp-lᵉ (λ τ → lookup τ) σ ρ) .app✴ sp n
  ren^⊨ (X ×i Y) ρ mn = ×.map (ren^⊨ X ρ) (ren^⊨ Y ρ) mn
  ren^⊨ (X →i Y) ρ m σ n = m (comp-iᵉ (λ τ → lookup-i τ) σ ρ) n
  ren^⊨ (Fl X) ρ fm = ⊎.map (ren^F (ren^⊨ X) ρ) (ren^n⊢ ρ) fm
  ren^⊨ (Gi A) ρ m = ren^G (ren^⊨ A) ρ m

  reify : (S : Ty m) → _⊨ S ⊆ _nf⊢ S
  reflect : (S : Ty m) → _ne⊢ S ⊆ _⊨ S

  reify ιl N = emb ιl-noη N
  reify ιi N = emb ιi-noη N
  reify (A ⊗l B) (inj₁ n) = ⊗I (map-✴ (reify A) (reify B) n)
  reify (A ⊗l B) (inj₂ N) = emb ⊗-noη N
  reify (A ⊸l B) n =
    let _ , sp+ , sp0 = identityʳ← refl-≈ in
    ⊸I (reify B (n id-lʳ .app✴ (sp+ -lʳ) (reflect A (var (here sp0)))))
  reify (X ×i Y) (m , n) = ×I (reify X m , reify Y n)
  reify (X →i Y) n =
    →I (reify Y (n [ there ] (reflect X (var here))))
  reify (Fl X) (inj₁ fm) = FI (map-F (reify X) fm)
  reify (Fl X) (inj₂ N) = emb F-noη N
  reify (Gi A) (rel G⟨ n ⟩) = GI (rel G⟨ reify A n ⟩)

  reflect ιl M = M
  reflect ιi M = M
  reflect (A ⊗l B) M = inj₂ M
  reflect (A ⊸l B) M ρ .app✴ sp+ n =
    reflect B (⊸E (sp+ ✴⟨ ren^n⊢ ρ M , reify A n ⟩))
  reflect (X ×i Y) M = reflect X (×El M) , reflect Y (×Er M)
  reflect (X →i Y) M ρ n =
    reflect Y (→E (ren^n⊢ ρ M , reify X n))
  reflect (Fl X) M = inj₂ M
  reflect (Gi A) M =
    let _ , rel = ∼-total← _ in
    rel G⟨ reflect A (GE (rel F⟨ M ⟩)) ⟩

  ⟦⊗E⟧ : ∀ C → (_⊨ A ⊗l B ✴ (_⊨ A ─✴ _⊨ B ─✴ _⊨ C)) ⊆ _⊨ C
  ⟦⊗E⟧ C (sp ✴⟨ inj₁ m , n ⟩) = uncurry✴ n .app✴ (comm sp) m
  ⟦⊗E⟧ {A} {B} C (sp ✴⟨ inj₂ M , n ⟩) =
    let _ , sp+ , sp0 = identityʳ← refl-≈ in
    reflect C $ ⊗E $′ sp ✴⟨ M ,
      reify C $ n
        .app✴ (sp+ -lʳ) (reflect A (var (here sp0)))
        .app✴ (sp+ -lˡ -lʳ) (reflect B (var (here sp0))) ⟩

  ⟦FE⟧ : (C : Ty lin) → (_⊨ Fl X ✴ □l (F (_⊨ X) ─✴ _⊨ C)) ⊆ _⊨ C
  ⟦FE⟧ C (sp ✴⟨ inj₁ m , n ⟩) = n id-lʳ .app✴ (comm sp) m
  ⟦FE⟧ {X} C (sp ✴⟨ inj₂ M , n ⟩) =
    let _ , sp+ , sp0 = identityʳ← refl-≈ in
    reflect C $ FE $′ sp ✴⟨ M ,
      reify C $ n (there-lʳ id-lʳ)
        .app✴ (sp+ -i*) (0→∼ sp0 -i* F⟨ reflect X (var here) ⟩) ⟩

  eval : ∀ {m Γ Δ} {S : Ty m} → [ _⊨_ ] Γ ⇒ᵉ Δ → Δ ⊢ S ⇒ Γ ⊨ S
  eval ρ (var i) = lookup ρ i
  eval ρ (⊗I (sp ✴⟨ M , N ⟩)) =
    inj₁ (map-✴ (λ σ → eval σ M) (λ τ → eval τ N) (env-✴ (_ , ρ , sp)))
  eval {S = C} ρ (⊗E (sp ✴⟨ M , N ⟩)) =
    ⟦⊗E⟧ C
    ∘ map-✴
      (λ σ → eval σ M)
      (λ τ → lam✴ λ spA a → lam✴ λ spB b →
        eval (snoc-l (spB ✴⟨ snoc-l (spA ✴⟨ τ , a ⟩) , b ⟩)) N)
    $ env-✴ (_ , ρ , sp)
  eval ρ (⊸I M) σ .app✴ sp+ n =
    eval (snoc-l (sp+ ✴⟨ comp-lᵉ (λ τ {S} → ren^⊨ S τ) σ ρ , n ⟩)) M
  eval ρ (⊸E (sp ✴⟨ M , N ⟩)) =
    eval✴ ∘ map-✴ (λ σ → eval σ M id-lʳ) (λ τ → eval τ N)
    $ env-✴ (_ , ρ , sp)
  eval ρ (×I (M , N)) = eval ρ M , eval ρ N
  eval ρ (×El M) = eval ρ M .proj₁
  eval ρ (×Er M) = eval ρ M .proj₂
  eval ρ (→I M) σ n =
    eval (comp-iᵉ (λ ([ τ ]) {X} → ren^⊨ X [ τ ]) σ ρ -,ᵉ n) M
  eval ρ (→E (M , N)) = (eval ρ M) (id-iᵉ id) (eval ρ N)
  eval ρ (FI (rel F⟨ M ⟩)) = inj₁ (map-F (λ σ → eval σ M) $ env-F (_ , ρ , rel))
  eval {S = C} ρ (FE (sp ✴⟨ M , N ⟩)) =
    ⟦FE⟧ C
    ∘ map-✴
      (λ σ → eval σ M)
      (λ τ {_} υ → lam✴ λ spX fx →
        eval (snoc-i (spX ✴⟨ comp-lᵉ (λ υ′ {S} → ren^⊨ S υ′) υ τ , fx ⟩)) N)
      -- TODO: remove explicit lam✴?
    $ env-✴ (_ , ρ , sp)
  eval ρ (GI (rel G⟨ M ⟩)) = map-G (λ σ → eval σ M) $′ env-G (_ , ρ , rel)
  eval ρ (GE (rel F⟨ M ⟩)) =
    FG-η ∘ map-F (λ ρ′ → eval ρ′ M) $ env-F (_ , ρ , rel)

{-
  record Kit (𝓥 : OpenFam) : Set where
    field
      wk : [ 𝓥 ] Γ ⊨_ ⊆ [ 𝓥 Γ -u A ⊨_ ]
      vr : _∋_ {A = Ty} ⊆ 𝓥
      tm : 𝓥 ⊆ _⊢_

    wkᵉ : ∀[ [ 𝓥 ] Γ ⇒ᵉ_ ⇒ [ 𝓥 ] Γ -u A ⇒ᵉ_ ]
    wkᵉ ([] (zs ✴⟨⟩)) = [] ((zs -u*) ✴⟨⟩)
    wkᵉ (snoc-l (as ✴⟨ ρ , v ⟩)) = snoc-l ((as -u*) ✴⟨ wkᵉ ρ , wk v ⟩)
    wkᵉ (snoc-u (as ✴⟨ ρ , zs □⟨ v ⟩ ⟩)) =
      snoc-u ((as -u*) ✴⟨ wkᵉ ρ , zs -u* □⟨ wk v ⟩ ⟩)

    bind : [ 𝓥 ] Γ ⇒ᵉ Δ → [ 𝓥 ] Γ -, (m , A) ⇒ᵉ Δ -, (m , A)
    bind {m = unr} ρ =
      let _ , as , zs = identityʳ← refl-≈ in
      snoc-u ((as -u*) ✴⟨ wkᵉ ρ , (zs -u*) □⟨ vr (here zs) ⟩ ⟩)
    bind {m = lin} ρ =
      let _ , as , zs = identityʳ← refl-≈ in
      snoc-l ((as -lʳ) ✴⟨ ρ , vr (here zs) ⟩)

    trav : [ 𝓥 ] Γ ⇒ᵉ Δ → Δ ⊢ A → Γ ⊢ A
    trav ρ (var x) = tm (lookup ρ x)
    trav ρ (⊸I M) = ⊸I (trav (bind ρ) M)
    trav ρ (⊸E (sp ✴⟨ M , N ⟩)) =
      ⊸E ∘ ✴-map ((λ ρ → trav ρ M) , (λ ρ → trav ρ N)) $ +-env (_ , ρ , sp)
    trav ρ (!I (zs □⟨ M ⟩)) = !I (0-env (_ , ρ , zs) .ℑ.split □⟨ trav ρ M ⟩)
    trav ρ (!E (sp ✴⟨ M , N ⟩)) =
      !E ∘ ✴-map ((λ ρ → trav ρ M) , (λ ρ → trav (bind ρ) N))
      $ +-env (_ , ρ , sp)
-}
