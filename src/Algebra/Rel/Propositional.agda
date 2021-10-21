module Algebra.Rel.Propositional where

  open import Data.Product
  open import Data.Unit using (⊤; tt)
  open import Function
  open import Level renaming (suc to lsuc)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nary

  -- First definition: directly transcribe what it means to be a monoid object
  -- in (Rel, ⊗).
  -- We have ε : I ⇸ M and ∙ : M ⊗ M ⇸ M satisfying identity and associativity.
  -- e.g, identityˡ says that ∀x,y. (∃z. ε((), z) ∧ ∙((z, x), y)) → x = y.
  -- That is, if z is an identity element that we can add to x to get y, then
  -- x = y.

  record RelMonoid : Set₁ where
    field
      Carrier : Set
      ε∼_ : Carrier → Set
      [_∙_]∼_ : (x y z : Carrier) → Set
      identityˡ : ∀ {x y} → ∃⟨ ε∼_ ∩ [_∙ x ]∼ y ⟩ ⇔ x ≡ y
      identityʳ : ∀ {x y} → ∃⟨ ε∼_ ∩ [ x ∙_]∼ y ⟩ ⇔ x ≡ y
      assoc : ∀ {w x y z} →
        ∃⟨ [ w ∙ x ]∼_ ∩ [_∙ y ]∼ z ⟩ ⇔ ∃⟨ [ x ∙ y ]∼_ ∩ [ w ∙_]∼ z ⟩

  -- Given the relational monoid operations, we can form the following
  -- combinators of Rel-monoid-indexed sets.
  -- Such families should form a monoidal category, with morphisms being
  -- index-preserving functions (∀[ T ⇒ U ]).
  -- What I show here amounts to these families forming a monoidal proset.

  -- First seen in:
  -- Intrinsically-Typed Definitional Interpreters for Linear, Session-Typed
  -- Languages; Rouvoet, Poulsen, Krebbers, Visser; 2020
  -- https://github.com/ajrouvoet/ternary.agda

  module Unit {A : Set} (ε∼_ : A → Set) where
    record ℑ (x : A) : Set where
      constructor ⟨⟩✴_
      field
        split : ε∼ x

  module Mult {A : Set} ([_∙_]∼_ : (x y z : A) → Set) where
    record _✴_ (T U : A → Set) (x : A) : Set where
      constructor ⟨_,_⟩✴_
      field
        {y z} : A
        T-prf : T y
        U-prf : U z
        split : [ y ∙ z ]∼ x

    ✴-map : ∀ {T T′ U U′} → ∀[ T ⇒ T′ ] → ∀[ U ⇒ U′ ] → ∀[ (T ✴ U) ⇒ (T′ ✴ U′) ]
    ✴-map f g (⟨ t , u ⟩✴ a) = ⟨ f t , g u ⟩✴ a

  infix 6 _⇔₁_
  _⇔₁_ : ∀ {A : Set} (T U : A → Set) → Set
  T ⇔₁ U = ∀ {x} → T x ⇔ U x

  -- Second definition: we take the family combinators and state that they obey
  -- the monoidal proset axioms.
  -- The specialisations at the bottom are useful for converting to the first
  -- definition.

  record RelMonoid′ : Set₁ where
    field
      Carrier : Set
      ε∼_ : Carrier → Set
      [_∙_]∼_ : (x y z : Carrier) → Set
    open Unit ε∼_
    open Mult [_∙_]∼_
    field
      identityˡ : ∀ {T} → ∀[ ℑ ✴ T ⇔₁ T ]
      identityʳ : ∀ {T} → ∀[ T ✴ ℑ ⇔₁ T ]
      assoc : ∀ {T U V} → ∀[ (T ✴ U) ✴ V ⇔₁ T ✴ (U ✴ V) ]

    identityˡ≡ : ∀ {x y : Carrier} → _
    identityˡ≡ {x} {y} = identityˡ {T = x ≡_} {y}
    identityʳ≡ : ∀ {x y : Carrier} → _
    identityʳ≡ {x} {y} = identityʳ {T = x ≡_} {y}
    assoc≡ : ∀ {w x y z : Carrier} → _
    assoc≡ {w} {x} {y} {z} = assoc {T = w ≡_} {x ≡_} {y ≡_} {z}

  -- We can convert between the two definitions.
  -- From first to second, we use the basic Rel-monoid axioms to deal with the
  -- algebraic parts, and the extra data are preserved and rearranged.
  -- From second to first, we fix all the families to be singletons around the
  -- inputs.

  to : RelMonoid → RelMonoid′
  to M = record
    { RelMonoid M
    ; identityˡ = mk⇔
      (λ (⟨ ⟨⟩✴ z , t ⟩✴ a) → subst _ (identityˡ .f (_ , z , a)) t)
      (λ t → let _ , z , a = identityˡ .g refl in ⟨ ⟨⟩✴ z , t ⟩✴ a)
    ; identityʳ = mk⇔
      (λ (⟨ t , ⟨⟩✴ z ⟩✴ a) → subst _ (identityʳ .f (_ , z , a)) t)
      (λ t → let _ , z , a = identityʳ .g refl in ⟨ t , ⟨⟩✴ z ⟩✴ a)
    ; assoc = mk⇔
      (λ (⟨ ⟨ t , u ⟩✴ b , v ⟩✴ a) →
        let _ , b′ , a′ = assoc .f (_ , b , a) in
        ⟨ t , ⟨ u , v ⟩✴ b′ ⟩✴ a′)
      (λ (⟨ t , ⟨ u , v ⟩✴ b ⟩✴ a) →
        let _ , b′ , a′ = assoc .g (_ , b , a) in
        ⟨ ⟨ t , u ⟩✴ b′ , v ⟩✴ a′)
    }
    where
    open RelMonoid M
    open Unit ε∼_
    open Mult [_∙_]∼_
    open Equivalence

  from : RelMonoid′ → RelMonoid
  from M = record
    { RelMonoid′ M
    ; identityˡ = λ {x y} → mk⇔
      (λ (_ , z , a) → identityˡ≡ .f (⟨ ⟨⟩✴ z , refl ⟩✴ a))
      identityˡ←
    ; identityʳ = λ {x y} → mk⇔
      (λ (_ , z , a) → identityʳ≡ .f (⟨ refl , ⟨⟩✴ z ⟩✴ a))
      identityʳ←
    ; assoc = λ {w x y z} → mk⇔ assoc→ assoc←
    }
    where
    open RelMonoid′ M
    open Unit ε∼_
    open Mult [_∙_]∼_
    open Equivalence

    identityˡ← : ∀ {x y} → x ≡ y → ∃⟨ ε∼_ ∩ [_∙ x ]∼ y ⟩
    identityˡ← q with ⟨ ⟨⟩✴ z , refl ⟩✴ a ← identityˡ≡ .g q = _ , z , a

    identityʳ← : ∀ {x y} → x ≡ y → ∃⟨ ε∼_ ∩ [ x ∙_]∼ y ⟩
    identityʳ← q with ⟨ refl , ⟨⟩✴ z ⟩✴ a ← identityʳ≡ .g q = _ , z , a

    assoc→ : ∀ {w x y z} →
      ∃⟨ [ w ∙ x ]∼_ ∩ [_∙ y ]∼ z ⟩ → ∃⟨ [ x ∙ y ]∼_ ∩ [ w ∙_]∼ z ⟩
    assoc→ (_ , a , b)
      with ⟨ refl , ⟨ refl , refl ⟩✴ a′ ⟩✴ b′ ←
        assoc≡ .f (⟨ ⟨ refl , refl ⟩✴ a , refl ⟩✴ b)
      = _ , a′ , b′

    assoc← : ∀ {w x y z} →
      ∃⟨ [ x ∙ y ]∼_ ∩ [ w ∙_]∼ z ⟩ → ∃⟨ [ w ∙ x ]∼_ ∩ [_∙ y ]∼ z ⟩
    assoc← (_ , a , b)
      with ⟨ ⟨ refl , refl ⟩✴ a′ , refl ⟩✴ b′ ←
        assoc≡ .g (⟨ refl , ⟨ refl , refl ⟩✴ a ⟩✴ b)
      = _ , a′ , b′

  -- The first definition is most direct, but the second definition is often
  -- much more ergonomic to use.
  -- Using the first definition regularly involves long lists of `let`s
  -- destructuring triples and quintuples, requiring names for all intermediate
  -- evidence.
  -- In contrast, the second definition lets us use a point-free style of
  -- function composition, letting us write essentially the same for
  -- implication proofs as we would for morphisms in a monoidal category.

  -- An example worth trying is assuming commutativity and proving interchange
  -- ((w + x) + (y + z) = (w + y) + (x + z)) in both styles.
  -- The second definition wins on both statement and proof.

  -- I wonder whether the second definition could be a basis for automation of
  -- relational algebra proofs.
