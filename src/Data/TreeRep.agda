
module Data.TreeRep where

open import Prelude
open import Container.Traversable
open import Builtin.Reflection
open import Builtin.Float

data Leaf : Set where
  char   : Char → Leaf
  string : String → Leaf
  float  : Float → Leaf
  name   : Name → Leaf

data TreeRep : Set where
  leaf : Leaf → TreeRep
  node : Nat → List TreeRep → TreeRep

--- Eq instance ---

private
  leaf-char-inj : ∀ {x y} → Leaf.char x ≡ char y → x ≡ y
  leaf-char-inj refl = refl

  leaf-string-inj : ∀ {x y} → Leaf.string x ≡ string y → x ≡ y
  leaf-string-inj refl = refl

  leaf-float-inj : ∀ {x y} → Leaf.float x ≡ float y → x ≡ y
  leaf-float-inj refl = refl

  leaf-name-inj : ∀ {x y} → Leaf.name x ≡ name y → x ≡ y
  leaf-name-inj refl = refl

  leaf-inj : ∀ {x y} → leaf x ≡ leaf y → x ≡ y
  leaf-inj refl = refl

  node-inj₁ : ∀ {x y z w} → node x z ≡ node y w → x ≡ y
  node-inj₁ refl = refl

  node-inj₂ : ∀ {x y z w} → node x z ≡ node y w → z ≡ w
  node-inj₂ refl = refl

  eq-leaf : (x y : Leaf) → Dec (x ≡ y)
  eq-leaf (char x) (char x₁) = decEq₁ leaf-char-inj (x == x₁)
  eq-leaf (string x) (string x₁) = decEq₁ leaf-string-inj (x == x₁)
  eq-leaf (float x) (float x₁) = decEq₁ leaf-float-inj (x == x₁)
  eq-leaf (name x) (name x₁) = decEq₁ leaf-name-inj (x == x₁)
  eq-leaf (char x) (string x₁) = no λ()
  eq-leaf (char x) (float x₁) = no λ()
  eq-leaf (char x) (name x₁) = no λ()
  eq-leaf (string x) (char x₁) = no λ()
  eq-leaf (string x) (float x₁) = no λ()
  eq-leaf (string x) (name x₁) = no λ()
  eq-leaf (float x) (char x₁) = no λ()
  eq-leaf (float x) (string x₁) = no λ()
  eq-leaf (float x) (name x₁) = no λ()
  eq-leaf (name x) (char x₁) = no λ()
  eq-leaf (name x) (string x₁) = no λ()
  eq-leaf (name x) (float x₁) = no λ()

instance
  EqLeaf : Eq Leaf
  _==_ {{EqLeaf}} = eq-leaf

private
  eq-tree  : (x y : TreeRep) → Dec (x ≡ y)
  eq-trees : (xs ys : List TreeRep) → Dec (xs ≡ ys)

  eq-tree (leaf x) (leaf x₁) = decEq₁ leaf-inj (x == x₁)
  eq-tree (leaf x) (node x₁ x₂) = no λ()
  eq-tree (node x x₁) (leaf x₂) = no λ()
  eq-tree (node x xs) (node y ys) = decEq₂ node-inj₁ node-inj₂ (x == y) (eq-trees xs ys)

  eq-trees [] [] = yes refl
  eq-trees [] (x ∷ ys) = no λ()
  eq-trees (x ∷ xs) [] = no λ()
  eq-trees (x ∷ xs) (y ∷ ys) = decEq₂ cons-inj-head cons-inj-tail (eq-tree x y) (eq-trees xs ys)

instance
  EqTree : Eq TreeRep
  _==_ {{EqTree}} = eq-tree

--- Ord instance ---

data LessLeaf : Leaf → Leaf → Set where
  char         : ∀ {x y} → x < y → LessLeaf (char x) (char y)
  string       : ∀ {x y} → x < y → LessLeaf (string x) (string y)
  float        : ∀ {x y} → x < y → LessLeaf (float x) (float y)
  name         : ∀ {x y} → x < y → LessLeaf (name x) (name y)
  char<string  : ∀ {x y} → LessLeaf (char x) (string y)
  char<float   : ∀ {x y} → LessLeaf (char x) (float y)
  char<name    : ∀ {x y} → LessLeaf (char x) (name y)
  string<float : ∀ {x y} → LessLeaf (string x) (float y)
  string<name  : ∀ {x y} → LessLeaf (string x) (name y)
  float<name   : ∀ {x y} → LessLeaf (float x) (name y)

private
  cmp-leaf : (a b : Leaf) → Comparison LessLeaf a b
  cmp-leaf (char x) (char x₁) = mapComparison char (compare x x₁)
  cmp-leaf (string x) (string x₁) = mapComparison string (compare x x₁)
  cmp-leaf (float x) (float x₁) = mapComparison float (compare x x₁)
  cmp-leaf (name x) (name x₁) = mapComparison name (compare x x₁)
  cmp-leaf (char x) (string x₁) = less char<string
  cmp-leaf (char x) (float x₁) = less char<float
  cmp-leaf (char x) (name x₁) = less char<name
  cmp-leaf (string x) (char x₁) = greater char<string
  cmp-leaf (string x) (float x₁) = less string<float
  cmp-leaf (string x) (name x₁) = less string<name
  cmp-leaf (float x) (char x₁) = greater char<float
  cmp-leaf (float x) (string x₁) = greater string<float
  cmp-leaf (float x) (name x₁) = less float<name
  cmp-leaf (name x) (char x₁) = greater char<name
  cmp-leaf (name x) (string x₁) = greater string<name
  cmp-leaf (name x) (float x₁) = greater float<name

instance
  OrdLeaf : Ord Leaf
  OrdLeaf = defaultOrd cmp-leaf

data LessTree : TreeRep → TreeRep → Set where
  leaf      : ∀ {x y} → x < y → LessTree (leaf x) (leaf y)
  leaf<node : ∀ {x y ys} → LessTree (leaf x) (node y ys)
  tag<      : ∀ {x y xs ys} → x < y → LessTree (node x xs) (node y ys)
  children< : ∀ {x xs ys} → LessList LessTree xs ys → LessTree (node x xs) (node x ys)

private
  cmp-tree  : ∀ x y → Comparison LessTree x y
  cmp-trees : ∀ xs ys → Comparison (LessList LessTree) xs ys

  cmp-tree (leaf x) (leaf y) = mapComparison leaf (compare x y)
  cmp-tree (leaf _) (node _ _) = less leaf<node
  cmp-tree (node _ _) (leaf _) = greater leaf<node
  cmp-tree (node x xs) (node  y ys)  with compare x y
  cmp-tree (node x xs) (node  y ys)  | less    x<y = less (tag< x<y)
  cmp-tree (node x xs) (node  y ys)  | greater x>y = greater (tag< x>y)
  cmp-tree (node x xs) (node .x ys)  | equal refl with cmp-trees xs ys
  cmp-tree (node x xs) (node .x ys)  | equal refl | less    lt = less (children< lt)
  cmp-tree (node x xs) (node .x .xs) | equal refl | equal refl = equal refl
  cmp-tree (node x xs) (node .x ys)  | equal refl | greater gt = greater (children< gt)

  cmp-trees [] [] = equal refl
  cmp-trees []       (x ∷ ys) = less nil<cons
  cmp-trees (x ∷ xs) []       = greater nil<cons
  cmp-trees (x ∷ xs) (y ∷ ys) = compareCons (cmp-tree x y) (cmp-trees xs ys)

instance
  OrdTree : Ord TreeRep
  OrdTree = defaultOrd cmp-tree

--- Encoding types as trees ---

record TreeEncoding {a} (A : Set a) : Set a where
  constructor treeEncoding
  field
    treeEncode : A → TreeRep
    treeDecode : TreeRep → Maybe A
    isTreeEmbedding : ∀ x → treeDecode (treeEncode x) ≡ just x

open TreeEncoding {{...}} public

module _ {a} {A : Set a} {{_ : TreeEncoding A}} where
  private
    encode-injective : (x y : A) → treeEncode x ≡ treeEncode y → x ≡ y
    encode-injective x y eq = eraseEquality $ just-inj $
      isTreeEmbedding x ʳ⟨≡⟩ cong treeDecode eq ⟨≡⟩ isTreeEmbedding y

    decTreeEq : (x y : A) → Dec (x ≡ y)
    decTreeEq x y with treeEncode x == treeEncode y
    decTreeEq x y | yes eq = yes (encode-injective x y eq)
    decTreeEq x y | no !eq = no λ x=y → !eq (cong treeEncode x=y)

  EqByTreeEncoding : Eq A
  _==_ {{EqByTreeEncoding}} = decTreeEq

  data LessEncoding (x y : A) : Set a where
    less-enc : treeEncode x < treeEncode y → LessEncoding x y

  OrdByTreeEncoding : Ord A
  OrdByTreeEncoding = defaultOrd λ x y → injectComparison (encode-injective _ _) less-enc $
                                          (compare on treeEncode) x y

--- Encodings for standard types ---

instance
  EncodeNat : TreeEncoding Nat
  EncodeNat = treeEncoding enc dec (λ _ → refl)
    where
      enc : Nat → TreeRep
      enc n = node n []

      dec : TreeRep → Maybe Nat
      dec (node n _) = just n
      dec (leaf _) = nothing

  EncodeBool : TreeEncoding Bool
  EncodeBool = treeEncoding enc dec emb
    where
      enc : Bool → TreeRep
      enc false = node 0 []
      enc true = node 1 []

      dec : TreeRep → Maybe Bool
      dec (node 0 _) = just false
      dec _          = just true

      emb : ∀ b → dec (enc b) ≡ just b
      emb false = refl
      emb true  = refl

  EncodeMaybe : ∀ {a} {A : Set a} {{_ : TreeEncoding A}} → TreeEncoding (Maybe A)
  EncodeMaybe {A = A} = treeEncoding enc dec emb
    where
      enc : Maybe A → TreeRep
      enc nothing  = node 0 []
      enc (just x) = node 1 [ treeEncode x ]

      dec : TreeRep → Maybe (Maybe A)
      dec (node 0 _)       = just nothing
      dec (node _ (x ∷ _)) = just <$> treeDecode x
      dec _                = nothing

      emb : ∀ x → dec (enc x) ≡ just x
      emb nothing  = refl
      emb (just x) = just =$= isTreeEmbedding x

  EncodeSigma : ∀ {a b} {A : Set a} {B : A → Set b}
                  {{EncA : TreeEncoding A}} {{EncB : ∀ {x} → TreeEncoding (B x)}} →
                  TreeEncoding (Σ A B)
  EncodeSigma {A = A} {B = B} = treeEncoding enc dec emb
    where
      enc : Σ A B → TreeRep
      enc (x , y) = node 0 (treeEncode x ∷ treeEncode y ∷ [])

      dec : TreeRep → Maybe (Σ A B)
      dec (node _ (x ∷ y ∷ _)) =
        do x ← treeDecode x
        =| y ← treeDecode y
        =| return (x , y)
      dec _ = nothing

      emb : ∀ x → dec (enc x) ≡ just x
      emb (x , y) rewrite isTreeEmbedding x | isTreeEmbedding y = refl

  EncodeList : ∀ {a} {A : Set a} {{_ : TreeEncoding A}} → TreeEncoding (List A)
  treeEncode {{EncodeList}} xs          = node 0 (map treeEncode xs)
  treeDecode {{EncodeList}} (node _ xs) = traverse′ treeDecode xs
  treeDecode {{EncodeList}} _           = nothing
  isTreeEmbedding {{EncodeList}} []       = refl
  isTreeEmbedding {{EncodeList}} (x ∷ xs) = _∷_ =$= isTreeEmbedding x =*= isTreeEmbedding xs

--- Example ---

-- private
--   data TestData : Set where
--     cA : TestData → TestData
--     cB : TestData → TestData → TestData
--     cC : TestData
--     cD : TestData → TestData → TestData

--   private
--     encodeTest : TestData → TreeRep
--     encodeTest (cA x)   = node 0 (encodeTest x ∷ [])
--     encodeTest (cB x y) = node 1 (encodeTest x ∷ encodeTest y ∷ [])
--     encodeTest cC       = node 2 []
--     encodeTest (cD x y) = node 3 (encodeTest x ∷ encodeTest y ∷ [])

--     decodeTest : TreeRep → Maybe TestData
--     decodeTest (leaf _) = nothing
--     decodeTest (node 0 (x ∷ []))     = cA <$> decodeTest x
--     decodeTest (node 1 (x ∷ y ∷ [])) = cB <$> decodeTest x <*> decodeTest y
--     decodeTest (node 2 [])           = just cC
--     decodeTest (node 3 (x ∷ y ∷ [])) = cD <$> decodeTest x <*> decodeTest y
--     decodeTest _ = nothing

--     embeddingTest : ∀ x → decodeTest (encodeTest x) ≡ just x
--     embeddingTest (cA x)   = cA =$= embeddingTest x
--     embeddingTest (cB x y) = cB =$= embeddingTest x =*= embeddingTest y
--     embeddingTest cC       = refl
--     embeddingTest (cD x y) = cD =$= embeddingTest x =*= embeddingTest y

--   instance
--     EncodeTest : TreeEncoding TestData
--     EncodeTest = record { treeEncode      = encodeTest
--                         ; treeDecode      = decodeTest
--                         ; isTreeEmbedding = embeddingTest }

--     EqTest : Eq TestData
--     EqTest = EqByTreeEncoding

--     OrdTest : Ord TestData
--     OrdTest = OrdByTreeEncoding
