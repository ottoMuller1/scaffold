{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Structure.Type ( 
    Algebraic ( .. ),
    StructureType ( .. ),
    Structure ( .. ),
    Equiv ( .. ),
    Separator ( .. ),
    Mod ( .. ),
    Marker ( .. ) ) where

-------------------------imports--------------------------------
-- foreign
import Data.Kind ( Type )
import Data.List ( union, intersect )
import GHC.Types ( Symbol )

----------------------type declaration--------------------------
-- an operation type synonimus
type Operation a = a -> a -> a


-- structure ( doesn't mean "algebraic" ) type
-- Show, Eq
data StructureType = Simple | Tree | Arrow | Relation deriving ( Show, Eq )


-- equivalense family
-- used in data class Equiv
{-
using like 
a === b mod q, where q is equivalence

data instance Mod "q" = ModQ
instance Marker ( Mod "q" ) where
    marker = ModQ
instance Equiv ( Mod "q" ) `some type` where
    ( a === b ) ModQ = ...
    ...
-}
data family Mod ( a :: Symbol )

-- Show, Eq, Marker
data instance Mod "default" = ModDefault

-- Show, Eq, Marker
data instance Mod "relation type" = RelationType

-- Show, Eq, Marker
data instance Mod "relation weight" = RelationWeight


-- helpful type to separate results of Equiv functions
-- Functor, Show, Eq
data Separator a = Sure a | Incorrect | No deriving ( Functor, Show, Eq )


-- a structure data family ( not algebraic )
data family Structure ( a :: StructureType ) ( b :: Type )

-- Show, Eq, Foldable, Ord, Algebraic, Equiv
data instance Structure 'Simple a where
    Rhombus :: Algebraic a => a -> ( a, a ) -> a -> Structure 'Simple a
    Order :: Algebraic a => a -> a -> Structure 'Simple a
    Dot :: Algebraic a => a -> Structure 'Simple a

-- Eq, Ord, Foldable, Functor, Equiv
data instance Structure 'Tree a =
    Node a ( Structure 'Tree a ) ( Structure 'Tree a ) | EmptyTree

-- Show, Eq, Semigroup, Functor
data instance Structure 'Arrow a where
    ( :-> ) :: a -> a -> Structure 'Arrow a

-- Show, Eq, Ord
data instance Structure 'Relation a where
    {-
        a graph member to build a custom graph
        using

        a :--- (b, Just 5)
        a :--> (b, Nothing)
        ...
    -}
    Noose :: ( Eq a, Show b ) => a -> Maybe b -> Structure 'Relation a
    ( :--- ) :: ( Eq a, Show b ) => a -> ( a, Maybe b ) -> Structure 'Relation a
    ( :--> ) :: ( Eq a, Show b ) => a -> ( a, Maybe b ) -> Structure 'Relation a
    ( :<-> ) :: ( Eq a, Show b ) => a -> ( a, Maybe b ) -> Structure 'Relation a
    NoGraph :: Eq a => Structure 'Relation a

----------------------class declarations------------------------
{-
Algebraic Structure is a set* where for all a, b from set* 
exists inf (a, b), sup (a, b) from set*
-}
class Ord a => Algebraic a where
    ( /\ ) :: Operation a  -- associative, commutative, absorbing
    ( \/ ) :: Operation a  -- associative, commutative, absorbing

    dot :: a -> Structure 'Simple a
    dot = Dot

    ( <+> ) :: a -> a -> Structure 'Simple a
    a <+> b
        | a > b = Order b a
        | b > a = Order a b
        | a == b = Dot a
        | otherwise = Rhombus ( a \/ b ) ( a, b ) ( a /\ b )

    rhombus :: a -> a -> a -> a -> Maybe ( Structure 'Simple a )
    rhombus a b c d
        | b > a && c > a && d > b && d > c && not ( b > c ) && not ( c > b ) = Just $ Rhombus a ( b, c ) d
        | otherwise = Nothing

    {-# MINIMAL ( /\ ), ( \/ ) #-}

{-
helpful class to make some type a marker
this is a marker for Equiv data class

using 

data MyType = MyType
instance Marker MyType where
    marker = MyType
instance Equiv `some type` where
    ( a === b ) MyType = ...
    ...
-}
class Marker a where
    marker :: a

{-
Equivalence is a relation that is transitive, reflexive and symmetric at the same time
-}
class ( Eq a, Marker b ) => Equiv b a where
    refl :: b -> a -> Separator ( Structure 'Arrow a )
    trans :: b -> Structure 'Arrow a -> Structure 'Arrow a -> Separator ( Structure 'Arrow a )
    sym :: b -> Structure 'Arrow a -> Separator ( Structure 'Arrow a )
    ( === ) :: a -> a -> b -> Bool
    -- default options
    refl _ a = Sure $ a :-> a
    trans _ ( a :-> b ) ( b' :-> c )
        | b /= b' = Incorrect
        | a /= b || b' /= c = No
        | otherwise = Sure $ a :-> c
    sym _ ( a :-> b )
        | a == b = Sure $ b :-> a
        | otherwise = No
    ( a === b ) marker = 
        refl marker a == ( Sure $ a :-> a ) && 
        refl marker b == ( Sure $ b :-> b ) &&
        sym marker ( a :-> b ) == ( Sure $ b :-> a ) &&
        sym marker ( b :-> a ) == ( Sure $ a :-> b )
        -- no such implementation of trans in ===

------------------------------instances-------------------------
--- - - - - - - - - - - - Show - - - - - - - - - - - ---
instance Show a => Show ( Structure 'Simple a ) where
    show ( Order a b ) = show a ++ " -> " ++ show b ++ "\n"
    show ( Rhombus a b c ) = show a ++ " -> " ++ show b ++ " -> " ++ show c ++ "\n"
    show ( Dot a ) = "dot " ++ show a ++ "\n"

instance Show a => Show ( Structure 'Arrow a ) where
    show ( a :-> b ) = show a ++ " |-> " ++ show b

instance Show a => Show ( Structure 'Relation a ) where
    show ( Noose a ( Just b ) ) = show a ++ " " ++ show b
    show ( Noose a Nothing ) = show a
    show NoGraph = "no graph"
    show ( a :--- ( b, Just c ) ) = show a ++ " --- " ++ show b ++ " " ++ show c
    show ( a :--- ( b, Nothing ) ) = show a ++ " --- " ++ show b
    show ( a :--> ( b, Just c ) ) = show a ++ " --> " ++ show b ++ " " ++ show c
    show ( a :--> ( b, Nothing ) ) = show a ++ " --> " ++ show b
    show ( a :<-> ( b, Just c ) ) = show a ++ " <-> " ++ show b ++ " " ++ show c
    show ( a :<-> ( b, Nothing ) ) = show a ++ " <-> " ++ show b

instance Show ( Mod "default" ) where
    show ModDefault = "default equivalence"

instance Show ( Mod "relation type" ) where
    show RelationType = "the same type of relation"

instance Show ( Mod "relation weight" ) where
    show RelationWeight = "the same weight of relation"

--- - - - - - - - - - - Semigroup - - - - - - - - - - ---
instance Algebraic a => Semigroup ( Structure 'Arrow a ) where
    ( a :-> b ) <> ( a' :-> b' ) = ( a \/ a' ) :-> ( b /\ b' )

--- - - - - - - - - - - - - - Eq - - - - - - - - - - ---
instance Eq a => Eq ( Structure 'Simple a ) where
    Dot a == Dot b = a == b
    Order a b == Order a' b' = a == a' && b == b'
    Rhombus a ( b1, b2 ) c == Rhombus a' ( b1', b2' ) c' = 
        a == a' && 
        c == c' && 
        ( ( b1 == b1' && b2 == b2' ) || ( b1 == b2' && b2 == b1' ) )
    _ == _ = False

instance Eq a => Eq ( Structure 'Tree a ) where
    EmptyTree == EmptyTree = True
    EmptyTree == _ = False
    _ == EmptyTree = False
    ( Node a left right ) == ( Node a' left' right' ) = a == a' && left == left' && right == right'

instance Eq a => Eq ( Structure 'Arrow a ) where
    ( a :-> b ) == ( a' :-> b' ) = a == a' && b == b'

instance Eq ( Structure 'Relation a ) where
    ( a :--- b ) == ( a' :--- b' ) = a == a' && fst b == fst b'
    ( a :--> b ) == ( a' :--> b' ) = a == a' && fst b == fst b'
    ( a :<-> b ) == ( a' :<-> b' ) = a == a' && fst b == fst b'
    Noose a _ == Noose a' _ = a == a'
    NoGraph == NoGraph = True
    _ == _ = False

instance Eq ( Mod "default" ) where
    ModDefault == ModDefault = True

instance Eq ( Mod "relation type" ) where
    RelationType == RelationType = True

instance Eq ( Mod "relation weight" ) where
    RelationWeight == RelationWeight = True

--- - - - - - - - - - - - Foldable - - - - - - - - - - - ---
instance Foldable ( Structure 'Simple ) where
    foldr f b ( Dot a ) = f a b
    foldr f b ( Order a a' ) = f a $ f a' b
    foldr f b ( Rhombus a ( a', a'' ) a''' ) = f a $ f a' $ f a'' $ f a''' b

instance Foldable ( Structure 'Tree ) where
    foldr _ b EmptyTree = b
    foldr f b ( Node a left right ) = foldr f ( f a $ foldr f b right ) left

--- - - - - - - - - - - - - - Functor - - - - - - - - - ---
instance Functor ( Structure 'Tree ) where
    fmap _ EmptyTree = EmptyTree
    fmap f ( Node a left right ) = Node ( f a ) ( fmap f left ) ( fmap f right )

instance Functor ( Structure 'Arrow ) where
    fmap f ( a :-> b ) = ( f a ) :-> ( f b )

--- - - - - - - - - - - - - - Ord - - - - - - - - - - ---
instance Algebraic a => Ord ( Structure 'Simple a ) where
    Dot a <= Dot b = a <= b
    Order a b <= Order a' b' = a \/ a' == a' && b /\ b' == b'
    Rhombus a _ c <= Rhombus a' _ c' = 
        a \/ a' == a' &&
        c /\ c' == c'
    Dot a <= right = any ( == a ) right
    Order a b <= right = any ( == a ) right && any ( == b ) right
    _ <= _ = False

instance Eq a => Ord ( Structure 'Tree a ) where
    EmptyTree <= EmptyTree = True
    ( Node _ _ _ ) <= EmptyTree = False
    a <= ( Node _ left' right' ) = a == left' || a == right'

instance Ord ( Structure 'Relation a ) where
    Noose a _ <= Noose b _ = a == b
    Noose a _ <= ( b :--- ( c, _ ) ) = a == b || a == c
    Noose a _ <= ( _ :--> ( c, _ ) ) = c == a
    Noose a _ <= ( b :<-> ( c, _ ) ) = a == b || a == c
    Noose _ _ <= NoGraph = False

    NoGraph <= _ = False

    ( a :--- ( b, _ ) ) <= Noose d _ = a == d || b == d
    ( a :--- ( b, _ ) ) <= ( a' :--- ( b', _ ) ) = a == a' || b == a' || a == b' || b == b'
    ( a :--- ( b, _ ) ) <= ( _ :--> ( b', _ ) ) = a == b' || b == b'
    ( a :--- ( b, _ ) ) <= ( a' :<-> ( b', _ ) ) = a == a' || b == a' || a == b' || b == b'
    ( _ :--- _ ) <= NoGraph = False

    ( a :--> _ ) <= Noose b _ = b == a
    ( a :--> _ ) <= ( a' :--- ( b', _ ) ) = a == b' || a == a'
    ( a :--> _ ) <= ( _ :--> ( b', _ ) ) = a == b'
    ( a :--> _ ) <= ( a' :<-> ( b', _ ) ) = a == b' || a == a'
    ( _ :--> _ ) <= NoGraph = False

    ( a :<-> ( b, _ ) ) <= Noose d _ = a == d || b == d
    ( a :<-> ( b, _ ) ) <= ( a' :--- ( b', _ ) ) = a == a' || b == a' || a == b' || b == b'
    ( a :<-> ( b, _ ) ) <= ( _ :--> ( b', _ ) ) = a == b' || b == b'
    ( a :<-> ( b, _ ) ) <= ( a' :<-> ( b', _ ) ) = a == a' || b == a' || a == b' || b == b'
    ( _ :<-> _ ) <= NoGraph = False

--- - - - - - - - - - - - - Marker - - - - - - - - - - - - - ---
-- this is a typical approach to derive Marker for every Mod example
instance Marker ( Mod "default" ) where
    marker = ModDefault

instance Marker ( Mod "relation type" ) where
    marker = RelationType

instance Marker ( Mod "relation weight" ) where
    marker = RelationWeight

--- - - - - - - - - - - - Equiv - - - - - - - - - - - - - ---
instance Algebraic a => Equiv ( Mod "default" ) ( Structure 'Simple a ) where
    ( Dot a === Dot b ) ModDefault = not ( a > b ) || not ( b > a )
    ( Order _ b === Order _ b' ) ModDefault = 
        not ( b' >= b ) || not ( b >= b' )
    ( Rhombus a ( g, h ) b === Rhombus a' ( g', h' ) b' ) ModDefault = 
        ( Order a b === Order a' b' ) ModDefault ||
        g <= g' ||
        g <= h' ||
        h <= g' ||
        h <= h'
    ( _ === _ ) ModDefault = False

instance Eq a => Equiv ( Mod "default" ) ( Structure 'Tree a )

-- default instances
instance Eq a => Equiv ( Mod "default" ) [ a ] where
    ( a === b ) ModDefault = all ( `elem` b ) a && all ( `elem` a ) b

instance Equiv ( Mod "default" ) Word

instance Equiv ( Mod "default" ) Ordering

instance Equiv ( Mod "default" ) Int

instance Equiv ( Mod "default" ) Integer

instance Equiv ( Mod "default" ) Float

instance Equiv ( Mod "default" ) Double

instance Equiv ( Mod "default" ) Char

instance Equiv ( Mod "default" ) Bool

instance Equiv ( Mod "default" ) ()

instance Eq a => Equiv ( Mod "default" ) ( Maybe a )

--- - - - - - - - - - - - Structure - - - - - - - - - - - ---
instance Algebraic a => Algebraic ( Structure 'Simple a ) where
    Dot a /\ Dot b
        | a > b = Order b a
        | b > a = Order a b
        | otherwise = Dot $ a /\ b
    Dot a /\ Order _ c = Dot $ a /\ c
    Dot a /\ Rhombus _ _ c = Dot $ a /\ c
    left@( Order a b ) /\ right@( Order a' b' )
        | left > right = Order a' b
        | right > left = Order a b'
        | left == right = Order a b
        | b == b' = Rhombus ( a \/ a' ) ( a, a' ) b
        | a == a' = Rhombus a ( b, b' ) ( b /\ b' )
        | otherwise = Order ( a \/ a' ) ( b /\ b' )
    Order a b /\ Rhombus _ ( a', b' ) _ = Order ( a \/ a' \/ b' ) ( b /\ a' /\ b' )
    Rhombus _ ( b, c ) _ /\ Rhombus _ ( b', c' ) _ = 
        Order ( b \/ c \/ b' \/ c' ) ( b /\ c /\ b' /\ c' )
    a /\ b = b /\ a

    Dot a \/ Dot b = Dot $ a \/ b
    Dot a \/ Order b _ = Dot $ a \/ b
    Dot a \/ Rhombus b _ _ = Dot $ a \/ b
    Order a _ \/ Order a' _ = Dot $ a \/ a'
    Order a b \/ Rhombus a' _ b' = Order ( a \/ a' ) ( b /\ b' )
    Rhombus a _ b \/ Rhombus a' _ b' = Order a b /\ Order a' b'
    a \/ b = b \/ a

-- default instances
instance Ord a => Algebraic [ a ] where
    ( /\ ) = union
    ( \/ ) = intersect

instance Algebraic Word where
    ( /\ ) = max
    ( \/ ) = min

instance Algebraic Ordering where
    ( /\ ) = max
    ( \/ ) = min

instance Algebraic Int where
    ( /\ ) = max
    ( \/ ) = min

instance Algebraic Integer where
    ( /\ ) = max
    ( \/ ) = min

instance Algebraic Float where
    ( /\ ) = max
    ( \/ ) = min

instance Algebraic Double where
    ( /\ ) = max
    ( \/ ) = min

instance Algebraic Char where
    ( /\ ) = max
    ( \/ ) = min

instance Algebraic Bool where
    ( /\ ) = max
    ( \/ ) = min

instance Algebraic () where
    _ /\ _ = ()
    _ \/ _ = ()

instance Algebraic a => Algebraic ( Maybe a ) where
    Nothing /\ _ = Nothing
    _ /\ Nothing = Nothing
    ( Just a ) /\ ( Just b ) = Just $ a /\ b
    Nothing \/ _ = Nothing
    _ \/ Nothing = Nothing
    ( Just a ) \/ ( Just b ) = Just $ a \/ b
