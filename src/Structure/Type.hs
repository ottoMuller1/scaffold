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
    StructureFamilyMember ( .. ),
    Equiv ( .. ),
    Separator ( .. ),
    Mod,
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
data StructureType = Simple | Tree | Arrow


-- equivalense family
data family Mod ( a :: Symbol )

data instance Mod "default" = ModDefault


-- helpful type to separate results of Equiv functions
data Separator a = Sure a | Incorrect | No deriving ( Functor, Show, Eq )


-- a structure data family ( not algebraic )
data family StructureFamilyMember ( a :: StructureType ) ( b :: Type )

data instance StructureFamilyMember 'Simple a where
    Rhombus :: Algebraic a => a -> ( a, a ) -> a -> StructureFamilyMember 'Simple a
    Order :: Algebraic a => a -> a -> StructureFamilyMember 'Simple a
    Dot :: Algebraic a => a -> StructureFamilyMember 'Simple a

data instance StructureFamilyMember 'Tree a =
    Node a ( StructureFamilyMember 'Tree a ) ( StructureFamilyMember 'Tree a ) | EmptyTree

data instance StructureFamilyMember 'Arrow a where
    ( :-> ) :: a -> a -> StructureFamilyMember 'Arrow a

----------------------class declarations------------------------
{-
Structure is a set* where for all a, b from set* 
exists inf (a, b), sup (a, b) from set*
-}
class Ord a => Algebraic a where
    ( /\ ) :: Operation a  -- associative, commutative, absorbing
    ( \/ ) :: Operation a  -- associative, commutative, absorbing 

{-
helpful class to make some type a marker
-}
class Marker a where
    marker :: a

{-
Equivalence is a relation that is transitive, reflexive and symmetric at the same time
-}
class ( Eq a, Marker b ) => Equiv b a where
    refl :: b -> a -> Separator ( StructureFamilyMember 'Arrow a )
    trans :: b -> StructureFamilyMember 'Arrow a -> StructureFamilyMember 'Arrow a -> Separator ( StructureFamilyMember 'Arrow a )
    sym :: b -> StructureFamilyMember 'Arrow a -> Separator ( StructureFamilyMember 'Arrow a )
    ( === ) :: a -> a -> b -> Bool
    -- default options
    refl marker a = Sure $ a :-> a
    trans marker ( a :-> b ) ( b' :-> c )
        | b /= b' = Incorrect
        | a /= b || b' /= c = No
        | otherwise = Sure $ a :-> c
    sym marker ( a :-> b )
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
instance Show a => Show ( StructureFamilyMember 'Simple a ) where
    show ( Order a b ) = show a ++ " -> " ++ show b ++ "\n"
    show ( Rhombus a b c ) = show a ++ " -> " ++ show b ++ " -> " ++ show c ++ "\n"
    show ( Dot a ) = "dot " ++ show a ++ "\n"

instance Show a => Show ( StructureFamilyMember 'Arrow a ) where
    show ( a :-> b ) = show a ++ " |-> " ++ show b

--- - - - - - - - - - - - - - Eq - - - - - - - - - - ---
instance Eq a => Eq ( StructureFamilyMember 'Simple a ) where
    Dot a == Dot b = a == b
    Order a b == Order a' b' = a == a' && b == b'
    Rhombus a ( b1, b2 ) c == Rhombus a' ( b1', b2' ) c' = 
        a == a' && 
        c == c' && 
        ( ( b1 == b1' && b2 == b2' ) || ( b1 == b2' && b2 == b1' ) )
    _ == _ = False

instance Eq a => Eq ( StructureFamilyMember 'Arrow a ) where
    ( a :-> b ) == ( a' :-> b' ) = a == a' && b == b'

--- - - - - - - - - - - - Foldable - - - - - - - - - - - ---
instance Foldable ( StructureFamilyMember 'Simple ) where
    foldr f b ( Dot a ) = f a b
    foldr f b ( Order a a' ) = f a $ f a' b
    foldr f b ( Rhombus a ( a', a'' ) a''' ) = f a $ f a' $ f a'' $ f a''' b

--- - - - - - - - - - - - - - Ord - - - - - - - - - - ---
instance Algebraic a => Ord ( StructureFamilyMember 'Simple a ) where
    Dot a <= Dot b = a <= b
    Order a b <= Order a' b' = a \/ a' == a' && b /\ b' == b'
    Rhombus a _ c <= Rhombus a' _ c' = 
        a \/ a' == a' &&
        c /\ c' == c'
    Dot a <= right = any ( == a ) right
    Order a b <= right = any ( == a ) right && any ( == b ) right
    _ <= _ = False

--- - - - - - - - - - - - - Marker - - - - - - - - - - - - - ---
-- this is a typical approach to derive Marker for every Mod example
instance ( a ~ Mod "default" ) => Marker a where
    marker = ModDefault

--- - - - - - - - - - - - Equiv - - - - - - - - - - - - - ---
instance Algebraic a => Equiv ( Mod "default" ) ( StructureFamilyMember 'Simple a ) where
    ( Dot a === Dot b ) ModDefault = not ( a > b ) || not ( b > a )
    ( Order _ b === Order _ b' ) ModDefault = 
        not ( b' >= b ) || not ( b >= b' )
    ( Rhombus a ( g, h ) b === Rhombus a' ( g', h' ) b' ) ModDefault = 
        ( Order a b === Order a' b' ) marker ||
        g <= g' ||
        g <= h' ||
        h <= g' ||
        h <= h'
    ( _ === _ ) ModDefault = False

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
instance Algebraic a => Algebraic ( StructureFamilyMember 'Simple a ) where
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
