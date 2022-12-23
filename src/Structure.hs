{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-#LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
module Structure ( 
    Structure ( .. ) ) where

import Data.Kind ( Type )

----------------------type declaration--------------------------
-- an operation type synonimus
type Operation a = a -> a -> a

-- tree type
data StructureType = Simple | Tree

-- a structure type family
data family StructureFamilyMember ( a :: StructureType ) ( b :: Type )

data instance StructureFamilyMember Simple a where
    Rhombus :: Structure a => a -> ( a, a ) -> a -> StructureFamilyMember Simple a
    Order :: Structure a => a -> a -> StructureFamilyMember Simple a
    Dot :: Structure a => a -> StructureFamilyMember Simple a

data instance StructureFamilyMember Tree a =
    Node a ( StructureFamilyMember Tree a ) ( StructureFamilyMember Tree a ) | EmptyTree

----------------------class declarations------------------------
{-
Structure is a set* where for all a, b from set* 
exists inf (a, b), sup (a, b) from set*
-}
class Ord a => Structure a where
    ( /\ ) :: Operation a  -- associative, commutative, absorbing
    ( \/ ) :: Operation a  -- associative, commutative, absorbing 

------------------------------instances-------------------------
--- - - - - - - - - - - - Show - - - - - - - - - - - ---
instance Show a => Show ( StructureFamilyMember Simple a ) where
    show ( Order a b ) = show a ++ " -> " ++ show b ++ "\n"
    show ( Rhombus a b c ) = show a ++ " -> " ++ show b ++ " -> " ++ show c ++ "\n"
    show ( Dot a ) = "dot " ++ show a ++ "\n"

--- - - - - - - - - - - - - - Eq - - - - - - - - - - ---
instance Eq a => Eq ( StructureFamilyMember Simple a ) where
    Dot a == Dot b = a == b
    Order a b == Order a' b' = a == a' && b == b'
    Rhombus a b c == Rhombus a' b' c' = a == a' && b == b' && c == c'
    _ == _ = False

--- - - - - - - - - - - - - - Ord - - - - - - - - - - ---
instance Ord a => Ord ( StructureFamilyMember Simple a ) where
    Dot a <= Dot b = a <= b
    Order a b <= Order a' b' = b == a' && a <= b && a' <= b' && a <= b'
    Rhombus a ( ba, bb ) c <= Rhombus a' ( ba', bb' ) c' = 
        a <= ba && a <= bb && ba <= c && bb <= c &&
        a' <= ba' && a' <= bb' && ba' <= c' && bb' <= c' &&
        c <= a' && a <= c'
    Dot _ <= Order _ _ = True
    Order _ _ <= Rhombus {} = True
    Dot _ <= Rhombus {} = True
    Order _ _ <= Dot _ = False
    Rhombus {} <= Order _ _ = False
    Rhombus {} <= Dot _ = False

--- - - - - - - - - - - - Structure - - - - - - - - - - - ---
instance Structure a => Structure ( StructureFamilyMember Simple a ) where
    Dot a /\ Dot b = Dot $ a /\ b
    Order a b /\ Order a' b' = Order ( a /\ a') $ b /\ b'
    Rhombus a b c /\ Rhombus a' b' c' = Rhombus ( a /\ a' ) ( b /\ b' ) ( c /\ c' )
    Dot _ /\ a = a
    Order _ _ /\ a = a
    a /\ Dot _ = a
    a /\ Order _ _ = a
    Dot a \/ Dot b = Dot $ a \/ b
    Order a b \/ Order a' b' = Order ( a \/ a' ) ( b \/ b' )
    Rhombus a b c \/ Rhombus a' b' c' = Rhombus ( a \/ a' ) ( b \/ b' ) ( c \/ c' )
    Rhombus {} \/ a = a
    Order _ _ \/ a = a
    a \/ Rhombus {} = a
    a \/ Order _ _ = a
 
instance Structure Word where
    ( /\ ) = max
    ( \/ ) = min

instance Structure Ordering where
    ( /\ ) = max
    ( \/ ) = min

instance Structure Int where
    ( /\ ) = max
    ( \/ ) = min

instance Structure Float where
    ( /\ ) = max
    ( \/ ) = min

instance Structure Double where
    ( /\ ) = max
    ( \/ ) = min

instance Structure Char where
    ( /\ ) = max
    ( \/ ) = min

instance Structure Bool where
    ( /\ ) = max
    ( \/ ) = min

instance Structure a => Structure ( Maybe a ) where
    Nothing /\ _ = Nothing
    _ /\ Nothing = Nothing
    ( Just a ) /\ ( Just b ) = Just $ a /\ b
    Nothing \/ _ = Nothing
    _ \/ Nothing = Nothing
    ( Just a ) \/ ( Just b ) = Just $ a \/ b

instance ( Structure a, Structure b ) => Structure ( a, b ) where
    ( a, b ) /\ ( c, d ) = ( a /\ c, b /\ d )
    ( a, b ) \/ ( c, d ) = ( a \/ c, b \/ d )
