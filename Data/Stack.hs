{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Stack (
        mirror,
        rearrangeL,
        rearrangeR,
        envelope,
        diag,
        wrap,
        mirrorA,
        rearrangeLA,
        rearrangeRA,
        Stack(..),
        BoolStack(..),
        BoundStack(..),
        IntegerStack(..),
        FramingStack(..),
        FrameStack,
        moveR,
        moveL,
        copyR,
        copyL,
        exch,
        toPairStack,
        fromPairStack,
        PairStack,
        dd
        ) where

import Control.Arrow
import Data.Dynamic
import Data.List
import Data.Maybe

mirror :: (a, b) -> (b, a)
mirror = snd &&& fst

rearrangeL :: (a, (b, c)) -> ((a, b), c)
rearrangeL = (fst &&& (snd >>> fst)) &&& (snd >>> snd)

rearrangeR :: ((a, b), c) -> (a, (b, c))
rearrangeR = (fst >>> fst) &&& ((fst >>> snd) &&& snd)

envelope :: (a, Either b c) -> Either (a, b) (a, c)
envelope = mirror >>> first ((flip (,) >>> (>>> Left)) ||| (flip (,) >>> (>>> Right))) >>> app

diag :: (a -> a -> b) -> (a -> b)
diag = uncurry >>> (id &&& id >>>)

wrap :: Arrow a => a b c -> a d e -> a c d -> a b e
wrap = (>>>) >>> (>>>) >>> (<<< (<<<))

mirrorA :: Arrow a => a (b, c) (d, e) -> a (c, b) (e, d)
mirrorA = (arr mirror) `wrap` (arr mirror)

rearrangeLA :: Arrow a => a (b, (c, d)) (e, (f, g)) -> a ((b, c), d) ((e, f), g)
rearrangeLA = (arr rearrangeR) `wrap` (arr rearrangeL)

rearrangeRA :: Arrow a => a ((b, c), d) ((e, f), g) -> a (b, (c, d)) (e, (f, g))
rearrangeRA = (arr rearrangeL) `wrap` (arr rearrangeR)

class Stack a b where

    new :: a b

    pop :: a b -> (b, a b)

    push :: (b, a b) -> a b

    push' :: b -> a b -> a b
    push' = curry push

    prc :: ((b, a b) -> (b, a b)) -> (a b -> a b)
    prc = pop `wrap` push

    yank :: (b -> b) -> (a b -> a b)
    yank = first >>> prc

    snip :: (a b -> a b) -> (a b -> a b)
    snip = second >>> prc

    prc2 :: (((b, b), a b) -> ((b, b), a b)) -> (a b -> a b)
    prc2 = rearrangeRA >>> (second pop) `wrap` (second push) >>> prc

    yank2 :: ((b, b) -> (b, b)) -> (a b -> a b)
    yank2 = first >>> prc2

    snip2 :: (a b -> a b) -> (a b -> a b)
    snip2 = second >>> prc2

    peek :: a b -> b
    peek = pop >>> fst

    inspect :: a b -> (b, a b)
    inspect = peek &&& id

    {- x -- -}
    discard :: a b -> a b
    discard = pop >>> snd

    {- y x -- x -}
    nip :: a b -> a b
    nip = snip discard

    {- x -- x x -}
    dup :: a b -> a b
    dup = inspect >>> push

    {- y x -- x y -}
    swap :: a b -> a b
    swap = yank2 mirror

    {- y x -- y x y -}
    over :: a b -> a b
    over = ((discard >>> peek) &&& id) >>> push

    {- y x -- x y x -}
    tuck :: a b -> a b
    tuck = swap >>> over

    {- z y x -- y x z -}
    rot :: a b -> a b
    rot = ((dd discard >>> peek) &&& snip2 discard) >>> push

    {- z y x -- x z y -}
    unrot :: a b -> a b
    unrot = rot >>> rot

    liftStack :: (b -> b) -> (a b -> a b)
    liftStack = yank

    liftStack2 :: (b -> b -> b) -> (a b -> a b)
    liftStack2 = (uncurry >>> first >>> ((second pop >>> rearrangeL) >>>)) >>> prc

    liftStack3 :: (b -> b -> b -> b) -> (a b -> a b)
    liftStack3 = (uncurry >>> uncurry >>> first >>>
            ((second pop >>> rearrangeL >>> second pop >>> rearrangeL) >>>)) >>>
            prc

    liftStack4 :: (b -> b -> b -> b -> b) -> (a b -> a b)
    liftStack4 = (uncurry >>> uncurry >>> uncurry >>> first >>>
            ((second pop >>> rearrangeL >>> second pop >>> rearrangeL >>>
            second pop >>> rearrangeL) >>>)) >>>
            prc

    liftStack5 :: (b -> b -> b -> b -> b -> b) -> (a b -> a b)
    liftStack5 = (uncurry >>> uncurry >>> uncurry >>> uncurry >>> first >>>
            ((second pop >>> rearrangeL >>> second pop >>> rearrangeL >>>
            second pop >>> rearrangeL >>> second pop >>> rearrangeL) >>>)) >>>
            prc

instance Stack [] a where

    new = []

    pop = head &&& tail

    push = uncurry (:)

class Stack a b => BoolStack a b where

    popBool :: a b -> (Bool, a b)

    pushBool :: (Bool, a b) -> a b

    pushBool' :: Bool -> a b -> a b
    pushBool' = curry pushBool

    peekBool :: a b -> Bool
    peekBool = popBool >>> fst

    inspectBool :: a b -> (Bool, a b)
    inspectBool = peekBool &&& id

    notBool :: a b -> a b
    notBool = popBool >>> first not >>> pushBool

    branch :: a b -> Either (a b) (a b)
    branch = popBool >>> uncurry (\p -> if p then Left else Right)

    ifThenElse :: (a b -> a b) -> (a b -> a b, a b -> a b) -> (a b -> a b)
    ifThenElse = curry (curry (first mirror >>> rearrangeR >>> second (app >>> branch) >>>
            envelope >>> (first fst ||| first snd) >>> app
            ))

    doWhile :: (a b -> a b) -> (a b -> a b) -> (a b -> a b)
    doWhile = curry (,) >>> (>>> (>>> (
            (fst &&& (rearrangeR >>> second (app >>> branch) >>> envelope)) >>> envelope >>>
            ((second app >>> uncurry (uncurry doWhile)) ||| (second snd >>> snd))
            )))

    whileDo :: (a b -> a b) -> (a b -> a b) -> (a b -> a b)
    whileDo = flip doWhile

    doUntil :: (a b -> a b) -> (a b -> a b) -> (a b -> a b)
    doUntil = curry (curry (first (second (>>> notBool)) >>> uncurry (uncurry doWhile)))

    untilDo :: (a b -> a b) -> (a b -> a b) -> (a b -> a b)
    untilDo = flip doUntil

instance BoolStack [] Dynamic where

    popBool = pop >>> first (fromDynamic >>> fromJust)

    pushBool = first toDyn >>> push

class BoolStack a b => BoundStack a b where

    isEmpty :: a b -> a b

    obliterate :: a b -> a b
    obliterate = discard `doUntil` isEmpty

instance BoundStack [] Dynamic where

    isEmpty = (null &&& id) >>> pushBool

class Stack a b => IntegerStack a b where

    popInteger :: a b -> (Integer, a b)

    pushInteger :: (Integer, a b) -> a b

    pushInteger' :: Integer -> a b -> a b
    pushInteger' = curry pushInteger

    peekInteger :: a b -> Integer
    peekInteger = popInteger >>> fst

    inspectInteger :: a b -> (Integer, a b)
    inspectInteger = peekInteger &&& id

instance IntegerStack [] Dynamic where

    popInteger = pop >>> first (fromDynamic >>> fromJust)

    pushInteger = first toDyn >>> push

class (BoolStack a b, IntegerStack a b) => FramingStack a b where

    newFrame :: a b -> a b

    frameSize :: a b -> a b

    destroyFrame :: a b -> a b
    destroyFrame = discard `doUntil` isFrameEmpty

    isFrameEmpty :: a b -> a b
    isFrameEmpty = frameSize >>> popInteger >>> first (== 0) >>> pushBool

data FrameStack a = FS { fs :: ([a], [Dynamic]) }

fs' = fs `wrap` FS

instance Stack FrameStack a where

    new = FS (new :: [a], pushInteger (0, new :: [Dynamic]))

    pop = fs >>> (pop *** (popInteger >>> first (+ (-1)) >>> ((fst >>> (< 0)) &&& pushInteger) >>>
            pushBool >>> branch >>> (error "frame empty" ||| id))) >>> rearrangeR >>> second FS

    push = second fs >>> rearrangeL >>> first push >>>
            second (popInteger >>> first (+1) >>> pushInteger) >>> FS

{-
    BoolStack instance may not simply forward to the underlying stack
    (like BoundStack's isEmpty does), since frame boundaries must be preserved
-}
instance BoolStack FrameStack Dynamic where

    popBool = pop >>> first (fromDynamic >>> fromJust)

    pushBool = first toDyn >>> push

instance BoundStack FrameStack Dynamic where

    isEmpty = fs' (first isEmpty)

    {- required due to FrameStack's additional state -}
    obliterate = fs' (obliterate *** (obliterate >>> ((const 0) &&& id) >>> pushInteger))

{-
    IntegerStack instance may not simply forward to the underlying stack
    (like BoundStack's isEmpty does), since frame boundaries must be preserved
-}
instance IntegerStack FrameStack Dynamic where

    popInteger = pop >>> first (fromDynamic >>> fromJust)

    pushInteger = first toDyn >>> push

instance FramingStack FrameStack Dynamic where

    newFrame = fs' (second (((const 0) &&& id) >>> pushInteger))

    frameSize = fs' copyL

{- x | -- | x -}
moveR :: Stack a b => (a b, a b) -> (a b, a b)
moveR = first (pop >>> mirror) >>> rearrangeR >>> second push

{- | x -- x | -}
moveL :: Stack a b => (a b, a b) -> (a b, a b)
moveL = mirrorA moveR

{- x | -- x | x -}
copyR :: Stack a b => (a b, a b) -> (a b, a b)
copyR = first dup >>> moveR

{- | x -- x | x -}
copyL :: Stack a b => (a b, a b) -> (a b, a b)
copyL = mirrorA copyR

{- x | y -- y | x -}
exch :: Stack a b => (a b, a b) -> (a b, a b)
exch = moveR >>> second swap >>> moveL

class Pair a b where

    wheep :: (a, a) -> b

    whoop :: b -> (a, a)

instance Pair a (a, a) where

    wheep = id

    whoop = id

data (Stack a b, Pair b c) => PairStack a b c = PS { ps :: ((((b, b) -> c), (c -> (b, b))), (a b)) }

toPairStack :: (Stack a b, Pair b c) => a b -> PairStack a b c
toPairStack = (,) (wheep, whoop) >>> PS

fromPairStack :: (Stack a b, Pair b c) => PairStack a b c -> a b
fromPairStack = ps >>> snd

getWheep :: (Stack a b, Pair b c) => PairStack a b c -> ((b, b) -> c)
getWheep = ps >>> fst >>> fst

getWhoop :: (Stack a b, Pair b c) => PairStack a b c -> (c -> (b, b))
getWhoop = ps >>> fst >>> snd

instance (Stack a b, Pair b c) => Stack (PairStack a b) c where

    new = toPairStack (new :: Stack a b => a b)

    pop = (getWheep &&& (fromPairStack >>> pop >>> second pop >>> rearrangeL)) >>>
            rearrangeL >>> (app *** toPairStack)

    push = second (getWhoop &&& fromPairStack) >>> rearrangeRA (first (mirror >>> app)) >>>
            second push >>> push >>> toPairStack

dd :: Stack a b => (PairStack a b (b, b) -> PairStack a b (b, b)) -> a b -> a b
dd = toPairStack `wrap` fromPairStack

