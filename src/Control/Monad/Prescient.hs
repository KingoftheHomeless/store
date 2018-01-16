{-# LANGUAGE FunctionalDependencies, GeneralizedNewtypeDeriving, LambdaCase, FlexibleInstances, DefaultSignatures #-}
module Control.Monad.Prescient where
import Data.Functor.Product
import Control.Monad.Writer hiding (Product)
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor.Classes
import Control.Monad.Identity

{-
    The story here is that I realized (Maybe s -> a) is isomorphic to (a, s -> a).
    This means that the
        data Prescient s a = Prescient { peek :: Maybe s -> a, pos :: s }
    I suggested in a comment to my original post was actually isomorphic to
        data Prescient s a = Prescient (s -> a) s a
        ~
        data Prescient s a = Prescient (s -> a) (s, a)
        ~
        Product ((,) s) ((->) s) a
    This is good if a bit disappointing. There is a version of the Store monad that have
    very similar (and arguable more useful) properties as the original one, and is a proper
    monad transformer. However, it's just a straight-up functor product, rather than anything new.

    Since there's an injection from StateT to WriterT, I figured I'd make a more general version
    of this using StateT rather than WriterT. This has the added benefit of allowing the monad
    to inspect the in-progress stored value as it is building it, which is something I wanted to make
    possible in my original post.
-}

-- I'm puzzled as to why Data.Functor.Product doesn't have these as field accessors.
getLeft :: Product f g a -> f a
getLeft (Pair f _) = f

getRight :: Product f g a -> g a
getRight (Pair _ g) = g

-- Short for Write then Read
newtype WtRT s m a = WtRT (Product (WriterT s m) (ReaderT s m) a)
    deriving (Functor, Applicative, Monad, MonadFix)

type WtR s = WtRT s Identity

runWtRT :: Monad m => WtRT s m a -> m a
runWtRT (WtRT (Pair st rd)) = execWriterT st >>= runReaderT rd

runWtR :: WtR s a -> a
runWtR = runIdentity . runWtRT

-- Short for State then Read
newtype StRT s m a = StRT (Product (StateT s m) (ReaderT s m) a)
    deriving (Functor, Applicative, Monad, MonadFix)

type StR s = StRT s Identity

runStRT :: Monad m => StRT s m a -> s -> m a
runStRT (StRT (Pair st rd)) = execStateT st >=> runReaderT rd

runStR :: StR s a -> s -> a
runStR = (runIdentity .) . runStRT

instance Monoid s => MonadTrans (WtRT s) where
    lift m = WtRT (Pair (lift m) (lift m))

instance (Monoid s, MonadIO m) => MonadIO (WtRT s m) where
    liftIO = lift . liftIO

instance MonadTrans (StRT s) where
    lift m = StRT (Pair (lift m) (lift m))

instance MonadIO m => MonadIO (StRT s m) where
    liftIO = lift . liftIO

class MonadWtR s m | m -> s where
    wTr :: (a, s) -> (s -> a) -> m a

    -- Causes s to be appended to the stored value during writing.
    write :: s -> m ()
    write s = wTr ((), s) (const ())

    -- If in the reading stage, reads the Just the stored value. Otherwise reads Nothing.
    scry :: Monoid s => m (Maybe s)
    scry = wTr (Nothing, mempty) Just

    -- Lifts a writing action to a MonadWtR
    liftWrite :: (a, s) -> m (Maybe a)
    liftWrite wr = wTr (let (a, s) = wr in (Just a, s)) (const Nothing)

    -- Lifts a reading action to a MonadWtR
    liftRead :: Monoid s => (s -> a) -> m (Maybe a)
    liftRead rd = wTr (Nothing, mempty) (Just . rd)

    -- appends s after the value stored in the MonadWtR
    writeAfter :: Monoid s => m a -> s -> m a
    default writeAfter :: (Monoid s, Applicative m) => m a -> s -> m a
    writeAfter m s = m <* write s

    -- appends s before the value stored in the MonadWtR
    writeBefore :: Monoid s => m a -> s -> m a
    default writeBefore :: (Monoid s, Applicative m) => m a -> s -> m a
    writeBefore m s = write s *> m

instance Applicative m => MonadWtR s (WtRT s m) where
    wTr wr rd = WtRT $ Pair (WriterT $ pure wr) (ReaderT $ pure . rd)

    writeAfter (WtRT (Pair (WriterT wr) rd)) s = WtRT $ Pair (WriterT $ (fmap . fmap) (`mappend` s) wr) rd
    writeBefore (WtRT (Pair (WriterT wr) rd)) s = WtRT $ Pair (WriterT $ (fmap . fmap) (mappend s) wr) rd

instance (Applicative m, Monoid s) => MonadWtR s (StRT s m) where
    wTr wr = sTr (\s -> fmap (mappend s) wr)

    writeAfter (StRT (Pair (StateT st) rd)) s =
        StRT $ Pair
            (StateT $ (fmap . fmap) (`mappend` s) . st)
            rd

    writeBefore (StRT (Pair (StateT st) rd)) s =
        StRT $ Pair
            (StateT $ (fmap . fmap) (mappend s) . st)
            rd


data Stored s = Writing s | Reading s deriving (Show, Eq)

instance Functor Stored where
    fmap f (Writing s) = Writing (f s)
    fmap f (Reading s) = Reading (f s)

class MonadStR s m | m -> s where
    sTr :: (s -> (a, s)) -> (s -> a) -> m a

    -- Replaces the stored value during writing.
    replace :: s -> m ()
    replace = alter . const

    -- Modifies the stored value during writing
    alter :: (s -> s) -> m ()
    alter f = sTr (\s -> ((), f s)) (const ())
    
    getStored :: m (Stored s)
    getStored = getsStored id

    getsStored :: (s -> a) -> m (Stored a)
    getsStored f = sTr (\s -> (Writing (f s), s)) (Reading . f)
    
    getWriting :: m (Maybe s)
    getWriting = getsWriting id
    
    getsWriting :: (s -> a) -> m (Maybe a)
    getsWriting f = sTr (\s -> (Just (f s), s)) (const Nothing)

    getReading :: m (Maybe s)
    getReading = getsReading id

    getsReading :: (s -> a) -> m (Maybe a)
    getsReading f = sTr (\s -> (Nothing, s)) (Just . f)
    
    -- The equivalent of scry
    getEither :: m s
    getEither = getsEither id

    getsEither :: (s -> a) -> m a
    getsEither f = sTr (\s -> (f s, s)) f

    -- Promotes a state action to a MonadStR.
    liftState :: (s -> (a, s)) -> m (Maybe a)
    liftState f = sTr ((\(~(a, s)) -> (Just a, s)) . f) (const Nothing)

    -- Promotes a reader action to a MonadStR.
    liftReader :: (s -> a) -> m (Maybe a)
    liftReader f = sTr ((,) Nothing) (Just . f)

    -- Promotes a state/reader action to a MonadStR. The new s is discarded if in the reading stage.
    liftEither :: (s -> (a, s)) -> m a
    liftEither f = sTr f (fst . f)

instance Applicative m => MonadStR s (StRT s m) where
    sTr rd wr = StRT $ Pair (StateT $ pure . rd) (ReaderT $ pure . wr)

stage :: (Monad m, MonadStR s m) => (s -> m a) -> (s -> m a) -> m a
stage wr rd = getStored >>= \case { Writing s -> wr s; Reading s -> rd s }

whenWriting :: (Monad m, MonadStR s m) => (s -> m ()) -> m ()
whenWriting f = getWriting >>= maybe (pure ()) f

whenReading :: (Monad m, MonadStR s m) => (s -> m ()) -> m ()
whenReading f = getReading >>= maybe (pure ()) f