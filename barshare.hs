import Haste
import Haste.Graphics.Canvas
import Haste.DOM
import Data.List
import Control.Monad


data State = Paid | Unpaid
data Item = Item { price :: Double, ammount :: Double, name :: String, code :: Int, state :: State }
data Bubble = Bubble { pos :: Point, direction :: Vector, item :: Item}

testItem1 :: Item
testItem1 = Item { price = 5.0, ammount = 7, name = "banana", code = 1, state = Unpaid }

type Model = [Bubble]

sortBubbles :: [Bubble] -> [Bubble]
sortBubbles = sortOn (fst . pos)

slow :: Double -> Double
slow = (*0.9)

move :: Point -> Bubble -> Bubble
move lm b = b { pos = (x', y'), direction = (dx', dy') }
  where (dx, dy) = direction b
        (x, y) = pos b
        (x', dx') = move1d (fst lm) (slow dx) x
        (y', dy') = move1d (snd lm) (slow dy) y

move1d :: Double -> Double -> Double -> (Double, Double)
move1d l v s | s + v < 0     = (-s', -v)
             | s + v > l     = (l + l - s', -v)
             | otherwise     = (s', v)
    where s' = s + v

resolve :: Point -> [Bubble] -> Bubble -> IO [Bubble]
resolve lm [] b = return [move lm b]
resolve lm bs b = return $ (move lm b):bs

-- | Perform the physics of the bubbles
physics :: Point -> Model -> IO Model
physics d bs = do
  bs' <- foldM (resolve d) [] (sortBubbles bs)
  return bs'

-- | Basic picture of an Item
itemShape :: Bubble -> Picture ()
itemShape bubble = do
  checkColor (state i) $ fill $ circle p (price i * ammount i)
  color (RGB 0 0 0) $ text p (name i)
  where checkColor Unpaid = color (RGB 255 0 0)
        checkColor Paid   = color (RGB 0 255 0)
        i = item bubble
        p = pos bubble

-- | Scatter a number of points across a canvas
scatter :: Point -> Int -> [Point]
scatter (w, h) n = zip xs ys
  where
        spy = h / (fromIntegral n + 1)
        spx = w / (fromIntegral n + 1)
        ys = iterate (+spy) spy
        xs = iterate (+spx) spx

-- | Places the items in the initial positions and attribute the state Unpaid
initialPositions :: Point -> [Item] -> Model
initialPositions wh items = [Bubble p (10, 10) i | (p, i) <- zip points items]
  where points = scatter wh (length items)

getDimensions :: Canvas -> IO Point
getDimensions can = do
  w <- read <$> getProp can "width"
  h <- read <$> getProp can "height"
  return (w, h)


-- | Then you grab a canvas object...
main :: IO ()
main = do
  Just e <- elemById "canvas"
  Just can <- fromElem e --ById "canvas"
  (w, h) <- getDimensions can
  animate can (initialPositions (w, h) (replicate 20 testItem1))

-- | ...and use the render function to draw your image.
--   The picture type is a monad, so you can compose several pictures easily
--   using do-notation.
animate :: Canvas -> Model -> IO ()
animate can bubbles = do
  -- There are several transformation functions as well. All of them take a
  -- Picture () as their argument, and apply their transformation only to that
  -- picture, so the user doesn't need to manage the canvas state machine
  -- explicitly.
  render can $ do
    mapM itemShape bubbles
    --translate (160, 160) $ rotate angle $ do
    --  color (RGB 255 255 0) $ itemShape testItem1
      --translate (100, 100) . rotate (-angle) . color (RGB 255 0 0) $ filledSquare
    --color (RGBA 0 0 255 0.5) . font "20px Bitstream Vera" $ do
      --text (10, 160) "You can use transparency too!"

  d <- getDimensions can
  bubbles' <- physics d bubbles
  setTimer (Once 20) $ animate can bubbles'
  return ()
