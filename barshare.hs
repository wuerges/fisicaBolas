import Haste
import Haste.Graphics.Canvas
import Haste.DOM
import Data.List

data State = Paid | Unpaid
data Item = Item { price :: Double, ammount :: Double, name :: String, code :: Int, state :: State }
data Bubble =
  Bubble { pos :: Point, direction :: Vector, item :: Item}


testItem1 :: Item
testItem1 = Item { price = 9.0, ammount = 7, name = "banana", code = 1, state = Unpaid }

type Model = [Bubble]

sortBubbles :: [Bubble] -> [Bubble]
sortBubbles = sortOn (\b -> distance (0, 0) (pos b)) -- (fst . pos)

radius :: Bubble -> Double
radius b = price (item b) * ammount (item b)

slow :: Double -> Double
slow = (* 0.95)

move :: Point -> Bubble -> Bubble
move lm b = b { pos = (x', y'), direction = (dx', dy') }
  where (dx, dy) = direction b
        (x, y) = pos b
        (x', dx') = move1d (radius b) (fst lm - radius b) (slow dx) x
        (y', dy') = move1d (radius b) (snd lm - radius b) (slow dy) y

move1d :: Double -> Double -> Double -> Double -> (Double, Double)
move1d le ld v s | s + v < le     = (le + le - s', -v)
                 | s + v > ld     = (ld + ld - s', -v)
                 | otherwise     = (s', v)
    where s' = s + v


negateV :: Vector -> Vector
negateV (x, y) = (-x, -y)

sumV :: Vector -> Vector -> Vector
(x1, y1) `sumV` (x2, y2) = (x1 + x2, y1 + y2)

minusV :: Vector -> Vector -> Vector
v1 `minusV` v2 = v1 `sumV` (negateV v2)

{-
mulV :: Vector -> Double -> Vector
(x1, y1) `mulV` s = (x1 * s, y1 * s)
-}

distance :: Point -> Point -> Double
distance (ax, ay) (bx, by) = sqrt $ ((ax - bx) ** 2) + ((ay - by) ** 2)




colides :: [Bubble] -> [Bubble]
colides []     = []
colides (a:as) = a' : colides as'
  where (a', as') = case partition (checkColide a) as of
                     ([],   bs) -> (a, bs)
                     (c:cs, bs) -> (a'', b'':(cs ++ bs))
                        where (a'', b'') = colide a c
        checkColide x y = radius x + radius y > distance (pos x) (pos y)


colide :: Bubble -> Bubble -> (Bubble, Bubble)
colide a b = (a', b')
--  | radius a + radius b > distance (pos a) (pos b) = (a', b')
--  | otherwise                                      = (a, b)
  where
        a' = incItem $ a { direction = dira', pos = posa' }
        b' = incItem $ b { direction = dirb', pos = posb' }
        cva = direction a `minusV` direction b
        cvb = direction b `minusV` direction a
        dira' = direction a `minusV` cva
        dirb' = direction b `minusV` cvb
        posa' = pos a `minusV` cva
        posb' = pos b `minusV` cvb
        incItem bub = bub { item = item' }
          where
            i = item bub
            item' = i { code = code i + 1 }

resolve :: Point -> [Bubble] -> [Bubble]
resolve lm bs = map (move lm) (colides bs)

-- | Perform the physics of the bubbles
physics :: Point -> Model -> IO Model
physics d bs = return $ resolve d (sortBubbles bs)

-- | Basic picture of an Item
itemShape :: Bubble -> Picture ()
itemShape bubble = do
  checkColor (state i) $ fill $ circle p (radius bubble)
  color (RGB 0 0 0) $ text p (show $ code i)
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
initialPositions wh items = [Bubble p (100, 100) i | (p, i) <- zip points items]
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
  animate can (initialPositions (w, h) (replicate 10 testItem1))

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
  setTimer (Once 16) $ animate can bubbles'
  return ()
