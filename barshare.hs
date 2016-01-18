import Haste
import Haste.Graphics.Canvas
import Haste.DOM


data State = Paid | Unpaid
data Item = Item { price :: Double, ammount :: Double, name :: String, code :: Int, state :: State }
data Bubble = Bubble { pos :: Point, direction :: Vector, speed :: Double, item :: Item}

testItem1 = Item { price = 5.0, ammount = 7, name = "banana", code = 1, state = Unpaid }

-- | Perform the physics of the bubbles
physics :: [Bubble] -> [Bubble]
physics bs = bs

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
scatter :: (Int, Int) -> Int -> [Point]
scatter (w, h) n = [(fromIntegral x, fromIntegral y) | x <- xs, y <- ys]
  where
        nsqr = ceiling $ sqrt $ fromIntegral n
        spx = w `div` (nsqr + 1)
        spy = h `div` (nsqr + 1)

        ny = h `div` spy
        nx = w `div` spx

        ys = map (*spy) [1..(ny - 1)]
        xs = map (*spx) [1..(nx - 1)]

-- | Places the items in the initial positions and attribute the state Unpaid
initialPositions :: (Int, Int) -> [Item] -> [Bubble]
initialPositions hw items = [Bubble p (0, 0) 0 i | (p, i) <- zip points items]
  where points = scatter hw (length items)

readInt :: String -> Int
readInt = read

-- | Then you grab a canvas object...
main :: IO ()
main = do
  Just e <- elemById "canvas"
  w <- readInt <$> getProp e "width"
  h <- readInt <$> getProp e "height"
  Just can <- fromElem e --ById "canvas"
  animate can (initialPositions (w, h) (replicate 20 testItem1))

-- | ...and use the render function to draw your image.
--   The picture type is a monad, so you can compose several pictures easily
--   using do-notation.
animate :: Canvas -> [Bubble] -> IO ()
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
  setTimer (Once 10) $ animate can (physics bubbles)
  return ()
