module Algorithm100Spec
{
  function FailureResult(): seq<string>
  {
    ["-1"]
  }

  function {:fuel 100} Min(a: int, b: int): int
  {
    if a <= b then a else b
  }

  predicate ValidScreen(n: int, m: int, screen: seq<string>)
  {
    |screen| == n &&
    forall r | 0 <= r < n ::
      |screen[r]| == m &&
      forall c | 0 <= c < m :: screen[r][c] == '.' || screen[r][c] == 'w'
  }

  predicate ValidOutputGrid(n: int, m: int, output_lines: seq<string>)
  {
    |output_lines| == n &&
    forall r | 0 <= r < n ::
      |output_lines[r]| == m &&
      forall c | 0 <= c < m ::
        output_lines[r][c] == '.' || output_lines[r][c] == 'w' || output_lines[r][c] == '+'
  }

  predicate Spec(n: int, m: int, screen: seq<string>, output_lines: seq<string>)
  {
    // There is at least one white pixel by problem statement
    ValidScreen(n, m, screen) &&
    // output_lines either single line "-1" or n lines of length m with valid chars
    (
      (output_lines == FailureResult() &&
       // no valid frame exists
       forall r1, c1, d ::
         0 <= r1 <= n - d && 0 <= c1 <= m - d && 1 <= d <= Min(n, m) ==>
           !(IsValidFrame(n, m, screen, r1, c1, d))
      )
      ||
      (
        ValidOutputGrid(n, m, output_lines) &&
        // there exists minimal frame parameters
        exists r1, c1, d ::
          0 <= r1 <= n - d &&
          0 <= c1 <= m - d &&
          1 <= d <= Min(n, m) &&
          IsValidFrame(n, m, screen, r1, c1, d) &&
          IsMinimalFrame(n, m, screen, r1, c1, d) &&
          FrameOutputLines(n, m, screen, r1, c1, d, output_lines)
      )
    )
  }

  /**
    * Determines whether the frame of size d with top-left corner at (r1, c1) is within the screen bounds.
    * @param n number of rows of the screen
    * @param m number of columns of the screen
    * @param r1 top row of the frame
    * @param c1 left column of the frame
    * @param d size (height and width) of the square frame
    */
  predicate IsFrameWithinBounds(n: int, m: int, r1: int, c1: int, d: int)
  {
    1 <= d <= Min(n, m) &&
    0 <= r1 <= n - d &&
    0 <= c1 <= m - d
  }

  function FramePixels(r1: int, c1: int, d: int): set<(int, int)>
  {
    (
      set c {:trigger (r1, c)} | c1 <= c < c1 + d :: (r1, c)
    )
    +
    (
      set c {:trigger (r1 + d - 1, c)} | c1 <= c < c1 + d :: (r1 + d - 1, c)
    )
    +
    (
      set r {:trigger (r, c1)} | r1 + 1 <= r < r1 + d - 1 :: (r, c1)
    )
    +
    (
      set r {:trigger (r, c1 + d - 1)} | r1 + 1 <= r < r1 + d - 1 :: (r, c1 + d - 1)
    )
  }

  predicate AllWhitesOnFrame(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
  {
    // Frame must be within bounds
    ValidScreen(n, m, screen) &&
    IsFrameWithinBounds(n, m, r1, c1, d) &&
    // All white pixels appear exactly on the frame border
    forall r, c :: 0 <= r < n && 0 <= c < m ==>
                     (screen[r][c] == 'w' ==> (r, c) in FramePixels(r1, c1, d))
  }

  predicate IsValidFrame(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
  {
    ValidScreen(n, m, screen) &&
    IsFrameWithinBounds(n, m, r1, c1, d) &&
    AllWhitesOnFrame(n, m, screen, r1, c1, d) &&
    // For all pixels in frame border, pixels are valid '.' or 'w'
    (forall r :: 0 <= r < n ==>
                   forall c :: 0 <= c < m ==>
                                 ( (r, c) in FramePixels(r1, c1, d) ==> (screen[r][c] == 'w' || screen[r][c] == '.') )
    )
  }

  predicate IsMinimalFrame(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int)
  {
    // The frame itself must be valid
    IsValidFrame(n, m, screen, r1, c1, d) &&
    // No strictly smaller valid frame exists that contains all white pixels
    forall d', r1', c1' {:trigger IsValidFrame(n, m, screen, r1', c1', d')} ::
      1 <= d' < d &&
      0 <= r1' <= n - d' &&
      0 <= c1' <= m - d' ==>
        !IsValidFrame(n, m, screen, r1', c1', d')
  }

  predicate FrameOutputLines(n: int, m: int, screen: seq<string>, r1: int, c1: int, d: int, output_lines: seq<string>)
  {
    ValidScreen(n, m, screen) &&
    |output_lines| == n &&
    forall r :: 0 <= r < n ==>
                  |output_lines[r]| == m &&
                  forall c :: 0 <= c < m ==>
                                if (r, c) in FramePixels(r1, c1, d) then
                                  if screen[r][c] == 'w' then output_lines[r][c] == 'w'
                                  else output_lines[r][c] == '+'
                                else
                                  output_lines[r][c] == screen[r][c]
  }
}
