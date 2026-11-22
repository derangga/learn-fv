import Base

# No Base stdin effect exists; /dev/stdin is opened as a file (Linux).
# Numbers are split on spaces and newlines; anything not a number is skipped.
def add(m: Maybe<&2, U32>, acc: U32) -> U32:
  match m:
    case None{}:
      acc
    case Some{n}:
      (acc + n : U32)

def sum_words(ws: List<&2, String>, acc: U32) -> U32:
  match ws:
    case Nil{}:
      acc
    case w <> t:
      sum_words(t, add(U32.read(w), acc))

def sum_lines(ls: List<&2, String>, acc: U32) -> U32:
  match ls:
    case Nil{}:
      acc
    case l <> t:
      sum_lines(t, sum_words(String.split(l, ' '), acc))

def finish(r: File & Result<&1, &1, U32 & String, String>) -> IO(Unit):
  (f, res) = r
  do IO<Unit>:
    text : String <- IO.pass(String, res)
    File.close(f)
    IO.print(U32.show(sum_lines(String.lines(text), 0)))

def main() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdin", "r"))
    r : File & Result<&1, &1, U32 & String, String> <- File.read(f, 16777216)
    finish(r)
