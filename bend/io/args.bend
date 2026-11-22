import Base

# Parse one argument; a non-number counts as 0.
def parse(s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

# Sum the parsed arguments.
def sum(xs: List<String>) -> U32:
  match xs:
    case Nil{}:
      0
    case h <> t:
      (parse(h) + sum(t) : U32)

# IO.args answers the program as invoked first, so drop the head.
def total(argv: List<String>) -> U32:
  match argv:
    case Nil{}:
      0
    case _ <> rest:
      sum(rest)

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    IO.print(U32.show(total(argv)))
