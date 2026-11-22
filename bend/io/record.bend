import Base

# A small record state folded over events from argv, printed as
# "balance=.. ops=.. last=.." for a Go harness to parse. The step is
# order-dependent, so a reordered event list changes the output.
type State is Data:
  St{balance: U32, ops: U32, last: U32}

def step(s: State, +e: U32) -> State:
  match s:
    case St{+b, +o, +l}:
      St{(b * 31 + e : U32), (o + 1 : U32), e}

def parse(s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

# the list comes first: the termination checker reads arguments left to right
def run(xs: List<String>, s: State) -> State:
  match xs:
    case Nil{}:
      s
    case h <> t:
      run(t, step(s, parse(h)))

def show(s: State) -> String:
  match s:
    case St{+b, +o, +l}:
      "balance=" ++ U32.show(b) ++ " ops=" ++ U32.show(o) ++ " last=" ++ U32.show(l)

def final(argv: List<String>) -> State:
  match argv:
    case Nil{}:
      St{0, 0, 0}
    case _ <> rest:
      run(rest, St{0, 0, 0})

def main() -> IO(Unit):
  do IO<Unit>:
    argv : List<String> <- IO.args()
    IO.print(show(final(argv)))
