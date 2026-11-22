import Base

# Computes a value purely, then prints it through the Base IO.print effect.
def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(U32.show((6 * 7 : U32)))
