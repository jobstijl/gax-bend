# Q1: pin the toolchain; a compiled IO main and a checker-normalized pure value.
import Base

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("bend ok: " ++ U32.show((6 * 7 : U32)))
