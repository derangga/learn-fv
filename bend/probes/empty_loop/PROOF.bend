import Base
import ./LAWS.bend as Laws

# Attempt: a def that calls itself with no decreasing argument. A loop "has"
# every type, so if it were accepted it would prove the false law.
def Laws.empty_loop():
  Laws.empty_loop()
