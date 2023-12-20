private newtype TDir =
  N() or
  S() or
  E() or
  W()

class Dir extends TDir {
  Dir opposite() {
    this = N() and result = S()
    or
    this = S() and result = N()
    or
    this = E() and result = W()
    or
    this = W() and result = E()
  }

  string toString() {
    this = N() and result = "N"
    or
    this = S() and result = "S"
    or
    this = E() and result = "E"
    or
    this = W() and result = "W"
  }

  string asDirChar() {
    this = N() and result = "^"
    or
    this = S() and result = "v"
    or
    this = E() and result = ">"
    or
    this = W() and result = "<"
  }

  Dir hitDownMirror() {
    this = N() and result = W()
    or
    this = S() and result = E()
    or
    this = E() and result = S()
    or
    this = W() and result = N()
  }

  Dir hitUpMirror() {
    this = N() and result = E()
    or
    this = S() and result = W()
    or
    this = E() and result = N()
    or
    this = W() and result = S()
  }

  int getDx() {
    this = E() and result = 1
    or
    this = W() and result = -1
    or
    this in [n(), s()] and result = 0
  }

  int getDy() {
    this = N() and result = -1
    or
    this = S() and result = 1
    or
    this in [e(), w()] and result = 0
  }
}

Dir n() { result = N() }

Dir s() { result = S() }

Dir e() { result = E() }

Dir w() { result = W() }
