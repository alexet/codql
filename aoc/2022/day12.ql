import lib

module Impl<inStr/0 input> {
  string squares(int i, int j) { result = Helpers<input/0>::lines(i).charAt(j) }

  predicate isStart(int i, int j) { squares(i, j) = "S" }

  predicate isEnd(int i, int j) { squares(i, j) = "E" }

  int value(int i, int j) {
    not isStart(i, j) and
    not isEnd(i, j) and
    squares(i, j) = result.toUnicode()
    or
    isStart(i, j) and result.toUnicode() = "a"
    or
    isEnd(i, j) and result.toUnicode() = "z"
  }
  newtype TCoord = MkCoord(int i, int j) { exists(squares(i, j)) }

  class Coord extends TCoord {
    int i() { this = MkCoord(result, _) }

    int j() { this = MkCoord(_, result) }

    int value() { result = value(this.i(), this.j()) }

    predicate isStart() { isStart(this.i(), this.j()) }

    predicate isEnd() { isEnd(this.i(), this.j()) }

    string toString() { result = "MkCoord(" + this.i() + ", " + this.j() + ")" }
  }

  predicate isAdjacent(Coord c1, Coord c2) {
    exists(int i1, int i2, int j1, int j2 |
      c1 = MkCoord(i1, j1) and
      c2 = MkCoord(i2, j2) and
      (
        i1 = i2 and j1 = j2 + 1
        or
        i1 = i2 and j1 = j2 - 1
        or
        i1 = i2 + 1 and j1 = j2
        or
        i1 = i2 - 1 and j1 = j2
      )
    )
  }

  predicate edge(Coord c1, Coord c2) {
    isAdjacent(c1, c2) and
    c1.value() + 1 >= c2.value()
  }

  predicate start(Coord c) {
    c.isStart()
  }

  predicate start2(Coord c) {
    c.isStart() or c.value().toUnicode() = "a"
  }

  int shortestSteps(Coord c1, Coord c2) = shortestDistances(start/1,edge/2)(c1, c2, result)
  int shortestSteps2(Coord c1, Coord c2) = shortestDistances(start2/1,edge/2)(c1, c2, result)

  int steps() { result = shortestSteps(any(Coord c | c.isStart()), any(Coord c | c.isEnd())) }
  int steps2() { result = min(shortestSteps2(any(Coord c | start2(c)), any(Coord c | c.isEnd()))) }
}

module TestImpl = Impl<testInput/0>;
module RealImpl = Impl<realInput/0>;

select TestImpl::steps(), RealImpl::steps(), TestImpl::steps2(), RealImpl::steps2()

string testInput() { result = "Sabqponm\nabcryxxl\naccszExk\nacctuvwj\nabdefghi" }

string realInput() { result = "abcccccaaaccccaacaaccaaaaaaaaaaaaaaaaaaaaccccccccccccccccccccccccccccccccccaaaaaa\nabcccccaaaacccaaaaaccaaaaaaaaaaaaaaaaaaaaacccccccccccccccccccccccccccccccccccaaaa\nabcccccaaaaccaaaaaccccaaaccaaaaaacccacaaaaccccccccccccccccaaaccccccccccccccccaaaa\nabcccccaaacccaaaaaaccccccccaaaaaacccccaaccccccccccccccccccaaaccccccccccccccccaaaa\nabcccccccccccccaaaacccccccaaaaaaaaccccccccccccccccccccccccaaacccccccccccccccaaaaa\nabccccccaacccccaacccccccccaaaaaaaaccccccccccccccccccccccccaaaaccaaacccccccccccccc\nabccccccaacccccccccccccccaaacccaaaacccaacaaccccccccccacaccaaacaajaacccccccccccccc\nabcccaaaaaaaaccccacccccccaaaccccaaacccaaaaaccccccccccaaaaaaajjjjkkkccccccaacccccc\nabcccaaaaaaaacaaaacccccccccccccccccccaaaaaccccccccciiiijjjjjjjjjkkkkcaaaaaacccccc\nabcccccaaaacccaaaaaacccccccccccccccccaaaaaacccccciiiiiijjjjjjjrrrkkkkaaaaaaaacccc\nabcccccaaaaacccaaaacccccccccaacccccccccaaaaccccciiiiiiiijjjjrrrrrsskkaaaaaaaacccc\nabccccaaaaaaccaaaaacccccccccaaaacccccccaccccccciiiiqqqqrrrrrrrrrssskkkaaaaaaacccc\nabaaccaaccaaccaacaacccccccaaaaaaccccccccccccccciiiqqqqqrrrrrrruussskkkaaaaacccccc\nabaaaacccccccccccccccccccccaaaaccccccccaaaccccciiqqqqqttrrrruuuuussskkaaaaacccccc\nabaaaacccccccccccccccccccccaaaaaccccccccaaaaccchiqqqtttttuuuuuuuussskkcccaacccccc\nabaaacccccaaaccacccccccccccaacaaccccccaaaaaaccchhqqqtttttuuuuxxuussslllcccccccccc\nabaaaaccccaaaaaacaaccccccaccccccccccccaaaaacccchhqqqttxxxxuuxxyyusssllllccccccccc\nabacaaccccaaaaaacaaaaaaaaaaccccccccccccaaaaaccchhqqqttxxxxxxxxyuusssslllccccccccc\nabcccccccaaaaaaacaaaaaaaaaccccaacccccccaaccaccchhhqqtttxxxxxxyyvvvsssslllcccccccc\nabcccccccaaaaaaaaaaaaaaaaaccccaaaaccccccccccccchhhppqttxxxxxyyyvvvvsqqqlllccccccc\nSbcccaaccaaaaaaaaaaaaaaaaaacaaaaaacccccccccccchhhhpptttxxxEzzyyyyvvvqqqqlllcccccc\nabcccaaccccaaacaaaaaaaaaaaaacaaaaccccccccccccchhhppptttxxxyyyyyyyyvvvqqqlllcccccc\nabaaaaaaaacaaacaaaaaaaaaaaaacaaaaacaaccccccccchhpppsssxxyyyyyyyyvvvvvqqqlllcccccc\nabaaaaaaaaccccccccaaacaaaccccaacaaaaaccccccaagggpppsswwwwwwyyyvvvvvvqqqmmmmcccccc\nabccaaaaccccaacaacaaacaaacccccccccaaacaaaccaagggppssswwwwwwyyywvvqqqqqqmmmccccccc\nabcaaaaaccccaaaaacaaccaaccaaaccaaaaaaaaaaaaaagggppsssswwwswwyywvrqqqqmmmmcccccccc\nabcaaaaaaccaaaaacccccccccaaaaccaaaaaaaaaacaaagggpppssssssswwwwwwrrqmmmmmccccccccc\nabcaacaaaccaaaaaaccccccccaaaaccccaaaaaacccaaagggppppssssssrwwwwrrrmmmmmdccccccccc\nabccccaaaccaaaaaaccccccccaaaaccccaaaaaacccaacggggpooooooosrrwwwrrnmmmddddcacccccc\nabccccaaaaaaaacccccccccccccccccccaaaaaaaccccccggggoooooooorrrrrrrnnmdddddaaaacccc\nabcccccaaaaaaccccccccccccccccccccaaacaaacccccccggggfffooooorrrrrrnnddddaaaaaacccc\nabccaaaaaaaacccccccccccccccccccccaccccccccccccccggffffffooonrrrrnnndddaaaaaaacccc\nabccaaaaaaaaaccccaacccccccccccccccccccccccccccccccfffffffoonnnnnnndddcaaaaacccccc\nabccaaaaaaaaaacccaaccccccccccccccaccccccccccccccccccccffffnnnnnnnedddaaaaaacccccc\nabcccccaaaaaaaaaaaacccccccaccccaaacccccccccccccccccccccfffeennnneeedcccccaacccccc\nabcccccaaacccaaaaaaaaccccaaacccaaaccacccccccccccccccccccafeeeeeeeeecccccccccccccc\nabcccccaaccccaaaaaaaaacccaaaaaaaaaaaaccccccaaaccccccccccaaeeeeeeeeeccccccccccccca\nabaccccccccccaaaaaaaaacccaaaaaaaaaaacccccccaaaaacccccccaaaaceeeeecccccccccccaccca\nabaccccccccccaaaaaaaaccaaaaaaaaaaaaaacccccaaaaaccccccccaaaccccaaacccccccccccaaaaa\nabaccccccccccaaaaaaacccaaaaaaaaaaaaaacccccaaaaacccccccccccccccccccccccccccccaaaaa\nabaccccccccccaccaaaacccaaaaaaaaaaaaaaccccccaaaaaccccccccccccccccccccccccccccaaaaa" }
