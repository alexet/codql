import lib

module Impl<inStr/0 input> {
  module H = Helpers<input/0>;

  string fish(int i) { result = H::lines(i) }

  int fishStart(int i) {
    exists(fish(i)) and result = 0
    or
    fish(i).charAt(result - 1) = ["[", ","]
  }

  int maxDepth() { result = 6 }

  class OptSnailFishIndex instanceof int {
    OptSnailFishIndex() { this in [-1 .. 2.pow(maxDepth()).(int) - 2] }

    string toString() { result = "N/A" and this = -1 }

    predicate isNone() { this = -1 }
  }

  class SnailFishIndex extends OptSnailFishIndex instanceof int {
    SnailFishIndex() { this in [0 .. 2.pow(maxDepth()).(int) - 2] }

    SnailFishIndex getLeft() { result = this * 2 + 1 }

    SnailFishIndex getRight() { result = this * 2 + 2 }

    SnailFishIndex shiftLeft() {
      this = 0 and result = this.getLeft()
      or
      exists(SnailFishIndex parent |
        parent.getLeft() = this and result = parent.shiftLeft().getLeft()
      )
      or
      exists(SnailFishIndex parent |
        parent.getRight() = this and result = parent.shiftLeft().getRight()
      )
    }

    SnailFishIndex shiftRight() {
      this = 0 and result = this.getRight()
      or
      exists(SnailFishIndex parent |
        parent.getLeft() = this and result = parent.shiftRight().getLeft()
      )
      or
      exists(SnailFishIndex parent |
        parent.getRight() = this and result = parent.shiftRight().getRight()
      )
    }

    SnailFishIndex getParent() {
      this != 0 and
      result = (this - 1) / 2
    }

    int depth() { result = (this + 1).log2().floor() }

    int invDepth() { result = maxDepth() - depth() - 1 }

    override string toString() {
      if not exists(this.getParent())
      then result = "root"
      else
        if this = this.getParent().getLeft()
        then result = this.getParent().toString() + "->left"
        else result = this.getParent().toString() + "->right"
    }

    int index() { result = this }

    private int leftmostOrder() {
      this = 0 and result = 0
      or
      this != 0 and
      (
        this = this.getParent().getLeft() and result = this.getParent().leftmostOrder()
        or
        this = this.getParent().getRight() and result = this.getParent().inOrder() + 1
      )
    }

    int inOrder() {
      this = 0 and result = 2.pow(maxDepth() - 1).(int) - 1
      or
      this != 0 and
      (
        this = this.getParent().getLeft() and
        result = this.getParent().leftmostOrder() + 2.pow(this.invDepth()).(int) - 1
        or
        this = this.getParent().getRight() and
        result = this.getParent().inOrder() + 2.pow(this.invDepth()).(int)
      )
    }
  }

  newtype TSnailFishKind =
    None() or
    Leaf(int index) { index in [0 .. 100] } or
    Branch()

  class SnailFishKind extends TSnailFishKind {
    string toString() {
      this = None() and result = "-"
      or
      this = Branch() and result = "[...]"
      or
      exists(int i | this = Leaf(i) and result = i.toString())
    }
  }

  newtype TSnailFish = OrigFish(int row, int start) { start = fishStart(row) }

  class OrigSnailFish extends OrigFish {
    int start;
    int row;

    OrigSnailFish() { this = OrigFish(row, start) }

    int leafValue() { result = fish(row).regexpFind("\\d+", _, start).toInt() }

    OrigSnailFish getLeftChild() { result = OrigFish(row, start + 1) }

    OrigSnailFish getRightChild() {
      result = OrigFish(row, getLeftChild().(OrigSnailFish).getEnd() + 1)
    }

    SnailFishKind getKind() {
      result = Leaf(this.leafValue())
      or
      exists(getLeftChild()) and result = Branch()
    }

    SnailFishIndex getIndex() {
      start = 0 and result = 0
      or
      exists(OrigSnailFish parent |
        parent.getLeftChild() = this and
        result = parent.getIndex().getLeft()
      )
      or
      exists(OrigSnailFish parent |
        parent.getRightChild() = this and
        result = parent.getIndex().getRight()
      )
    }

    private int getEnd() {
      result = start + fish(row).regexpFind("\\d+", _, start).length() or
      result = getRightChild().(OrigSnailFish).getEnd() + 1
    }

    int getDepth() {
      start = 0 and result = 0
      or
      exists(OrigSnailFish parent | parent.getLeftChild() = this or parent.getRightChild() = this |
        result = parent.getDepth() + 1
      )
    }

    string toString() {
      result = leafValue().toString() or
      result = "[" + getLeftChild().toString() + "," + getRightChild() + "]"
    }

    int getRow() { result = row }
  }

  SnailFishKind baseSnailFishAt(int row, SnailFishIndex index) {
    exists(fish(row)) and
    (
      exists(OrigSnailFish fish |
        fish.getRow() = row and index = fish.getIndex() and result = fish.getKind()
      )
      or
      not exists(OrigSnailFish fish | fish.getRow() = row and index = fish.getIndex()) and
      result = None()
    )
  }

  signature module ReduceInput {
    bindingset[this]
    class InKey;

    SnailFishKind baseInput(InKey row, SnailFishIndex index);
  }

  module Reduce<ReduceInput In> {
    class InKey = In::InKey;

    SnailFishKind snailFishAt(InKey row, int iter, SnailFishIndex index) {
      result = In::baseInput(row, index) and iter = 0
      or
      result = postSimpl(row, iter - 1, index)
    }

    SnailFishKind reducedSnailFish(InKey row, SnailFishIndex index) {
      exists(int iter |
        result = snailFishAt(row, iter, index) and
        rowExplodes(row, iter) = false and
        rowSplits(row, iter) = false
      )
    }

    pragma[noinline]
    boolean couldExplodeBase(InKey row, int iter, SnailFishIndex index) {
      if index.depth() >= 4
      then
        snailFishAt(row, iter, index) = Branch() and result = true
        or
        snailFishAt(row, iter, index) != Branch() and result = false
      else (
        exists(snailFishAt(row, iter, _)) and result = false
      )
    }

    pragma[noinline]
    boolean couldSplitBase(InKey row, int iter, SnailFishIndex index) {
      exists(SnailFishKind elem | elem = snailFishAt(row, iter, index) |
        exists(int value | elem = Leaf(value) |
          if value >= 10 then result = true else result = false
        )
        or
        not elem instanceof Leaf and
        result = false
      )
    }

    pragma[noinline]
    predicate cantExplodeBase(InKey row, int iter, SnailFishIndex index) {
      couldExplodeBase(row, iter, index) = false
    }

    pragma[noinline]
    predicate cantSplitBase(InKey row, int iter, SnailFishIndex index) {
      couldSplitBase(row, iter, index) = false
    }

    boolean rowExplodes(InKey row, int iter) {
      couldExplodeBase(row, iter, _) = true and result = true
      or
      forall(SnailFishIndex index | cantExplodeBase(row, iter, index)) and
      result = false and
      exists(snailFishAt(row, iter, _))
    }

    boolean rowSplits(InKey row, int iter) {
      rowExplodes(row, iter) = true and result = false
      or
      rowExplodes(row, iter) = false and couldSplitBase(row, iter, _) = true and result = true
      or
      forall(SnailFishIndex index | cantSplitBase(row, iter, index)) and
      result = false and
      exists(snailFishAt(row, iter, _))
    }

    language[monotonicAggregates]
    pragma[noinline]
    SnailFishIndex leftmostExplodeIndex(InKey row, int iter) {
      rowExplodes(row, iter) = true and
      result =
        min(SnailFishIndex index |
          |
          index order by couldExplodeBase(row, iter, index) desc, index.inOrder()
        )
    }

    language[monotonicAggregates]
    pragma[noinline]
    SnailFishIndex leftmostSplitIndex(InKey row, int iter) {
      rowSplits(row, iter) = true and
      result =
        min(SnailFishIndex index |
          |
          index order by couldSplitBase(row, iter, index) desc, index.inOrder()
        )
    }

    int leftLeafWeight(InKey row, int iter, OptSnailFishIndex index) {
      index.isNone() and exists(snailFishAt(row, iter, _)) and result = 255
      or
      exists(SnailFishKind kind | snailFishAt(row, iter, index) = kind and not kind instanceof Leaf) and
      result = 512
      or
      snailFishAt(row, iter, index) instanceof Leaf and result = -index.(SnailFishIndex).inOrder()
    }

    int rightLeafWeight(InKey row, int iter, OptSnailFishIndex index) {
      index.isNone() and exists(snailFishAt(row, iter, _)) and result = 255
      or
      exists(SnailFishKind kind | snailFishAt(row, iter, index) = kind and not kind instanceof Leaf) and
      result = 512
      or
      snailFishAt(row, iter, index) instanceof Leaf and result = index.(SnailFishIndex).inOrder()
    }

    language[monotonicAggregates]
    OptSnailFishIndex leftOfExplosion(InKey row, int iter) {
      exists(SnailFishIndex leftExplodeIndex |
        leftExplodeIndex = leftmostExplodeIndex(row, iter).getLeft()
      |
        forall(SnailFishIndex index | index.inOrder() < leftExplodeIndex.index() |
          exists(SnailFishKind kind |
            snailFishAt(row, iter, index) = kind and not kind instanceof Leaf
          )
        ) and
        result = -1
        or
        result =
          min(OptSnailFishIndex index |
            index.(SnailFishIndex).inOrder() < leftExplodeIndex.inOrder() or
            index.isNone()
          |
            index order by leftLeafWeight(row, iter, index)
          )
      )
    }

    language[monotonicAggregates]
    OptSnailFishIndex rightOfExplosion(InKey row, int iter) {
      exists(SnailFishIndex leftExplodeIndex |
        leftExplodeIndex = leftmostExplodeIndex(row, iter).getRight()
      |
        forall(SnailFishIndex index | index.inOrder() > leftExplodeIndex.index() |
          exists(SnailFishKind kind |
            snailFishAt(row, iter, index) = kind and not kind instanceof Leaf
          )
        ) and
        result = -1
        or
        result =
          min(OptSnailFishIndex index |
            index.(SnailFishIndex).inOrder() > leftExplodeIndex.inOrder() or
            index.isNone()
          |
            index order by rightLeafWeight(row, iter, index)
          )
      )
    }

    predicate explosionRelevant(
      InKey row, int iter, SnailFishIndex explodeIndex, OptSnailFishIndex leftExplode,
      OptSnailFishIndex rightExplode, int leftVal, int rightVal
    ) {
      explodeIndex = leftmostExplodeIndex(row, iter) and
      leftExplode = leftOfExplosion(row, iter) and
      rightExplode = rightOfExplosion(row, iter) and
      Leaf(leftVal) = snailFishAt(row, iter, explodeIndex.getLeft()) and
      Leaf(rightVal) = snailFishAt(row, iter, explodeIndex.getRight())
    }

    SnailFishKind postExplosion(InKey row, int iter, SnailFishIndex index) {
      exists(
        SnailFishIndex explodeIndex, OptSnailFishIndex leftExplode, OptSnailFishIndex rightExplode,
        int leftVal, int rightVal, SnailFishKind prevKind, SnailFishIndex explodeLeft,
        SnailFishIndex explodeRight
      |
        explosionRelevant(row, iter, explodeIndex, leftExplode, rightExplode, leftVal, rightVal) and
        prevKind = snailFishAt(row, iter, index) and
        explodeLeft = explodeIndex.getLeft() and
        explodeRight = explodeIndex.getRight() and
        (
          if index = explodeLeft
          then result = None()
          else
            if index = explodeRight
            then result = None()
            else
              if index = explodeIndex
              then result = Leaf(0)
              else
                if index = leftExplode
                then
                  exists(int prevVal |
                    Leaf(prevVal) = prevKind and
                    result = Leaf(prevVal + leftVal)
                  )
                else
                  if index = rightExplode
                  then
                    exists(int prevVal |
                      Leaf(prevVal) = prevKind and
                      result = Leaf(prevVal + rightVal)
                    )
                  else result = prevKind
        )
      )
    }

    SnailFishKind postSplit(InKey row, int iter, SnailFishIndex index) {
      rowSplits(row, iter) = true and
      exists(SnailFishIndex splitIndex, int splitVal, SnailFishKind prevKind |
        splitIndex = leftmostSplitIndex(row, iter) and
        Leaf(splitVal) = snailFishAt(row, iter, splitIndex) and
        prevKind = snailFishAt(row, iter, index) and
        (
          if index = splitIndex.getLeft()
          then result = Leaf(splitVal / 2)
          else
            if index = splitIndex.getRight()
            then result = Leaf(splitVal - splitVal / 2)
            else
              if index = splitIndex
              then result = Branch()
              else result = prevKind
        )
      )
    }

    pragma[noopt]
    SnailFishKind postSimpl(InKey row, int iter, SnailFishIndex index) {
      result = postSplit(row, iter, index)
      or
      result = postExplosion(row, iter, index)
    }
  }

  module P1Reduce = Reduce<P1In>;

  module P1In implements ReduceInput {
    class InKey = int;

    SnailFishKind baseInput(int row, SnailFishIndex index) {
      result = baseSnailFishAt(0, index) and
      row = 0
      or
      result = addFish(row, index)
    }

    private SnailFishKind addFish(int row, SnailFishIndex index) {
      row != 0 and
      exists(fish(row)) and
      (
        index = 0 and result = Branch()
        or
        exists(SnailFishIndex prev |
          result = P1Reduce::reducedSnailFish(row - 1, prev) and
          index = prev.shiftLeft()
        )
        or
        exists(SnailFishIndex prev |
          result = baseSnailFishAt(row, prev) and
          index = prev.shiftRight()
        )
      )
    }
  }

  module P2In implements ReduceInput {
    newtype InKey = additional P2Key(int i, int j) { exists(fish(i)) and exists(fish(j)) and i != j }

    SnailFishKind baseInput(InKey row, SnailFishIndex index) {
      exists(int i, int j | row = P2Key(i, j) |
        index = 0 and result = Branch()
        or
        exists(SnailFishIndex prev |
          result = baseSnailFishAt(i, prev) and
          index = prev.shiftLeft()
        )
        or
        exists(SnailFishIndex prev |
          result = baseSnailFishAt(j, prev) and
          index = prev.shiftRight()
        )
      )
    }
  }

  module P2Reduce = Reduce<P2In>;

  string printPostAt(int row, int iter, SnailFishIndex cur) {
    exists(int i | Leaf(i) = P1Reduce::postSimpl(row, iter, cur) and result = i.toString())
    or
    Branch() = P1Reduce::postSimpl(row, iter, cur) and
    result =
      "[" + printPostAt(row, iter, cur.getLeft()) + "," + printPostAt(row, iter, cur.getRight()) +
        "]"
  }

  string printPost(int row, int iter) { result = printPostAt(row, iter, 0) }


  string printPostAt2(P2In::InKey row, int iter, SnailFishIndex cur) {
    exists(int i | Leaf(i) = P2Reduce::postSimpl(row, iter, cur) and result = i.toString())
    or
    Branch() = P2Reduce::postSimpl(row, iter, cur) and
    result =
      "[" + printPostAt2(row, iter, cur.getLeft()) + "," + printPostAt2(row, iter, cur.getRight()) +
        "]"
  }

  string printPost2(P2In::InKey row, int iter) { result = printPostAt2(row, iter, 0) }

  int magnitude() { result = magnitudeAt(0) }

  int magnitudeAt(SnailFishIndex index) {
    exists(int row, SnailFishKind kind |
      not exists(fish(row + 1)) and
      kind = P1Reduce::reducedSnailFish(row, index) and
      (
        Leaf(result) = kind
        or
        kind = Branch() and
        result = 3 * magnitudeAt(index.getLeft()) + 2 * magnitudeAt(index.getRight())
      )
    )
  }

  int magnitude(P2In::InKey row) { result = magnitudeAt(row, 0) }

  int magnitudeAt(P2In::InKey row,SnailFishIndex index) {
    exists(SnailFishKind kind |
      kind = P2Reduce::reducedSnailFish(row, index) and
      (
        Leaf(result) = kind
        or
        kind = Branch() and
        result = 3 * magnitudeAt(row,index.getLeft()) + 2 * magnitudeAt(row, index.getRight())
      )
    )
  }

  int maxMag() {
    result = max(magnitude(_))
  }


}

string testInput() {
  result =
    "[[[0,[4,5]],[0,0]],[[[4,5],[2,6]],[9,5]]]\n[7,[[[3,7],[4,3]],[[6,3],[8,8]]]]\n[[2,[[0,8],[3,4]]],[[[6,7],1],[7,[1,6]]]]\n[[[[2,4],7],[6,[0,5]]],[[[6,8],[2,8]],[[2,1],[4,5]]]]\n[7,[5,[[3,8],[1,4]]]]\n[[2,[2,2]],[8,[8,1]]]\n[2,9]\n[1,[[[9,3],9],[[9,0],[0,7]]]]\n[[[5,[7,4]],7],1]\n[[[[4,2],2],6],[8,7]]\n"
}

string testInputExtra() { result = "[[[[[4,3],4],4],[7,[[8,4],9]]],[1,1]]" }

string testInputExtra2() {
  result =
    "[[[0,[5,8]],[[1,7],[9,6]]],[[4,[1,2]],[[1,4],2]]]\n[[[5,[2,8]],4],[5,[[9,9],0]]]\n[6,[[[6,2],[5,6]],[[7,6],[4,7]]]]\n[[[6,[0,7]],[0,9]],[4,[9,[9,0]]]]\n[[[7,[6,4]],[3,[1,3]]],[[[5,5],1],9]]\n[[6,[[7,3],[3,2]]],[[[3,8],[5,7]],4]]\n[[[[5,4],[7,7]],8],[[8,3],8]]\n[[9,3],[[9,9],[6,[4,9]]]]\n[[2,[[7,7],7]],[[5,8],[[9,3],[0,2]]]]\n[[[[5,2],5],[8,[3,7]]],[[5,[7,5]],[4,4]]]"
}

string realInput() {
  result =
    "[[[9,2],[[2,9],0]],[1,[[2,3],0]]]\n[[[[2,0],2],[[6,4],[7,3]]],[0,[[3,0],[0,6]]]]\n[[[[7,2],2],[9,[6,5]]],[[2,4],5]]\n[[[[7,8],2],1],[[[5,4],[2,9]],[7,8]]]\n[[[0,7],[1,[6,6]]],[[[0,7],9],4]]\n[[[3,[9,6]],[5,1]],[[[0,1],6],[[7,6],0]]]\n[[[3,0],[7,[4,0]]],[4,[[6,6],[5,3]]]]\n[[[1,[4,8]],[2,[5,8]]],[[[3,6],[2,2]],[[3,8],[7,0]]]]\n[9,[[[5,0],[0,3]],[2,[2,6]]]]\n[[[3,[8,2]],[[8,0],5]],[[[7,6],[4,9]],[7,5]]]\n[[7,[[4,1],9]],[5,1]]\n[[[5,[7,5]],1],[8,[5,8]]]\n[[[[0,2],7],[[1,4],[9,8]]],[[3,[0,3]],7]]\n[[[[4,3],[7,4]],[6,[6,4]]],[8,0]]\n[[[1,1],1],[[5,[2,7]],7]]\n[[[5,4],5],[[7,[6,3]],[[8,4],6]]]\n[[[7,9],[[4,4],[0,0]]],[[[8,6],6],[2,[6,4]]]]\n[[[[4,7],[4,9]],3],[[[7,1],[8,6]],[9,[8,2]]]]\n[6,[6,[2,9]]]\n[[4,[[5,5],[5,0]]],[[[3,4],[9,5]],[8,6]]]\n[2,[0,[2,5]]]\n[[[4,[7,1]],[2,8]],[[7,0],[[1,6],1]]]\n[[[3,4],[[7,8],[6,7]]],[[[6,2],[1,2]],5]]\n[[[8,[0,8]],[[9,9],0]],[[[3,5],[4,2]],7]]\n[[0,[[0,3],2]],[4,1]]\n[[[[0,4],6],7],[[4,[9,1]],3]]\n[[0,[[7,0],8]],[2,[8,[8,2]]]]\n[[[[3,6],2],[9,4]],[6,[[7,9],[4,5]]]]\n[[[[4,9],1],[[9,6],[8,8]]],[[7,[7,6]],[[8,3],[9,0]]]]\n[2,0]\n[[[[8,2],0],[3,5]],[[7,2],0]]\n[[[[1,9],9],6],[9,[[9,3],[8,7]]]]\n[[[9,[4,0]],[[7,1],[4,4]]],[[4,[2,3]],[8,7]]]\n[[[[9,7],[5,6]],[4,[6,7]]],7]\n[5,[[[8,2],8],[6,[7,9]]]]\n[0,[[9,[0,1]],[[8,3],7]]]\n[[[[4,5],[4,2]],[[5,2],[3,1]]],[[[3,1],[8,5]],8]]\n[[0,4],[[2,[2,6]],[[1,1],3]]]\n[[[0,8],[7,[5,8]]],7]\n[[[7,2],[[6,6],[2,7]]],[[0,[9,3]],2]]\n[[[[0,9],2],[[6,0],4]],3]\n[[5,[[9,6],9]],[[6,[1,2]],[1,[6,2]]]]\n[[[[3,9],5],[9,[7,2]]],[5,[[3,4],[0,6]]]]\n[[2,[6,7]],[0,[[2,0],7]]]\n[[2,[[5,4],[2,1]]],[2,[[8,7],[5,3]]]]\n[[[[0,4],[2,5]],[1,2]],[5,[8,[0,3]]]]\n[[[[9,2],[3,2]],[[2,9],4]],5]\n[[[[8,9],5],1],[9,3]]\n[[5,2],[3,[[8,5],2]]]\n[[[0,1],[7,8]],[[[6,2],4],[[6,2],[9,5]]]]\n[[[[9,6],5],2],2]\n[[[[3,2],3],3],[[[0,1],1],[[8,4],8]]]\n[[4,[2,[3,0]]],[[6,[7,0]],6]]\n[[6,[[7,8],3]],[[[2,7],4],9]]\n[0,2]\n[[[9,1],[[3,7],[6,0]]],[[0,[4,1]],[[5,4],7]]]\n[[[3,[9,4]],8],[[5,3],2]]\n[[6,6],[[[0,5],[0,9]],[[5,5],4]]]\n[[[[1,2],4],[[2,4],[8,0]]],[0,[[4,4],[5,8]]]]\n[0,[[[9,0],3],[8,4]]]\n[[4,5],[[[9,9],[3,5]],[8,[1,4]]]]\n[[7,8],[[[3,1],[7,0]],[[4,7],[9,1]]]]\n[[4,[2,[1,9]]],[[6,[6,1]],[[0,3],3]]]\n[[[5,[0,9]],6],[[[3,4],[9,6]],[[4,0],[0,4]]]]\n[[[1,5],[8,[2,8]]],[[5,[0,8]],[[0,7],[4,6]]]]\n[[9,[0,2]],[[3,3],[3,1]]]\n[[[[2,8],[5,9]],[2,[1,5]]],9]\n[[3,[[8,9],[3,1]]],[[[9,0],7],[[0,4],3]]]\n[[[[1,5],2],[5,[5,9]]],[5,[[0,1],[0,2]]]]\n[6,[[[0,4],8],[[8,2],[5,5]]]]\n[[[[7,7],5],[[8,2],7]],[2,5]]\n[[[1,1],[[7,8],0]],3]\n[[6,[[4,2],9]],[[[5,4],4],3]]\n[[[[5,8],3],[[0,4],9]],[[[2,9],2],[3,4]]]\n[[0,[4,8]],6]\n[[[[9,5],[1,9]],[[3,7],[5,5]]],8]\n[[1,9],6]\n[[[4,[1,5]],3],0]\n[[[2,[6,9]],5],[[5,7],[5,[7,1]]]]\n[[[[3,1],[7,3]],[[1,0],[4,6]]],[[[4,9],[4,1]],[9,[2,0]]]]\n[[[5,0],[[9,4],6]],[1,[[0,4],[9,9]]]]\n[[[[9,8],3],[7,5]],[[[9,5],2],[9,9]]]\n[[8,[[8,0],[2,3]]],[[[3,8],[2,6]],[[1,0],0]]]\n[[[7,[7,1]],[[6,6],[2,9]]],[[5,[2,0]],[[3,9],[7,4]]]]\n[1,[4,[[9,7],[1,3]]]]\n[[0,3],[[[4,1],7],[[4,1],[3,0]]]]\n[[0,[[7,7],6]],[[4,9],2]]\n[[0,8],[4,[4,5]]]\n[[[8,[0,5]],[[1,3],[0,5]]],[[2,6],[1,5]]]\n[[[[7,6],8],[0,[2,7]]],8]\n[8,[[[5,4],8],[[2,1],[7,5]]]]\n[[[[7,3],[7,1]],0],[[[7,9],2],3]]\n[[8,5],[6,6]]\n[[[[5,2],8],7],[[[6,8],[1,0]],[[0,0],1]]]\n[[[[1,0],1],6],[9,8]]\n[[[[1,2],7],[1,[2,8]]],[[8,1],[[7,5],2]]]\n[[0,6],[[2,8],[9,0]]]\n[[[0,[7,7]],[2,[0,8]]],[[[7,4],4],[7,[4,0]]]]\n[[[2,[9,3]],[[3,7],3]],[[[9,7],[5,6]],8]]\n[[2,[[8,7],2]],[[8,[1,8]],[[7,2],1]]]"
}

module TestImpl = Impl<testInput/0>;

module ExtraImpl = Impl<testInputExtra/0>;

module ExtraImpl2 = Impl<testInputExtra2/0>;

module RealImpl2 = Impl<realInput/0>;

select 1
