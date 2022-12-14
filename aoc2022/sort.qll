bindingset[this]
signature class Type;

signature module Comparator<Type T> {
  bindingset[i, j]
  predicate isLess(T i, T j);

  bindingset[i, j]
  predicate isLessOrEq(T i, T j);
}

signature module List<Type T> {
  T getElem(int i);
}

module IntCompare implements Comparator<int> {
  bindingset[i, j]
  predicate isLess(int i, int j) { i < j }

  bindingset[i, j]
  predicate isLessOrEq(int i, int j) { i <= j }
}

module TestList implements List<int> {
  int getElem(int i) { i in [0 .. 100000] and result = (i * 57637) % 100000 }
}

module SmallTestList implements List<int> {
  int getElem(int i) { i in [0 .. 100] and result = (i * 57) % 100 }
}

predicate sorted = MergeSort<int, IntCompare, SmallTestList>::getElem/1;

predicate sorted2 = BitonicSort<int, IntCompare, TestList>::getElem/1;

int sortedSample(int i) { i in [1 .. 1000] and result = sorted(i) }

module MergeSort<Type T, Comparator<T> C, List<T> L> {
  cached
  T getElem(int i) { result = listIter(numIters(), 0, i) }

  predicate needsCompare(T a, T b) {
    exists(int iter, int listIndex, int prevLhs, int prevRhs |
      iter(iter, listIndex, _, prevLhs, prevRhs) and
      a = iterListLhs(iter, listIndex, prevLhs) and
      b = iterListRhs(iter, listIndex, prevRhs)
    )
  }

  predicate expectedIndex(int iter, int listIndex, int indexInList) {
    exists(int origIndex |
      origIndex in [0 .. totalLen() - 1] and
      listIndex = origIndex / initLen(iter) and
      indexInList = origIndex % initLen(iter)
    )
  }

  private int numIters() { result = totalLen().log2().ceil() - 1 }

  private int initLen(int iter) {
    iter in [0 .. numIters()] and
    result = 2.pow(iter)
  }

  private T partialResult(int iter, int listIndex, int indexInList) {
    result = L::getElem(listIndex) and indexInList = 0 and iter = 0
    or
    result = listIter(iter - 1, listIndex, indexInList)
  }

  private T iterListLhs(int iter, int i, int j) {
    exists(int origIndex |
      result = partialResult(iter, origIndex, j) and i = origIndex / 2 and 0 = origIndex % 2
    )
  }

  private T iterListRhs(int iter, int i, int j) {
    exists(int origIndex |
      result = partialResult(iter, origIndex, j) and i = origIndex / 2 and 1 = origIndex % 2
    )
  }

  private int listLenLhs(int iter, int listId) {
    exists(int prevId |
      listId = prevId / 2 and prevId % 2 = 0 and result = listLen(prevId, initLen(iter))
    )
  }

  private int listLenRhs(int iter, int listId) {
    exists(int prevId |
      listId = prevId / 2 and prevId % 2 = 1 and result = listLen(prevId, initLen(iter))
    )
  }

  private int totalLen() { result = max(int i | exists(L::getElem(i))) + 1 }

  private predicate iterBothIndex(int iter, int i) {
    i in [0 .. (inputListInIter(iter) / 2) - 1] and iter >= 0
  }

  private int inputListInIter(int iter) { result = (totalLen() - 1) / initLen(iter) + 1 }

  private predicate iterLHSOnly(int iter, int i) {
    i = inputListInIter(iter) / 2 and inputListInIter(iter) % 2 != 0
  }

  pragma[assume_small_delta]
  pragma[nomagic]
  T lhsAtIter(int iter, int listIndex, int resultIndex) {
    exists(int lhsIndex |
      iter(iter, listIndex, resultIndex, lhsIndex, _) and
      result = iterListLhs(iter, listIndex, lhsIndex)
    )
  }

  pragma[assume_small_delta]
  pragma[nomagic]
  T rhsAtIter(int iter, int listIndex, int resultIndex) {
    exists(int rhsIndex |
      iter(iter, listIndex, resultIndex, _, rhsIndex) and
      result = iterListRhs(iter, listIndex, rhsIndex)
    )
  }

  pragma[assume_small_delta]
  pragma[nomagic]
  private predicate iter(int iter, int listIndex, int resultIndex, int lhsIndex, int rhsIndex) {
    resultIndex = 0 and lhsIndex = 0 and rhsIndex = 0 and iterBothIndex(iter, listIndex)
    or
    exists(int prevLhs, int prevRhs |
      exists(T a, T b |
        iter(iter, listIndex, resultIndex - 1, prevLhs, prevRhs) and
        a = lhsAtIter(iter, listIndex, resultIndex - 1) and
        b = rhsAtIter(iter, listIndex, resultIndex - 1) and
        C::isLess(a, b) and
        lhsIndex = prevLhs + 1 and
        rhsIndex = prevRhs
        or
        iter(iter, listIndex, resultIndex - 1, prevLhs, prevRhs) and
        a = lhsAtIter(iter, listIndex, resultIndex - 1) and
        b = rhsAtIter(iter, listIndex, resultIndex - 1) and
        C::isLessOrEq(b, a) and
        lhsIndex = prevLhs and
        rhsIndex = prevRhs + 1
      )
      or
      iter(iter, listIndex, resultIndex - 1, prevLhs, prevRhs) and
      prevLhs = listLenLhs(iter, listIndex) and
      prevRhs != listLenRhs(iter, listIndex) and
      lhsIndex = prevLhs and
      rhsIndex = prevRhs + 1
      or
      iter(iter, listIndex, resultIndex - 1, prevLhs, prevRhs) and
      prevLhs != listLenLhs(iter, listIndex) and
      prevRhs = listLenRhs(iter, listIndex) and
      lhsIndex = prevLhs + 1 and
      rhsIndex = prevRhs
    )
  }

  bindingset[desiredLen]
  private int listLen(int listId, int desiredLen) {
    listId in [0 .. (totalLen() / desiredLen) - 1] and result = desiredLen
    or
    listId = (totalLen() / desiredLen) and result = (totalLen() % desiredLen) and result != 0
  }

  pragma[assume_small_delta]
  pragma[nomagic]
  private T listIter(int iter, int listIndex, int resultIndex) {
    exists(T a, T b |
      a = lhsAtIter(iter, listIndex, resultIndex) and
      b = rhsAtIter(iter, listIndex, resultIndex) and
      C::isLess(a, b) and
      result = a
      or
      a = lhsAtIter(iter, listIndex, resultIndex) and
      b = rhsAtIter(iter, listIndex, resultIndex) and
      C::isLessOrEq(b, a) and
      result = b
    )
    or
    exists(int prevLhs, int prevRhs |
      iter(iter, listIndex, resultIndex, prevLhs, prevRhs) and
      prevLhs = listLenLhs(iter, listIndex) and
      result = iterListRhs(iter, listIndex, prevRhs) and
      prevRhs != listLenRhs(iter, listIndex)
      or
      iter(iter, listIndex, resultIndex, prevLhs, prevRhs) and
      prevRhs = listLenRhs(iter, listIndex) and
      result = iterListLhs(iter, listIndex, prevLhs) and
      prevLhs != listLenLhs(iter, listIndex)
    )
    or
    iterLHSOnly(iter, listIndex) and result = iterListLhs(iter, listIndex, resultIndex)
  }
}

module BitonicSort<Type T, Comparator<T> C, List<T> L> {
  private int listLen() { result = max(int i | exists(L::getElem(i))) + 1 }

  T getElem(int x) { exists(int k | result = iterValue(k, 1, x) and k >= listLen()) }

  pragma[noinline]
  private T getInitLVal(int k, int i, int l) {
    exists(int prevK |
      result = iterValue(prevK, 1, l) and
      k = prevK * 2 and
      i = l.bitXor(k - 1) and
      prevK < listLen()
    )
  }

  pragma[noinline]
  private T getInitIVal(int k, int i, int l) {
    exists(int prevK |
      result = iterValue(prevK, 1, i) and
      k = prevK * 2 and
      l = i.bitXor(k - 1) and
      prevK < listLen()
    )
  }

  pragma[noinline]
  private T getLVal(int k, int j, int i, int l) {
    exists(int prevJ |
      result = iterValue(k, prevJ, l) and
      j = prevJ / 2 and
      i = l.bitXor(j)
    )
  }

  pragma[noinline]
  private T getIVal(int k, int j, int i, int l) {
    exists(int prevJ |
      result = iterValue(k, prevJ, i) and
      j = prevJ / 2 and
      l = i.bitXor(j)
    )
  }

  private T iterValue(int k, int j, int x) {
    k = 1 and result = L::getElem(x) and j = 1
    or
    exists(int l, T iPrev, int prevK |
      iPrev = iterValue(prevK, 1, x) and
      k = prevK * 2 and
      l = x.bitXor(k - 1) and
      x < l and
      prevK < listLen() and
      l >= listLen() and
      result = iPrev and
      j = k / 2
    )
    or
    exists(int i, int l, T iPrev, T lPrev |
      iPrev = getInitIVal(k, i, l) and
      lPrev = getInitLVal(k, i, l) and
      i < l and
      (
        C::isLess(lPrev, iPrev) and
        (
          result = iPrev and x = l
          or
          result = lPrev and x = i
        )
        or
        C::isLessOrEq(iPrev, lPrev) and
        (
          result = iPrev and x = i
          or
          result = lPrev and x = l
        )
      ) and
      j = k / 2
    )
    or
    exists(int i, int l, T iPrev, int prevJ |
      j > 0 and
      l = i.bitXor(j) and
      j = prevJ / 2 and
      iPrev = iterValue(k, prevJ, i) and
      (
        l >= listLen() and
        result = iPrev and
        x = i
      )
    )
    or
    exists(int i, int l, T iPrev, T lPrev |
      j > 0 and
      iPrev = getIVal(k, j, i, l) and
      lPrev = getLVal(k, j, i, l) and
      x = i and
      (
        l > i and
        (
          C::isLess(lPrev, iPrev) and
          result = lPrev
          or
          C::isLessOrEq(iPrev, lPrev) and
          result = iPrev
        )
        or
        l < i and
        (
          C::isLess(iPrev, lPrev) and
          result = lPrev
          or
          C::isLessOrEq(lPrev, iPrev) and
          result = iPrev
        )
      )
    )
  }
}
