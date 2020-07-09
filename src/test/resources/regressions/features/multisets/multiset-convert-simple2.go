package pkg

func example1(ghost x int, ghost xs seq[int]) {
  ghost m := mset(xs)
  assert x # xs == x # m
  assert 0 < x # xs ==> x in m
  assert x in m ==> 0 < x # xs
}

func example2(ghost xs seq[int], ghost ys seq[int]) {
  assert mset(xs ++ ys) == mset(xs) union mset(ys)
}

func example3(ghost xs seq[int]) {
  assert mset(mset(xs)) == mset(xs)
  assert |mset(xs)| == len(xs)
}

func example4() {
  assert mset(seq[int] { }) == mset[int] { }
  assert mset(seq[int] { 42 }) == mset[int] { 42 }
  assert mset(seq[int] { 1, 2, 2, 3 }) == mset[int] { 3, 2, 2, 1 }
}

func example5(ghost x int, ghost xs seq[int]) {
  assert x in xs ==> x in mset(xs)
  assert x in mset(xs) ==> x in xs
}

func example6() {
  assert mset(seq[int] { 1, 2 }) intersection mset(seq[int] { 2, 3 }) == mset[int] { 2 }
  assert mset(seq[int] { 1, 2 }) setminus mset(seq[int] { 2, 3 }) == mset[int] { 1 }
}

func example7(ghost xs seq[int], ghost ys seq[int]) {
  assert mset(xs) subset mset(xs ++ ys)
  assert mset(xs) intersection mset(xs ++ ys) == mset(xs)
}

func example8(ghost xs seq[int], n int, i int) {
  assert xs == xs[:i] ++ xs[i:] // can we also do without this assertion?
  assert n in xs[:i] ==> n in mset(xs)
  assert n in xs[i:] ==> n in mset(xs)
  assert n in xs[i:] ==> n in mset(xs[i:])
}
