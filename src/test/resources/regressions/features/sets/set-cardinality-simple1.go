package pkg

func example1(ghost s set[int]) (ghost n int) {
  n = |s|;
}

func example2(ghost s set[int], ghost t set[int]) {
  // assert s subset t ==> |s| <= |t|; -- doesn't verify??
  // assert |s union t| <= |s|; -- doesn't verify??
  // assert |s| <= |s intersection t|; -- doesn't verify??
}

func example3() {
  assert |set[int] { 1, 2, 3 }| == 3
  assert |set[int] { 1 }| == len(seq[int] { 2 })
}

ensures n == |s union set[int] { 42 }|;
func example4(ghost s set[int]) (ghost n int) {
  n = |s union set[int] { 42 }|;
}

requires |s| == |t|;
func example5(ghost s set[int], ghost t set[bool]) {
}
