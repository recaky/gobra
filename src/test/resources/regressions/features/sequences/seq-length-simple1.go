package pkg

// very simple use of the unary sequence length operator
requires 0 < len(xs)
func example1(ghost xs seq[int]) {
}

// simple use of sequence append and sequence size operators
requires 0 < len(xs)
requires 0 < len(ys)
ensures 0 < len(zs)
func example2(ghost xs seq[int], ghost ys seq[int]) (ghost zs seq[int]) {
  zs = xs ++ ys
}

// ghost state and sequence length
func example3() {
  ghost xs := seq[int] { 1, 7, 32 }
  assert len(xs) == 3
}

// simple example of sequence length in combination with sequence literals
func example4() {
  assert len(seq[bool] { true, false }) == 2
  assert len(seq[bool] { true }) == len(seq[int] { 42 })
  assert len(seq[seq[int]] { seq[int] { 1 }, seq[int] { 17, 142 } }) == 2;
  assert seq[int] { len(seq[int] { 1 }), len(seq[int] { 17, 142 }) } == seq[int] { 1, 2 };
}