package pkg

func example1(ghost xs seq[int]) {
  ghost ys := xs[1:14]
}

func example2() {
  assert seq[0..10][5:] == seq[5..10]
  assert seq[0..10][:5] == seq[0..5]
}

func example3() {
  assert seq[0..10][1:][2:][3:] == seq[6..10]
  assert seq[0..10][:5][:3] == seq[0..3]
}

func example4(ghost xs seq[int]) {
  assert xs[0:] == xs
  assert xs[:len(xs)] == xs
  assert xs[:] == xs
  assert xs[0:len(xs)] == xs
}

func example5() {
  assert seq[int] { 1, 2, 4, 8 }[2:] == seq[int] { 4, 8 }
  assert seq[int] { 1, 2, 4, 8 }[:2] == seq[int] { 1, 2 }
  assert seq[int] { 1, 2, 4, 8 }[1:3] == seq[int] { 2, 4 }
}

func example6() {
  assert seq[0..9][-10:] == seq[0..9]
  assert seq[0..9][:1000] == seq[0..9]
  assert seq[0..9][-100:100] == seq[0..9]
  assert seq[0..9][100:-100] == seq[int] { }
}

func example7() {
  assert len(seq[0..9][5:]) == 4
  assert len(seq[0..9][:5]) == 5
  assert len(seq[0..9][2:8]) == 6
}

requires x in xs[4:]
func example8(ghost xs seq[int], x int) { 
  assert x in xs
}

requires x in xs[:7]
func example9(ghost xs seq[int], x int) { 
  assert x in xs
}

requires !(x in xs[5:])
requires !(x in xs[:5])
func example10(ghost xs seq[int], x int) {
  assert !(x in xs)
}

ensures xs == xs[:n] ++ xs[n:]
func example11(ghost xs seq[int], n int) {
} 
