package pkg

func example1(ghost s set[int]) {
}

func example2() {
  ghost var s set[int]
}

func example3() (ghost s set[int]) {
}

ensures s1 == s2
func example4(ghost s1 set[int]) (ghost s2 set[int]) {
  s2 = s1
}

func example5(ghost s set[bool]) {
  ghost t := s
}

func example6(ghost s set[set[set[bool]]]) {
}
