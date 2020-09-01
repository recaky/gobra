package main

func foo() {
  r := Rectangle{Width: 5, Height: 5}
  assert Square(5) == r
}

type Rectangle struct {
    Width, Height int
}

ensures res == r.Width && res == r.Height
func Square(res int) (r Rectangle) {
    return Rectangle{res, res}
}

pure func Square2(res int) (r Rectangle) {
    return Rectangle{res, res}
}