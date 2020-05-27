package viper.gobra

import org.scalatest.{FunSuite, Inside, Matchers}
import viper.gobra.ast.internal._
import viper.gobra.reporting.Source.Parser.Unsourced

class InternalPrettyPrinterUnitTests extends FunSuite with Matchers with Inside {
  val frontend = new TestFrontend()

  test("PrettyPrinter: should correctly show a standard sequence index expression") {
    val expr = SequenceIndex(
      LocalVar.Ref("xs", SequenceT(IntT))(Unsourced),
      IntLit(BigInt(42))(Unsourced)
    )(Unsourced)

    frontend.show(expr) should matchPattern {
      case "xs[42]" =>
    }
  }

  test("PrettyPrinter: should correctly show a sequence update expression") {
    val expr = SequenceUpdate(
      LocalVar.Ref("xs", SequenceT(BoolT))(Unsourced),
      IntLit(BigInt(4))(Unsourced),
      BoolLit(false)(Unsourced)
    )(Unsourced)

    frontend.show(expr) should matchPattern {
      case "xs[4 = false]" =>
    }
  }

  test("PrettyPrinter: should correctly show an empty integer sequence") {
    val expr = EmptySequence(IntT)(Unsourced)

    frontend.show(expr) should matchPattern {
      case "seq[int] { }" =>
    }
  }

  test("PrettyPrinter: should correctly show an empty (nested) Boolean sequence") {
    val expr = EmptySequence(SequenceT(SequenceT(BoolT)))(Unsourced)

    frontend.show(expr) should matchPattern {
      case "seq[seq[seq[bool]]] { }" =>
    }
  }

  test("PrettyPrinter: should correctly show a sequence range expression") {
    val expr = RangeSequence(
      IntLit(BigInt(2))(Unsourced),
      IntLit(BigInt(44))(Unsourced)
    )(Unsourced)

    frontend.show(expr) should matchPattern {
      case "seq[2 .. 44]" =>
    }
  }

  test("PrettyPrinter: should correctly show a non-empty simple integer sequence literal") {
    val expr = SequenceLiteral(
      Vector(
        IntLit(BigInt(2))(Unsourced),
        IntLit(BigInt(4))(Unsourced),
        IntLit(BigInt(8))(Unsourced)
      )
    )(Unsourced)

    frontend.show(expr) should matchPattern {
      case "seq { 2, 4, 8 }" =>
    }
  }

  test("PrettyPrinter: should correctly show a singleton integer sequence literal") {
    val expr = SequenceLiteral(
      Vector(IntLit(BigInt(42))(Unsourced))
    )(Unsourced)

    frontend.show(expr) should matchPattern {
      case "seq { 42 }" =>
    }
  }

  test("PrettyPrinter: should correctly show an empty sequence literal") {
    val expr = SequenceLiteral(Vector())(Unsourced)

    frontend.show(expr) should matchPattern {
      case "seq { }" =>
    }
  }

  test("PrettyPrinter: should correctly show an ordinary sequence drop operation") {
    val expr = SequenceDrop(
      LocalVar.Ref("xs", SequenceT(IntT))(Unsourced),
      IntLit(BigInt(42))(Unsourced)
    )(Unsourced)

    frontend.show(expr) should matchPattern {
      case "xs[42:]" =>
    }
  }

  test("PrettyPrinter: should correctly show an ordinary sequence take operation") {
    val expr = SequenceTake(
      LocalVar.Ref("xs", SequenceT(IntT))(Unsourced),
      IntLit(BigInt(4))(Unsourced)
    )(Unsourced)

    frontend.show(expr) should matchPattern {
      case "xs[:4]" =>
    }
  }

  test("PrettyPrinter: should correctly show a sequence drop followed by a take") {
    val expr1 = SequenceDrop(
      LocalVar.Ref("xs", SequenceT(IntT))(Unsourced),
      IntLit(BigInt(2))(Unsourced)
    )(Unsourced)
    val expr2 = SequenceTake(
      expr1, IntLit(BigInt(4))(Unsourced)
    )(Unsourced)

    frontend.show(expr2) should matchPattern {
      case "xs[2:][:4]" =>
    }
  }

  class TestFrontend {
    val printer = new DefaultPrettyPrinter()
    def show(n : Node) : String = printer.format(n)
  }
}
