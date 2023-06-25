// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

/*package viper.gobra.ast.internal.transform

import viper.gobra.ast.{internal => in}
import viper.gobra.reporting.Source
//import viper.gobra.reporting.Source.SlicingExpressionAnnotation
import viper.gobra.reporting.Source.Parser.Single
import viper.gobra.util.Violation.violation

/**
  * Transformation responsible for generating call-graph edges from interface methods to their implementations' methods.
  * This is necessary to soundly verify termination in the presence of dynamic method binding.
  */
object SyntacticCheck2 extends InternalTransform {
  override def name(): String = "syntactic_check_for_interface"
  var methodsToAdd: Set[in.Member] = Set.empty
  /**
    * Program-to-program transformation
    */
  override def transform(p: in.Program): in.Program = p match {
    case in.Program(_, members, _) =>

      def checkBody(m: in.Member): Unit = m match {
        case m: in.Function =>
          m.body match {
            case Some(in.MethodBody(_, seqn, _)) =>
              seqn.stmts.foreach(
                s => s.visit {
                  case elem: in.Stmt =>
                    if (checkStmt(elem)) {
                      println("The function " + m.name + " contains subslicing expressions");
                      m.Annotation().setslices(0)
                      println(m.Annotation().slices)
                      //m.withInfo(createAnnotatedInfo(m.info))
                      return
                    } else {}
                  case _ =>
              })
              println("The function " + m.name + " does not contain subslicing expressions")
              m.Annotation().setslices(1)
              println(m.Annotation().slices)
            case _ => m.Annotation().setslices(1) 
          }
        case _ =>
      }

      /*
      Checks the expressions for subslicing expressions
       */
      def checkExpr(e: in.Expr): Boolean = {
        var slice = false
        e.visit {
          case elem: in.Slice => slice = true
          case _ =>
        }
        slice
      }
     
      /*
      Checks the statements for subslicing expressions
       */
      def checkSameEncoding(s: in.Stmt, m: in.Member, p: in.Program): Boolean = s match {
        case s: in.If => checkSameEncoding(s.cond) && checkSameEncoding(s.thn) && checkSameEncoding(s.els)
        case s: in.While =>  checkSameEncoding(s.cond) && checkSameEncoding(s.body)
        case s: in.SingleAss => checkSameEncoding(s.right)
        case s: in.FunctionCall => {
        val member = p.lookup(s.func)
        if (member.slices==m.slices) {} else {
          val newMember = in.Function( member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, None)(member.info)
          methodsToAdd += newMember


}






        }
        case s: in.MethodCall => {
        val member = p.lookup(s.meth)
        if (member.slices==m.slices) {} else {
        val newMember = in.Method( member.receiver, member.name, member.args, member.results, member.pres, member.posts, member.terminationMeasures, None)(member.info)
        methodsToAdd += newMember
                
}






        }
        case _ => false
      }

     /* def createAnnotatedInfo(info: Source.Parser.Info): Source.Parser.Info =
        info match {
          case s: Single => s.createAnnotatedInfo(SlicingExpressionAnnotation)
          case i => violation(s"l.op.info ($i) is expected to be a Single")
        }*/

      members.foreach(checkBody)

    in.Program(
      types = p.types,
      members = p.members,
      table = p.table,
    )(p.info)
  }
}
*/